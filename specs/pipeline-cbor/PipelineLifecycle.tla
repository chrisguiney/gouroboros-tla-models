-------------------------- MODULE PipelineLifecycle --------------------------
(***************************************************************************)
(* The block pipeline's goroutines, locks and channels, one Go operation   *)
(* per step: how Submit, Stop, WaitForDrain, a parent-context cancel and   *)
(* the user's ApplyFunc interleave, and what a panic in a stage does       *)
(* (StagePanic, checked against gOuroboros 7cd17437). BlockPipeline.tla    *)
(* checks what the pipeline decides (order, failure, drain); this module   *)
(* checks whether                                                          *)
(* every goroutine can finish, whether Stop joins them, and whether the    *)
(* retained-CBOR budget comes back.                                        *)
(*                                                                         *)
(* gOuroboros 5c4f31c1 (pipeline/ is unchanged since d8f5bc2a), tagged     *)
(* [G] with pipeline.go line numbers unless a file is named:               *)
(*   submit 757-847: reserveRawCborBytes (770; waits on rawBytesFreed or   *)
(*     the contexts, 397-405), lockSubmit (783; submitGate, a 1-slot       *)
(*     channel used as a lock, 470), waitForPendingCapacity (790),         *)
(*     cancellation and stopping re-checks, trackItem (808), then a        *)
(*     select on submitChan <- item or the contexts (834-845); the gate    *)
(*     is released by defer.                                               *)
(*   worker_pool.go 117-153: a decode worker selects ctx.Done or an input  *)
(*     item, then selects output <- item or ctx.Done.                      *)
(*   apply_stage.go 460-510: the runner selects ctx.Done or an input item; *)
(*     applyPending first checks ctx (321-326), then calls ApplyFunc       *)
(*     (271, no context), markProcessed, and forwardItem (615-635), which  *)
(*     sends to resultsQueue or gives up on ctx.Done. close(done) at 464.  *)
(*   forwardResults 686-713: receive from resultsQueue, then hand the item *)
(*     to the unbuffered resultsChan and return its reservation            *)
(*     (markItemDelivered). It exits only when resultsQueue is closed.     *)
(*   Stop 958-1038, holding mu throughout: stopping, cancel (971), take    *)
(*     the gate, close submitChan, release the gate (975-979), join the    *)
(*     decode workers and close decodedChan (982-983), start a goroutine   *)
(*     that joins the runner and closes applyDone (994-998), drain         *)
(*     resultsChan until applyDone (999-1009), close resultsQueue and      *)
(*     drain until resultsDone (1013-1026), releaseActiveItems (1029),     *)
(*     wg.Wait for the metrics collector (1035).                           *)
(*   WaitForDrain 1071-1093: once stopping, it returns nil at once.        *)
(* The validate stage has the same shape as the decode stage (a worker     *)
(* pool joined, then its output closed); one stage stands for both.        *)
(*                                                                         *)
(* PR #3161 (branch fix/pipeline-reference-behaviour, 0dbc3775; merged   *)
(* to gOuroboros main as 1559924b) is switch PR3161: the forwarder always  *)
(* accepts from resultsQueue and returns the reservation at once, Stop     *)
(* joins the runner directly and waits for resultsDone, and WaitForDrain   *)
(* during Stop waits for the runner to exit (waitForApplyRunner). Main     *)
(* from 1559924b is PR3161 with NewStop and CancelCleanup off.             *)
(*                                                                         *)
(* PR #3233 (fix/pipeline-lifecycle) folds NewStop and CancelCleanup      *)
(* together on top of PR3161: Stop(ctx) and the parent-cancel watcher both *)
(* go through requestStop, which starts the one teardown goroutine; the    *)
(* watcher only requests and returns, and Stop waits for the teardown and  *)
(* the watcher. The Main configs check that combination.                   *)
(*                                                                         *)
(* No specification source: this is gOuroboros' own Go API. The reference  *)
(* counterpart, the ChainDB add-block runner (ouroboros-consensus          *)
(* ec239d57f618, Storage/ChainDB/Impl/Background.hs 755-815), is a thread  *)
(* in a resource registry: closing the ChainDB cancels it with an          *)
(* asynchronous exception, which interrupts chain selection. Go cannot     *)
(* interrupt ApplyFunc, so Stop has to wait for it.                        *)
(*                                                                         *)
(* A critical section on a leaf lock (rawBudgetMu, activeItemsMu,          *)
(* completionMu, BlockItem.mu) that does nothing blocking is one step:     *)
(* no other goroutine can see inside it. mu and submitGate, which are held *)
(* across waits, have explicit owners.                                     *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header, and   *)
(* the literal readings use README.md's "Reading a formula literally".    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,             \* how many blocks the client submits
    Cap,           \* PrefetchBufferSize: the buffer of submitChan, decodedChan, resultsQueue
    Budget,        \* MaxRawCborBytes, in blocks
    MaxPending,    \* MaxPendingBlocks
    ApplyMode,     \* what ApplyFunc does:
                   \*   "returns": it returns
                   \*   "blocks": it never returns (it has no context to watch)
                   \*   "callsStop": it calls Stop, then returns
                   \*   "callsDrain": it calls WaitForDrain with the item's context, then returns
                   \*   "callsStopOther": it calls Stop with a context that does not carry
                   \*      this pipeline's marker (for example another pipeline's)
    Reader,        \* TRUE: someone reads Results until it is closed
    OwnerStop,     \* TRUE: the owner may call Stop at any time
    SecondStop,    \* TRUE: another goroutine may also call Stop
    ParentCancel,  \* TRUE: the context passed to Start may be cancelled
    Drainer,       \* TRUE: a client calls WaitForDrain, then rolls back
    PR3161,        \* TRUE: PR #3161's forwarder, Stop and WaitForDrain
    CallbackMarker,\* TRUE: the fix: ApplyFunc's item context carries this pipeline's
                   \*   marker, and Stop or WaitForDrain given it skips the self-wait
    NewStop,       \* TRUE: the fix on fix/pipeline-callback-stop: Stop(ctx) signals,
                   \*   one teardown goroutine does the work, and Stop waits for it
                   \*   or for ctx. FALSE: Stop does the work holding mu
    StopTimeout,   \* TRUE: a waiting Stop(ctx) caller's ctx may end, so it returns
    CancelCleanup, \* TRUE: the fix on fix/pipeline-cancel-cleanup: a watcher started by
                   \*   Start tears the pipeline down when the parent context ends
    StagePanic,    \* where a stage may panic, for any block (see "Stage panics" below):
                   \*   "none"; "decode": the decode stage (or the BlockTypeResolver
                   \*   it calls); "apply": ApplyFunc (or the chain-context and
                   \*   ordered validators, guarded the same way)
    Mutation       \* "None", or a deliberate defect:
                   \*   "CloseBeforeJoin": Stop closes decodedChan without joining the workers
                   \*   "SkipRunnerJoin": Stop does not wait for the runner
                   \*   "NoReleaseActive": Stop skips releaseActiveItems
                   \*   "ReleaseTwice": Stop's Release of a drained result returns its
                   \*      budget again (no reserveOnce), clamped at zero as in
                   \*      releaseRawCborBytes 414-418
                   \*   "MarkerForAll": every Stop(ctx) caller skips the join
                   \*   "NoWatchJoin": Stop does not wait for the cancel watcher
                   \*   "LateStopUnpublished": with NewStop, only the call that
                   \*      starts the teardown publishes stopping, so a Stop after
                   \*      the watcher's teardown leaves it false (requestStop
                   \*      returning at teardownStarted before p.stopping.Store)
                   \*   "PanicUnmarked": a contained stage panic leaves the item
                   \*      looking decoded (no markUnresolvedPhase)
                   \*   "PanicLosesItem": the panicking worker exits without
                   \*      forwarding its item (recover around the loop, not the call)
                   \*   "PanicNotFatal": the runner reports a panicked item as an
                   \*      ordinary error and goes on to the next block

ASSUME ApplyMode \in {"returns", "blocks", "callsStop", "callsDrain", "callsStopOther"}
ASSUME Mutation \in {"None", "CloseBeforeJoin", "SkipRunnerJoin",
                     "NoReleaseActive", "ReleaseTwice", "MarkerForAll", "NoWatchJoin",
                     "LateStopUnpublished", "PanicUnmarked", "PanicLosesItem",
                     "PanicNotFatal"}
ASSUME StagePanic \in {"none", "decode", "apply"}

\* In English: the goroutines that may run Stop's steps: the owner, a
\* second goroutine, ApplyFunc itself ("cb"), the teardown goroutine of
\* NewStop ("td"), and the parent-cancel watcher of CancelCleanup ("watch").
\* Literally: "StopIds is defined as the set containing "owner", "second",
\*   "cb", "td" and "watch"."
StopIds == {"owner", "second", "cb", "td", "watch"}

\* In English: ApplyFunc's Stop call carries this pipeline's marker.
\* Literally: "CbMarked is defined as: ApplyMode equals "callsStop" and
\*   CallbackMarker."
CbMarked == ApplyMode = "callsStop" /\ CallbackMarker

\* Literally: "Seqs is defined as 0 through N minus 1."
Seqs == 0 .. N - 1

VARIABLES
    budget,     \* rawBytesInUse, in blocks
    active,     \* activeItems: items still holding their reservation
    subPc,      \* the submitter: "idle", "reserve", "gate", "capacity", "track", "send", "done"
    subSeq,     \* sequenceCounter: blocks accepted so far (also the next one's number)
    subHeld,    \* the submitter holds a reservation not yet given to an item
    gate,       \* submitGate's holder: "none", "sub" or "drain"
    mu,         \* BlockPipeline.mu's holder: "none" or a member of StopIds
    submitQ,    \* submitChan's buffered items
    submitClosed,
    decQ,       \* decodedChan's buffered items
    decClosed,
    resQ,       \* resultsQueue's buffered items
    resQClosed,
    resultsClosed, \* resultsChan is closed (forwardResults' defer)
    wPc,        \* the decode worker: "recv", "send", "exited"
    wItem,
    rPc,        \* the runner: "recv", "check", "apply", "applyStop", "applyDrain",
                \*   "forward", "exited"
    rItem,
    completed,  \* completedSequence
    fPc,        \* the forwarder: "select", "handoff", "exited"
    fItem,
    fPending,   \* PR3161: results accepted and not yet handed to the reader
    readerPc,   \* the Results reader: "recv" or "exited"
    stopPc,     \* stopPc[s]: where Stop called by s is
    waiterPc,   \* Stop's helper goroutine that joins the runner: "none", "waiting", "exited"
    metricsPc,  \* metricsCollector: "running" or "exited"
    canceled,   \* the pipeline context is done
    stopping,
    stopped,
    dPc,        \* the drainer: "idle", "fenceGate", "fenceWait", "waitRunner", "ok", "failed"
    dTarget,    \* the Fence boundary the drainer captured
    dBoundary,  \* blocks below this must not commit after the drainer's success
    lateCommit, \* a block below dBoundary committed after the drainer succeeded
    panicked,   \* a send on a closed channel, or a double close
    bad,        \* blocks whose stage panicked: the item carries ErrStagePanic
    fatal,      \* the runner recorded a fatal error (setFatalError) and cancelled
    parentDone, \* the context given to Start has ended
    commitLog   \* the blocks ApplyFunc committed, in commit order

\* Literally: "stV is defined as the tuple of bad, fatal, parentDone and
\*   commitLog."
stV == <<bad, fatal, parentDone, commitLog>>

\* Literally: "vars is defined as the tuple of all thirty-eight variables."
vars == <<budget, active, subPc, subSeq, subHeld, gate, mu, submitQ,
          submitClosed, decQ, decClosed, resQ, resQClosed, resultsClosed,
          wPc, wItem, rPc, rItem, completed, fPc, fItem, fPending, readerPc,
          stopPc, waiterPc, metricsPc, canceled, stopping, stopped,
          dPc, dTarget, dBoundary, lateCommit, panicked, stV>>

\* Variable groups, so each step can say what it leaves alone.
\* Literally: "subV is defined as the tuple of subPc, subSeq and subHeld."
subV == <<subPc, subSeq, subHeld>>
\* Literally: "budV is defined as the tuple of budget and active."
budV == <<budget, active>>
\* Literally: "chanV is defined as the tuple of submitQ, submitClosed, decQ,
\*   decClosed, resQ, resQClosed and resultsClosed."
chanV == <<submitQ, submitClosed, decQ, decClosed, resQ, resQClosed, resultsClosed>>
\* Literally: "wV is defined as the tuple of wPc and wItem."
wV == <<wPc, wItem>>
\* Literally: "rV is defined as the tuple of rPc, rItem and completed."
rV == <<rPc, rItem, completed>>
\* Literally: "fV is defined as the tuple of fPc, fItem, fPending and
\*   readerPc."
fV == <<fPc, fItem, fPending, readerPc>>
\* Literally: "lifeV is defined as the tuple of stopPc, waiterPc,
\*   metricsPc, canceled, stopping and stopped."
lifeV == <<stopPc, waiterPc, metricsPc, canceled, stopping, stopped>>
\* Literally: "dV is defined as the tuple of dPc, dTarget, dBoundary and
\*   lateCommit."
dV == <<dPc, dTarget, dBoundary, lateCommit>>

\* In English: Release of item i: if it still holds its reservation, the
\* reservation is returned once (reserveOnce); otherwise nothing happens.
\* Literally: "Release of i is defined as: if i is a member of active, then
\*   (active in the next state equals active without the members of the set
\*   containing i, and budget in the next state equals budget minus 1),
\*   else budV is unchanged."
Release(i) ==
    IF i \in active
      THEN /\ active' = active \ {i}
           /\ budget' = budget - 1
      ELSE UNCHANGED budV

\* In English: the variables have the shapes the comments say.
\* Literally: "TypeOK is defined as: budget is a natural number, and active
\*   is a subset of Seqs, and mu is a member of the union of the set
\*   containing "none" and StopIds, and gate is a member of the set
\*   containing "none", "sub" and "drain", and the length of submitQ, of
\*   decQ and of resQ is each less than or equal to Cap."
TypeOK ==
    /\ budget \in Nat
    /\ active \subseteq Seqs
    /\ mu \in {"none"} \cup StopIds
    /\ gate \in {"none", "sub", "drain"}
    /\ Len(submitQ) <= Cap /\ Len(decQ) <= Cap /\ Len(resQ) <= Cap
    /\ bad \subseteq Seqs

\* In English: the pipeline has just been started: every goroutine is
\* waiting for work and nothing is held.
\* Literally: "Init is defined as: budget equals 0, and active equals the
\*   empty set, and subPc equals "idle", and subSeq equals 0, and subHeld
\*   equals FALSE, and gate equals "none", and mu equals "none", and
\*   submitQ, decQ and resQ equal the empty sequence, and submitClosed,
\*   decClosed, resQClosed and resultsClosed equal FALSE, and wPc equals
\*   "recv", and wItem equals 0, and rPc equals "recv", and rItem equals 0,
\*   and completed equals 0, and fPc equals "select", and fItem equals 0,
\*   and fPending equals the empty sequence, and readerPc equals "recv",
\*   and stopPc maps every s in StopIds to (if s equals "watch" and
\*   CancelCleanup then "watchWait" else "idle"), and waiterPc equals
\*   "none", and metricsPc equals "running", and canceled, stopping and
\*   stopped equal FALSE, and dPc equals "idle", and dTarget and dBoundary
\*   equal 0, and lateCommit and panicked equal FALSE."
Init ==
    /\ budget = 0 /\ active = {}
    /\ subPc = "idle" /\ subSeq = 0 /\ subHeld = FALSE
    /\ gate = "none" /\ mu = "none"
    /\ submitQ = <<>> /\ submitClosed = FALSE
    /\ decQ = <<>> /\ decClosed = FALSE
    /\ resQ = <<>> /\ resQClosed = FALSE /\ resultsClosed = FALSE
    /\ wPc = "recv" /\ wItem = 0
    /\ rPc = "recv" /\ rItem = 0 /\ completed = 0
    /\ fPc = "select" /\ fItem = 0 /\ fPending = <<>> /\ readerPc = "recv"
    /\ stopPc = [s \in StopIds |-> IF s = "watch" /\ CancelCleanup THEN "watchWait" ELSE "idle"]
    /\ waiterPc = "none" /\ metricsPc = "running"
    /\ canceled = FALSE /\ stopping = FALSE /\ stopped = FALSE
    /\ dPc = "idle" /\ dTarget = 0 /\ dBoundary = 0 /\ lateCommit = FALSE
    /\ panicked = FALSE
    /\ bad = {} /\ fatal = FALSE /\ parentDone = FALSE /\ commitLog = <<>>

---------------------------------------------------------------------------
(* The submitter: one goroutine calling Submit for blocks 0..N-1. A Submit *)
(* that returns an error ends the client ("done").                         *)

\* In English: Submit for the next block begins.
\* Literally: "SubCall is defined as: subPc equals "idle", and subSeq is
\*   less than N, and subPc in the next state equals "reserve", and every
\*   other variable is unchanged."
SubCall ==
    /\ subPc = "idle" /\ subSeq < N
    /\ subPc' = "reserve"
    /\ UNCHANGED <<subSeq, subHeld, budV, gate, mu, chanV, wV, rV, fV, lifeV, dV, panicked, stV>>

\* In English: [G] reserveRawCborBytes: take a block's worth of budget if
\* there is room; otherwise wait until some is freed or a context ends,
\* which returns an error. When both are possible Go may do either.
\* Literally: "SubReserve is defined as: subPc equals "reserve", and either
\*   (budget is less than Budget, and budget in the next state equals
\*   budget plus 1, and subHeld in the next state equals TRUE, and subPc in
\*   the next state equals "gate") or (canceled is true, and subPc in the
\*   next state equals "done", and budget and subHeld are unchanged); and
\*   every other variable is unchanged."
SubReserve ==
    /\ subPc = "reserve"
    /\ \/ /\ budget < Budget
          /\ budget' = budget + 1 /\ subHeld' = TRUE /\ subPc' = "gate"
       \/ /\ canceled                                  \* <-p.ctx.Done()
          /\ subPc' = "done" /\ UNCHANGED <<budget, subHeld>>
    /\ UNCHANGED <<subSeq, active, gate, mu, chanV, wV, rV, fV, lifeV, dV, panicked, stV>>

\* In English: [G] lockSubmit: take submitGate, or return an error (and
\* the deferred release of the reservation) once the context is done.
\* Literally: "SubGate is defined as: subPc equals "gate", and either
\*   (canceled is not true, and gate equals "none", and gate in the next
\*   state equals "sub", and subPc in the next state equals "capacity", and
\*   budget and subHeld are unchanged) or (canceled is true, and budget in
\*   the next state equals budget minus 1, and subHeld in the next state
\*   equals FALSE, and subPc in the next state equals "done", and gate is
\*   unchanged); and every other variable is unchanged."
SubGate ==
    /\ subPc = "gate"
    /\ \/ /\ ~canceled /\ gate = "none"
          /\ gate' = "sub" /\ subPc' = "capacity"
          /\ UNCHANGED <<budget, subHeld>>
       \/ /\ canceled
          /\ budget' = budget - 1 /\ subHeld' = FALSE /\ subPc' = "done"
          /\ UNCHANGED gate
    /\ UNCHANGED <<subSeq, active, mu, chanV, wV, rV, fV, lifeV, dV, panicked, stV>>

\* In English: [G] waitForPendingCapacity, holding the gate: go on once
\* fewer than MaxPending blocks are accepted but not completed, or give up
\* (release gate and reservation) once the context is done.
\* Literally: "SubCapacity is defined as: subPc equals "capacity", and
\*   either (subSeq minus completed is less than or equal to MaxPending,
\*   and subPc in the next state equals "track", and gate, budget and
\*   subHeld are unchanged) or (canceled is true, and gate in the next
\*   state equals "none", and budget in the next state equals budget minus
\*   1, and subHeld in the next state equals FALSE, and subPc in the next
\*   state equals "done"); and every other variable is unchanged."
SubCapacity ==
    /\ subPc = "capacity"
    /\ \/ /\ subSeq - completed <= MaxPending
          /\ subPc' = "track" /\ UNCHANGED <<gate, budget, subHeld>>
       \/ /\ canceled
          /\ gate' = "none" /\ budget' = budget - 1 /\ subHeld' = FALSE
          /\ subPc' = "done"
    /\ UNCHANGED <<subSeq, active, mu, chanV, wV, rV, fV, lifeV, dV, panicked, stV>>

\* In English: [G] the cancellation and stopping checks, then trackItem:
\* the reservation now belongs to the item, in activeItems.
\* Literally: "SubTrack is defined as: subPc equals "track", and if
\*   canceled or stopping, then (gate in the next state equals "none", and
\*   budget in the next state equals budget minus 1, and subHeld in the
\*   next state equals FALSE, and subPc in the next state equals "done",
\*   and active is unchanged), else (active in the next state equals the
\*   union of active and the set containing subSeq, and subHeld in the next
\*   state equals FALSE, and subPc in the next state equals "send", and
\*   gate and budget are unchanged); and every other variable is
\*   unchanged."
SubTrack ==
    /\ subPc = "track"
    /\ IF canceled \/ stopping
         THEN /\ gate' = "none" /\ budget' = budget - 1 /\ subHeld' = FALSE
              /\ subPc' = "done" /\ UNCHANGED active
         ELSE /\ active' = active \cup {subSeq} /\ subHeld' = FALSE
              /\ subPc' = "send" /\ UNCHANGED <<gate, budget>>
    /\ UNCHANGED <<subSeq, mu, chanV, wV, rV, fV, lifeV, dV, panicked, stV>>

\* In English: [G] select { submitChan <- item; <-ctx.Done() }, then the
\* deferred unlock of the gate. A send on a closed submitChan would panic.
\* Literally: "SubSend is defined as: subPc equals "send", and either
\*   (submitClosed is not true, and the length of submitQ is less than Cap,
\*   and submitQ in the next state equals submitQ with subSeq appended, and
\*   subSeq in the next state equals subSeq plus 1, and subPc in the next
\*   state equals "idle", and budV and panicked are unchanged) or
\*   (submitClosed is true, and panicked in the next state equals TRUE, and
\*   subPc in the next state equals "done", and submitQ, subSeq and budV
\*   are unchanged) or (canceled is true, and Release of subSeq, and subPc
\*   in the next state equals "done", and submitQ, subSeq and panicked are
\*   unchanged); and gate in the next state equals "none", and every other
\*   variable is unchanged."
SubSend ==
    /\ subPc = "send"
    /\ \/ /\ ~submitClosed /\ Len(submitQ) < Cap
          /\ submitQ' = Append(submitQ, subSeq)
          /\ subSeq' = subSeq + 1 /\ subPc' = "idle"
          /\ UNCHANGED <<budV, panicked, stV>>
       \/ /\ submitClosed                          \* a send on a closed channel
          /\ panicked' = TRUE /\ subPc' = "done"
          /\ UNCHANGED <<submitQ, subSeq, budV>>
       \/ /\ canceled
          /\ Release(subSeq) /\ subPc' = "done"     \* deferred item.Release
          /\ UNCHANGED <<submitQ, subSeq, panicked, stV>>
    /\ gate' = "none"                              \* deferred unlockSubmit
    /\ UNCHANGED <<subHeld, mu, submitClosed, decQ, decClosed, resQ, resQClosed,
                   resultsClosed, wV, rV, fV, lifeV, dV, stV>>

---------------------------------------------------------------------------
(* The decode worker. *)

\* In English: [G worker_pool.go 120-126] select on ctx.Done or the input:
\* take the next item, or exit on a closed, empty input or a done context.
\* Literally: "WorkerRecv is defined as: wPc equals "recv", and either
\*   (submitQ does not equal the empty sequence, and wItem in the next state
\*   equals the head of submitQ, and submitQ in the next state equals the
\*   tail of submitQ, and wPc in the next state equals "send") or
\*   (submitQ equals the empty sequence and submitClosed is true, or
\*   canceled is true; and wPc in the next state equals "exited", and wItem
\*   and submitQ are unchanged); and every other variable is unchanged."
WorkerRecv ==
    /\ wPc = "recv"
    /\ \/ /\ submitQ /= <<>>
          /\ wItem' = Head(submitQ) /\ submitQ' = Tail(submitQ) /\ wPc' = "send"
          /\ UNCHANGED bad
       \/ /\ (submitQ = <<>> /\ submitClosed) \/ canceled
          /\ wPc' = "exited" /\ UNCHANGED <<wItem, submitQ, bad>>
    /\ UNCHANGED <<subV, budV, gate, mu, submitClosed, decQ, decClosed, resQ,
                   resQClosed, resultsClosed, rV, fV, lifeV, dV, panicked,
                   fatal, parentDone, commitLog>>

\* In English: [G worker_pool.go process, panic.go markUnresolvedPhase]
\* the decode stage panics on the item the worker holds. The deferred
\* recover turns the panic into this item's decode error (ErrStagePanic),
\* offers it to the errors channel without waiting, and the worker goes
\* on to forward the item like any other. With "PanicLosesItem" the worker
\* dies holding it (the item stays in activeItems). ("PanicUnmarked" is
\* in RunnerCheck: the runner cannot see the panic.)
\* Literally: "WorkerPanic is defined as: StagePanic equals "decode", and
\*   wPc equals "send", and wItem is not a member of bad, and bad in the
\*   next state equals bad with wItem added, and wPc in the next state
\*   equals (if Mutation equals "PanicLosesItem" then "exited", else
\*   "send"), and every other variable is unchanged."
WorkerPanic ==
    /\ StagePanic = "decode" /\ wPc = "send" /\ wItem \notin bad
    /\ bad' = bad \cup {wItem}
    /\ wPc' = IF Mutation = "PanicLosesItem" THEN "exited" ELSE "send"
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wItem, rV, fV, lifeV, dV,
                   panicked, fatal, parentDone, commitLog>>

\* In English: [G worker_pool.go 148-151] select { output <- item;
\* <-ctx.Done() }. A send on a closed output panics; on ctx.Done the worker
\* exits and the item stays in activeItems.
\* Literally: "WorkerSend is defined as: wPc equals "send", and either
\*   (decClosed is not true, and the length of decQ is less than Cap, and
\*   decQ in the next state equals decQ with wItem appended, and wPc in the
\*   next state equals "recv", and panicked is unchanged) or (decClosed is
\*   true, and panicked in the next state equals TRUE, and wPc in the next
\*   state equals "exited", and decQ is unchanged) or (canceled is true,
\*   and wPc in the next state equals "exited", and decQ and panicked are
\*   unchanged); and every other variable is unchanged."
WorkerSend ==
    /\ wPc = "send"
    /\ \/ /\ ~decClosed /\ Len(decQ) < Cap
          /\ decQ' = Append(decQ, wItem) /\ wPc' = "recv" /\ UNCHANGED panicked
       \/ /\ decClosed
          /\ panicked' = TRUE /\ wPc' = "exited" /\ UNCHANGED decQ
       \/ /\ canceled
          /\ wPc' = "exited" /\ UNCHANGED <<decQ, panicked, stV>>
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, submitClosed, decClosed, resQ,
                   resQClosed, resultsClosed, wItem, rV, fV, lifeV, dV, stV>>

---------------------------------------------------------------------------
(* The apply runner. *)

\* In English: [G apply_stage.go 470-476] select on ctx.Done or the input.
\* Literally: "RunnerRecv is defined as: rPc equals "recv", and either
\*   (decQ does not equal the empty sequence, and rItem in the next state
\*   equals the head of decQ, and decQ in the next state equals the tail of
\*   decQ, and rPc in the next state equals "check") or (decQ equals the
\*   empty sequence and decClosed is true, or canceled is true; and rPc in
\*   the next state equals "exited", and rItem and decQ are unchanged); and
\*   every other variable is unchanged."
RunnerRecv ==
    /\ rPc = "recv"
    /\ \/ /\ decQ /= <<>>
          /\ rItem' = Head(decQ) /\ decQ' = Tail(decQ) /\ rPc' = "check"
       \/ /\ (decQ = <<>> /\ decClosed) \/ canceled
          /\ rPc' = "exited" /\ UNCHANGED <<rItem, decQ>>
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, submitClosed, decClosed, resQ,
                   resQClosed, resultsClosed, wV, completed, fV, lifeV, dV, panicked, stV>>

\* In English: [G apply_stage.go run, ApplyStageRunner.fail] a rejected
\* item, here one whose stage panicked, is fatal: the runner records the
\* error (setFatalError, which Fence, WaitForDrain and Submit then
\* return), cancels the pipeline context, and returns, closing done. It
\* does not end the context given to Start, so the pipeline is torn
\* down only by Stop or by that context ending. With "PanicNotFatal" the
\* runner reports the error and takes the next item instead.
\* Literally: "RunnerFail is defined as: if Mutation equals
\*   "PanicNotFatal", then (rPc in the next state equals "recv", and
\*   canceled and fatal are unchanged), else (canceled in the next state
\*   equals TRUE, and fatal in the next state equals TRUE, and rPc in the
\*   next state equals "exited")."
RunnerFail ==
    IF Mutation = "PanicNotFatal"
      THEN rPc' = "recv" /\ UNCHANGED <<canceled, fatal>>
      ELSE canceled' = TRUE /\ fatal' = TRUE /\ rPc' = "exited"

\* In English: [G apply_stage.go 321-326] applyPending checks the context
\* first: if it is done the item is dropped (it stays in activeItems) and
\* the runner goes back to its select. [G apply_stage.go maybeApply] An
\* item that carries a stage error, here a contained panic, is rejected
\* before any callback runs (RunnerFail). Otherwise ApplyFunc is called;
\* with ApplyMode "callsStop" or "callsStopOther" it calls Stop as
\* goroutine "cb".
\* Literally: "RunnerCheck is defined as: rPc equals "check", and if
\*   canceled, then (rPc in the next state equals "recv", and stopPc,
\*   canceled and fatal are unchanged), else if rItem is a member of bad
\*   and Mutation does not equal "PanicUnmarked", then (RunnerFail, and
\*   stopPc is unchanged), else (rPc in the next state equals, in the case ApplyMode
\*   is a member of the set containing "callsStop" and "callsStopOther",
\*   "applyStop"; in the case ApplyMode equals "callsDrain", "applyDrain";
\*   in every other case, "apply"; and stopPc in the next state equals (if
\*   ApplyMode is a member of that set, then stopPc except that its "cb"
\*   entry is (if NewStop then "signal" else "lockMu"), else stopPc; and
\*   canceled and fatal are unchanged); and every other variable is
\*   unchanged."
RunnerCheck ==
    /\ rPc = "check"
    /\ IF canceled
         THEN /\ rPc' = "recv" /\ UNCHANGED <<stopPc, canceled, fatal>>
         ELSE IF rItem \in bad /\ Mutation /= "PanicUnmarked"
         THEN /\ RunnerFail /\ UNCHANGED stopPc
         ELSE /\ rPc' = CASE ApplyMode \in {"callsStop", "callsStopOther"} -> "applyStop"
                          [] ApplyMode = "callsDrain" -> "applyDrain"
                          [] OTHER -> "apply"
              /\ stopPc' = IF ApplyMode \in {"callsStop", "callsStopOther"}
                             THEN [stopPc EXCEPT !["cb"] =
                                     IF NewStop THEN "signal" ELSE "lockMu"]
                             ELSE stopPc
              /\ UNCHANGED <<canceled, fatal>>
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rItem, completed, fV,
                   waiterPc, metricsPc, stopping, stopped, dV, panicked,
                   bad, parentDone, commitLog>>

\* In English: ApplyFunc returns and the block is committed: markProcessed
\* advances completedSequence. If a drainer has already reported success
\* for a boundary above this block, the commit is late.
\* Literally: "Commit is defined as: completed in the next state equals
\*   rItem plus 1, and lateCommit in the next state equals (lateCommit, or
\*   dPc equals "ok" and rItem is less than dBoundary), and rPc in the next
\*   state equals "forward"."
Commit ==
    /\ completed' = rItem + 1
    /\ lateCommit' = (lateCommit \/ (dPc = "ok" /\ rItem < dBoundary))
    /\ commitLog' = Append(commitLog, rItem)
    /\ rPc' = "forward"

\* In English: ApplyFunc returns. With ApplyMode "blocks" it never does.
\* Literally: "RunnerApply is defined as: rPc equals "apply", and ApplyMode
\*   equals "returns", and Commit, and every other variable is unchanged."
RunnerApply ==
    /\ rPc = "apply" /\ ApplyMode = "returns"
    /\ Commit
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rItem, fV, lifeV,
                   dPc, dTarget, dBoundary, panicked, bad, fatal, parentDone>>

\* In English: [G apply_stage.go callApplyFunc] ApplyFunc panics. The
\* deferred panics.Guard turns the panic into the item's apply error, so
\* the block is not committed and the item is rejected (RunnerFail).
\* Literally: "RunnerApplyPanic is defined as: StagePanic equals "apply",
\*   and rPc equals "apply", and bad in the next state equals bad with
\*   rItem added, and RunnerFail, and every other variable is unchanged."
RunnerApplyPanic ==
    /\ StagePanic = "apply" /\ rPc = "apply"
    /\ bad' = bad \cup {rItem}
    /\ RunnerFail
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rItem, completed, fV,
                   stopPc, waiterPc, metricsPc, stopping, stopped, dV,
                   panicked, parentDone, commitLog>>

\* In English: ApplyFunc's own call to Stop has returned (joined, only
\* signalled, or given up when its ctx ended); ApplyFunc then returns.
\* Literally: "RunnerApplyStop is defined as: rPc equals "applyStop", and
\*   stopPc of "cb" is a member of the set containing "returned",
\*   "requested" and "timedOut", and Commit, and every other variable is
\*   unchanged."
RunnerApplyStop ==
    /\ rPc = "applyStop" /\ stopPc["cb"] \in {"returned", "requested", "timedOut"}
    /\ Commit
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rItem, fV, lifeV,
                   dPc, dTarget, dBoundary, panicked, bad, fatal, parentDone>>

\* In English: ApplyFunc's own WaitForDrain returns, then ApplyFunc
\* returns. Its Fence boundary includes the block being applied, so the
\* Fence can only end when the pipeline context is done. Then gOuroboros
\* returns nil (stopping) or an error; with PR3161, once Stop has begun, it
\* waits for the runner to exit, that is, for itself. With the marker,
\* PR3161 skips that wait (nil once stopping), and NewStop's
\* WaitForDrain does not wait at all (nil while stopping, an error
\* otherwise).
\* Literally: "RunnerApplyDrain is defined as: rPc equals "applyDrain", and
\*   in the case CallbackMarker and NewStop, TRUE; in the case
\*   CallbackMarker and PR3161, canceled is true or stopping is true; in the
\*   case PR3161, canceled is true and stopping is not true; in every other
\*   case, canceled is true or stopping is true; and Commit, and every other
\*   variable is unchanged."
RunnerApplyDrain ==
    /\ rPc = "applyDrain"
    /\ CASE CallbackMarker /\ NewStop -> TRUE
         [] CallbackMarker /\ PR3161 -> canceled \/ stopping
         [] PR3161 -> canceled /\ ~stopping
         [] OTHER -> canceled \/ stopping
    /\ Commit
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rItem, fV, lifeV,
                   dPc, dTarget, dBoundary, panicked, bad, fatal, parentDone>>

\* In English: [G apply_stage.go 615-635] forwardItem: send to
\* resultsQueue if it has room (tried first), else wait for room or for
\* ctx.Done; on ctx.Done the item is not forwarded and stays in
\* activeItems.
\* Literally: "RunnerForward is defined as: rPc equals "forward", and
\*   either (resQClosed is not true, and the length of resQ is less than
\*   Cap, and resQ in the next state equals resQ with rItem appended, and
\*   panicked is unchanged) or (resQClosed is true, and panicked in the next
\*   state equals TRUE, and resQ is unchanged) or (the length of resQ is
\*   not less than Cap, and resQClosed is not true, and canceled is true,
\*   and resQ and panicked are unchanged); and rPc in the next state equals
\*   "recv", and every other variable is unchanged."
RunnerForward ==
    /\ rPc = "forward"
    /\ \/ /\ ~resQClosed /\ Len(resQ) < Cap
          /\ resQ' = Append(resQ, rItem) /\ UNCHANGED panicked
       \/ /\ resQClosed
          /\ panicked' = TRUE /\ UNCHANGED resQ
       \/ /\ ~(Len(resQ) < Cap) /\ ~resQClosed /\ canceled
          /\ UNCHANGED <<resQ, panicked, stV>>
    /\ rPc' = "recv"
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, submitClosed, decQ, decClosed,
                   resQClosed, resultsClosed, wV, rItem, completed, fV, lifeV, dV, stV>>

---------------------------------------------------------------------------
(* forwardResults, and the Results reader. *)

\* In English: [G 694-699] gOuroboros: take the next queued result, or exit
\* (closing resultsChan) once resultsQueue is closed and empty. It does not
\* watch the context.
\* Literally: "FwdSelect is defined as: PR3161 is not true, and fPc equals
\*   "select", and either (resQ does not equal the empty sequence, and
\*   fItem in the next state equals the head of resQ, and resQ in the next
\*   state equals the tail of resQ, and fPc in the next state equals
\*   "handoff", and resultsClosed is unchanged) or (resQ equals the empty
\*   sequence, and resQClosed is true, and fPc in the next state equals
\*   "exited", and resultsClosed in the next state equals TRUE, and fItem
\*   and resQ are unchanged); and every other variable is unchanged."
FwdSelect ==
    /\ ~PR3161 /\ fPc = "select"
    /\ \/ /\ resQ /= <<>>
          /\ fItem' = Head(resQ) /\ resQ' = Tail(resQ) /\ fPc' = "handoff"
          /\ UNCHANGED resultsClosed
       \/ /\ resQ = <<>> /\ resQClosed
          /\ fPc' = "exited" /\ resultsClosed' = TRUE
          /\ UNCHANGED <<fItem, resQ>>
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, submitClosed, decQ, decClosed,
                   resQClosed, wV, rV, fPending, readerPc, lifeV, dV, panicked, stV>>

\* In English: [G 700-705] the unbuffered hand-off: the reader, or a Stop
\* that is draining, takes the item, and its reservation is returned
\* (markItemDelivered). The taker's own Release is then a no-op; with
\* ReleaseTwice, Stop's Release returns budget again, clamped at zero.
\* Literally: "FwdHandoff is defined as: PR3161 is not true, and fPc equals
\*   "handoff", and active in the next state equals active without the
\*   members of the set containing fItem, and, letting b be (if fItem is a
\*   member of active then budget minus 1 else budget): either (Reader,
\*   and readerPc equals "recv", and budget in the next state equals b) or
\*   (there exists an s in StopIds such that stopPc of s is a member of the
\*   set containing "drainApply" and "drainDone", and budget in the next
\*   state equals (if Mutation equals "ReleaseTwice" then (if b is greater
\*   than 0 then b minus 1 else 0) else b)); and fPc in the next state
\*   equals "select", and every other variable is unchanged."
FwdHandoff ==
    /\ ~PR3161 /\ fPc = "handoff"
    /\ active' = active \ {fItem}
    /\ LET b == IF fItem \in active THEN budget - 1 ELSE budget
       IN \/ /\ Reader /\ readerPc = "recv"                  \* the reader takes it
             /\ budget' = b
          \/ /\ \E s \in StopIds : stopPc[s] \in {"drainApply", "drainDone"}
             /\ budget' = IF Mutation = "ReleaseTwice"         \* Stop takes it
                            THEN (IF b > 0 THEN b - 1 ELSE 0)
                            ELSE b
    /\ fPc' = "select"
    /\ UNCHANGED <<subV, gate, mu, chanV, wV, rV, fItem, fPending, readerPc,
                   lifeV, dV, panicked, stV>>

\* In English: PR #3161's forwarder: accept a queued result at once,
\* returning its reservation; hand the oldest accepted result to the
\* reader; or, once resultsQueue is closed and empty, release what is left
\* and exit. It notices the context but still exits only on the close.
\* Literally: "FwdPR is defined as: PR3161, and fPc equals "select", and
\*   either (resQ does not equal the empty sequence, and Release of the
\*   head of resQ, and fPending in the next state equals fPending with the
\*   head of resQ appended, and resQ in the next state equals the tail of
\*   resQ, and fPc and resultsClosed are unchanged) or (fPending does not
\*   equal the empty sequence, and Reader, and readerPc equals "recv", and
\*   fPending in the next state equals the tail of fPending, and budV, resQ,
\*   fPc and resultsClosed are unchanged) or (resQ equals the empty
\*   sequence, and resQClosed is true, and fPending in the next state
\*   equals the empty sequence, and fPc in the next state equals "exited",
\*   and resultsClosed in the next state equals TRUE, and budV and resQ are
\*   unchanged); and every other variable is unchanged."
FwdPR ==
    /\ PR3161 /\ fPc = "select"
    /\ \/ /\ resQ /= <<>>
          /\ Release(Head(resQ))
          /\ fPending' = Append(fPending, Head(resQ)) /\ resQ' = Tail(resQ)
          /\ UNCHANGED <<fPc, resultsClosed>>
       \/ /\ fPending /= <<>> /\ Reader /\ readerPc = "recv"
          /\ fPending' = Tail(fPending)
          /\ UNCHANGED <<budV, resQ, fPc, resultsClosed>>
       \/ /\ resQ = <<>> /\ resQClosed
          /\ fPending' = <<>> /\ fPc' = "exited" /\ resultsClosed' = TRUE
          /\ UNCHANGED <<budV, resQ>>
    /\ UNCHANGED <<subV, gate, mu, submitQ, submitClosed, decQ, decClosed,
                   resQClosed, wV, rV, fItem, readerPc, lifeV, dV, panicked, stV>>

\* In English: the reader's range over Results ends when it is closed.
\* Literally: "ReaderExit is defined as: Reader, and readerPc equals
\*   "recv", and resultsClosed is true, and readerPc in the next state
\*   equals "exited", and every other variable is unchanged."
ReaderExit ==
    /\ Reader /\ readerPc = "recv" /\ resultsClosed
    /\ readerPc' = "exited"
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fPc, fItem, fPending,
                   lifeV, dV, panicked, stV>>

---------------------------------------------------------------------------
(* Stop, the goroutine it starts, the metrics collector, and the parent   *)
(* context. *)

\* In English: the owner, or the second goroutine, calls Stop.
\* Literally: "StopCall of s is defined as: s is a member of the set
\*   containing "owner" and "second", and (s equals "owner" and OwnerStop,
\*   or s equals "second" and SecondStop), and stopPc of s equals "idle",
\*   and stopPc in the next state equals stopPc except that its s entry is
\*   (if NewStop then "signal" else "lockMu"), and every other variable is
\*   unchanged."
StopCall(s) ==
    /\ s \in {"owner", "second"}
    /\ (s = "owner" /\ OwnerStop) \/ (s = "second" /\ SecondStop)
    /\ stopPc[s] = "idle"
    /\ stopPc' = [stopPc EXCEPT ![s] = IF NewStop THEN "signal" ELSE "lockMu"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc,
                   metricsPc, canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 959-964] p.mu.Lock(); a pipeline already stopped
\* unlocks at once, and then (CancelCleanup) waits for the watcher; the
\* watcher itself just exits.
\* Literally: "StopLock of s is defined as: stopPc of s equals "lockMu",
\*   and mu equals "none", and if stopped, then (stopPc in the next state
\*   equals stopPc except that its s entry is (if s equals "watch" then
\*   "exited" else "joinWatch"), and mu is unchanged), else (mu in the next
\*   state equals s, and stopPc in the next state equals stopPc except that
\*   its s entry is "cancel"); and every other variable is unchanged."
StopLock(s) ==
    /\ stopPc[s] = "lockMu" /\ mu = "none"
    /\ IF stopped
         THEN /\ stopPc' = [stopPc EXCEPT ![s] = IF s = "watch" THEN "exited" ELSE "joinWatch"]
              /\ UNCHANGED mu
         ELSE /\ mu' = s /\ stopPc' = [stopPc EXCEPT ![s] = "cancel"]
    /\ UNCHANGED <<subV, budV, gate, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 968-971] stopping, then cancel. The cancel watcher does
\* not set stopping: no explicit Stop was asked for, so a drain still
\* reports the cancellation as an error.
\* Literally: "StopCancel of s is defined as: stopPc of s equals "cancel",
\*   and stopping in the next state equals (stopping, or s does not equal
\*   "watch"), and canceled in the next state equals TRUE, and stopPc in the
\*   next state equals stopPc except that its s entry is "gate", and every
\*   other variable is unchanged."
StopCancel(s) ==
    /\ stopPc[s] = "cancel"
    /\ stopping' = (stopping \/ s /= "watch") /\ canceled' = TRUE
    /\ stopPc' = [stopPc EXCEPT ![s] = "gate"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc,
                   metricsPc, stopped, dV, panicked, stV>>

\* In English: [G 975-979] take the gate (so no Submit is mid-send), set
\* stopped, close submitChan, give the gate back.
\* Literally: "StopGate of s is defined as: stopPc of s equals "gate", and
\*   gate equals "none", and stopped in the next state equals TRUE, and
\*   submitClosed in the next state equals TRUE, and panicked in the next
\*   state equals (panicked or submitClosed), and stopPc in the next state
\*   equals stopPc except that its s entry is "joinDecode", and every other
\*   variable is unchanged."
StopGate(s) ==
    /\ stopPc[s] = "gate" /\ gate = "none"
    /\ stopped' = TRUE
    /\ submitClosed' = TRUE
    /\ panicked' = (panicked \/ submitClosed)       \* a double close panics
    /\ stopPc' = [stopPc EXCEPT ![s] = "joinDecode"]
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, decQ, decClosed, resQ,
                   resQClosed, resultsClosed, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, dV, stV>>

\* In English: [G 982-983] decodePool.Stop joins the workers, then
\* decodedChan is closed. CloseBeforeJoin does not wait.
\* Literally: "StopJoinDecode of s is defined as: stopPc of s equals
\*   "joinDecode", and (wPc equals "exited" or Mutation equals
\*   "CloseBeforeJoin"), and decClosed in the next state equals TRUE, and
\*   stopPc in the next state equals stopPc except that its s entry is (if
\*   PR3161 then "joinRunner" else "spawn"), and every other variable is
\*   unchanged."
StopJoinDecode(s) ==
    /\ stopPc[s] = "joinDecode"
    /\ wPc = "exited" \/ Mutation = "CloseBeforeJoin"
    /\ decClosed' = TRUE
    /\ stopPc' = [stopPc EXCEPT ![s] = IF PR3161 THEN "joinRunner" ELSE "spawn"]
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, submitClosed, decQ, resQ,
                   resQClosed, resultsClosed, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 994-998] start the goroutine that joins the runner.
\* Literally: "StopSpawn of s is defined as: stopPc of s equals "spawn",
\*   and waiterPc in the next state equals "waiting", and stopPc in the
\*   next state equals stopPc except that its s entry is "drainApply", and
\*   every other variable is unchanged."
StopSpawn(s) ==
    /\ stopPc[s] = "spawn"
    /\ waiterPc' = "waiting"
    /\ stopPc' = [stopPc EXCEPT ![s] = "drainApply"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G apply_stage.go 457, 464] the helper's applyRunner.Stop
\* returns once the runner has closed done; then it closes applyDone.
\* Literally: "WaiterDone is defined as: waiterPc equals "waiting", and rPc
\*   equals "exited", and waiterPc in the next state equals "exited", and
\*   every other variable is unchanged."
WaiterDone ==
    /\ waiterPc = "waiting" /\ rPc = "exited"
    /\ waiterPc' = "exited"
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, stopPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 999-1009] Stop leaves its draining loop once applyDone is
\* closed (the hand-offs it takes meanwhile are FwdHandoff steps). With
\* PR3161, [PR] Stop calls applyRunner.Stop directly. SkipRunnerJoin does
\* not wait.
\* Literally: "StopJoinRunner of s is defined as: (stopPc of s equals
\*   "drainApply" and (waiterPc equals "exited" or Mutation equals
\*   "SkipRunnerJoin")) or (stopPc of s equals "joinRunner" and (rPc equals
\*   "exited" or Mutation equals "SkipRunnerJoin")); and stopPc in the next
\*   state equals stopPc except that its s entry is "closeQueue", and every
\*   other variable is unchanged."
StopJoinRunner(s) ==
    /\ \/ stopPc[s] = "drainApply" /\ (waiterPc = "exited" \/ Mutation = "SkipRunnerJoin")
       \/ stopPc[s] = "joinRunner" /\ (rPc = "exited" \/ Mutation = "SkipRunnerJoin")
    /\ stopPc' = [stopPc EXCEPT ![s] = "closeQueue"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 1014] close(resultsQueue).
\* Literally: "StopCloseQueue of s is defined as: stopPc of s equals
\*   "closeQueue", and resQClosed in the next state equals TRUE, and
\*   panicked in the next state equals (panicked or resQClosed), and stopPc
\*   in the next state equals stopPc except that its s entry is
\*   "drainDone", and every other variable is unchanged."
StopCloseQueue(s) ==
    /\ stopPc[s] = "closeQueue"
    /\ resQClosed' = TRUE
    /\ panicked' = (panicked \/ resQClosed)
    /\ stopPc' = [stopPc EXCEPT ![s] = "drainDone"]
    /\ UNCHANGED <<subV, budV, gate, mu, submitQ, submitClosed, decQ, decClosed,
                   resQ, resultsClosed, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, stV>>

\* In English: [G 1015-1025] keep draining until resultsDone is closed
\* (the forwarder has exited).
\* Literally: "StopDrainDone of s is defined as: stopPc of s equals
\*   "drainDone", and fPc equals "exited", and stopPc in the next state
\*   equals stopPc except that its s entry is "releaseActive", and every
\*   other variable is unchanged."
StopDrainDone(s) ==
    /\ stopPc[s] = "drainDone" /\ fPc = "exited"
    /\ stopPc' = [stopPc EXCEPT ![s] = "releaseActive"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 1029, 439-449] releaseActiveItems: every item still
\* holding its reservation returns it (items stranded in the channels by
\* the cancel). NoReleaseActive skips it.
\* Literally: "StopReleaseActive of s is defined as: stopPc of s equals
\*   "releaseActive", and if Mutation equals "NoReleaseActive", then budV is
\*   unchanged, else (budget in the next state equals budget minus the
\*   number of members of active, and active in the next state equals the
\*   empty set); and stopPc in the next state equals stopPc except that its
\*   s entry is "wgWait", and every other variable is unchanged."
StopReleaseActive(s) ==
    /\ stopPc[s] = "releaseActive"
    /\ IF Mutation = "NoReleaseActive"
         THEN UNCHANGED budV
         ELSE /\ budget' = budget - Cardinality(active) /\ active' = {}
    /\ stopPc' = [stopPc EXCEPT ![s] = "wgWait"]
    /\ UNCHANGED <<subV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 1035-1037] wg.Wait for the metrics collector, then the
\* unlock of mu. The watcher and the teardown goroutine are then done; a
\* Stop caller goes on to join the watcher.
\* Literally: "StopReturn of s is defined as: stopPc of s equals "wgWait",
\*   and metricsPc equals "exited", and mu in the next state equals (if mu
\*   equals s then "none" else mu), and stopPc in the next state equals
\*   stopPc except that its s entry is (if s is a member of the set
\*   containing "watch" and "td" then "returned" else "joinWatch"), and
\*   every other variable is unchanged."
StopReturn(s) ==
    /\ stopPc[s] = "wgWait" /\ metricsPc = "exited"
    /\ mu' = IF mu = s THEN "none" ELSE mu
    /\ stopPc' = [stopPc EXCEPT ![s] = IF s \in {"watch", "td"} THEN "returned" ELSE "joinWatch"]
    /\ UNCHANGED <<subV, budV, gate, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [fix/pipeline-cancel-cleanup] after unlocking mu, Stop waits
\* for the cancel watcher to exit, so the watcher is joined too. Without
\* CancelCleanup there is no watcher and this step is immediate.
\* Literally: "StopJoinWatch of s is defined as: stopPc of s equals
\*   "joinWatch", and (stopPc of "watch" is a member of the set containing
\*   "idle", "exited" and "returned", or Mutation equals "NoWatchJoin"), and
\*   stopPc in the next state equals stopPc except that its s entry is
\*   "returned", and every other variable is unchanged."
StopJoinWatch(s) ==
    /\ stopPc[s] = "joinWatch"
    /\ stopPc["watch"] \in {"idle", "exited", "returned"} \/ Mutation = "NoWatchJoin"
    /\ stopPc' = [stopPc EXCEPT ![s] = "returned"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [fix/pipeline-cancel-cleanup] the watcher wakes when the
\* pipeline context is done. If an explicit Stop has begun it exits;
\* otherwise it runs Stop's teardown itself. With NewStop (PR #3233,
\* watchParentCancel and requestStop(false)) it never runs the teardown
\* itself: it starts the teardown goroutine unless an explicit Stop has
\* begun or the teardown has already started, and exits. It watches the
\* context given to Start and Stop's signal, not the pipeline context, so
\* a fatal error's cancel alone does not wake it.
\* Literally: "WatchWake is defined as: stopPc of "watch" equals
\*   "watchWait", and canceled is true, and (fatal is not true, or
\*   parentDone is true, or stopping is true), and stopPc in the next state equals:
\*   if NewStop, then stopPc except that its "watch" entry is "exited" and
\*   its "td" entry is (if stopping or the old entry does not equal "idle"
\*   then the old entry else "gate"); else stopPc except that its "watch"
\*   entry is (if stopping then "exited" else "lockMu"); and every other
\*   variable is unchanged."
WatchWake ==
    /\ stopPc["watch"] = "watchWait" /\ canceled
    /\ ~fatal \/ parentDone \/ stopping      \* a fatal cancel alone does not wake it
    /\ stopPc' = IF NewStop
                   THEN [stopPc EXCEPT !["watch"] = "exited",
                                       !["td"] = IF stopping \/ @ /= "idle" THEN @ ELSE "gate"]
                   ELSE [stopPc EXCEPT !["watch"] = IF stopping THEN "exited" ELSE "lockMu"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [fix/pipeline-callback-stop] Stop(ctx) signals: stopping,
\* cancel, and start the one teardown goroutine if it has not started. A
\* caller whose ctx carries this pipeline's ApplyFunc marker returns at
\* once (it may be the runner itself); any other caller waits.
\* Every explicit Stop publishes stopping, even one that finds the teardown
\* already started by the watcher, so Start and WaitForDrain see the stop.
\* LateStopUnpublished publishes it only from the call that starts the
\* teardown, so after the watcher has started it a later Stop leaves
\* stopping false.
\* Literally: "StopSignal of s is defined as: stopPc of s equals "signal",
\*   and stopping in the next state equals (stopping, or stopPc of "td"
\*   equals "idle", or Mutation does not equal "LateStopUnpublished"), and
\*   canceled in the next
\*   state equals TRUE, and stopPc in the next state equals stopPc except
\*   that its s entry is (if (s equals "cb" and CbMarked) or Mutation
\*   equals "MarkerForAll" then "requested" else "waitTd"), and its "td"
\*   entry is (if the old entry equals "idle" then "gate" else the old
\*   entry), and every other variable is unchanged."
StopSignal(s) ==
    /\ stopPc[s] = "signal"
    /\ stopping' = (stopping \/ stopPc["td"] = "idle"
                    \/ Mutation /= "LateStopUnpublished")
    /\ canceled' = TRUE
    /\ stopPc' = [stopPc EXCEPT
                    ![s] = IF (s = "cb" /\ CbMarked) \/ Mutation = "MarkerForAll"
                             THEN "requested" ELSE "waitTd",
                    !["td"] = IF @ = "idle" THEN "gate" ELSE @]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   stopped, dV, panicked, stV>>

\* In English: [fix/pipeline-callback-stop] a waiting Stop(ctx) returns nil
\* once the teardown goroutine has finished, or ctx.Err() once its ctx
\* ends (with StopTimeout).
\* With CancelCleanup (PR #3233) it also waits for the watcher, as Stop
\* waits for watcherDone after teardownDone; NoWatchJoin does not.
\* Literally: "StopWaitTd of s is defined as: stopPc of s equals "waitTd",
\*   and either (stopPc of "td" equals "returned", and (stopPc of "watch"
\*   is a member of the set containing "idle", "exited" and "returned", or
\*   Mutation equals "NoWatchJoin"), and stopPc in the next state equals
\*   stopPc except that its s entry is "returned") or
\*   (StopTimeout and stopPc in the next state equals stopPc except that
\*   its s entry is "timedOut"); and every other variable is unchanged."
StopWaitTd(s) ==
    /\ stopPc[s] = "waitTd"
    /\ \/ /\ stopPc["td"] = "returned"
          /\ stopPc["watch"] \in {"idle", "exited", "returned"} \/ Mutation = "NoWatchJoin"
          /\ stopPc' = [stopPc EXCEPT ![s] = "returned"]
       \/ StopTimeout /\ stopPc' = [stopPc EXCEPT ![s] = "timedOut"]
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, waiterPc, metricsPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: [G 1097-1107] the metrics collector exits once the context
\* is done.
\* Literally: "MetricsExit is defined as: metricsPc equals "running", and
\*   canceled is true, and metricsPc in the next state equals "exited", and
\*   every other variable is unchanged."
MetricsExit ==
    /\ metricsPc = "running" /\ canceled
    /\ metricsPc' = "exited"
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, stopPc, waiterPc,
                   canceled, stopping, stopped, dV, panicked, stV>>

\* In English: the context given to Start is cancelled, without Stop.
\* A fatal error has already cancelled the pipeline context but not this
\* one, so after a fatal error it can still end.
\* Literally: "CancelParent is defined as: ParentCancel, and parentDone is
\*   not true, and (canceled is not true, or fatal is true), and canceled
\*   and parentDone in the next state equal TRUE, and every other variable
\*   is unchanged."
CancelParent ==
    /\ ParentCancel /\ ~parentDone /\ (~canceled \/ fatal)
    /\ canceled' = TRUE /\ parentDone' = TRUE
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, stopPc, waiterPc,
                   metricsPc, stopping, stopped, dV, panicked, bad, fatal,
                   commitLog>>

---------------------------------------------------------------------------
(* The drainer: WaitForDrain(Background), then a rollback. *)

\* In English: the drainer's success: blocks below boundary b must not be
\* committed from now on.
\* Literally: "DrainOK of b is defined as: dPc in the next state equals
\*   "ok", and dBoundary in the next state equals b."
DrainOK(b) == dPc' = "ok" /\ dBoundary' = b

\* In English: [G 1078-1089] once Stop has begun, gOuroboros returns nil
\* at once (nothing may commit after that); PR #3161 first waits for the
\* runner. A context done without Stop is an error.
\* Literally: "DrainStopped is defined as: if stopping, then (if PR3161
\*   then (dPc in the next state equals "waitRunner" and dBoundary is
\*   unchanged) else DrainOK of N), else (dPc in the next state equals
\*   "failed" and dBoundary is unchanged)."
DrainStopped ==
    IF stopping
      THEN IF PR3161 THEN dPc' = "waitRunner" /\ UNCHANGED dBoundary
                     ELSE DrainOK(N)
      ELSE dPc' = "failed" /\ UNCHANGED dBoundary

\* In English: WaitForDrain begins: if Stop has begun, see DrainStopped;
\* otherwise go to Fence.
\* Literally: "DrainCall is defined as: Drainer, and dPc equals "idle", and
\*   if stopping, then DrainStopped, else (dPc in the next state equals
\*   "fenceGate" and dBoundary is unchanged); and every other variable is
\*   unchanged."
DrainCall ==
    /\ Drainer /\ dPc = "idle"
    /\ IF stopping THEN DrainStopped
                   ELSE dPc' = "fenceGate" /\ UNCHANGED dBoundary
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, lifeV, dTarget,
                   lateCommit, panicked, stV>>

\* In English: [G 866-875] Fence takes the gate, reads sequenceCounter as
\* its target and gives the gate back (no wait in between); or the
\* context is done.
\* Literally: "DrainGate is defined as: dPc equals "fenceGate", and either
\*   (canceled is not true, and gate equals "none", and dTarget in the next
\*   state equals subSeq, and dPc in the next state equals "fenceWait", and
\*   dBoundary is unchanged) or (canceled is true, and DrainStopped, and
\*   dTarget is unchanged); and every other variable is unchanged."
DrainGate ==
    /\ dPc = "fenceGate"
    /\ \/ /\ ~canceled /\ gate = "none"
          /\ dTarget' = subSeq /\ dPc' = "fenceWait" /\ UNCHANGED dBoundary
       \/ /\ canceled /\ DrainStopped /\ UNCHANGED dTarget
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, lifeV,
                   lateCommit, panicked, stV>>

\* In English: [G 880-899] the Fence returns once completedSequence reaches
\* its target (success, with that boundary, unless Stop has begun), or
\* once the context is done.
\* Literally: "DrainWait is defined as: dPc equals "fenceWait", and either
\*   (completed is greater than or equal to dTarget, and if stopping and
\*   PR3161 then (dPc in the next state equals "waitRunner" and dBoundary is
\*   unchanged) else DrainOK of dTarget) or (canceled is true and
\*   DrainStopped); and every other variable is unchanged."
DrainWait ==
    /\ dPc = "fenceWait"
    /\ \/ /\ completed >= dTarget
          /\ IF stopping /\ PR3161
               THEN dPc' = "waitRunner" /\ UNCHANGED dBoundary
               ELSE DrainOK(dTarget)
       \/ canceled /\ DrainStopped
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, lifeV, dTarget,
                   lateCommit, panicked, stV>>

\* In English: [PR] waitForApplyRunner returns once the runner has exited.
\* Literally: "DrainWaitRunner is defined as: dPc equals "waitRunner", and
\*   rPc equals "exited", and DrainOK of N, and every other variable is
\*   unchanged."
DrainWaitRunner ==
    /\ dPc = "waitRunner" /\ rPc = "exited"
    /\ DrainOK(N)
    /\ UNCHANGED <<subV, budV, gate, mu, chanV, wV, rV, fV, lifeV, dTarget,
                   lateCommit, panicked, stV>>

---------------------------------------------------------------------------

\* In English: no API call is left waiting: every Stop has returned or was
\* never called, the submitter and the drainer are finished, and ApplyFunc
\* is not inside a call back into the pipeline. Goroutines the pipeline
\* started may still be parked; NoLeakWhenQuiescent judges those.
\* Literally: "CallersFinished is defined as: for all s in StopIds, stopPc
\*   of s is a member of the set containing "idle", "returned",
\*   "requested", "timedOut", "exited" and "watchWait"; and
\*   (subPc equals "done", or subPc equals "idle" and subSeq equals N); and
\*   dPc is a member of the set containing "idle", "ok" and "failed"; and
\*   rPc is not a member of the set containing "applyStop" and
\*   "applyDrain"."
CallersFinished ==
    /\ \A s \in StopIds :
         stopPc[s] \in {"idle", "returned", "requested", "timedOut", "exited", "watchWait"}
    /\ subPc = "done" \/ (subPc = "idle" /\ subSeq = N)
    /\ dPc \in {"idle", "ok", "failed"}
    /\ rPc \notin {"applyStop", "applyDrain"}

\* Literally: "Progress is defined as: SubCall, or SubReserve, or SubGate,
\*   or SubCapacity, or SubTrack, or SubSend, or WorkerRecv, or WorkerSend,
\*   or RunnerRecv, or RunnerCheck, or RunnerApply, or RunnerApplyStop, or
\*   RunnerApplyDrain, or RunnerForward, or FwdSelect, or FwdHandoff, or
\*   FwdPR, or ReaderExit, or WaiterDone, or MetricsExit, or DrainCall, or
\*   DrainGate, or DrainWait, or DrainWaitRunner, or there exists an s in
\*   StopIds such that StopCall of s, or StopLock of s, or StopCancel of s,
\*   or StopGate of s, or StopJoinDecode of s, or StopSpawn of s, or
\*   StopJoinRunner of s, or StopCloseQueue of s, or StopDrainDone of s, or
\*   StopReleaseActive of s, or StopReturn of s, or StopJoinWatch of s, or
\*   StopSignal of s, or StopWaitTd of s; or WatchWake."
Progress ==
    \/ SubCall \/ SubReserve \/ SubGate \/ SubCapacity \/ SubTrack \/ SubSend
    \/ WorkerRecv \/ WorkerSend
    \/ WorkerPanic \/ RunnerApplyPanic
    \/ RunnerRecv \/ RunnerCheck \/ RunnerApply \/ RunnerApplyStop
    \/ RunnerApplyDrain \/ RunnerForward
    \/ FwdSelect \/ FwdHandoff \/ FwdPR \/ ReaderExit
    \/ WaiterDone \/ MetricsExit
    \/ DrainCall \/ DrainGate \/ DrainWait \/ DrainWaitRunner
    \/ \E s \in StopIds :
         \/ StopCall(s) \/ StopLock(s) \/ StopCancel(s) \/ StopGate(s)
         \/ StopJoinDecode(s) \/ StopSpawn(s) \/ StopJoinRunner(s)
         \/ StopCloseQueue(s) \/ StopDrainDone(s) \/ StopReleaseActive(s)
         \/ StopReturn(s) \/ StopJoinWatch(s) \/ StopSignal(s) \/ StopWaitTd(s)
    \/ WatchWake

\* In English: nothing can move, but no caller is waiting: a legitimate
\* end. Any other state with no step is a deadlock that TLC reports.
\* Literally: "Rest is defined as: Progress is not enabled, and
\*   CallersFinished, and vars is unchanged."
Rest == ~ENABLED Progress /\ CallersFinished /\ UNCHANGED vars

\* Literally: "Next is defined as: Progress or CancelParent or Rest."
Next == Progress \/ CancelParent \/ Rest

\* Literally: "Spec is defined as: Init, and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties. *)

\* In English: nothing sends on a closed channel or closes one twice.
\* Literally: "NoPanic is defined as: panicked is not true."
NoPanic == ~panicked

\* In English: rawBytesInUse is exactly the reservations held: one per
\* item in activeItems, plus the submitter's not yet given to an item.
\* Literally: "BudgetMatchesActive is defined as: budget equals the number
\*   of members of active, plus (if subHeld then 1 else 0)."
BudgetMatchesActive ==
    budget = Cardinality(active) + (IF subHeld THEN 1 ELSE 0)

\* In English: some Stop has returned nil as a join: any caller that
\* finished, or a caller other than ApplyFunc's own that returned without
\* waiting. Only ApplyFunc's marked call may return without the join.
\* Literally: "StopReturned is defined as: there exists an s in StopIds
\*   such that stopPc of s equals "returned", or s does not equal "cb" and
\*   stopPc of s equals "requested"."
StopReturned ==
    \E s \in StopIds :
        stopPc[s] = "returned" \/ (s /= "cb" /\ stopPc[s] = "requested")

\* In English: once Stop has returned, no item holds a reservation and the
\* only budget in use is a Submit's that has not yet seen the stop.
\* Literally: "AllReleasedAfterStop is defined as: if StopReturned, then
\*   active equals the empty set and budget equals (if subHeld then 1 else
\*   0)."
AllReleasedAfterStop ==
    StopReturned => (active = {} /\ budget = IF subHeld THEN 1 ELSE 0)

\* In English: a Stop caller, not the teardown goroutine, has returned nil
\* as a join. The teardown goroutine finishing joins the pipeline's
\* workers but not the cancel watcher, which the caller joins after it.
\* Literally: "CallerReturned is defined as: there exists an s in StopIds
\*   other than "td" such that stopPc of s equals "returned", or s does not
\*   equal "cb" and stopPc of s equals "requested"."
CallerReturned ==
    \E s \in StopIds \ {"td"} :
        stopPc[s] = "returned" \/ (s /= "cb" /\ stopPc[s] = "requested")

\* In English: once Stop has returned nil, every goroutine Start or Stop
\* started has exited (the join), and once a Stop caller has returned, the
\* cancel watcher has exited too.
\* Literally: "JoinedAfterStop is defined as: (if StopReturned, then wPc
\*   equals "exited", and rPc equals "exited", and fPc equals "exited", and
\*   metricsPc equals "exited", and waiterPc does not equal "waiting"), and
\*   (if CallerReturned, then stopPc of "watch" is a member of the set
\*   containing "idle", "exited" and "returned")."
JoinedAfterStop ==
    /\ StopReturned =>
          /\ wPc = "exited" /\ rPc = "exited" /\ fPc = "exited"
          /\ metricsPc = "exited" /\ waiterPc /= "waiting"
    /\ CallerReturned => stopPc["watch"] \in {"idle", "exited", "returned"}

\* In English: after a successful WaitForDrain, no block below its boundary
\* is committed.
\* Literally: "NoCommitAfterDrain is defined as: lateCommit is not true."
NoCommitAfterDrain == ~lateCommit

\* In English: when nothing can move and the context is done, the
\* forwarder has exited and no item holds a reservation. A fatal error
\* alone does not count: by design [G watchParentCancel] the pipeline
\* then keeps its committed results, and the items it held, until Stop
\* or the end of the context given to Start (MainFatalHoldsProbeBug shows it).
\* Literally: "CancelEnded is defined as: canceled is true, and (fatal is
\*   not true, or parentDone is true, or stopping is true)."
CancelEnded == canceled /\ (~fatal \/ parentDone \/ stopping)

\* Literally: "NoLeakWhenQuiescent is defined as: if Progress is not
\*   enabled and CancelEnded, then fPc equals "exited" and active equals
\*   the empty set."
NoLeakWhenQuiescent ==
    (~ENABLED Progress /\ CancelEnded) => (fPc = "exited" /\ active = {})

\* In English: Stop never holds mu while it waits for a runner that is
\* inside ApplyFunc. Expected to be violated: this is how Stop works.
\* Literally: "MuNotHeldAcrossApply is defined as: there does not exist an
\*   s in StopIds such that mu equals s and stopPc of s is a member of the
\*   set containing "drainApply" and "joinRunner" and rPc is a member of
\*   the set containing "apply", "applyStop" and "applyDrain"."
MuNotHeldAcrossApply ==
    ~\E s \in StopIds :
        /\ mu = s /\ stopPc[s] \in {"drainApply", "joinRunner"}
        /\ rPc \in {"apply", "applyStop", "applyDrain"}

\* Probe, expected to be violated: "Stop never waits for the gate while a
\* Submit holds it".
\* Literally: "ProbeNoGateWait is defined as: there does not exist an s in
\*   StopIds such that stopPc of s equals "gate" and gate equals "sub"."
ProbeNoGateWait == ~\E s \in StopIds : stopPc[s] = "gate" /\ gate = "sub"

\* Probe, expected to be violated: "Stop never takes a result from the
\* forwarder" (gOuroboros' Stop drains Results while it waits).
\* Literally: "ProbeNoStopDrain is defined as: there does not exist an s in
\*   StopIds such that stopPc of s equals "drainApply" and fPc equals
\*   "handoff" and Reader is not true."
ProbeNoStopDrain ==
    ~\E s \in StopIds : stopPc[s] = "drainApply" /\ fPc = "handoff" /\ ~Reader

\* In English: with NewStop, once an explicit Stop has signalled, the
\* pipeline records that Stop has begun, so a later Start returns
\* ErrPipelineStopped and WaitForDrain does not report the stop as a
\* cancellation.
\* Literally: "StopPublished is defined as: if NewStop, then for all s in the
\*   set containing "owner", "second" and "cb", if stopPc of s is a member of
\*   the set containing "waitTd", "requested", "returned" and "timedOut",
\*   then stopping."
StopPublished ==
    NewStop =>
        \A s \in {"owner", "second", "cb"} :
            stopPc[s] \in {"waitTd", "requested", "returned", "timedOut"} => stopping

---------------------------------------------------------------------------
(* Stage panics.                                                           *)

\* In English: ApplyFunc commits blocks in submission order, each once.
\* Literally: "AppliedInOrderOnce is defined as: for every i in 1 through
\*   the length of commitLog, entry i of commitLog equals i minus 1."
AppliedInOrderOnce ==
    \A i \in 1 .. Len(commitLog) : commitLog[i] = i - 1

\* In English: no block whose stage panicked is committed, and no block
\* after it is either.
\* Literally: "NoApplyAfterPanic is defined as: for every b in bad and
\*   every i in 1 through the length of commitLog, entry i of commitLog is
\*   less than b."
NoApplyAfterPanic ==
    \A b \in bad : \A i \in 1 .. Len(commitLog) : commitLog[i] < b

\* In English: Fence and WaitForDrain never report success over a block
\* whose stage panicked; the panic reaches the caller as their error.
\* (Once Stop has begun, WaitForDrain succeeds without a boundary.)
\* Literally: "PanicFailsDrain is defined as: if dPc equals "ok" and
\*   stopping is not true, then every b in bad is at least dBoundary."
PanicFailsDrain ==
    (dPc = "ok" /\ ~stopping) => \A b \in bad : b >= dBoundary

\* In English: a probe: a panicked block reaches the runner and is
\* reported, so the properties above are not vacuous.
\* Literally: "ProbeNoFatalPanic is defined as: fatal is not true."
ProbeNoFatalPanic == ~fatal

\* In English: a probe: after a fatal panic with no Stop and no parent
\* cancel, nothing moves and items still hold their reservations, the
\* documented hold until Stop.
\* Literally: "ProbeNothingHeldWhenStuck is defined as: if Progress is
\*   not enabled and canceled is true, then active equals the empty set."
ProbeNothingHeldWhenStuck == (~ENABLED Progress /\ canceled) => active = {}

=============================================================================
