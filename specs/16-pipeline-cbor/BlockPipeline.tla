---------------------------- MODULE BlockPipeline ----------------------------
(***************************************************************************)
(* gOuroboros' block pipeline: blocks are submitted in chain order, decoded *)
(* and validated by parallel workers (so they may finish out of order), and *)
(* applied one at a time, in sequence order, by a single apply runner.     *)
(* A failed block stops the pipeline. A client waits for an ordering       *)
(* boundary with Fence or WaitForDrain, and may roll its own state back    *)
(* after a successful WaitForDrain. An owner may Stop the pipeline.        *)
(*                                                                         *)
(* The network specification does not cover this: it is node-internal.    *)
(* The reference counterpart is the ChainDB add-block queue in             *)
(* IntersectMBO/ouroboros-consensus ec239d57f618 (README.md has links):    *)
(*   [R1] Storage/ChainDB/Impl/Types.hs 602-618, 664-696: a bounded FIFO   *)
(*        queue; addBlockToAdd blocks when it is full (backpressure).      *)
(*   [R2] Storage/ChainDB/Impl/Background.hs 755-815: one background      *)
(*        thread pops a block and runs chain selection for it to           *)
(*        completion before popping the next (one at a time, in order).    *)
(*   [R3] Storage/ChainDB/Impl/ChainSel.hs 506-516, 1487-1495, 1588-1595:*)
(*        an invalid block is recorded; it and its successors are ignored.*)
(*   [R4] Storage/ChainDB/Impl/Background.hs 779-800 and Types.hs 786-798:*)
(*        on close, the block being processed and every queued block get   *)
(*        FailedToAddBlock: each in-flight block is reported.              *)
(* gOuroboros rules are tagged [G]: pipeline/pipeline.go (Submit, Fence,   *)
(* WaitForDrain, Stop, waitForPendingCapacity, forwardResults) and         *)
(* pipeline/apply_stage.go (processWithStatus, applyPending, maybeApply,   *)
(* ApplyStageRunner.run, forwardItem), gouroboros commit 61046085.         *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla. New     *)
(* here: SubSeq(s, m, n) is the slice s[m..n]; Cardinality(S) is the size  *)
(* of a set S (from the FiniteSets module).                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,                  \* how many blocks the client submits (keeps the model finite)
    MaxPending,         \* MaxPendingBlocks: out-of-order blocks the apply stage may buffer [G]
    CapacityBound,      \* Submit waits while submitted - completed > CapacityBound. [G] uses MaxPending
    QueueCap,           \* results the runner may hand off before a consumer takes one [G]
    Consumer,           \* TRUE: someone reads Results. FALSE: nobody does
    CanFail,            \* TRUE: any block may turn out invalid when applied
    StopAllowed,        \* TRUE: the owner may call Stop at any time
    DrainWaitsForApply, \* TRUE: the fix. FALSE: gOuroboros 61046085, where WaitForDrain
                        \* returns success during Stop without waiting for ApplyFunc
    FailStops,          \* TRUE: [G] and [R3]. FALSE: a mutation that keeps applying after a failure
    ResultsNonBlocking, \* TRUE: the fix, where handing a result off never waits and a full
                        \* Results buffer drops its oldest entry. FALSE: gOuroboros 61046085,
                        \* where the runner waits for room in Results
    LosslessResults     \* TRUE: WithLosslessResults on top of the fix. A full Results
                        \* buffer then makes the runner wait for the reader, as before the
                        \* fix, and drops are allowed only once Stop has begun [G]

ASSUME MaxPending \in Nat /\ MaxPending >= 1 /\ CapacityBound \in Nat
ASSUME QueueCap \in Nat /\ QueueCap >= 1   \* the fix keeps at least one result

\* Sequence numbers. Submit hands them out in order, with no gaps [G].
Seqs == 0 .. N - 1
None == N  \* a value that is not a sequence number

VARIABLES
    outcome,     \* outcome[s]: "ok" or "bad"; whether block s will apply cleanly
    submitted,   \* sequenceCounter: how many blocks Submit has accepted
    stage,       \* blocks in the decode and validate stages, finishing in any order
    pending,     \* the apply stage's out-of-order buffer
    nextSeq,     \* the apply stage's nextSequence
    cur,         \* the block the runner is applying, or None
    rpc,         \* the runner: "idle", "applying", "forward" or "exited"
    toForward,   \* committed blocks the runner still has to hand to Results
    results,     \* blocks handed off and not yet read
    completed,   \* completedSequence: every block below it has been applied
    applied,     \* the list of blocks ApplyFunc committed, in commit order
    canceled,    \* the pipeline context is canceled
    stopping,    \* Stop has begun
    failed,      \* a block was rejected
    overflow,    \* the apply stage raised ErrPendingLimitExceeded
    pc,          \* the client: "idle", "fence", "drain", "drainStop", "rollback", "done"
    target,      \* the boundary the client's Fence or WaitForDrain waits for
    rolledBack,  \* the client has rolled its own state back
    boundary,    \* blocks below this were drained before the rollback
    lateCommit,  \* a block below the boundary was committed after the rollback
    afterFail,   \* a block was committed after a failure
    dropped,     \* how many results the fix discarded because Results was full
    read         \* the blocks the consumer read from Results, in reading order

vars == <<outcome, submitted, stage, pending, nextSeq, cur, rpc, toForward,
          results, completed, applied, canceled, stopping, failed, overflow,
          pc, target, rolledBack, boundary, lateCommit, afterFail,
          dropped, read>>

\* In English: the outcomes a block may have.
Outcomes == IF CanFail THEN {"ok", "bad"} ELSE {"ok"}

\* In English: the pipeline starts empty, each block's outcome is fixed in
\* advance, and the client is idle.
Init ==
    /\ outcome \in [Seqs -> Outcomes]  \* every combination of good and bad blocks
    /\ submitted = 0                   \* nothing accepted yet
    /\ stage = {}                      \* no block in decode or validate
    /\ pending = {}                    \* apply buffer empty
    /\ nextSeq = 0                     \* the apply stage waits for block 0
    /\ cur = None                      \* not applying anything
    /\ rpc = "idle"                    \* the runner waits for input
    /\ toForward = <<>>                \* nothing to hand off
    /\ results = <<>>                  \* Results is empty
    /\ completed = 0                   \* no block completed
    /\ applied = <<>>                  \* nothing committed
    /\ canceled = FALSE
    /\ stopping = FALSE
    /\ failed = FALSE
    /\ overflow = FALSE
    /\ pc = "idle"
    /\ target = 0
    /\ rolledBack = FALSE
    /\ boundary = 0
    /\ lateCommit = FALSE
    /\ afterFail = FALSE
    /\ dropped = 0                     \* no result discarded
    /\ read = <<>>                     \* the consumer has read nothing

---------------------------------------------------------------------------
(* The client. *)

\* In English: Submit accepts the next block only while fewer than
\* CapacityBound blocks are accepted but not completed, and only while the
\* pipeline runs. The accepted block enters the decode and validate stages.
\* [G] submit: waitForPendingCapacity, then the stopping checks, then
\* enqueue and sequenceCounter.Add(1), all under submitGate (one step here).
Submit ==
    /\ pc = "idle"
    /\ submitted < N                            \* the client has blocks left
    /\ submitted - completed <= CapacityBound   \* backpressure [G] waitForPendingCapacity
    /\ ~canceled                                \* a stopped pipeline refuses [G]
    /\ stage' = stage \cup {submitted}          \* the block enters the workers
    /\ submitted' = submitted + 1               \* the sequence is committed after enqueue [G]
    /\ UNCHANGED <<outcome, pending, nextSeq, cur, rpc, toForward, results,
                   completed, applied, canceled, stopping, failed, overflow,
                   pc, target, rolledBack, boundary, lateCommit, afterFail>>

\* In English: Fence records the current submission count as its target,
\* under the same gate Submit holds, then waits. chain-sync's client calls
\* it after every roll-forward [G] protocol/chainsync/client.go 1755.
StartFence ==
    /\ pc = "idle"
    /\ ~canceled                \* Fence refuses a stopped pipeline at once [G]
    /\ target' = submitted      \* the boundary [G] Fence
    /\ pc' = "fence"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, rolledBack, boundary, lateCommit, afterFail>>

\* In English: Fence returns success once everything below its target is
\* completed, or an error once the pipeline is canceled. When both hold Go's
\* select may pick either.
FenceReturn ==
    /\ pc = "fence"
    /\ \/ completed >= target /\ pc' = "idle"   \* success: the client carries on
       \/ canceled /\ pc' = "done"              \* stoppedError: the client gives up
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, target, rolledBack, boundary, lateCommit,
                   afterFail>>

\* In English: what WaitForDrain does once it decides to report success
\* because Stop has begun. gOuroboros returns at once; the fix first waits
\* for the apply runner to exit, so no ApplyFunc call is still running.
DrainSucceedsOnStop(t) ==
    /\ target' = t
    /\ pc' = IF DrainWaitsForApply THEN "drainStop" ELSE "rollback"

\* In English: WaitForDrain. If Stop has begun it succeeds at once
\* ("explicit shutdown makes the drain vacuous" [G] WaitForDrain);
\* otherwise it is a Fence.
StartDrain ==
    /\ pc = "idle"
    /\ \/ /\ stopping
          /\ DrainSucceedsOnStop(submitted)
       \/ /\ ~stopping
          /\ ~canceled
          /\ target' = submitted
          /\ pc' = "drain"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, rolledBack, boundary, lateCommit, afterFail>>

\* In English: the Fence inside WaitForDrain returns. Success leads to the
\* rollback. Cancellation is an error, unless Stop has begun, in which case
\* WaitForDrain again reports success [G] WaitForDrain lines after Fence.
DrainReturn ==
    /\ pc = "drain"
    /\ \/ /\ completed >= target
          /\ pc' = "rollback"
       \/ /\ canceled /\ stopping
          /\ DrainSucceedsOnStop(target)
       \/ /\ canceled /\ ~stopping
          /\ pc' = "done"           \* parent cancellation is reported as an error
    /\ target' \in {target}        \* the boundary is kept (DrainSucceedsOnStop may set it to the same value)
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, rolledBack, boundary, lateCommit, afterFail>>

\* In English: with the fix, the successful drain during Stop returns only
\* after the apply runner has exited.
DrainStopReturn ==
    /\ pc = "drainStop"
    /\ rpc = "exited"
    /\ pc' = "rollback"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, target, rolledBack, boundary, lateCommit,
                   afterFail>>

\* In English: the client rolls its own state back past every block below
\* the drain boundary. WaitForDrain's documented purpose is that no such
\* block is applied afterwards [G] WaitForDrain doc comment.
Rollback ==
    /\ pc = "rollback"
    /\ rolledBack' = TRUE
    /\ boundary' = target
    /\ pc' = "done"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, target, lateCommit, afterFail>>

\* In English: a client with nothing left to submit stops.
ClientFinish ==
    /\ pc = "idle"
    /\ submitted = N
    /\ pc' = "done"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, target, rolledBack, boundary, lateCommit,
                   afterFail>>

---------------------------------------------------------------------------
(* The owner and the Results consumer. *)

\* In English: Stop marks the pipeline stopping and cancels its context
\* before anything else [G] Stop.
Stop ==
    /\ StopAllowed
    /\ ~stopping
    /\ stopping' = TRUE
    /\ canceled' = TRUE
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, failed, overflow,
                   pc, target, rolledBack, boundary, lateCommit, afterFail>>

\* In English: a block leaves Results, read either by a consumer or by
\* Stop, which drains Results while it waits for the runner [G] Stop.
\* Only a consumer's read is recorded; Stop just releases the block.
TakeResult ==
    /\ Consumer \/ stopping
    /\ results # <<>>
    /\ results' = Tail(results)
    /\ read' = IF Consumer THEN Append(read, Head(results)) ELSE read
    /\ UNCHANGED dropped
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, completed, applied, canceled, stopping, failed,
                   overflow, pc, target, rolledBack, boundary, lateCommit,
                   afterFail>>

---------------------------------------------------------------------------
(* The apply runner: one goroutine, so one step at a time [G], like the    *)
(* single ChainSel thread of [R2].                                         *)

\* In English: the runner takes any block that has left the workers. If it
\* is the next in sequence it starts applying it; otherwise it buffers it,
\* or, with the buffer full, fails the pipeline with ErrPendingLimitExceeded.
\* [G] processWithStatus.
Receive ==
    /\ rpc = "idle"
    /\ ~canceled                           \* the run loop exits on ctx.Done [G]
    /\ \E s \in stage :
        /\ stage' = stage \ {s}
        /\ IF s = nextSeq
           THEN /\ cur' = s                \* apply it now
                /\ rpc' = "applying"
                /\ UNCHANGED <<pending, overflow, canceled, failed>>
           ELSE IF Cardinality(pending) >= MaxPending
           THEN /\ overflow' = TRUE        \* fatal: the buffer is full
                /\ failed' = TRUE
                /\ canceled' = TRUE
                /\ rpc' = "exited"
                /\ UNCHANGED <<pending, cur>>
           ELSE /\ pending' = pending \cup {s}   \* wait for the gap to fill
                /\ UNCHANGED <<cur, rpc, overflow, canceled, failed>>
    /\ UNCHANGED <<outcome, submitted, nextSeq, toForward, results, completed,
                   applied, stopping, pc, target, rolledBack, boundary,
                   lateCommit, afterFail>>

\* In English: ApplyFunc commits the current block. It records a commit
\* below a client's rollback boundary, and a commit after a failure. Then
\* the runner stops if the context is canceled [G] applyPending's ctx
\* check; otherwise it continues with the next block if it is buffered;
\* otherwise it marks the batch completed and starts handing it off.
Commit ==
    /\ rpc = "applying"
    /\ outcome[cur] = "ok"
    /\ applied' = Append(applied, cur)
    /\ toForward' = Append(toForward, cur)
    /\ nextSeq' = cur + 1
    /\ lateCommit' = (lateCommit \/ (rolledBack /\ cur < boundary))
    /\ afterFail' = (afterFail \/ failed)
    /\ IF canceled
       THEN /\ completed' = cur + 1        \* accountProcessed runs first [G] run
            /\ rpc' = "exited"
            /\ cur' = None
            /\ UNCHANGED pending
       ELSE IF cur + 1 \in pending
       THEN /\ cur' = cur + 1              \* applyPending takes the next one
            /\ pending' = pending \ {cur + 1}
            /\ UNCHANGED <<completed, rpc>>
       ELSE /\ completed' = cur + 1        \* markProcessed after the batch [G]
            /\ rpc' = "forward"
            /\ cur' = None
            /\ UNCHANGED pending
    /\ UNCHANGED <<outcome, submitted, stage, results, canceled, stopping,
                   failed, overflow, pc, target, rolledBack, boundary>>

\* In English: the current block is rejected (decode, validation, chain
\* context or ApplyFunc error). gOuroboros records the failure, cancels the
\* pipeline and exits the runner, marking only the prefix before the block
\* completed [G] run, fatal branch. The mutation FailStops = FALSE skips
\* the block and carries on.
Reject ==
    /\ rpc = "applying"
    /\ outcome[cur] = "bad"
    /\ failed' = TRUE
    /\ IF FailStops
       THEN /\ canceled' = TRUE
            /\ completed' = cur
            /\ rpc' = "exited"
            /\ cur' = None
            /\ UNCHANGED <<nextSeq, pending>>
       ELSE /\ nextSeq' = cur + 1
            /\ IF cur + 1 \in pending
               THEN /\ cur' = cur + 1
                    /\ pending' = pending \ {cur + 1}
                    /\ UNCHANGED <<completed, rpc>>
               ELSE /\ completed' = cur + 1
                    /\ rpc' = "forward"
                    /\ cur' = None
                    /\ UNCHANGED pending
            /\ UNCHANGED canceled
    /\ UNCHANGED <<outcome, submitted, stage, toForward, results, applied,
                   stopping, overflow, pc, target, rolledBack, boundary,
                   lateCommit, afterFail>>

\* In English: the runner hands the next committed block to Results. With
\* room, the block joins the end [G] forwardItem. Without room,
\* gOuroboros 61046085 waits, so this step is disabled until a consumer
\* reads; the fix instead drops the oldest waiting result and adds the new
\* one, so the runner never waits for a reader [G] forwardResults on the
\* fix branch. ChainDB followers pull, so a slow or absent follower never
\* holds back chain selection [R2].
Forward ==
    /\ rpc = "forward"
    /\ toForward # <<>>
    /\ \/ /\ Len(results) < QueueCap                         \* room: append
          /\ results' = Append(results, Head(toForward))
          /\ UNCHANGED dropped
       \/ /\ ResultsNonBlocking                              \* the fix only
          /\ ~LosslessResults \/ stopping                    \* lossless: only once Stop began
          /\ Len(results) >= QueueCap                        \* no room
          /\ results' = Append(Tail(results), Head(toForward)) \* drop the oldest
          /\ dropped' = dropped + 1
    /\ toForward' = Tail(toForward)
    /\ UNCHANGED read
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   completed, applied, canceled, stopping, failed, overflow,
                   pc, target, rolledBack, boundary, lateCommit, afterFail>>

\* In English: with everything handed off the runner waits for input again.
ForwardDone ==
    /\ rpc = "forward"
    /\ toForward = <<>>
    /\ rpc' = "idle"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, pc, target, rolledBack, boundary,
                   lateCommit, afterFail>>

\* In English: a canceled runner that is idle or handing off exits; the
\* blocks it had not handed off are dropped (Results is observational [G]).
RunnerExit ==
    /\ rpc \in {"idle", "forward"}
    /\ canceled
    /\ rpc' = "exited"
    /\ toForward' = <<>>
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, results,
                   completed, applied, canceled, stopping, failed, overflow,
                   pc, target, rolledBack, boundary, lateCommit, afterFail>>

\* In English: once the client is done and the runner has nothing it can
\* do, the system rests. TLC treats a state with no next step as a
\* deadlock, so this step marks the intended end.
Terminated ==
    /\ pc = "done"
    /\ rpc \in {"exited", "idle"}
    /\ UNCHANGED vars

\* In English: any step. Only Forward and TakeResult touch the record of
\* dropped and read results; every other step leaves it alone.
Next ==
    \/ /\ \/ Submit \/ StartFence \/ FenceReturn \/ StartDrain \/ DrainReturn
          \/ DrainStopReturn \/ Rollback \/ ClientFinish
          \/ Stop
          \/ Receive \/ Commit \/ Reject \/ ForwardDone \/ RunnerExit
       /\ UNCHANGED <<dropped, read>>
    \/ TakeResult \/ Forward
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* What must always be true. *)

\* In English: variables hold the kinds of values they should.
TypeOK ==
    /\ submitted \in 0 .. N
    /\ stage \subseteq Seqs /\ pending \subseteq Seqs
    /\ rpc \in {"idle", "applying", "forward", "exited"}
    /\ pc \in {"idle", "fence", "drain", "drainStop", "rollback", "done"}
    /\ completed \in 0 .. N

\* In English: ApplyFunc committed blocks 0, 1, 2, ... in that order, each
\* once. [R2] adds blocks one at a time; [G] promises sequence order.
AppliedInOrderOnce ==
    \A i \in 1 .. Len(applied) : applied[i] = i - 1

\* In English: completedSequence never runs ahead of what was committed, so
\* a successful Fence means its blocks were applied.
CompletedMeansApplied ==
    completed <= Len(applied) \/ (~FailStops /\ failed)

\* In English: no block is committed after a block was rejected. [R3]
\* ignores every successor of an invalid block.
NoApplyAfterFailure == ~afterFail

\* In English: the consumer reads results in commit order, never one twice,
\* and only blocks that ApplyFunc committed.
ReadInCommitOrder ==
    /\ \A i \in 1 .. Len(read) - 1 : read[i] < read[i + 1]
    /\ \A i \in 1 .. Len(read) : \E j \in 1 .. Len(applied) : applied[j] = read[i]

\* In English: while no result has been dropped, the consumer has read
\* exactly the first blocks committed, with nothing missing. So a reader
\* that keeps up loses nothing.
ReadLosslessWithoutDrops ==
    dropped = 0 => \A i \in 1 .. Len(read) : read[i] = applied[i]

\* In English: Submit's backpressure keeps the apply stage from ever raising
\* ErrPendingLimitExceeded.
PendingBounded == ~overflow

\* In English: in lossless mode no committed result is dropped before Stop
\* begins, so a reader receives every block it was handed.
LosslessNeverDropsBeforeStop == LosslessResults => (dropped = 0 \/ stopping)

\* In English: after a successful WaitForDrain and the client's rollback,
\* no block from before the drain boundary is committed.
NoCommitAfterRollback == ~lateCommit

---------------------------------------------------------------------------
(* Reachability probes: each claims something never happens. A probe     *)
(* config expects TLC to show it does, so a passing check is not vacuous.  *)

\* In English: claims the apply stage never buffers an out-of-order block.
ProbeNeverReordered == pending = {}

\* In English: claims Stop never begins while ApplyFunc is running.
ProbeNeverStopWhileApplying == ~(stopping /\ rpc = "applying")

\* In English: claims the client never rolls back.
ProbeNeverRollback == ~rolledBack

\* In English: claims every block gets applied.
ProbeAllApplied == pc = "done" => Len(applied) = N

\* In English: claims no result is ever dropped.
ProbeNeverDrop == dropped = 0

\* Probe, EXPECTED to be violated: "In lossless mode the runner never waits
\* for the reader." Violated = a full Results buffer does hold it back.
ProbeLosslessNeverHoldsBack ==
    ~(LosslessResults /\ ~stopping /\ rpc = "forward" /\ toForward # <<>>
      /\ Len(results) >= QueueCap)
=============================================================================
