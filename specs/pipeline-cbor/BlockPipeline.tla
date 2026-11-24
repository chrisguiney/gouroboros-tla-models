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
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla. New     *)
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
    LosslessResults,    \* TRUE: WithLosslessResults on top of the fix. A full Results
                        \* buffer then makes the runner wait for the reader, as before the
                        \* fix, and drops are allowed only once Stop has begun [G]
    HasApplyFunc,       \* TRUE: full mode, where ApplyFunc is the commit sink. FALSE:
                        \* WithHeaderOnly or WithTrustedDecodeOnly, where Start forbids an
                        \* ApplyFunc and Results is the only output [G]
    DecodeOnlyLossless  \* TRUE: the fix, where Start makes Results lossless when there
                        \* is no ApplyFunc. FALSE: gOuroboros 805d32ab, where decode-only
                        \* modes drop undelivered results unless WithLosslessResults is set

ASSUME MaxPending \in Nat /\ MaxPending >= 1 /\ CapacityBound \in Nat
ASSUME QueueCap \in Nat /\ QueueCap >= 1   \* the fix keeps at least one result

\* In English: whether Results is lossless. WithLosslessResults asks for it;
\* with the fix, a pipeline without an ApplyFunc gets it by default [G] Start.
\* Literally: "Lossless is defined as: LosslessResults, or (HasApplyFunc is not
\*   true and DecodeOnlyLossless)."
Lossless == LosslessResults \/ (~HasApplyFunc /\ DecodeOnlyLossless)

\* Sequence numbers. Submit hands them out in order, with no gaps [G].
\* Literally: "Seqs is defined as 0 through N minus 1."
Seqs == 0 .. N - 1
\* Literally: "None is defined as N."
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

\* Literally: "vars is defined as the tuple of all twenty-three variables."
vars == <<outcome, submitted, stage, pending, nextSeq, cur, rpc, toForward,
          results, completed, applied, canceled, stopping, failed, overflow,
          pc, target, rolledBack, boundary, lateCommit, afterFail,
          dropped, read>>

\* In English: the outcomes a block may have.
\* Literally: "Outcomes is defined as: if CanFail then the set containing "ok"
\*   and "bad", else the set containing "ok"."
Outcomes == IF CanFail THEN {"ok", "bad"} ELSE {"ok"}

\* In English: the pipeline starts empty, each block's outcome is fixed in
\* advance, and the client is idle.
\* Literally: "Init is defined as: outcome is a member of the set of functions
\*   from Seqs to Outcomes, and submitted equals 0, and stage equals the empty
\*   set, and pending equals the empty set, and nextSeq equals 0, and cur equals
\*   None, and rpc equals "idle", and toForward equals the empty sequence, and
\*   results equals the empty sequence, and completed equals 0, and applied
\*   equals the empty sequence, and canceled equals FALSE, and stopping equals
\*   FALSE, and failed equals FALSE, and overflow equals FALSE, and pc equals
\*   "idle", and target equals 0, and rolledBack equals FALSE, and boundary
\*   equals 0, and lateCommit equals FALSE, and afterFail equals FALSE, and
\*   dropped equals 0, and read equals the empty sequence."
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
\* Literally: "Submit is defined as: pc equals "idle", and submitted is less
\*   than N, and submitted minus completed is less than or equal to
\*   CapacityBound, and canceled is not true, and stage in the next state equals
\*   the union of stage and the set containing submitted, and submitted in the
\*   next state equals submitted plus 1, and outcome, pending, nextSeq, cur,
\*   rpc, toForward, results, completed, applied, canceled, stopping, failed,
\*   overflow, pc, target, rolledBack, boundary, lateCommit and afterFail are
\*   unchanged."
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
\* Literally: "StartFence is defined as: pc equals "idle", and canceled is not
\*   true, and target in the next state equals submitted, and pc in the next
\*   state equals "fence", and outcome, submitted, stage, pending, nextSeq, cur,
\*   rpc, toForward, results, completed, applied, canceled, stopping, failed,
\*   overflow, rolledBack, boundary, lateCommit and afterFail are unchanged."
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
\* Literally: "FenceReturn is defined as: pc equals "fence", and either
\*   (completed is greater than or equal to target and pc in the next state
\*   equals "idle") or (canceled is true and pc in the next state equals
\*   "done"), and outcome, submitted, stage, pending, nextSeq, cur, rpc,
\*   toForward, results, completed, applied, canceled, stopping, failed,
\*   overflow, target, rolledBack, boundary, lateCommit and afterFail are
\*   unchanged."
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
\* Literally: "DrainSucceedsOnStop of t is defined as: target in the next state
\*   equals t, and pc in the next state equals: if DrainWaitsForApply then
\*   "drainStop", else "rollback"."
DrainSucceedsOnStop(t) ==
    /\ target' = t
    /\ pc' = IF DrainWaitsForApply THEN "drainStop" ELSE "rollback"

\* In English: WaitForDrain. If Stop has begun it succeeds at once
\* ("explicit shutdown makes the drain vacuous" [G] WaitForDrain);
\* otherwise it is a Fence.
\* Literally: "StartDrain is defined as: pc equals "idle", and either (stopping
\*   is true, and DrainSucceedsOnStop of submitted) or (stopping is not true,
\*   and canceled is not true, and target in the next state equals submitted,
\*   and pc in the next state equals "drain"), and outcome, submitted, stage,
\*   pending, nextSeq, cur, rpc, toForward, results, completed, applied,
\*   canceled, stopping, failed, overflow, rolledBack, boundary, lateCommit and
\*   afterFail are unchanged."
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
\* Literally: "DrainReturn is defined as: pc equals "drain", and either
\*   (completed is greater than or equal to target, and pc in the next state
\*   equals "rollback"), or (canceled is true and stopping is true, and
\*   DrainSucceedsOnStop of target), or (canceled is true and stopping is not
\*   true, and pc in the next state equals "done"); and target in the next state
\*   is a member of the set containing target, and outcome, submitted, stage,
\*   pending, nextSeq, cur, rpc, toForward, results, completed, applied,
\*   canceled, stopping, failed, overflow, rolledBack, boundary, lateCommit and
\*   afterFail are unchanged."
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
\* Literally: "DrainStopReturn is defined as: pc equals "drainStop", and rpc
\*   equals "exited", and pc in the next state equals "rollback", and outcome,
\*   submitted, stage, pending, nextSeq, cur, rpc, toForward, results,
\*   completed, applied, canceled, stopping, failed, overflow, target,
\*   rolledBack, boundary, lateCommit and afterFail are unchanged."
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
\* Literally: "Rollback is defined as: pc equals "rollback", and rolledBack in
\*   the next state equals TRUE, and boundary in the next state equals target,
\*   and pc in the next state equals "done", and outcome, submitted, stage,
\*   pending, nextSeq, cur, rpc, toForward, results, completed, applied,
\*   canceled, stopping, failed, overflow, target, lateCommit and afterFail are
\*   unchanged."
Rollback ==
    /\ pc = "rollback"
    /\ rolledBack' = TRUE
    /\ boundary' = target
    /\ pc' = "done"
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   toForward, results, completed, applied, canceled, stopping,
                   failed, overflow, target, lateCommit, afterFail>>

\* In English: a client with nothing left to submit stops.
\* Literally: "ClientFinish is defined as: pc equals "idle", and submitted
\*   equals N, and pc in the next state equals "done", and outcome, submitted,
\*   stage, pending, nextSeq, cur, rpc, toForward, results, completed, applied,
\*   canceled, stopping, failed, overflow, target, rolledBack, boundary,
\*   lateCommit and afterFail are unchanged."
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
\* Literally: "Stop is defined as: StopAllowed is true, and stopping is not
\*   true, and stopping in the next state equals TRUE, and canceled in the next
\*   state equals TRUE, and outcome, submitted, stage, pending, nextSeq, cur,
\*   rpc, toForward, results, completed, applied, failed, overflow, pc, target,
\*   rolledBack, boundary, lateCommit and afterFail are unchanged."
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
\* Literally: "TakeResult is defined as: Consumer or stopping, and results does
\*   not equal the empty sequence, and results in the next state equals the tail
\*   of results, and read in the next state equals: if Consumer then read with
\*   the head of results appended, else read; and dropped is unchanged, and
\*   outcome, submitted, stage, pending, nextSeq, cur, rpc, toForward,
\*   completed, applied, canceled, stopping, failed, overflow, pc, target,
\*   rolledBack, boundary, lateCommit and afterFail are unchanged."
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
\* Literally: "Receive is defined as: rpc equals "idle", and canceled is not
\*   true, and there exists an s in stage such that stage in the next state
\*   equals stage without the members of the set containing s, and: if s equals
\*   nextSeq, then cur in the next state equals s, and rpc in the next state
\*   equals "applying", and pending, overflow, canceled and failed are
\*   unchanged; else if the number of members of pending is greater than or
\*   equal to MaxPending, then overflow in the next state equals TRUE, and
\*   failed in the next state equals TRUE, and canceled in the next state equals
\*   TRUE, and rpc in the next state equals "exited", and pending and cur are
\*   unchanged; else pending in the next state equals the union of pending and
\*   the set containing s, and cur, rpc, overflow, canceled and failed are
\*   unchanged; and outcome, submitted, nextSeq, toForward, results, completed,
\*   applied, stopping, pc, target, rolledBack, boundary, lateCommit and
\*   afterFail are unchanged."
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
\* Literally: "Commit is defined as: rpc equals "applying", and outcome of cur
\*   equals "ok", and applied in the next state equals applied with cur
\*   appended, and toForward in the next state equals toForward with cur
\*   appended, and nextSeq in the next state equals cur plus 1, and lateCommit
\*   in the next state equals (lateCommit or (rolledBack and cur is less than
\*   boundary)), and afterFail in the next state equals (afterFail or failed),
\*   and: if canceled, then completed in the next state equals cur plus 1, and
\*   rpc in the next state equals "exited", and cur in the next state equals
\*   None, and pending is unchanged; else if cur plus 1 is a member of pending,
\*   then cur in the next state equals cur plus 1, and pending in the next state
\*   equals pending without the members of the set containing cur plus 1, and
\*   completed and rpc are unchanged; else completed in the next state equals
\*   cur plus 1, and rpc in the next state equals "forward", and cur in the next
\*   state equals None, and pending is unchanged; and outcome, submitted, stage,
\*   results, canceled, stopping, failed, overflow, pc, target, rolledBack and
\*   boundary are unchanged."
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
\* Literally: "Reject is defined as: rpc equals "applying", and outcome of cur
\*   equals "bad", and failed in the next state equals TRUE, and: if FailStops,
\*   then canceled in the next state equals TRUE, and completed in the next
\*   state equals cur, and rpc in the next state equals "exited", and cur in the
\*   next state equals None, and nextSeq and pending are unchanged; else nextSeq
\*   in the next state equals cur plus 1, and (if cur plus 1 is a member of
\*   pending, then cur in the next state equals cur plus 1, and pending in the
\*   next state equals pending without the members of the set containing cur
\*   plus 1, and completed and rpc are unchanged; else completed in the next
\*   state equals cur plus 1, and rpc in the next state equals "forward", and
\*   cur in the next state equals None, and pending is unchanged), and canceled
\*   is unchanged; and outcome, submitted, stage, toForward, results, applied,
\*   stopping, overflow, pc, target, rolledBack, boundary, lateCommit and
\*   afterFail are unchanged."
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
\* Literally: "Forward is defined as: rpc equals "forward", and toForward does
\*   not equal the empty sequence, and either (the length of results is less
\*   than QueueCap, and results in the next state equals results with the head
\*   of toForward appended, and dropped is unchanged) or (ResultsNonBlocking is
\*   true, and (Lossless is not true, or stopping is true), and the length of
\*   results is greater than or equal to QueueCap, and results in the next state
\*   equals the tail of results with the head of toForward appended, and dropped
\*   in the next state equals dropped plus 1); and toForward in the next state
\*   equals the tail of toForward, and read is unchanged, and outcome,
\*   submitted, stage, pending, nextSeq, cur, rpc, completed, applied, canceled,
\*   stopping, failed, overflow, pc, target, rolledBack, boundary, lateCommit
\*   and afterFail are unchanged."
Forward ==
    /\ rpc = "forward"
    /\ toForward # <<>>
    /\ \/ /\ Len(results) < QueueCap                         \* room: append
          /\ results' = Append(results, Head(toForward))
          /\ UNCHANGED dropped
       \/ /\ ResultsNonBlocking                              \* the fix only
          /\ ~Lossless \/ stopping                           \* lossless: only once Stop began
          /\ Len(results) >= QueueCap                        \* no room
          /\ results' = Append(Tail(results), Head(toForward)) \* drop the oldest
          /\ dropped' = dropped + 1
    /\ toForward' = Tail(toForward)
    /\ UNCHANGED read
    /\ UNCHANGED <<outcome, submitted, stage, pending, nextSeq, cur, rpc,
                   completed, applied, canceled, stopping, failed, overflow,
                   pc, target, rolledBack, boundary, lateCommit, afterFail>>

\* In English: with everything handed off the runner waits for input again.
\* Literally: "ForwardDone is defined as: rpc equals "forward", and toForward
\*   equals the empty sequence, and rpc in the next state equals "idle", and
\*   outcome, submitted, stage, pending, nextSeq, cur, toForward, results,
\*   completed, applied, canceled, stopping, failed, overflow, pc, target,
\*   rolledBack, boundary, lateCommit and afterFail are unchanged."
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
\* Literally: "RunnerExit is defined as: rpc is a member of the set containing
\*   "idle" and "forward", and canceled is true, and rpc in the next state
\*   equals "exited", and toForward in the next state equals the empty sequence,
\*   and outcome, submitted, stage, pending, nextSeq, cur, results, completed,
\*   applied, canceled, stopping, failed, overflow, pc, target, rolledBack,
\*   boundary, lateCommit and afterFail are unchanged."
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
\* Literally: "Terminated is defined as: pc equals "done", and rpc is a member
\*   of the set containing "exited" and "idle", and vars is unchanged."
Terminated ==
    /\ pc = "done"
    /\ rpc \in {"exited", "idle"}
    /\ UNCHANGED vars

\* In English: any step. Only Forward and TakeResult touch the record of
\* dropped and read results; every other step leaves it alone.
\* Literally: "Next is defined as: (Submit or StartFence or FenceReturn or
\*   StartDrain or DrainReturn or DrainStopReturn or Rollback or ClientFinish or
\*   Stop or Receive or Commit or Reject or ForwardDone or RunnerExit, and
\*   dropped and read are unchanged), or TakeResult or Forward, or Terminated."
Next ==
    \/ /\ \/ Submit \/ StartFence \/ FenceReturn \/ StartDrain \/ DrainReturn
          \/ DrainStopReturn \/ Rollback \/ ClientFinish
          \/ Stop
          \/ Receive \/ Commit \/ Reject \/ ForwardDone \/ RunnerExit
       /\ UNCHANGED <<dropped, read>>
    \/ TakeResult \/ Forward
    \/ Terminated

\* In English: "Start in Init, and take only Next steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* What must always be true. *)

\* In English: variables hold the kinds of values they should.
\* Literally: "TypeOK is defined as: submitted is a member of 0 through N, and
\*   stage is a subset of Seqs, and pending is a subset of Seqs, and rpc is a
\*   member of the set containing "idle", "applying", "forward" and "exited",
\*   and pc is a member of the set containing "idle", "fence", "drain",
\*   "drainStop", "rollback" and "done", and completed is a member of 0 through
\*   N."
TypeOK ==
    /\ submitted \in 0 .. N
    /\ stage \subseteq Seqs /\ pending \subseteq Seqs
    /\ rpc \in {"idle", "applying", "forward", "exited"}
    /\ pc \in {"idle", "fence", "drain", "drainStop", "rollback", "done"}
    /\ completed \in 0 .. N

\* In English: ApplyFunc committed blocks 0, 1, 2, ... in that order, each
\* once. [R2] adds blocks one at a time; [G] promises sequence order.
\* Literally: "AppliedInOrderOnce is defined as: for all i in 1 through the
\*   length of applied, element i of applied equals i minus 1."
AppliedInOrderOnce ==
    \A i \in 1 .. Len(applied) : applied[i] = i - 1

\* In English: completedSequence never runs ahead of what was committed, so
\* a successful Fence means its blocks were applied.
\* Literally: "CompletedMeansApplied is defined as: completed is less than or
\*   equal to the length of applied, or (FailStops is not true and failed is
\*   true)."
CompletedMeansApplied ==
    completed <= Len(applied) \/ (~FailStops /\ failed)

\* In English: no block is committed after a block was rejected. [R3]
\* ignores every successor of an invalid block.
\* Literally: "NoApplyAfterFailure is defined as: afterFail is not true."
NoApplyAfterFailure == ~afterFail

\* In English: the consumer reads results in commit order, never one twice,
\* and only blocks that ApplyFunc committed.
\* Literally: "ReadInCommitOrder is defined as: for all i in 1 through the
\*   length of read minus 1, element i of read is less than element i plus 1 of
\*   read; and for all i in 1 through the length of read, there exists a j in 1
\*   through the length of applied such that element j of applied equals element
\*   i of read."
ReadInCommitOrder ==
    /\ \A i \in 1 .. Len(read) - 1 : read[i] < read[i + 1]
    /\ \A i \in 1 .. Len(read) : \E j \in 1 .. Len(applied) : applied[j] = read[i]

\* In English: while no result has been dropped, the consumer has read
\* exactly the first blocks committed, with nothing missing. So a reader
\* that keeps up loses nothing.
\* Literally: "ReadLosslessWithoutDrops is defined as: if dropped equals 0, then
\*   for all i in 1 through the length of read, element i of read equals element
\*   i of applied."
ReadLosslessWithoutDrops ==
    dropped = 0 => \A i \in 1 .. Len(read) : read[i] = applied[i]

\* In English: Submit's backpressure keeps the apply stage from ever raising
\* ErrPendingLimitExceeded.
\* Literally: "PendingBounded is defined as: overflow is not true."
PendingBounded == ~overflow

\* In English: in lossless mode no committed result is dropped before Stop
\* begins, so a reader receives every block it was handed.
\* Literally: "LosslessNeverDropsBeforeStop is defined as: if Lossless, then
\*   dropped equals 0 or stopping is true."
LosslessNeverDropsBeforeStop == Lossless => (dropped = 0 \/ stopping)

\* In English: a pipeline without an ApplyFunc (WithHeaderOnly or
\* WithTrustedDecodeOnly) delivers blocks only through Results, so it must
\* not drop a committed result before Stop begins, whether or not the caller
\* asked for WithLosslessResults.
\* Literally: "DecodeOnlyNeverDropsBeforeStop is defined as: if HasApplyFunc is
\*   not true, then dropped equals 0 or stopping is true."
DecodeOnlyNeverDropsBeforeStop == ~HasApplyFunc => (dropped = 0 \/ stopping)

\* In English: after a successful WaitForDrain and the client's rollback,
\* no block from before the drain boundary is committed.
\* Literally: "NoCommitAfterRollback is defined as: lateCommit is not true."
NoCommitAfterRollback == ~lateCommit

---------------------------------------------------------------------------
(* Reachability probes: each claims something never happens. A probe     *)
(* config expects TLC to show it does, so a passing check is not vacuous.  *)

\* In English: claims the apply stage never buffers an out-of-order block.
\* Literally: "ProbeNeverReordered is defined as: pending equals the empty set."
ProbeNeverReordered == pending = {}

\* In English: claims Stop never begins while ApplyFunc is running.
\* Literally: "ProbeNeverStopWhileApplying is defined as: (stopping is true and
\*   rpc equals "applying") is not true."
ProbeNeverStopWhileApplying == ~(stopping /\ rpc = "applying")

\* In English: claims the client never rolls back.
\* Literally: "ProbeNeverRollback is defined as: rolledBack is not true."
ProbeNeverRollback == ~rolledBack

\* In English: claims every block gets applied.
\* Literally: "ProbeAllApplied is defined as: if pc equals "done", then the
\*   length of applied equals N."
ProbeAllApplied == pc = "done" => Len(applied) = N

\* In English: claims no result is ever dropped.
\* Literally: "ProbeNeverDrop is defined as: dropped equals 0."
ProbeNeverDrop == dropped = 0

\* Probe, EXPECTED to be violated: "In lossless mode the runner never waits
\* for the reader." Violated = a full Results buffer does hold it back.
\* Literally: "ProbeLosslessNeverHoldsBack is defined as: (Lossless, and
\*   stopping is not true, and rpc equals "forward", and toForward does not
\*   equal the empty sequence, and the length of results is greater than or
\*   equal to QueueCap) is not true."
ProbeLosslessNeverHoldsBack ==
    ~(Lossless /\ ~stopping /\ rpc = "forward" /\ toForward # <<>>
      /\ Len(results) >= QueueCap)
=============================================================================
