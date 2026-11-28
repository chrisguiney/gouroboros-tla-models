------------------------ MODULE BlockFetchRequestChans ------------------------
(***************************************************************************)
(* The gOuroboros BlockFetch client's per-request result channels and the  *)
(* GetBlock waiter that reads them (protocol/blockfetch/client.go,         *)
(* v0.222.0 0c00b799).                                                     *)
(*                                                                         *)
(* A request has three channels of capacity 1 (:1225-1227): startChan,     *)
(* blockChan and doneChan. Every send on them is non-blocking, with a      *)
(* `default:` that drops the value when the slot is full:                  *)
(*   handleStartBatch   startChan <- nil                 (:1678-1681)      *)
(*   handleBlock        blockChan <- block               (:1903-1906)      *)
(*   resolve(err)       startChan <- err if err != nil,  (:1505-1522)      *)
(*                      doneChan  <- err; once per request (resolveOnce)   *)
(* resolve runs for MsgBatchDone (nil), for a failure (deadline, peer      *)
(* error), and from the shutdown watcher once the protocol ends            *)
(* (ErrProtocolShuttingDown), whichever is first.                          *)
(*                                                                         *)
(* The waiter (GetBlock: waitForBatchStart :1424-1435, awaitBlock          *)
(* :850-880, waitForBatchDone :888-905, completedBlockOrShutdown           *)
(* :910-926) selects on one or two of them and on protocolDone; its        *)
(* shutdown branches read the channels again without blocking, so a result *)
(* reported just before shutdown became observable is kept.                *)
(*                                                                         *)
(* Question: can a dropped send lose the outcome? Each channel is sent at  *)
(* most once per value the waiter needs (startChan's second, error, send   *)
(* only matters if the first was not read, and then the error also reaches *)
(* doneChan), so with capacity 1 the drop only ever discards a value that  *)
(* is redundant. Cap = 0 is the mutation that shows the slot is what makes *)
(* `default:` safe: an unbuffered send with `default:` succeeds only while *)
(* the waiter is parked on it (approximated here as: the value is kept     *)
(* only when the waiter is at a select that includes the channel).         *)
(*                                                                         *)
(* The reference client (ouroboros-network BlockFetch client, STM) hands   *)
(* results through TVars the waiter retries on, so nothing can be dropped. *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the top-level README's "Reading a formula      *)
(*   literally" table. `srv` is the receive loop handling the peer's       *)
(*   messages in order; `cpc` is the GetBlock caller.                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Cap     \* capacity of startChan, blockChan and doneChan (1 in Go)

VARIABLES
    startQ, blockQ, doneQ,  \* channel buffers (sequences of values)
    srv,        \* the peer as seen by the receive loop: "idle", "started", "block", "quiet"
    resolved,   \* the request's outcome: "none", "ok", "err", "shutdown"
    early,      \* the outcome was reported while protocolDone was still open
    blockSent,  \* handleBlock ran for this request
    protoDone,  \* protocolDone is closed
    cpc,        \* caller: "start", "await", "batchdone", "done"
    got,        \* the block the caller holds (awaitBlock's `block`)
    result      \* what GetBlock returned: "none", "block", "err", "noblocks", "shutdown"

vars == <<startQ, blockQ, doneQ, srv, resolved, early, blockSent, protoDone,
          cpc, got, result>>

Init ==
    /\ startQ = <<>> /\ blockQ = <<>> /\ doneQ = <<>>
    /\ srv = "idle" /\ resolved = "none" /\ early = FALSE
    /\ blockSent = FALSE /\ protoDone = FALSE
    /\ cpc = "start" /\ got = FALSE /\ result = "none"

\* In English: "The caller is parked at a select that includes channel ch."
Parked(ch) ==
    \/ ch = "start" /\ cpc = "start"
    \/ ch = "block" /\ cpc = "await"
    \/ ch = "done" /\ cpc \in {"await", "batchdone"}

\* In English: "A non-blocking send of v on q: kept if there is room (with an
\* unbuffered channel, if the caller is parked on it), otherwise dropped."
TrySend(q, ch, v) ==
    IF (Cap > 0 /\ Len(q) < Cap) \/ (Cap = 0 /\ Len(q) = 0 /\ Parked(ch))
    THEN Append(q, v) ELSE q

\* In English: "resolve(outcome), once: startChan gets the error if there is
\* one, doneChan gets the outcome."
Resolve(out) ==
    /\ resolved = "none"
    /\ resolved' = out
    /\ early' = ~protoDone
    /\ startQ' = IF out = "ok" THEN startQ ELSE TrySend(startQ, "start", out)
    /\ doneQ' = TrySend(doneQ, "done", out)

-----------------------------------------------------------------------------
\* The receive loop and the shutdown watcher.

StartBatch ==
    /\ srv = "idle" /\ resolved = "none" /\ ~protoDone
    /\ srv' = "started"
    /\ startQ' = TrySend(startQ, "start", "ok")
    /\ UNCHANGED <<blockQ, doneQ, resolved, early, blockSent, protoDone, cpc, got, result>>

Block ==
    /\ srv = "started" /\ resolved = "none" /\ ~protoDone
    /\ srv' = "block" /\ blockSent' = TRUE
    /\ blockQ' = TrySend(blockQ, "block", "b")
    /\ UNCHANGED <<startQ, doneQ, resolved, early, protoDone, cpc, got, result>>

\* In English: "MsgBatchDone resolves the request with success (with or
\* without a block before it)."
BatchDone ==
    /\ srv \in {"started", "block"} /\ ~protoDone
    /\ Resolve("ok") /\ srv' = "quiet"
    /\ UNCHANGED <<blockQ, blockSent, protoDone, cpc, got, result>>

\* In English: "A failure (deadline, peer error) resolves the request."
Fail ==
    /\ srv /= "quiet" /\ ~protoDone
    /\ Resolve("err") /\ srv' = "quiet"
    /\ UNCHANGED <<blockQ, blockSent, protoDone, cpc, got, result>>

Shutdown ==
    /\ ~protoDone
    /\ protoDone' = TRUE
    /\ UNCHANGED <<startQ, blockQ, doneQ, srv, resolved, early, blockSent, cpc, got, result>>

\* In English: "The shutdown watcher resolves what is still outstanding."
Watcher ==
    /\ protoDone
    /\ Resolve("shutdown") /\ srv' = "quiet"
    /\ UNCHANGED <<blockQ, blockSent, protoDone, cpc, got, result>>

-----------------------------------------------------------------------------
\* The GetBlock caller.

Return(r) == cpc' = "done" /\ result' = r

\* In English: "The value an error-or-nil channel's non-blocking read gives:
\* the queued value, or shutdown when empty (requestResultOrShutdown)."
OrShutdown(q) == IF q = <<>> THEN "shutdown" ELSE Head(q)
Drop1(q) == IF q = <<>> THEN q ELSE Tail(q)

\* waitForBatchStart
StartRecv ==
    /\ cpc = "start" /\ startQ /= <<>>
    /\ startQ' = Tail(startQ)
    /\ IF Head(startQ) = "ok" THEN cpc' = "await" /\ UNCHANGED result
       ELSE Return(Head(startQ))
    /\ UNCHANGED <<blockQ, doneQ, srv, resolved, early, blockSent, protoDone, got>>

StartShutdown ==
    /\ cpc = "start" /\ protoDone
    /\ startQ' = Drop1(startQ)
    /\ IF OrShutdown(startQ) = "ok" THEN cpc' = "await" /\ UNCHANGED result
       ELSE Return(OrShutdown(startQ))
    /\ UNCHANGED <<blockQ, doneQ, srv, resolved, early, blockSent, protoDone, got>>

\* completedBlockOrShutdown, with the block the caller already holds.
CompletedOrShutdown(held) ==
    LET d == OrShutdown(doneQ) IN
    /\ doneQ' = Drop1(doneQ)
    /\ IF d /= "ok" THEN Return(d) /\ UNCHANGED blockQ
       ELSE IF held THEN Return("block") /\ UNCHANGED blockQ
       ELSE IF blockQ /= <<>> THEN Return("block") /\ blockQ' = Tail(blockQ)
       ELSE Return("noblocks") /\ UNCHANGED blockQ

\* awaitBlock
AwaitBlock ==
    /\ cpc = "await" /\ blockQ /= <<>>
    /\ blockQ' = Tail(blockQ) /\ got' = TRUE /\ cpc' = "batchdone"
    /\ UNCHANGED <<startQ, doneQ, srv, resolved, early, blockSent, protoDone, result>>

AwaitDone ==
    /\ cpc = "await" /\ doneQ /= <<>>
    /\ doneQ' = Tail(doneQ)
    /\ IF Head(doneQ) /= "ok" THEN Return(Head(doneQ)) /\ UNCHANGED blockQ
       ELSE IF blockQ /= <<>> THEN Return("block") /\ blockQ' = Tail(blockQ)
       ELSE Return("noblocks") /\ UNCHANGED blockQ
    /\ UNCHANGED <<startQ, srv, resolved, early, blockSent, protoDone, got>>

AwaitShutdown ==
    /\ cpc = "await" /\ protoDone
    /\ CompletedOrShutdown(FALSE)
    /\ UNCHANGED <<startQ, srv, resolved, early, blockSent, protoDone, got>>

\* waitForBatchDone
BatchDoneRecv ==
    /\ cpc = "batchdone" /\ doneQ /= <<>>
    /\ doneQ' = Tail(doneQ)
    /\ Return(IF Head(doneQ) = "ok" THEN "block" ELSE Head(doneQ))
    /\ UNCHANGED <<startQ, blockQ, srv, resolved, early, blockSent, protoDone, got>>

BatchDoneShutdown ==
    /\ cpc = "batchdone" /\ protoDone
    /\ CompletedOrShutdown(TRUE)
    /\ UNCHANGED <<startQ, srv, resolved, early, blockSent, protoDone, got>>

-----------------------------------------------------------------------------

\* In English: "The caller has returned and the request is resolved."
Finished == cpc = "done" /\ resolved /= "none"

Next ==
    \/ StartBatch \/ Block \/ BatchDone \/ Fail \/ Shutdown \/ Watcher
    \/ StartRecv \/ StartShutdown \/ AwaitBlock \/ AwaitDone \/ AwaitShutdown
    \/ BatchDoneRecv \/ BatchDoneShutdown
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "What the caller should return for the request's outcome."
Expected ==
    CASE resolved = "ok" /\ blockSent  -> "block"
      [] resolved = "ok"               -> "noblocks"
      [] OTHER                         -> resolved

\* In English: "When the outcome was reported before shutdown, the caller
\* returns exactly that outcome; when shutdown came first, it reports
\* shutdown."
Faithful == Finished => result = Expected

\* In English: "The caller never reports a block that was not delivered."
NoFalseBlock == result = "block" => blockSent /\ resolved = "ok"
=============================================================================
