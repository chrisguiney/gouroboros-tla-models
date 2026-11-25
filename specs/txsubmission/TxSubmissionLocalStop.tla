------------------------ MODULE TxSubmissionLocalStop ------------------------
(***************************************************************************)
(* A tx-submission CLIENT (the outbound side, which holds a mempool) that  *)
(* is waiting to answer a blocking MsgRequestTxIds when its own node stops *)
(* the connection. TxSubmission.tla checks the messages; this module       *)
(* checks what happens to the one request that is still being answered    *)
(* when the stop arrives.                                                   *)
(*                                                                         *)
(* A blocking request has no timeout, and its reply must hold at least     *)
(* one id. With an empty mempool the client waits for a transaction. The   *)
(* reference waits in STM for either a transaction or the Terminate        *)
(* control message; on Terminate it sends MsgDone, which the protocol      *)
(* allows only as the answer to a blocking request [R1][R2]. It never      *)
(* sends an empty reply, and its stop never reports a protocol error.      *)
(*                                                                         *)
(* In gOuroboros the wait is the application's RequestTxIdsFunc callback   *)
(* (Dingo: ouroboros/txsubmission.go txsubmissionClientRequestTxIds). The  *)
(* client then judges the callback's answer [G1]:                          *)
(*   - ErrStopServerProcess: send MsgDone;                                 *)
(*   - an empty list for a blocking request: refuse it as a protocol       *)
(*     violation (reconcileTxIds [G2]), which becomes the error the        *)
(*     connection reports as it closes;                                    *)
(*   - ErrProtocolShuttingDown: end quietly [G3].                          *)
(*                                                                         *)
(* How the stop reaches the callback, the constant Callback:               *)
(*   "reference":   the reference, Terminate wakes the wait [R1][R2].      *)
(*   "waitCleanup": Dingo main. The wait ends only when the mempool        *)
(*                  consumer is released: Dingo's connection-closed        *)
(*                  cleanup cancels it after Close returns, and node       *)
(*                  shutdown stops the mempool before it drains the        *)
(*                  connections. It then answers an empty list (or, once   *)
(*                  the consumer is gone, an error).                       *)
(*   "emptyOnStop": the integration's first adaptation. The wait also ends *)
(*                  on the protocol's StopChan, and answers the same way.  *)
(*   "doneOnStop":  the fix. Every wait that ends without a transaction,   *)
(*                  and a blocking request with no consumer, answers       *)
(*                  ErrStopServerProcess.                                  *)
(*                                                                         *)
(* Whether Close waits for running callbacks, the constant JoinsCallbacks: *)
(* FALSE for gOuroboros main, where Close returns while a callback still   *)
(* runs; TRUE once Stop and Close join the protocol's goroutines [G4].     *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e:            *)
(*   [R1] ouroboros-network/lib/Ouroboros/Network/TxSubmission/            *)
(*        Outbound.hs 193-210: the blocking wait is                        *)
(*        timeoutWithControlMessage; Nothing (Terminate) -> SendMsgDone;   *)
(*        a reply is NonEmpty, an empty one is an internal error.          *)
(*   [R2] ouroboros-network/api/lib/Ouroboros/Network/ControlMessage.hs    *)
(*        43-55: Terminate returns Nothing; Continue and Quiesce retry.    *)
(*   [R3] ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/      *)
(*        TxSubmission2/Type.hs 214-241: MsgDone only from the blocking    *)
(*        state; a blocking reply holds at least one id.                   *)
(* gOuroboros (integration tree 96088e56), protocol/:                      *)
(*   [G1] txsubmission/client.go handleRequestTxIds: ErrStopServerProcess  *)
(*        on a blocking request sends MsgDone.                             *)
(*   [G2] txsubmission/validation.go reconcileTxIds: "blocking request for *)
(*        %d transaction IDs received an empty reply", a protocol          *)
(*        violation.                                                       *)
(*   [G3] protocol.go recvLoop: a handler error that is                    *)
(*        ErrProtocolShuttingDown ends the loop without SendError; any     *)
(*        other is sent to the connection's error channel.                 *)
(*   [G4] protocol.go Stop and connection.go Close wait for the protocol's *)
(*        goroutines, which include a running callback.                    *)
(* Dingo (integration tree), ouroboros/txsubmission.go:                    *)
(*   [D1] txsubmissionClientRequestTxIds and nextTxUntilStopped.           *)
(*   [D2] mempool/consumer.go NextTx(true): returns nil once the consumer  *)
(*        is cancelled or the mempool stops; the connection-closed handler *)
(*        cancels it.                                                      *)
(*   [D3] node_shutdown.go phase 2: the mempool capability is stopped      *)
(*        before the connection manager drains the connections.           *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Callback,        \* "reference", "waitCleanup", "emptyOnStop" or "doneOnStop"
    JoinsCallbacks,  \* TRUE: Close waits for a running callback [G4]
    MaxTx            \* transactions that may reach the mempool (0: a quiet node)

VARIABLES
    conn,       \* "open", "closing" (Close called, waiting) or "closed" (Close returned)
    waiting,    \* TRUE while the callback answering the blocking request runs
    mempool,    \* transactions available to announce
    cancelled,  \* TRUE once the consumer's wait is released: cleanup or mempool stop [D2]
    sent,       \* what the client put on the wire: "nothing", "reply" or "done"
    closeErr    \* the error the connection reports: "none" or "protocolViolation"

\* Literally: "vars is defined as the tuple of all six variables."
vars == <<conn, waiting, mempool, cancelled, sent, closeErr>>

\* In English: "Every variable holds a value of the right kind."
\* Literally: "TypeOK is defined as: conn is one of the three connection
\*   phases, and waiting and cancelled are booleans, and mempool is a natural
\*   number, and sent is one of three wire outcomes, and closeErr is one of two
\*   errors."
TypeOK ==
    /\ conn \in {"open", "closing", "closed"}
    /\ waiting \in BOOLEAN /\ cancelled \in BOOLEAN
    /\ mempool \in Nat
    /\ sent \in {"nothing", "reply", "done"}
    /\ closeErr \in {"none", "protocolViolation"}

\* In English: "The server's blocking request has arrived and the callback
\* is waiting with an empty mempool; nothing is closing yet."
\* Literally: "Init is defined as: conn equals "open", and waiting equals TRUE,
\*   and mempool equals 0, and cancelled equals FALSE, and sent equals
\*   "nothing", and closeErr equals "none"."
Init ==
    /\ conn = "open"
    /\ waiting = TRUE
    /\ mempool = 0
    /\ cancelled = FALSE
    /\ sent = "nothing"
    /\ closeErr = "none"
-----------------------------------------------------------------------------
(* Steps. *)

\* In English: "A transaction reaches the mempool, at most MaxTx in all."
\* Literally: "TxArrives is defined as: mempool is less than MaxTx, and mempool
\*   in the next state equals mempool plus 1, and the other variables are
\*   unchanged."
TxArrives ==
    /\ mempool < MaxTx
    /\ mempool' = mempool + 1
    /\ UNCHANGED <<conn, waiting, cancelled, sent, closeErr>>

\* In English: "Our own node calls Close: StopChan closes, and in the
\* reference the control message becomes Terminate [R2]."
\* Literally: "Close is defined as: conn equals "open", and conn in the next
\*   state equals "closing", and the other variables are unchanged."
Close ==
    /\ conn = "open"
    /\ conn' = "closing"
    /\ UNCHANGED <<waiting, mempool, cancelled, sent, closeErr>>

\* In English: "Close returns: at once, or, with JoinsCallbacks, only after
\* the callback has returned [G4]."
\* Literally: "CloseReturns is defined as: conn equals "closing", and if
\*   JoinsCallbacks then waiting is FALSE, and conn in the next state equals
\*   "closed", and the other variables are unchanged."
CloseReturns ==
    /\ conn = "closing"
    /\ JoinsCallbacks => ~waiting                 \* the join [G4]
    /\ conn' = "closed"
    /\ UNCHANGED <<waiting, mempool, cancelled, sent, closeErr>>

\* In English: "After Close returns, Dingo's connection-closed handler
\* cancels the connection's mempool consumer [D2]."
\* Literally: "Cleanup is defined as: conn equals "closed", and cancelled is
\*   FALSE, and cancelled in the next state equals TRUE, and the other
\*   variables are unchanged."
Cleanup ==
    /\ conn = "closed" /\ ~cancelled
    /\ cancelled' = TRUE
    /\ UNCHANGED <<conn, waiting, mempool, sent, closeErr>>

\* In English: "Node shutdown stops the mempool while the connection is
\* still open, before it drains the connections [D3]; that too releases
\* the consumer's wait [D2]."
\* Literally: "MempoolStops is defined as: conn equals "open", and cancelled
\*   is FALSE, and cancelled in the next state equals TRUE, and the other
\*   variables are unchanged."
MempoolStops ==
    /\ conn = "open" /\ ~cancelled
    /\ cancelled' = TRUE
    /\ UNCHANGED <<conn, waiting, mempool, sent, closeErr>>

\* In English: "A transaction is there, so the callback answers it; the
\* client sends the reply while the connection is open. Once it is closing
\* the send fails with ErrProtocolShuttingDown, which ends quietly [G3]."
\* Literally: "ReplyTx is defined as: waiting is TRUE, and mempool is greater
\*   than 0, and waiting in the next state equals FALSE, and sent in the next
\*   state equals (if conn equals "open" then "reply", else sent), and the
\*   other variables are unchanged."
ReplyTx ==
    /\ waiting /\ mempool > 0
    /\ waiting' = FALSE
    /\ sent' = IF conn = "open" THEN "reply" ELSE sent   \* [R1] 210, [G3]
    /\ UNCHANGED <<conn, mempool, cancelled, closeErr>>

\* In English: "The stop wakes the wait with nothing to announce. The
\* reference and the fix send MsgDone [R1][G1]; the first adaptation answers
\* an empty list, which the gOuroboros client refuses as a protocol
\* violation that the closing connection then reports [G2][G3]. The wait in
\* Dingo main does not watch the stop at all."
\* Literally: "StopWakes is defined as: waiting is TRUE, and mempool equals 0,
\*   and conn does not equal "open", and Callback is not "waitCleanup", and
\*   waiting in the next state equals FALSE, and sent in the next state equals
\*   (if Callback is "emptyOnStop" then sent, else "done"), and closeErr in
\*   the next state equals (if Callback is "emptyOnStop" then
\*   "protocolViolation", else closeErr), and the other variables are
\*   unchanged."
StopWakes ==
    /\ waiting /\ mempool = 0 /\ conn # "open"
    /\ Callback # "waitCleanup"                   \* [D1] on Dingo main
    /\ waiting' = FALSE
    /\ sent' = IF Callback = "emptyOnStop" THEN sent ELSE "done"
    /\ closeErr' = IF Callback = "emptyOnStop"
                      THEN "protocolViolation" ELSE closeErr   \* [G2]
    /\ UNCHANGED <<conn, mempool, cancelled>>

\* In English: "Releasing the consumer makes NextTx return nothing [D2].
\* The fix (and the reference, whose shutdown is Terminate) answers with
\* MsgDone, sent if the connection is still open. The others answer an
\* empty list, which the client refuses [G2]; the connection reports that
\* only if Close has not returned yet: after it returns, nobody reads the
\* error any more."
\* Literally: "CancelWakes is defined as: waiting is TRUE, and mempool equals
\*   0, and cancelled is TRUE, and waiting in the next state equals FALSE, and
\*   if Callback is "reference" or "doneOnStop", then sent in the next state
\*   equals (if conn equals "open" then "done", else sent) and closeErr is
\*   unchanged, else closeErr in the next state equals (if conn equals
\*   "closed" then closeErr, else "protocolViolation") and sent is unchanged;
\*   and the other variables are unchanged."
CancelWakes ==
    /\ waiting /\ mempool = 0 /\ cancelled
    /\ waiting' = FALSE
    /\ IF Callback \in {"reference", "doneOnStop"}
          THEN /\ sent' = IF conn = "open" THEN "done" ELSE sent   \* [R1] 201
               /\ UNCHANGED closeErr
          ELSE /\ closeErr' = IF conn = "closed" THEN closeErr
                              ELSE "protocolViolation"              \* [G2]
               /\ UNCHANGED sent
    /\ UNCHANGED <<conn, mempool, cancelled>>

\* In English: "Once the callback has returned and the connection is closed
\* and cleaned up, or the callback has answered and nobody closes, nothing
\* changes any more." This tells TLC that this is an expected ending, not a
\* deadlock.
\* Literally: "Finished is defined as: waiting is FALSE, and (conn equals
\*   "open", or conn equals "closed" and cancelled is TRUE), and vars is
\*   unchanged."
Finished ==
    /\ ~waiting
    /\ conn = "open" \/ (conn = "closed" /\ cancelled)
    /\ UNCHANGED vars

\* In English: "A step is any one of the steps above."
\* Literally: "Next is defined as: TxArrives, or Close, or CloseReturns, or
\*   Cleanup, or MempoolStops, or ReplyTx, or StopWakes, or CancelWakes, or
\*   Finished."
Next ==
    \/ TxArrives \/ Close \/ CloseReturns \/ Cleanup \/ MempoolStops
    \/ ReplyTx \/ StopWakes \/ CancelWakes
    \/ Finished

\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(* Invariants. Deadlock, which TLC checks by default, is the third question:
   does Close ever wait for a callback that waits for Close? *)

\* In English: "Stopping our own connection never reports a protocol
\* violation: the peer sent nothing wrong." The reference's stop is
\* Terminate, which ends the wait with MsgDone [R1][R2].
\* Literally: "LocalStopBlamesNoPeer is defined as: closeErr equals "none"."
LocalStopBlamesNoPeer == closeErr = "none"

\* In English: "The client sends only what a blocking request allows: a
\* non-empty reply or MsgDone [R3]." The model has no step that sends an
\* empty reply, so this holds by construction; it is listed so that a
\* change that adds one is checked.
\* Literally: "BlockingAnswerLegal is defined as: sent is one of "nothing",
\*   "reply" and "done"."
BlockingAnswerLegal == sent \in {"nothing", "reply", "done"}
=============================================================================
