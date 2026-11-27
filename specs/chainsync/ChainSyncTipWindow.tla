-------------------------- MODULE ChainSyncTipWindow --------------------------
(***************************************************************************)
(* Model `chainsync`, slice 7: how deep the sync window runs at the        *)
(* server's tip, and what that costs Reintersect.                          *)
(*                                                                         *)
(* gOuroboros, protocol/chainsync/client.go: syncLoop refills the window   *)
(* to PipelineLimit (75 by default) after every consumed reply [G1].       *)
(* Reintersect must wait until every outstanding MsgRequestNext is         *)
(* answered before it may send MsgFindIntersect [C1][R2]. A request the    *)
(* server receives at its tip is answered with MsgAwaitReply and then only *)
(* when the server's chain grows by one block [C1]. So a client following *)
(* the tip with a full window has PipelineLimit requests that each need    *)
(* their own new block, and Reintersect waits PipelineLimit blocks.        *)
(*                                                                         *)
(* The reference client decides per step instead [R4]: it pipelines       *)
(* another request only while its own tip block number plus the requests  *)
(* already outstanding is below the server's tip block number, and        *)
(* otherwise collects. At the tip that leaves one request outstanding.     *)
(*                                                                         *)
(* This slice abstracts the goroutines and locks of slice 1 away: a reply  *)
(* is consumed and the window topped up in one step. It keeps only what    *)
(* decides the window's depth: block numbers.                              *)
(*                                                                         *)
(* Questions: can a request be outstanding more than one block beyond the  *)
(* server's tip? How many new blocks can Reintersect's drain need? Does    *)
(* the client still fill its window while it is behind, and still reach    *)
(* the tip?                                                                *)
(*                                                                         *)
(* Sources (see README.md, slice 7):                                       *)
(*   [C1] miniprotocols.tex: chain-sync states; MsgAwaitReply then         *)
(*        MsgRollForward when the server's chain grows; MsgFindIntersect   *)
(*        only from StIdle.                                                *)
(*   [R2] ClientPipelined.hs: SendMsgFindIntersect only at Z.              *)
(*   [R4] PipelineDecision.hs pipelineDecisionMax: Collect when the        *)
(*        client's tip block number plus n reaches the server's.           *)
(*   [G1] gOuroboros protocol/chainsync/client.go: syncLoop, quiesceSync.  *)
(*                                                                         *)
(* Not in this slice: rollbacks (the server only extends its chain), the   *)
(* locks and signals of slice 1, Stop.                                     *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Limit,      \* PipelineLimit
    InitTip,    \* the server's tip block number when the model starts
    MaxTip,     \* the server stops producing here (keeps the model finite)
    TipAware    \* TRUE: the window follows [R4]; FALSE: always refill to Limit

\* In English: "The smaller and the larger of two numbers."
Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

VARIABLES
    tip,        \* the server's tip block number
    served,     \* block number of the last reply the server sent
    pending,    \* requests the server has received and not yet answered
    toClient,   \* replies in transit, oldest first: [blk, tip]
    pos,        \* block number of the last reply the client consumed
    seenTip,    \* the server tip that reply carried
    inFlight,   \* requests sent whose replies the client has not consumed
    rpc,        \* Reintersect: "idle", "drain", "done"
    drainTip    \* the server's tip when the drain began

vars == <<tip, served, pending, toClient, pos, seenTip, inFlight, rpc,
          drainTip>>

\* In English: "How many requests the client wants outstanding after it has
\* consumed a reply for block p carrying server tip t: with TipAware, one
\* per block it is behind, at least one and at most Limit [R4]; otherwise
\* always Limit [G1]."
Desired(p, t) ==
    IF TipAware THEN Max(1, Min(Limit, t - p))   \* [R4] pipelineDecisionMax
                ELSE Limit                       \* [G1] syncLoop top-up

\* In English: "The client has just intersected at block 0 and sent its
\* first request; the server is InitTip blocks ahead."
Init ==
    /\ tip = InitTip
    /\ served = 0 /\ pending = 1 /\ toClient = <<>>
    /\ pos = 0 /\ seenTip = 0 /\ inFlight = 1
    /\ rpc = "idle" /\ drainTip = 0

-----------------------------------------------------------------------------
(* The server [C1]. *)

\* In English: "The server's chain grows by one block."
Produce ==
    /\ tip < MaxTip                  \* bound only
    /\ tip' = tip + 1
    /\ UNCHANGED <<served, pending, toClient, pos, seenTip, inFlight, rpc,
                   drainTip>>

\* In English: "The server answers the oldest request with the next block,
\* if it has one. A request received at the tip stays unanswered (the
\* server has sent MsgAwaitReply) until Produce adds a block [C1]."
ServerAnswer ==
    /\ pending > 0                   \* a request is waiting
    /\ served < tip                  \* and the server has a block for it
    /\ served' = served + 1
    /\ pending' = pending - 1
    /\ toClient' = Append(toClient, [blk |-> served + 1, tip |-> tip])
    /\ UNCHANGED <<tip, pos, seenTip, inFlight, rpc, drainTip>>

-----------------------------------------------------------------------------
(* The client [G1]. *)

\* In English: "The client consumes the oldest reply. Unless Reintersect is
\* draining, it then tops the window up to Desired."
ClientConsume ==
    /\ toClient /= <<>>
    /\ LET m    == Head(toClient)
           left == inFlight - 1
           more == IF rpc = "drain" THEN 0
                   ELSE Max(0, Desired(m.blk, m.tip) - left)
       IN /\ pos' = m.blk                        \* the client's new tip
          /\ seenTip' = m.tip                    \* the server tip it carried
          /\ inFlight' = left + more             \* top-up
          /\ pending' = pending + more           \* the new requests
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<tip, served, rpc, drainTip>>

\* In English: "Reintersect starts: the loop stops sending, and the drain
\* waits for every outstanding request [R2][G1]."
ReBegin ==
    /\ rpc = "idle"
    /\ rpc' = "drain"
    /\ drainTip' = tip                         \* remember the tip now
    /\ UNCHANGED <<tip, served, pending, toClient, pos, seenTip, inFlight>>

\* In English: "Every request is answered: Reintersect sends
\* MsgFindIntersect, and the server finds the client's own tip, so the
\* client resumes from there with one request, as
\* sendInitialRequestAndStartSyncLoop does [G1]. The intersection exchange
\* itself is slice 1's; here it moves nothing."
ReDrained ==
    /\ rpc = "drain"
    /\ inFlight = 0                            \* nothing outstanding [R2]
    /\ rpc' = "done"
    /\ inFlight' = 1 /\ pending' = 1          \* the resumed sync's request
    /\ UNCHANGED <<tip, served, toClient, pos, seenTip, drainTip>>

\* In English: "Nothing else can happen: stay put."
Finished ==
    /\ ~ENABLED (Produce \/ ServerAnswer \/ ClientConsume \/ ReBegin
                 \/ ReDrained)
    /\ UNCHANGED vars

Next ==
    \/ Produce \/ ServerAnswer \/ ClientConsume \/ ReBegin \/ ReDrained
    \/ Finished

Spec == Init /\ [][Next]_vars

\* In English: "Spec, and every step of the server and the client that stays
\* possible is eventually taken; Reintersect is not forced to start."
\* WF_vars(A) is weak fairness: an action that stays enabled is taken.
\* https://lamport.azurewebsites.net/tla/book.html (chapter 8)
FairSpec ==
    /\ Spec
    /\ WF_vars(Produce) /\ WF_vars(ServerAnswer) /\ WF_vars(ClientConsume)
    /\ WF_vars(ReDrained)

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "The last block requested: every outstanding request asks for
\* the block after the one before it."
LastRequested == served + pending

\* In English: "No request is outstanding more than one block beyond the
\* server's tip." Each such request needs a block the server has not made.
WithinOneOfTip == LastRequested <= tip + 1

\* In English: "Reintersect's drain never needs more than one new block
\* beyond the server's tip when it began."
DrainNeedsAtMostOneBlock ==
    rpc = "drain" => LastRequested <= drainTip + 1

\* In English: "The client never has more than the window outstanding."
WindowBound == inFlight <= Limit

\* In English: "The client and the server agree on what is outstanding."
Accounting == inFlight = pending + Len(toClient)

-----------------------------------------------------------------------------
(* Liveness. *)

\* In English: "The client eventually consumes the last block the server
\* makes." <> is "eventually".
ReachesTip == <>(pos = MaxTip)

-----------------------------------------------------------------------------
(* Reachability probes: each is EXPECTED to be violated. *)

\* In English: "The window never fills." Violated = while behind, the client
\* does pipeline a full window, so the fix does not just cap it at one.
ProbeNeverFull == inFlight < Limit

\* In English: "Reintersect never finishes draining." Violated = it does.
ProbeNeverDrained == rpc /= "done"
=============================================================================
