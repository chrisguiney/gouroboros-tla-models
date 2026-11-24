-------------------------- MODULE EnginePipelining --------------------------
(***************************************************************************)
(* Model 03, slice 2: pipelined requests, end to end.                      *)
(*                                                                         *)
(* A client PIPELINES when it sends its next request before the reply to  *)
(* the last one has arrived. gOuroboros does it in protocol/protocol.go:   *)
(*                                                                         *)
(*   Sending (sendLoop, resolvePipelinedDequeue): in a state where the     *)
(*   peer has agency, AllowPipelinedSend is set, and the message's type is *)
(*   in PipelinedMessageTypes, the message is written at once and its      *)
(*   state change is DEFERRED: queued, counted (pendingPipelinedRequests), *)
(*   and applied, in send order, each time agency comes back. A message    *)
(*   that is not pipelinable now but legal in some state where we have    *)
(*   agency is HELD until agency returns.                                  *)
(*                                                                         *)
(*   Agency TOKEN: whenever a state change gives us agency, stateLoop puts *)
(*   one token in sendReadyChan (capacity one). sendLoop waits for it, and *)
(*   some paths drain it.                                                  *)
(*                                                                         *)
(*   Replies (reserveInboundAdmission, recvLoop, stateLoop): a reply to a  *)
(*   pipelined request can arrive while we still have agency, before its   *)
(*   request's deferred change. If a pipelined request has no reply       *)
(*   reserved yet, the reply is admitted against it                        *)
(*   (pendingPipelinedReplies), waits in recvLoop until the peer has       *)
(*   agency, and is applied then. The snapshot waits while a reserved     *)
(*   reply is unapplied (waitForInboundSnapshot).                          *)
(*                                                                         *)
(* The reference implementation does the same job differently:            *)
(* typed-protocols' YieldPipelined is sent from a state where the client   *)
(* HAS agency, the client's view jumps to the end of the round trip, a     *)
(* counter n counts outstanding requests, a receiver thread handles their  *)
(* replies in order, and plain Yield, Await, and Done are allowed only at  *)
(* n = Zero. The specification only says: send requests without waiting,  *)
(* the server handles them in turn, the mux keeps order, never overrun    *)
(* the server's buffer.                                                    *)
(*                                                                         *)
(* So the questions: with an honest server that follows the spec, does     *)
(* gOuroboros ever refuse a reply, apply a change in the wrong state,      *)
(* error on a message its client may send, send its final message while   *)
(* requests are outstanding (which the reference's n = Zero rule forbids), *)
(* or deadlock?                                                            *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex:                                  *)
(*   [P1] 2180-2208 "Pipelining of Mini Protocols".                        *)
(*   [C1] 838-849, 894-907 chain-sync; [B1] 1160-1202 block-fetch.         *)
(*   Reference, IntersectMBO/typed-protocols 8fa4ed2f:                     *)
(*   [R1] typed-protocols/src/Network/TypedProtocol/Peer.hs: YieldPipelined*)
(*        and Collect; Driver.hs runPipelinedPeerSender: Yield, Await, and *)
(*        Done only at Zero outstanding.                                   *)
(*   gOuroboros, blinklabs-io/gouroboros 79786c01:                         *)
(*   [G1] protocol/protocol.go sendLoop, resolvePipelinedDequeue,          *)
(*        takeAgencyToken, observeStateAndDrainSendReady,                  *)
(*        flushQueuedStateTransitions, reserveInboundAdmission,            *)
(*        reservePipelinedReply, waitForInboundSnapshot, recvLoop,         *)
(*        stateLoop (setState).                                            *)
(*   [G2] protocol/blockfetch/blockfetch.go StateMap and client.go         *)
(*        protocolStateMap (RequestPipelining sets AllowPipelinedSend in   *)
(*        StBusy and StStreaming); protocol/chainsync/chainsync.go         *)
(*        StateMapNtN (AllowPipelinedSend in StCanAwait; RequestNext is    *)
(*        also listed, for receiving, in StMustReply).                     *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Proto,              \* "BlockFetch" or "ChainSync"
    MaxRequests,        \* how many requests the client's application sends
    MaxBlocks,          \* how many blocks the server streams per batch
    MaxBatch,           \* how many queued messages sendLoop puts in one segment
    ReplyReservation    \* TRUE (gOuroboros): admit a reply before its request's change

\* In English: "The value that stands for no message."
\* Literally: "NoMsg is defined as "none"."
NoMsg == "none"

(***************************************************************************)
(* The protocols: the specification's transitions [B1][C1], and what       *)
(* gOuroboros's state tables add for pipelining [G2]. We are the client.  *)
(***************************************************************************)
\* In English: "The protocol's transitions: block-fetch's or chain-sync's."
\* Literally: "Transitions is defined as: if Proto equals "BlockFetch" then the
\*   set containing these six tuples: <<"StIdle", "MsgRequestRange", "StBusy">>,
\*   <<"StIdle", "MsgClientDone", "StDone">>, <<"StBusy", "MsgNoBlocks",
\*   "StIdle">>, <<"StBusy", "MsgStartBatch", "StStreaming">>, <<"StStreaming",
\*   "MsgBlock", "StStreaming">>, and <<"StStreaming", "MsgBatchDone",
\*   "StIdle">>; else the set containing these five tuples: <<"StIdle",
\*   "MsgRequestNext", "StCanAwait">>, <<"StIdle", "MsgDone", "StDone">>,
\*   <<"StCanAwait", "MsgAwaitReply", "StMustReply">>, <<"StCanAwait",
\*   "MsgRollForward", "StIdle">>, and <<"StMustReply", "MsgRollForward",
\*   "StIdle">>."
Transitions ==
    IF Proto = "BlockFetch"
    THEN { <<"StIdle",      "MsgRequestRange", "StBusy">>,
           <<"StIdle",      "MsgClientDone",   "StDone">>,
           <<"StBusy",      "MsgNoBlocks",     "StIdle">>,
           <<"StBusy",      "MsgStartBatch",   "StStreaming">>,
           <<"StStreaming", "MsgBlock",        "StStreaming">>,
           <<"StStreaming", "MsgBatchDone",    "StIdle">> }
    ELSE { <<"StIdle",      "MsgRequestNext",  "StCanAwait">>,
           <<"StIdle",      "MsgDone",         "StDone">>,
           <<"StCanAwait",  "MsgAwaitReply",   "StMustReply">>,
           <<"StCanAwait",  "MsgRollForward",  "StIdle">>,
           <<"StMustReply", "MsgRollForward",  "StIdle">> }

\* In English: "The protocol's request message."
\* Literally: "Request is defined as: if Proto equals "BlockFetch" then
\*   "MsgRequestRange", else "MsgRequestNext"."
Request == IF Proto = "BlockFetch" THEN "MsgRequestRange" ELSE "MsgRequestNext"
\* In English: "The protocol's final message."
\* Literally: "Final is defined as: if Proto equals "BlockFetch" then
\*   "MsgClientDone", else "MsgDone"."
Final   == IF Proto = "BlockFetch" THEN "MsgClientDone"   ELSE "MsgDone"

\* In English: "In StIdle the client may send; in StDone nobody may; the
\* server may in every other state."
\* Literally: "Agency of s is defined as: if s equals "StIdle" then "Client",
\*   else if s equals "StDone" then "Nobody", else "Server"."
Agency(s) == IF s = "StIdle" THEN "Client"
             ELSE IF s = "StDone" THEN "Nobody" ELSE "Server"

\* In English: "Message m is legal in state s if some transition starts with s
\* and m."
\* Literally: "IsLegal of s and m is defined as: there exists a t in Transitions
\*   such that element 1 of t equals s and element 2 of t equals m."
IsLegal(s, m) == \E t \in Transitions : t[1] = s /\ t[2] = m
\* In English: "The state that sending m in s moves to."
\* Literally: "After of s and m is defined as element 3 of the t, chosen from
\*   Transitions, such that element 1 of t equals s and element 2 of t equals
\*   m."
After(s, m)   == (CHOOSE t \in Transitions : t[1] = s /\ t[2] = m)[3]

\* In English: "m's type is listed in s's PipelinedMessageTypes" [G2].
\* Literally: "Fits of s and m is defined as: m equals Request, and if Proto
\*   equals "BlockFetch" then s is a member of the set containing "StBusy" and
\*   "StStreaming", else s is a member of the set containing "StCanAwait" and
\*   "StMustReply"."
Fits(s, m) ==
    /\ m = Request
    /\ IF Proto = "BlockFetch" THEN s \in {"StBusy", "StStreaming"}
                               ELSE s \in {"StCanAwait", "StMustReply"}

\* In English: "s sets AllowPipelinedSend" [G2].
\* Literally: "AllowPipelinedSend of s is defined as: if Proto equals
\*   "BlockFetch" then s is a member of the set containing "StBusy" and
\*   "StStreaming", else s equals "StCanAwait"."
AllowPipelinedSend(s) ==
    IF Proto = "BlockFetch" THEN s \in {"StBusy", "StStreaming"}
                            ELSE s = "StCanAwait"

\* In English: "we may pipeline in s: it allows it, and the peer has
\* agency" (roleMayPipeline).
\* Literally: "MayPipeline of s is defined as: AllowPipelinedSend of s, and
\*   Agency of s equals "Server"."
MayPipeline(s) == AllowPipelinedSend(s) /\ Agency(s) = "Server"

\* In English: "m is legal in some state where we have agency"
\* (messageHasAgencyTransition).
\* Literally: "LegalSomewhere of m is defined as IsLegal of "StIdle" and m."
LegalSomewhere(m) == IsLegal("StIdle", m)

-----------------------------------------------------------------------------

VARIABLES
    \* the client's application
    sq,         \* sendQueueChan: messages enqueued, not yet taken by sendLoop
    enq,        \* requests enqueued so far
    finalEnq,   \* TRUE once the final message is enqueued
    \* sendLoop
    sl,         \* its next step
    cand,       \* the message it is resolving
    held,       \* pipelinedOutbound: a message held back, or NoMsg
    heldWait,   \* TRUE while held waits for agency
    ha,         \* haveAgency for the current batch
    queued,     \* queuedStateTransitions: deferred changes, in send order
    batch,      \* messages gathered for the next segment
    fProg,      \* the current flush applied at least one deferred change
    fStop,      \* the current flush stopped at a change illegal in the state
    \* the engine's shared state
    cur,        \* currentState
    gen,        \* currentStateGeneration
    reserved,   \* peerAgencyReserved
    pReq,       \* pendingPipelinedRequests
    pRep,       \* pendingPipelinedReplies
    token,      \* TRUE when sendReadyChan holds a token
    \* readLoop and recvLoop
    rl,         \* readLoop: "idle", "started", or "stopped"
    snapState, snapGen, snapUnres,  \* the snapshot
    rq,         \* admitted replies: [m |-> message, rr |-> reserved reply?]
    \* the wire
    toServer, toClient,
    \* the honest server
    pview,      \* the state the server believes the protocol is in
    blocks,     \* blocks sent in the current batch
    awaited,    \* TRUE once the server sent MsgAwaitReply for this request
    \* outcomes
    refused,    \* readLoop refused an honest reply
    badChange,  \* a state change was applied in a state where it is illegal
    sendErr,    \* sendLoop rejected a message the client may send
    srvBad,     \* the server received a message illegal in its state
    finalEarly  \* the final message went out with requests outstanding

\* In English: "The client application's variables."
\* Literally: "appVars is defined as the tuple of sq, enq and finalEnq."
appVars  == <<sq, enq, finalEnq>>
\* In English: "sendLoop's variables."
\* Literally: "sendVars is defined as the tuple of sl, cand, held, heldWait, ha,
\*   queued, batch, fProg and fStop."
sendVars == <<sl, cand, held, heldWait, ha, queued, batch, fProg, fStop>>
\* In English: "The engine's shared state."
\* Literally: "engVars is defined as the tuple of cur, gen, reserved, pReq, pRep
\*   and token."
engVars  == <<cur, gen, reserved, pReq, pRep, token>>
\* In English: "readLoop's and recvLoop's variables."
\* Literally: "readVars is defined as the tuple of rl, snapState, snapGen,
\*   snapUnres and rq."
readVars == <<rl, snapState, snapGen, snapUnres, rq>>
\* In English: "The wire."
\* Literally: "wireVars is defined as the tuple of toServer and toClient."
wireVars == <<toServer, toClient>>
\* In English: "The honest server's variables."
\* Literally: "srvVars is defined as the tuple of pview, blocks and awaited."
srvVars  == <<pview, blocks, awaited>>
\* In English: "The outcomes."
\* Literally: "outVars is defined as the tuple of refused, badChange, sendErr,
\*   srvBad and finalEarly."
outVars  == <<refused, badChange, sendErr, srvBad, finalEarly>>
\* Literally: "vars is defined as the tuple of appVars, sendVars, engVars,
\*   readVars, wireVars, srvVars and outVars."
vars == <<appVars, sendVars, engVars, readVars, wireVars, srvVars, outVars>>

\* In English: "Nothing is enqueued, sendLoop waits holding nothing, both sides
\* are in StIdle with nothing pending or in flight, we hold the token, and
\* nothing has failed."
\* Literally: "Init is defined as: sq equals the empty sequence, and enq equals
\*   0, and finalEnq equals FALSE, and sl equals "wait", and cand equals NoMsg,
\*   and held equals NoMsg, and heldWait equals FALSE, and ha equals FALSE, and
\*   queued equals the empty sequence, and batch equals the empty sequence, and
\*   fProg equals FALSE, and fStop equals FALSE, and cur equals "StIdle", and
\*   gen equals 0, and reserved equals FALSE, and pReq equals 0, and pRep equals
\*   0, and token equals TRUE, and rl equals "idle", and snapState equals
\*   "StIdle", and snapGen equals 0, and snapUnres equals FALSE, and rq equals
\*   the empty sequence, and toServer equals the empty sequence, and toClient
\*   equals the empty sequence, and pview equals "StIdle", and blocks equals 0,
\*   and awaited equals FALSE, and refused equals FALSE, and badChange equals
\*   FALSE, and sendErr equals FALSE, and srvBad equals FALSE, and finalEarly
\*   equals FALSE."
Init ==
    /\ sq = <<>> /\ enq = 0 /\ finalEnq = FALSE
    /\ sl = "wait" /\ cand = NoMsg /\ held = NoMsg /\ heldWait = FALSE
    /\ ha = FALSE /\ queued = <<>> /\ batch = <<>>
    /\ fProg = FALSE /\ fStop = FALSE
    /\ cur = "StIdle" /\ gen = 0 /\ reserved = FALSE
    /\ pReq = 0 /\ pRep = 0 /\ token = TRUE   \* we start with agency
    /\ rl = "idle" /\ snapState = "StIdle" /\ snapGen = 0 /\ snapUnres = FALSE
    /\ rq = <<>>
    /\ toServer = <<>> /\ toClient = <<>>
    /\ pview = "StIdle" /\ blocks = 0 /\ awaited = FALSE
    /\ refused = FALSE /\ badChange = FALSE /\ sendErr = FALSE
    /\ srvBad = FALSE /\ finalEarly = FALSE

(***************************************************************************)
(* stateLoop's setState [G1]. In English: "Move to s; the generation moves *)
(* on; the reservation clears. A consumed reply gives back its             *)
(* reservation; a consumed deferred request is no longer pending. On      *)
(* entering a state where the peer talks (or consuming a request), the    *)
(* reservation is re-taken if a reserved reply is still waiting. If we    *)
(* now have agency, a token is deposited."                                *)
(***************************************************************************)
\* Literally: "SetState of s, consumesReply and consumesRequest is defined as:
\*   letting rep be (if consumesReply is true and pRep is greater than 0 then
\*   pRep minus 1, else pRep), and req be (if consumesRequest is true and pReq
\*   is greater than 0 then pReq minus 1, else pReq): cur in the next state
\*   equals s, and gen in the next state equals gen plus 1, and pRep in the next
\*   state equals rep, and pReq in the next state equals req, and reserved in
\*   the next state equals: if consumesRequest is true or Agency of s equals
\*   "Server", then rep is greater than 0, else FALSE; and token in the next
\*   state equals: if Agency of s equals "Client" then TRUE, else token."
SetState(s, consumesReply, consumesRequest) ==
    LET rep == IF consumesReply /\ pRep > 0 THEN pRep - 1 ELSE pRep
        req == IF consumesRequest /\ pReq > 0 THEN pReq - 1 ELSE pReq
    IN /\ cur' = s
       /\ gen' = gen + 1
       /\ pRep' = rep
       /\ pReq' = req
       /\ reserved' = IF consumesRequest \/ Agency(s) = "Server"
                         THEN rep > 0 ELSE FALSE
       /\ token' = IF Agency(s) = "Client" THEN TRUE ELSE token

\* In English: "Apply m's change if it is legal now; otherwise it is an
\* error and nothing changes."
\* Literally: "Apply of m, consumesReply and consumesRequest is defined as: if
\*   IsLegal of cur and m, then SetState of After of cur and m, consumesReply
\*   and consumesRequest, and badChange is unchanged; else badChange in the next
\*   state equals TRUE, and engVars is unchanged."
Apply(m, consumesReply, consumesRequest) ==
    IF IsLegal(cur, m)
       THEN SetState(After(cur, m), consumesReply, consumesRequest)
            /\ UNCHANGED badChange
       ELSE badChange' = TRUE /\ UNCHANGED engVars

-----------------------------------------------------------------------------
(* The client's application: requests, then the final message. *)

\* In English: "While it has requests left, the application enqueues a request."
\* Literally: "AppRequest is defined as: enq is less than MaxRequests, and sq in
\*   the next state equals sq with Request appended, and enq in the next state
\*   equals enq plus 1, and finalEnq, sendVars, engVars, readVars, wireVars,
\*   srvVars and outVars are unchanged."
AppRequest ==
    /\ enq < MaxRequests
    /\ sq' = Append(sq, Request) /\ enq' = enq + 1
    /\ UNCHANGED <<finalEnq, sendVars, engVars, readVars, wireVars, srvVars, outVars>>

\* In English: "After its last request, the application enqueues the final
\* message once."
\* Literally: "AppFinal is defined as: enq equals MaxRequests, and finalEnq is
\*   not true, and sq in the next state equals sq with Final appended, and
\*   finalEnq in the next state equals TRUE, and enq, sendVars, engVars,
\*   readVars, wireVars, srvVars and outVars are unchanged."
AppFinal ==
    /\ enq = MaxRequests /\ ~finalEnq
    /\ sq' = Append(sq, Final) /\ finalEnq' = TRUE
    /\ UNCHANGED <<enq, sendVars, engVars, readVars, wireVars, srvVars, outVars>>

-----------------------------------------------------------------------------
(* sendLoop [G1]. *)

\* In English: "sendLoop waits. Holding a message: for a token. Where it may
\* pipeline: for a token, or a message to dequeue. Otherwise: for a token."
\* Literally: "SendWaitToken is defined as: sl equals "wait", and token is true,
\*   and token in the next state equals FALSE, and ha in the next state equals
\*   TRUE, and heldWait in the next state equals FALSE, and sl in the next state
\*   equals "agency", and cand, held, queued, batch, cur, gen, reserved, pReq,
\*   pRep, fProg and fStop are unchanged, and appVars, readVars, wireVars,
\*   srvVars and outVars are unchanged."
SendWaitToken ==
    /\ sl = "wait" /\ token
    /\ token' = FALSE
    /\ ha' = TRUE
    /\ heldWait' = FALSE
    /\ sl' = "agency"
    /\ UNCHANGED <<cand, held, queued, batch, cur, gen, reserved, pReq, pRep, fProg, fStop>>
    /\ UNCHANGED <<appVars, readVars, wireVars, srvVars, outVars>>

\* haveAgency starts false on every pass of the wait loop; only a token
\* (or resolvePipelinedDequeue) sets it.
\* In English: "Holding nothing, where it may pipeline, sendLoop dequeues the
\* next message to resolve."
\* Literally: "SendWaitDequeue is defined as: sl equals "wait", and held equals
\*   NoMsg, and MayPipeline of cur, and sq does not equal the empty sequence,
\*   and cand in the next state equals the head of sq, and sq in the next state
\*   equals the tail of sq, and ha in the next state equals FALSE, and sl in the
\*   next state equals "resolve", and enq, finalEnq, held, heldWait, queued,
\*   batch, fProg and fStop are unchanged, and engVars, readVars, wireVars,
\*   srvVars and outVars are unchanged."
SendWaitDequeue ==
    /\ sl = "wait" /\ held = NoMsg /\ MayPipeline(cur) /\ sq /= <<>>
    /\ cand' = Head(sq) /\ sq' = Tail(sq)
    /\ ha' = FALSE
    /\ sl' = "resolve"
    /\ UNCHANGED <<enq, finalEnq, held, heldWait, queued, batch, fProg, fStop>>
    /\ UNCHANGED <<engVars, readVars, wireVars, srvVars, outVars>>

\* resolvePipelinedDequeue, first look. In English: "If the message is
\* pipelinable here, send it now. If we lack agency, hold it if it is legal
\* somewhere we have agency, else error. If we have agency (the state
\* changed under us), wait for the token, then flush."
\* Literally: "SendResolve is defined as: sl equals "resolve", and: if Fits of
\*   cur and cand, then held in the next state equals cand, and heldWait in the
\*   next state equals FALSE, and sl in the next state equals "first", and
\*   sendErr is unchanged; else if Agency of cur does not equal "Client", then
\*   (if LegalSomewhere of cand, then held in the next state equals cand, and
\*   heldWait in the next state equals TRUE, and sl in the next state equals
\*   "wait", and sendErr is unchanged; else sendErr in the next state equals
\*   TRUE, and sl in the next state equals "stopped", and held and heldWait are
\*   unchanged); else sl in the next state equals "resolveToken", and held,
\*   heldWait and sendErr are unchanged; and cand, ha, queued, batch, fProg and
\*   fStop are unchanged, and appVars, engVars, readVars, wireVars and srvVars
\*   are unchanged, and refused, badChange, srvBad and finalEarly are
\*   unchanged."
SendResolve ==
    /\ sl = "resolve"
    /\ IF Fits(cur, cand)
          THEN /\ held' = cand /\ heldWait' = FALSE /\ sl' = "first"
               /\ UNCHANGED sendErr
       ELSE IF Agency(cur) /= "Client"
          THEN IF LegalSomewhere(cand)
                  THEN /\ held' = cand /\ heldWait' = TRUE /\ sl' = "wait"
                       /\ UNCHANGED sendErr
                  ELSE /\ sendErr' = TRUE /\ sl' = "stopped"
                       /\ UNCHANGED <<held, heldWait>>
       ELSE /\ sl' = "resolveToken"
            /\ UNCHANGED <<held, heldWait, sendErr>>
    /\ UNCHANGED <<cand, ha, queued, batch, fProg, fStop>>
    /\ UNCHANGED <<appVars, engVars, readVars, wireVars, srvVars>>
    /\ UNCHANGED <<refused, badChange, srvBad, finalEarly>>

\* In English: "Having agency after the state changed under it, sendLoop takes
\* the token and starts a flush."
\* Literally: "SendResolveToken is defined as: sl equals "resolveToken", and
\*   token is true, and token in the next state equals FALSE, and sl in the next
\*   state equals "flush", and fProg in the next state equals FALSE, and fStop
\*   in the next state equals FALSE, and cand, held, heldWait, ha, queued,
\*   batch, cur, gen, reserved, pReq and pRep are unchanged, and appVars,
\*   readVars, wireVars, srvVars and outVars are unchanged."
SendResolveToken ==
    /\ sl = "resolveToken" /\ token
    /\ token' = FALSE
    /\ sl' = "flush"
    /\ fProg' = FALSE /\ fStop' = FALSE
    /\ UNCHANGED <<cand, held, heldWait, ha, queued, batch, cur, gen, reserved, pReq, pRep>>
    /\ UNCHANGED <<appVars, readVars, wireVars, srvVars, outVars>>

\* flushQueuedStateTransitions, one deferred change per step. In English:
\* "Apply the oldest deferred change if it is legal now. If it is not,
\* stateLoop refuses it and changes nothing, and the flush stops there,
\* keeping it and the rest queued." A refused change is not an error here;
\* resolvePipelinedDequeue decides below whether it matters.
\* Literally: "SendFlushOne is defined as: sl equals "flush", and queued does
\*   not equal the empty sequence, and fStop is not true, and: if IsLegal of cur
\*   and the head of queued, then SetState of After of cur and the head of
\*   queued, FALSE and TRUE, and queued in the next state equals the tail of
\*   queued, and fProg in the next state equals TRUE, and fStop is unchanged;
\*   else fStop in the next state equals TRUE, and queued, fProg and engVars are
\*   unchanged; and sl, cand, held, heldWait, ha and batch are unchanged, and
\*   appVars, readVars, wireVars, srvVars and outVars are unchanged."
SendFlushOne ==
    /\ sl = "flush" /\ queued /= <<>> /\ ~fStop
    /\ IF IsLegal(cur, Head(queued))
          THEN /\ SetState(After(cur, Head(queued)), FALSE, TRUE)
               /\ queued' = Tail(queued)
               /\ fProg' = TRUE
               /\ UNCHANGED fStop
          ELSE /\ fStop' = TRUE
               /\ UNCHANGED <<queued, fProg, engVars>>
    /\ UNCHANGED <<sl, cand, held, heldWait, ha, batch>>
    /\ UNCHANGED <<appVars, readVars, wireVars, srvVars, outVars>>

\* After the flush (observeStateAndDrainSendReady drains the token). In
\* English: "Pipelinable now: send it. Lacking agency: hold it (or error if
\* it is never legal). Having agency with nothing deferred: send it as an
\* ordinary message if legal, else error. Having agency with changes still
\* deferred: flush again if this flush made progress, else the refused
\* change is an error."
\* Literally: "SendPostFlush is defined as: sl equals "flush", and (queued
\*   equals the empty sequence or fStop is true), and token in the next state
\*   equals FALSE, and: if Fits of cur and cand, then held in the next state
\*   equals cand, and heldWait in the next state equals FALSE, and sl in the
\*   next state equals "first", and ha, sendErr, fProg and fStop are unchanged;
\*   else if Agency of cur does not equal "Client", then (if LegalSomewhere of
\*   cand, then held in the next state equals cand, and heldWait in the next
\*   state equals TRUE, and sl in the next state equals "wait", and ha, sendErr,
\*   fProg and fStop are unchanged; else sendErr in the next state equals TRUE,
\*   and sl in the next state equals "stopped", and held, heldWait, ha, fProg
\*   and fStop are unchanged); else if queued equals the empty sequence, then
\*   (if IsLegal of cur and cand, then held in the next state equals cand, and
\*   heldWait in the next state equals FALSE, and ha in the next state equals
\*   TRUE, and sl in the next state equals "first", and sendErr, fProg and fStop
\*   are unchanged; else sendErr in the next state equals TRUE, and sl in the
\*   next state equals "stopped", and held, heldWait, ha, fProg and fStop are
\*   unchanged); else if fProg is true, then fProg in the next state equals
\*   FALSE, and fStop in the next state equals FALSE, and held, heldWait, ha, sl
\*   and sendErr are unchanged; else sendErr in the next state equals TRUE, and
\*   sl in the next state equals "stopped", and held, heldWait, ha, fProg and
\*   fStop are unchanged; and cand, queued, batch, cur, gen, reserved, pReq and
\*   pRep are unchanged, and appVars, readVars, wireVars and srvVars are
\*   unchanged, and refused, badChange, srvBad and finalEarly are unchanged."
SendPostFlush ==
    /\ sl = "flush" /\ (queued = <<>> \/ fStop)
    /\ token' = FALSE
    /\ IF Fits(cur, cand)
          THEN /\ held' = cand /\ heldWait' = FALSE /\ sl' = "first"
               /\ UNCHANGED <<ha, sendErr, fProg, fStop>>
       ELSE IF Agency(cur) /= "Client"
          THEN IF LegalSomewhere(cand)
                  THEN /\ held' = cand /\ heldWait' = TRUE /\ sl' = "wait"
                       /\ UNCHANGED <<ha, sendErr, fProg, fStop>>
                  ELSE /\ sendErr' = TRUE /\ sl' = "stopped"
                       /\ UNCHANGED <<held, heldWait, ha, fProg, fStop>>
       ELSE IF queued = <<>>
          THEN IF IsLegal(cur, cand)
                  THEN /\ held' = cand /\ heldWait' = FALSE /\ ha' = TRUE
                       /\ sl' = "first"
                       /\ UNCHANGED <<sendErr, fProg, fStop>>
                  ELSE /\ sendErr' = TRUE /\ sl' = "stopped"
                       /\ UNCHANGED <<held, heldWait, ha, fProg, fStop>>
       ELSE IF fProg
          THEN /\ fProg' = FALSE /\ fStop' = FALSE     \* flush again
               /\ UNCHANGED <<held, heldWait, ha, sl, sendErr>>
          ELSE /\ sendErr' = TRUE /\ sl' = "stopped"
               /\ UNCHANGED <<held, heldWait, ha, fProg, fStop>>
    /\ UNCHANGED <<cand, queued, batch, cur, gen, reserved, pReq, pRep>>
    /\ UNCHANGED <<appVars, readVars, wireVars, srvVars>>
    /\ UNCHANGED <<refused, badChange, srvBad, finalEarly>>

\* In English: "With agency and deferred changes pending, apply the oldest
\* one and go back to waiting; with none, start a batch."
\* Literally: "SendAgency is defined as: sl equals "agency", and: if queued does
\*   not equal the empty sequence, then Apply of the head of queued, FALSE and
\*   TRUE, and queued in the next state equals the tail of queued, and sl in the
\*   next state equals "wait"; else sl in the next state equals "first", and
\*   queued, engVars and badChange are unchanged; and cand, held, heldWait, ha,
\*   batch, fProg and fStop are unchanged, and appVars, readVars, wireVars and
\*   srvVars are unchanged, and refused, sendErr, srvBad and finalEarly are
\*   unchanged."
SendAgency ==
    /\ sl = "agency"
    /\ IF queued /= <<>>
          THEN /\ Apply(Head(queued), FALSE, TRUE)
               /\ queued' = Tail(queued)
               /\ sl' = "wait"
          ELSE /\ sl' = "first"
               /\ UNCHANGED <<queued, engVars, badChange>>
    /\ UNCHANGED <<cand, held, heldWait, ha, batch, fProg, fStop>>
    /\ UNCHANGED <<appVars, readVars, wireVars, srvVars>>
    /\ UNCHANGED <<refused, sendErr, srvBad, finalEarly>>

\* The batch's first message: the held one, or the next dequeued (sendLoop
\* blocks for it). In English: "With agency, apply its change now - and if
\* it is the final message, note whether requests are still outstanding.
\* Without agency (pipelined), defer its change and count it."
\* Literally: "SendFirst is defined as: sl equals "first", and (held does not
\*   equal NoMsg or sq does not equal the empty sequence), and, letting m be (if
\*   held does not equal NoMsg then held, else the head of sq): (if ha is true,
\*   then Apply of m, FALSE and FALSE, and finalEarly in the next state equals
\*   (finalEarly or (m equals Final and (pReq is greater than 0 or queued does
\*   not equal the empty sequence))), and queued is unchanged; else queued in
\*   the next state equals queued with m appended, and pReq in the next state
\*   equals pReq plus 1, and cur, gen, reserved, pRep, token, badChange and
\*   finalEarly are unchanged), and batch in the next state equals the tuple of
\*   m; and sq in the next state equals: if held does not equal NoMsg then sq,
\*   else the tail of sq; and held in the next state equals NoMsg, and sl in the
\*   next state equals "more", and enq, finalEnq, cand, heldWait, ha, fProg and
\*   fStop are unchanged, and readVars, wireVars and srvVars are unchanged, and
\*   refused, sendErr and srvBad are unchanged."
SendFirst ==
    /\ sl = "first"
    /\ held /= NoMsg \/ sq /= <<>>
    /\ LET m == IF held /= NoMsg THEN held ELSE Head(sq) IN
       /\ IF ha
             THEN /\ Apply(m, FALSE, FALSE)
                  /\ finalEarly' = (finalEarly \/ (m = Final /\ (pReq > 0 \/ queued /= <<>>)))
                  /\ UNCHANGED queued
             ELSE /\ queued' = Append(queued, m)
                  /\ pReq' = pReq + 1
                  /\ UNCHANGED <<cur, gen, reserved, pRep, token, badChange, finalEarly>>
       /\ batch' = <<m>>
    /\ sq' = IF held /= NoMsg THEN sq ELSE Tail(sq)
    /\ held' = NoMsg
    /\ sl' = "more"
    /\ UNCHANGED <<enq, finalEnq, cand, heldWait, ha, fProg, fStop>>
    /\ UNCHANGED <<readVars, wireVars, srvVars>>
    /\ UNCHANGED <<refused, sendErr, srvBad>>

\* Later messages in the batch, only if one is already waiting. In English:
\* "If nothing is deferred and we have agency now, take the token and apply
\* its change now. Else if we may pipeline it here, defer and count it.
\* Else hold it (or error if it is never legal) and end the batch."
\* Literally: "SendMore is defined as: sl equals "more", and sq does not equal
\*   the empty sequence, and the length of batch is less than MaxBatch, and,
\*   letting m be the head of sq: if queued equals the empty sequence and Agency
\*   of cur equals "Client", then Apply of m, FALSE and FALSE, and finalEarly in
\*   the next state equals (finalEarly or (m equals Final and pReq is greater
\*   than 0)), and batch in the next state equals batch with m appended, and sq
\*   in the next state equals the tail of sq, and queued, held, heldWait, sl and
\*   sendErr are unchanged; else if MayPipeline of cur and Fits of cur and m,
\*   then queued in the next state equals queued with m appended, and pReq in
\*   the next state equals pReq plus 1, and batch in the next state equals batch
\*   with m appended, and sq in the next state equals the tail of sq, and cur,
\*   gen, reserved, pRep, token, held, heldWait, sl, badChange, sendErr and
\*   finalEarly are unchanged; else if LegalSomewhere of m, then held in the
\*   next state equals m, and heldWait in the next state equals TRUE, and sq in
\*   the next state equals the tail of sq, and sl in the next state equals
\*   "write", and queued, batch, engVars, badChange, sendErr and finalEarly are
\*   unchanged; else sendErr in the next state equals TRUE, and sl in the next
\*   state equals "stopped", and queued, batch, sq, held, heldWait, engVars,
\*   badChange and finalEarly are unchanged; and enq, finalEnq, cand, ha, fProg
\*   and fStop are unchanged, and readVars, wireVars and srvVars are unchanged,
\*   and refused and srvBad are unchanged."
SendMore ==
    /\ sl = "more" /\ sq /= <<>> /\ Len(batch) < MaxBatch
    /\ LET m == Head(sq) IN
       IF queued = <<>> /\ Agency(cur) = "Client"
          THEN /\ Apply(m, FALSE, FALSE)                  \* (token taken)
               /\ finalEarly' = (finalEarly \/ (m = Final /\ pReq > 0))
               /\ batch' = Append(batch, m)
               /\ sq' = Tail(sq)
               /\ UNCHANGED <<queued, held, heldWait, sl, sendErr>>
       ELSE IF MayPipeline(cur) /\ Fits(cur, m)
          THEN /\ queued' = Append(queued, m)
               /\ pReq' = pReq + 1
               /\ batch' = Append(batch, m)
               /\ sq' = Tail(sq)
               /\ UNCHANGED <<cur, gen, reserved, pRep, token, held, heldWait,
                              sl, badChange, sendErr, finalEarly>>
       ELSE IF LegalSomewhere(m)
          THEN /\ held' = m /\ heldWait' = TRUE /\ sq' = Tail(sq)
               /\ sl' = "write"
               /\ UNCHANGED <<queued, batch, engVars, badChange, sendErr, finalEarly>>
          ELSE /\ sendErr' = TRUE /\ sl' = "stopped"
               /\ UNCHANGED <<queued, batch, sq, held, heldWait, engVars,
                              badChange, finalEarly>>
    /\ UNCHANGED <<enq, finalEnq, cand, ha, fProg, fStop>>
    /\ UNCHANGED <<readVars, wireVars, srvVars>>
    /\ UNCHANGED <<refused, srvBad>>

\* In English: "When no more messages are waiting (or the batch is full),
\* write the batch as one segment."
\* Literally: "SendMoreDone is defined as: sl equals "more", and (sq equals the
\*   empty sequence or the length of batch is greater than or equal to
\*   MaxBatch), and sl in the next state equals "write", and appVars, cand,
\*   held, heldWait, ha, queued, batch, fProg and fStop are unchanged, and
\*   engVars, readVars, wireVars, srvVars and outVars are unchanged."
SendMoreDone ==
    /\ sl = "more" /\ (sq = <<>> \/ Len(batch) >= MaxBatch)
    /\ sl' = "write"
    /\ UNCHANGED <<appVars, cand, held, heldWait, ha, queued, batch, fProg, fStop>>
    /\ UNCHANGED <<engVars, readVars, wireVars, srvVars, outVars>>

\* In English: "sendLoop writes the batch to the wire as one segment and goes
\* back to waiting."
\* Literally: "SendWrite is defined as: sl equals "write", and toServer in the
\*   next state equals toServer followed by batch, and batch in the next state
\*   equals the empty sequence, and ha in the next state equals FALSE, and sl in
\*   the next state equals "wait", and appVars, cand, held, heldWait, queued,
\*   fProg and fStop are unchanged, and engVars, readVars, toClient, srvVars and
\*   outVars are unchanged."
SendWrite ==
    /\ sl = "write"
    /\ toServer' = toServer \o batch
    /\ batch' = <<>> /\ ha' = FALSE /\ sl' = "wait"
    /\ UNCHANGED <<appVars, cand, held, heldWait, queued, fProg, fStop>>
    /\ UNCHANGED <<engVars, readVars, toClient, srvVars, outVars>>

-----------------------------------------------------------------------------
(* readLoop and recvLoop [G1]. *)

\* waitForInboundSnapshot, then the snapshot. In English: "When a reply's
\* first bytes are in, and no reserved reply is still unapplied (unless a
\* pipelined request still has no reply), take the snapshot, noting whether
\* a pipelined request is still without a reply."
\* Literally: "ReadStart is defined as: rl equals "idle", and toClient does not
\*   equal the empty sequence, and (pRep is less than pReq, or pRep equals 0),
\*   and snapState in the next state equals cur, and snapGen in the next state
\*   equals gen, and snapUnres in the next state equals (pRep is less than
\*   pReq), and rl in the next state equals "started", and rq, appVars,
\*   sendVars, engVars, wireVars, srvVars and outVars are unchanged."
ReadStart ==
    /\ rl = "idle" /\ toClient /= <<>>
    /\ pRep < pReq \/ pRep = 0
    /\ snapState' = cur /\ snapGen' = gen /\ snapUnres' = (pRep < pReq)
    /\ rl' = "started"
    /\ UNCHANGED <<rq, appVars, sendVars, engVars, wireVars, srvVars, outVars>>

\* reserveInboundAdmission. In English:
\*   peer has agency: refuse if the generation moved and neither the
\*     one-step allowance nor an unreplied pipelined request explains it;
\*     else admit and reserve, or wait if reserved;
\*   we have agency: admit as the reply to a pipelined request if one has
\*     no reply yet (reserving it); otherwise refuse;
\*   nobody: drain.
\* Literally: "Admit is defined as: rl equals "started", and, letting m be the
\*   head of toClient and cont be (gen equals snapGen plus 1 and Agency of
\*   snapState equals "Server"): if Agency of cur equals "Server", then (if gen
\*   does not equal snapGen and cont is not true and snapUnres is not true, then
\*   refused in the next state equals TRUE, and rl in the next state equals
\*   "stopped", and rq, reserved, pRep and toClient are unchanged; else if
\*   reserved is true, then FALSE; else reserved in the next state equals TRUE,
\*   and rq in the next state equals rq with the record whose field m is m and
\*   field rr is FALSE appended, and toClient in the next state equals the tail
\*   of toClient, and rl in the next state equals "idle", and refused and pRep
\*   are unchanged); else if Agency of cur equals "Client", then (if
\*   ReplyReservation is true and snapUnres is true and pRep is less than pReq,
\*   then pRep in the next state equals pRep plus 1, and rq in the next state
\*   equals rq with the record whose field m is m and field rr is TRUE appended,
\*   and toClient in the next state equals the tail of toClient, and rl in the
\*   next state equals "idle", and refused and reserved are unchanged; else
\*   refused in the next state equals TRUE, and rl in the next state equals
\*   "stopped", and rq, reserved, pRep and toClient are unchanged); else
\*   toClient in the next state equals the tail of toClient, and rl in the next
\*   state equals "idle", and rq, reserved, pRep and refused are unchanged; and
\*   snapState, snapGen, snapUnres, cur, gen, pReq and token are unchanged, and
\*   appVars, sendVars, toServer and srvVars are unchanged, and badChange,
\*   sendErr, srvBad and finalEarly are unchanged."
Admit ==
    /\ rl = "started"
    /\ LET m == Head(toClient)
           cont == gen = snapGen + 1 /\ Agency(snapState) = "Server"
       IN
       IF Agency(cur) = "Server"
          THEN IF gen /= snapGen /\ ~cont /\ ~snapUnres
                  THEN /\ refused' = TRUE /\ rl' = "stopped"
                       /\ UNCHANGED <<rq, reserved, pRep, toClient>>
               ELSE IF reserved
                  THEN FALSE                                   \* wait
                  ELSE /\ reserved' = TRUE
                       /\ rq' = Append(rq, [m |-> m, rr |-> FALSE])
                       /\ toClient' = Tail(toClient) /\ rl' = "idle"
                       /\ UNCHANGED <<refused, pRep>>
       ELSE IF Agency(cur) = "Client"
          THEN IF ReplyReservation /\ snapUnres /\ pRep < pReq
                  THEN /\ pRep' = pRep + 1
                       /\ rq' = Append(rq, [m |-> m, rr |-> TRUE])
                       /\ toClient' = Tail(toClient) /\ rl' = "idle"
                       /\ UNCHANGED <<refused, reserved>>
                  ELSE /\ refused' = TRUE /\ rl' = "stopped"
                       /\ UNCHANGED <<rq, reserved, pRep, toClient>>
       ELSE /\ toClient' = Tail(toClient) /\ rl' = "idle"        \* drain
            /\ UNCHANGED <<rq, reserved, pRep, refused>>
    /\ UNCHANGED <<snapState, snapGen, snapUnres, cur, gen, pReq, token>>
    /\ UNCHANGED <<appVars, sendVars, toServer, srvVars>>
    /\ UNCHANGED <<badChange, sendErr, srvBad, finalEarly>>

\* In English: "Once the peer has agency, recvLoop applies the oldest
\* admitted reply, giving back its reply reservation if it had one."
\* Literally: "Handle is defined as: rq does not equal the empty sequence, and
\*   Agency of cur equals "Server", and Apply of the head of rq's m, the head of
\*   rq's rr, and FALSE, and rq in the next state equals the tail of rq, and rl,
\*   snapState, snapGen and snapUnres are unchanged, and appVars, sendVars,
\*   wireVars and srvVars are unchanged, and refused, sendErr, srvBad and
\*   finalEarly are unchanged."
Handle ==
    /\ rq /= <<>> /\ Agency(cur) = "Server"
    /\ Apply(Head(rq).m, Head(rq).rr, FALSE)
    /\ rq' = Tail(rq)
    /\ UNCHANGED <<rl, snapState, snapGen, snapUnres>>
    /\ UNCHANGED <<appVars, sendVars, wireVars, srvVars>>
    /\ UNCHANGED <<refused, sendErr, srvBad, finalEarly>>

-----------------------------------------------------------------------------
(* The honest server: it reads only when it is waiting for us [S8], and    *)
(* answers each request in turn [P1].                                      *)

\* In English: "When the server has given us agency, it reads our oldest message
\* and follows it, or notes that it is illegal."
\* Literally: "ServerRecv is defined as: toServer does not equal the empty
\*   sequence, and Agency of pview equals "Client", and: if IsLegal of pview and
\*   the head of toServer, then pview in the next state equals After of pview
\*   and the head of toServer, and srvBad is unchanged; else srvBad in the next
\*   state equals TRUE, and pview is unchanged; and toServer in the next state
\*   equals the tail of toServer, and blocks in the next state equals 0, and
\*   awaited in the next state equals FALSE, and appVars, sendVars, engVars,
\*   readVars and toClient are unchanged, and refused, badChange, sendErr and
\*   finalEarly are unchanged."
ServerRecv ==
    /\ toServer /= <<>> /\ Agency(pview) = "Client"
    /\ IF IsLegal(pview, Head(toServer))
          THEN /\ pview' = After(pview, Head(toServer)) /\ UNCHANGED srvBad
          ELSE /\ srvBad' = TRUE /\ UNCHANGED pview
    /\ toServer' = Tail(toServer)
    /\ blocks' = 0 /\ awaited' = FALSE
    /\ UNCHANGED <<appVars, sendVars, engVars, readVars, toClient>>
    /\ UNCHANGED <<refused, badChange, sendErr, finalEarly>>

\* In English: "When the server has agency, it sends a legal message: at most
\* MaxBlocks blocks in a batch, and at most one MsgAwaitReply per request."
\* Literally: "ServerSend of m is defined as: Agency of pview equals "Server",
\*   and IsLegal of pview and m, and if m equals "MsgBlock" then blocks is less
\*   than MaxBlocks, and if m equals "MsgAwaitReply" then awaited is not true,
\*   and pview in the next state equals After of pview and m, and toClient in
\*   the next state equals toClient with m appended, and blocks in the next
\*   state equals: if m equals "MsgBlock" then blocks plus 1, else blocks; and
\*   awaited in the next state equals (awaited or m equals "MsgAwaitReply"), and
\*   appVars, sendVars, engVars, readVars, toServer and outVars are unchanged."
ServerSend(m) ==
    /\ Agency(pview) = "Server" /\ IsLegal(pview, m)
    /\ m = "MsgBlock" => blocks < MaxBlocks
    /\ m = "MsgAwaitReply" => ~awaited
    /\ pview' = After(pview, m)
    /\ toClient' = Append(toClient, m)
    /\ blocks' = IF m = "MsgBlock" THEN blocks + 1 ELSE blocks
    /\ awaited' = (awaited \/ m = "MsgAwaitReply")
    /\ UNCHANGED <<appVars, sendVars, engVars, readVars, toServer, outVars>>

-----------------------------------------------------------------------------

\* In English: "Every message type that appears in some transition."
\* Literally: "Messages is defined as the set of element 2 of t, for every t
\*   that is a member of Transitions."
Messages == {t[2] : t \in Transitions}

\* In English: "Something failed."
\* Literally: "Failed is defined as: refused or badChange or sendErr or srvBad."
Failed == refused \/ badChange \/ sendErr \/ srvBad

\* In English: "Finished: we ended the protocol and everything has been
\* sent, read, and applied - or something failed."
\* Literally: "Finished is defined as: (cur equals "StDone", and finalEnq is
\*   true, and sq equals the empty sequence, and held equals NoMsg, and queued
\*   equals the empty sequence, and batch equals the empty sequence, and
\*   toServer equals the empty sequence, and toClient equals the empty sequence,
\*   and rq equals the empty sequence), or Failed; and vars is unchanged."
Finished ==
    /\ \/ /\ cur = "StDone" /\ finalEnq
          /\ sq = <<>> /\ held = NoMsg /\ queued = <<>> /\ batch = <<>>
          /\ toServer = <<>> /\ toClient = <<>> /\ rq = <<>>
       \/ Failed
    /\ UNCHANGED vars

\* In English: "A step is any one step of the application, sendLoop, readLoop,
\* recvLoop, or the server, or being finished."
\* Literally: "Next is defined as: AppRequest or AppFinal, or SendWaitToken or
\*   SendWaitDequeue or SendResolve or SendResolveToken, or SendFlushOne or
\*   SendPostFlush or SendAgency or SendFirst, or SendMore or SendMoreDone or
\*   SendWrite, or ReadStart or Admit or Handle, or ServerRecv or there exists
\*   an m in Messages such that ServerSend of m, or Finished."
Next ==
    \/ AppRequest \/ AppFinal
    \/ SendWaitToken \/ SendWaitDequeue \/ SendResolve \/ SendResolveToken
    \/ SendFlushOne \/ SendPostFlush \/ SendAgency \/ SendFirst
    \/ SendMore \/ SendMoreDone \/ SendWrite
    \/ ReadStart \/ Admit \/ Handle
    \/ ServerRecv \/ \E m \in Messages : ServerSend(m)
    \/ Finished

\* In English: "Start in Init, and take only Next steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Nothing fails: no honest reply refused, no change applied
\* where it is illegal, no legal client message rejected, nothing illegal
\* reaches the server."
\* Literally: "NothingFails is defined as: Failed is not true."
NothingFails == ~Failed

\* In English: "The final message never goes out with pipelined requests
\* still outstanding" - the reference's rule that Done needs n = Zero [R1].
\* Literally: "FinalOnlyWhenNothingOutstanding is defined as: finalEarly is not
\*   true."
FinalOnlyWhenNothingOutstanding == ~finalEarly

\* In English: "When nothing is in flight or pending, both sides agree."
\* Literally: "ViewsAgreeWhenQuiet is defined as: if toServer equals the empty
\*   sequence and toClient equals the empty sequence and rq equals the empty
\*   sequence and queued equals the empty sequence and batch equals the empty
\*   sequence, then cur equals pview."
ViewsAgreeWhenQuiet ==
    (/\ toServer = <<>> /\ toClient = <<>> /\ rq = <<>> /\ queued = <<>>
     /\ batch = <<>>) => cur = pview
=============================================================================
