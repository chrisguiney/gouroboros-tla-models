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

NoMsg == "none"

(***************************************************************************)
(* The protocols: the specification's transitions [B1][C1], and what       *)
(* gOuroboros's state tables add for pipelining [G2]. We are the client.  *)
(***************************************************************************)
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

Request == IF Proto = "BlockFetch" THEN "MsgRequestRange" ELSE "MsgRequestNext"
Final   == IF Proto = "BlockFetch" THEN "MsgClientDone"   ELSE "MsgDone"

\* In English: "In StIdle the client may send; in StDone nobody may; the
\* server may in every other state."
Agency(s) == IF s = "StIdle" THEN "Client"
             ELSE IF s = "StDone" THEN "Nobody" ELSE "Server"

IsLegal(s, m) == \E t \in Transitions : t[1] = s /\ t[2] = m
After(s, m)   == (CHOOSE t \in Transitions : t[1] = s /\ t[2] = m)[3]

\* In English: "m's type is listed in s's PipelinedMessageTypes" [G2].
Fits(s, m) ==
    /\ m = Request
    /\ IF Proto = "BlockFetch" THEN s \in {"StBusy", "StStreaming"}
                               ELSE s \in {"StCanAwait", "StMustReply"}

\* In English: "s sets AllowPipelinedSend" [G2].
AllowPipelinedSend(s) ==
    IF Proto = "BlockFetch" THEN s \in {"StBusy", "StStreaming"}
                            ELSE s = "StCanAwait"

\* In English: "we may pipeline in s: it allows it, and the peer has
\* agency" (roleMayPipeline).
MayPipeline(s) == AllowPipelinedSend(s) /\ Agency(s) = "Server"

\* In English: "m is legal in some state where we have agency"
\* (messageHasAgencyTransition).
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

appVars  == <<sq, enq, finalEnq>>
sendVars == <<sl, cand, held, heldWait, ha, queued, batch, fProg, fStop>>
engVars  == <<cur, gen, reserved, pReq, pRep, token>>
readVars == <<rl, snapState, snapGen, snapUnres, rq>>
wireVars == <<toServer, toClient>>
srvVars  == <<pview, blocks, awaited>>
outVars  == <<refused, badChange, sendErr, srvBad, finalEarly>>
vars == <<appVars, sendVars, engVars, readVars, wireVars, srvVars, outVars>>

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
Apply(m, consumesReply, consumesRequest) ==
    IF IsLegal(cur, m)
       THEN SetState(After(cur, m), consumesReply, consumesRequest)
            /\ UNCHANGED badChange
       ELSE badChange' = TRUE /\ UNCHANGED engVars

-----------------------------------------------------------------------------
(* The client's application: requests, then the final message. *)

AppRequest ==
    /\ enq < MaxRequests
    /\ sq' = Append(sq, Request) /\ enq' = enq + 1
    /\ UNCHANGED <<finalEnq, sendVars, engVars, readVars, wireVars, srvVars, outVars>>

AppFinal ==
    /\ enq = MaxRequests /\ ~finalEnq
    /\ sq' = Append(sq, Final) /\ finalEnq' = TRUE
    /\ UNCHANGED <<enq, sendVars, engVars, readVars, wireVars, srvVars, outVars>>

-----------------------------------------------------------------------------
(* sendLoop [G1]. *)

\* In English: "sendLoop waits. Holding a message: for a token. Where it may
\* pipeline: for a token, or a message to dequeue. Otherwise: for a token."
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
SendMoreDone ==
    /\ sl = "more" /\ (sq = <<>> \/ Len(batch) >= MaxBatch)
    /\ sl' = "write"
    /\ UNCHANGED <<appVars, cand, held, heldWait, ha, queued, batch, fProg, fStop>>
    /\ UNCHANGED <<engVars, readVars, wireVars, srvVars, outVars>>

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

ServerRecv ==
    /\ toServer /= <<>> /\ Agency(pview) = "Client"
    /\ IF IsLegal(pview, Head(toServer))
          THEN /\ pview' = After(pview, Head(toServer)) /\ UNCHANGED srvBad
          ELSE /\ srvBad' = TRUE /\ UNCHANGED pview
    /\ toServer' = Tail(toServer)
    /\ blocks' = 0 /\ awaited' = FALSE
    /\ UNCHANGED <<appVars, sendVars, engVars, readVars, toClient>>
    /\ UNCHANGED <<refused, badChange, sendErr, finalEarly>>

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

Messages == {t[2] : t \in Transitions}

Failed == refused \/ badChange \/ sendErr \/ srvBad

\* In English: "Finished: we ended the protocol and everything has been
\* sent, read, and applied - or something failed."
Finished ==
    /\ \/ /\ cur = "StDone" /\ finalEnq
          /\ sq = <<>> /\ held = NoMsg /\ queued = <<>> /\ batch = <<>>
          /\ toServer = <<>> /\ toClient = <<>> /\ rq = <<>>
       \/ Failed
    /\ UNCHANGED vars

Next ==
    \/ AppRequest \/ AppFinal
    \/ SendWaitToken \/ SendWaitDequeue \/ SendResolve \/ SendResolveToken
    \/ SendFlushOne \/ SendPostFlush \/ SendAgency \/ SendFirst
    \/ SendMore \/ SendMoreDone \/ SendWrite
    \/ ReadStart \/ Admit \/ Handle
    \/ ServerRecv \/ \E m \in Messages : ServerSend(m)
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Nothing fails: no honest reply refused, no change applied
\* where it is illegal, no legal client message rejected, nothing illegal
\* reaches the server."
NothingFails == ~Failed

\* In English: "The final message never goes out with pipelined requests
\* still outstanding" - the reference's rule that Done needs n = Zero [R1].
FinalOnlyWhenNothingOutstanding == ~finalEarly

\* In English: "When nothing is in flight or pending, both sides agree."
ViewsAgreeWhenQuiet ==
    (/\ toServer = <<>> /\ toClient = <<>> /\ rq = <<>> /\ queued = <<>>
     /\ batch = <<>>) => cur = pview
=============================================================================
