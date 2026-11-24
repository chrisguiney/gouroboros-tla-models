--------------------------- MODULE EngineAdmission ---------------------------
(***************************************************************************)
(* Model 03, slice 1: how the gOuroboros protocol engine decides whether  *)
(* to accept an incoming message ("admission"), for protocols that do not *)
(* pipeline.                                                               *)
(*                                                                         *)
(* Every mini-protocol in gOuroboros runs on one engine,                   *)
(* protocol/protocol.go. Four goroutines share each protocol instance:     *)
(*   readLoop   reads bytes and decides, message by message, whether to    *)
(*              admit it;                                                  *)
(*   recvLoop   takes admitted messages, applies their state change, and   *)
(*              calls the protocol's handler;                              *)
(*   sendLoop   sends this side's messages, applying each one's state      *)
(*              change BEFORE writing it to the wire;                      *)
(*   stateLoop  applies every state change, one at a time.                 *)
(*                                                                         *)
(* The admission rule (reserveInboundAdmission), read from the code:       *)
(*   - When a message's first bytes arrive, readLoop takes a SNAPSHOT of   *)
(*     the current state and its GENERATION (a counter stateLoop bumps on  *)
(*     every state change).                                                *)
(*   - When its type is known, readLoop asks to admit it, against the      *)
(*     state at that moment:                                               *)
(*       peer has agency: refuse if the generation moved since the         *)
(*         snapshot - unless it moved by exactly one and the snapshot's    *)
(*         state also had the peer talking (continuesPeerAgency). Then,    *)
(*         if no earlier message is still reserved, admit and reserve      *)
(*         (peerAgencyReserved); if one is, wait and ask again.            *)
(*       we have agency, or nobody does: refuse (a terminal state drains   *)
(*         the message instead).                                           *)
(*   - Every state change clears the reservation.                          *)
(*                                                                         *)
(* The peer is honest: it sends only when it has agency, and only legal    *)
(* messages. The property: such a peer is never refused, and nothing       *)
(* deadlocks - for every interleaving of the four goroutines and the       *)
(* network.                                                                *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e,            *)
(* docs/network-spec/miniprotocols.tex:                                    *)
(*   [S1] 27-36: one side has agency at a time.                            *)
(*   [C1] 838-849, 894-907: chain-sync agencies and transitions.           *)
(*   [B1] 1160-1202: block-fetch agencies and transitions.                 *)
(*   [K1] 1575-1598: keep-alive.                                           *)
(* gOuroboros (blinklabs-io/gouroboros commit 79786c01), protocol.go:      *)
(*   reserveInboundAdmission, waitForInboundAdmissionWithWait, readLoop    *)
(*   (snapshot at the first bytes, admission at the type), recvLoop (waits *)
(*   for peerHasAgency, then transitionInboundState), stateLoop (setState: *)
(*   generation++, peerAgencyReserved = false), sendLoop (transitionState  *)
(*   before the segment is written).                                       *)
(*                                                                         *)
(* Not in this slice: pipelining (PipelinedMessageTypes, pipelined         *)
(* requests and replies), which the next slices add.                       *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Proto,                  \* "KeepAlive", "ChainSync", or "BlockFetch"
    MaxRequests,            \* how many requests our side (the client) makes
    MaxStreak,              \* how many messages in a row the peer may send
    ContinuesPeerAgency,    \* TRUE (gOuroboros): allow one generation of drift
    ReserveOne              \* TRUE (gOuroboros): admit one message at a time

(***************************************************************************)
(* The protocols, from the specification. We are the client; the peer is  *)
(* the server. Each transition is <<from-state, message, to-state>>.       *)
(***************************************************************************)

\* [K1]
KATransitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

\* [C1]
CSTransitions ==
    { <<"StIdle",      "MsgRequestNext",       "StCanAwait">>,
      <<"StIdle",      "MsgFindIntersect",     "StIntersect">>,
      <<"StIdle",      "MsgDone",              "StDone">>,
      <<"StCanAwait",  "MsgAwaitReply",        "StMustReply">>,
      <<"StCanAwait",  "MsgRollForward",       "StIdle">>,
      <<"StCanAwait",  "MsgRollBackward",      "StIdle">>,
      <<"StMustReply", "MsgRollForward",       "StIdle">>,
      <<"StMustReply", "MsgRollBackward",      "StIdle">>,
      <<"StIntersect", "MsgIntersectFound",    "StIdle">>,
      <<"StIntersect", "MsgIntersectNotFound", "StIdle">> }

\* [B1]
BFTransitions ==
    { <<"StIdle",      "MsgRequestRange", "StBusy">>,
      <<"StIdle",      "MsgClientDone",   "StDone">>,
      <<"StBusy",      "MsgNoBlocks",     "StIdle">>,
      <<"StBusy",      "MsgStartBatch",   "StStreaming">>,
      <<"StStreaming", "MsgBlock",        "StStreaming">>,
      <<"StStreaming", "MsgBatchDone",    "StIdle">> }

\* In English: "the transitions, initial state, and client-agency states of
\* the protocol being checked."
Transitions == CASE Proto = "KeepAlive"  -> KATransitions
               []   Proto = "ChainSync"  -> CSTransitions
               []   Proto = "BlockFetch" -> BFTransitions

Initial == IF Proto = "KeepAlive" THEN "StClient" ELSE "StIdle"

ClientStates == IF Proto = "KeepAlive" THEN {"StClient"} ELSE {"StIdle"}

\* In English: "who may send in state s: the client in its states, nobody in
\* StDone, the server everywhere else" ([K1][C1][B1] agency tables).
Agency(s) == IF s \in ClientStates THEN "Client"
             ELSE IF s = "StDone" THEN "Nobody"
             ELSE "Server"

IsLegal(s, m) == \E t \in Transitions : t[1] = s /\ t[2] = m
After(s, m)   == (CHOOSE t \in Transitions : t[1] = s /\ t[2] = m)[3]

\* In English: "m is how the client ends the protocol."
IsDone(m) == m \in {"MsgDone", "MsgClientDone"}

\* In English: "m keeps the server talking" - a message the server may send
\* several of in a row, which the model bounds with MaxStreak.
KeepsPeerTalking(s, m) == IsLegal(s, m) /\ Agency(After(s, m)) = "Server"

-----------------------------------------------------------------------------

VARIABLES
    \* --- our side: the gOuroboros engine ---
    cur,        \* currentState
    gen,        \* currentStateGeneration
    reserved,   \* peerAgencyReserved
    rq,         \* messages readLoop admitted, waiting for recvLoop
    rl,         \* readLoop: "idle", "started" (snapshot taken), or "stopped"
    snapState,  \* the snapshot's state
    snapGen,    \* the snapshot's generation
    requests,   \* requests our side has made
    \* --- the wire ---
    toClient,   \* messages from the peer, not yet read, oldest first
    toServer,   \* messages from us, not yet read by the peer
    \* --- the honest peer ---
    pview,      \* the state the peer believes the protocol is in
    streak,     \* messages the peer has sent in a row
    \* --- outcomes ---
    refused,    \* TRUE if readLoop refused a message
    badChange   \* TRUE if recvLoop found an admitted message illegal

vars == <<cur, gen, reserved, rq, rl, snapState, snapGen, requests, toClient,
          toServer, pview, streak, refused, badChange>>

engineVars == <<cur, gen, reserved, rq, rl, snapState, snapGen>>

\* In English: "Both sides start in the initial state, with nothing sent."
Init ==
    /\ cur = Initial
    /\ gen = 0
    /\ reserved = FALSE
    /\ rq = <<>>
    /\ rl = "idle"
    /\ snapState = Initial
    /\ snapGen = 0
    /\ requests = 0
    /\ toClient = <<>>
    /\ toServer = <<>>
    /\ pview = Initial
    /\ streak = 0
    /\ refused = FALSE
    /\ badChange = FALSE

-----------------------------------------------------------------------------
(* Our side. *)

\* In English: "When we have agency, our sendLoop sends a legal message: a
\* request while we have requests left, or done when we do not. stateLoop
\* applies its state change first - the generation moves on and the
\* reservation clears - and only then is it written to the wire."
LocalSend(m) ==
    /\ Agency(cur) = "Client"
    /\ IsLegal(cur, m)
    /\ IF IsDone(m) THEN requests = MaxRequests ELSE requests < MaxRequests
    /\ cur' = After(cur, m)
    /\ gen' = gen + 1
    /\ reserved' = FALSE
    /\ toServer' = Append(toServer, m)
    /\ requests' = IF IsDone(m) THEN requests ELSE requests + 1
    /\ UNCHANGED <<rq, rl, snapState, snapGen, toClient, pview, streak,
                   refused, badChange>>

\* In English: "When the oldest unread message's first bytes are in, and
\* readLoop is free, it snapshots the current state and generation."
ReadStart ==
    /\ rl = "idle"
    /\ toClient /= <<>>
    /\ snapState' = cur
    /\ snapGen' = gen
    /\ rl' = "started"
    /\ UNCHANGED <<cur, gen, reserved, rq, requests, toClient, toServer,
                   pview, streak, refused, badChange>>

\* In English: "the generation has not moved since the snapshot, or it moved
\* by exactly one while the peer was talking in the snapshot's state too."
GenerationOK ==
    \/ gen = snapGen
    \/ /\ ContinuesPeerAgency
       /\ gen = snapGen + 1
       /\ Agency(snapState) = "Server"

\* In English: "readLoop asks to admit the message, against the state now:
\*   - peer has agency, generation OK, no reservation: admit and reserve;
\*   - peer has agency, generation OK, reserved: wait (no step until
\*     something changes - gOuroboros polls every millisecond);
\*   - peer has agency, generation moved: refuse;
\*   - nobody has agency (StDone): drain the message;
\*   - we have agency: refuse."
Admit ==
    /\ rl = "started"
    /\ LET m == Head(toClient) IN
       IF Agency(cur) = "Server"
          THEN IF ~GenerationOK
                  THEN /\ refused' = TRUE
                       /\ rl' = "stopped"
                       /\ UNCHANGED <<rq, reserved, toClient>>
               ELSE IF ReserveOne /\ reserved
                  THEN FALSE                            \* wait
                  ELSE /\ rq' = Append(rq, m)           \* admit
                       /\ reserved' = TRUE
                       /\ toClient' = Tail(toClient)
                       /\ rl' = "idle"
                       /\ UNCHANGED refused
       ELSE IF Agency(cur) = "Nobody"
          THEN /\ toClient' = Tail(toClient)             \* drain
               /\ rl' = "idle"
               /\ UNCHANGED <<rq, reserved, refused>>
          ELSE /\ refused' = TRUE                        \* refuse
               /\ rl' = "stopped"
               /\ UNCHANGED <<rq, reserved, toClient>>
    /\ UNCHANGED <<cur, gen, snapState, snapGen, requests, toServer, pview,
                   streak, badChange>>

\* In English: "Once the peer has agency, recvLoop takes the oldest admitted
\* message and asks stateLoop to apply it: if it is legal, the state moves
\* on, the generation moves on, and the reservation clears; if not, that is
\* an error."
Handle ==
    /\ rq /= <<>>
    /\ Agency(cur) = "Server"
    /\ LET m == Head(rq) IN
       IF IsLegal(cur, m)
          THEN /\ cur' = After(cur, m)
               /\ gen' = gen + 1
               /\ reserved' = FALSE
               /\ UNCHANGED badChange
          ELSE /\ badChange' = TRUE
               /\ UNCHANGED <<cur, gen, reserved>>
    /\ rq' = Tail(rq)
    /\ UNCHANGED <<rl, snapState, snapGen, requests, toClient, toServer,
                   pview, streak, refused>>

-----------------------------------------------------------------------------
(* The honest peer. *)

\* In English: "The peer reads our oldest message and follows it."
PeerRecv ==
    /\ toServer /= <<>>
    /\ pview' = After(pview, Head(toServer))
    /\ toServer' = Tail(toServer)
    /\ streak' = 0
    /\ UNCHANGED engineVars
    /\ UNCHANGED <<requests, toClient, refused, badChange>>

\* In English: "When the peer believes it has agency, it sends any legal
\* message; one that keeps it talking only while its streak allows."
PeerSend(m) ==
    /\ Agency(pview) = "Server"
    /\ IsLegal(pview, m)
    /\ KeepsPeerTalking(pview, m) => streak < MaxStreak
    /\ pview' = After(pview, m)
    /\ toClient' = Append(toClient, m)
    /\ streak' = streak + 1
    /\ UNCHANGED engineVars
    /\ UNCHANGED <<requests, toServer, refused, badChange>>

-----------------------------------------------------------------------------

Messages == {t[2] : t \in Transitions}

\* In English: "Everything is finished: we ended the protocol and every
\* message has been read and handled." Anything else where no step is
\* possible is a deadlock.
Finished ==
    /\ \/ /\ cur = "StDone"
          /\ toClient = <<>> /\ toServer = <<>> /\ rq = <<>>
       \/ refused \/ badChange
    /\ UNCHANGED vars

Next ==
    \/ \E m \in Messages : LocalSend(m) \/ PeerSend(m)
    \/ ReadStart \/ Admit \/ Handle \/ PeerRecv
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "An honest peer is never refused, and nothing admitted is
\* ever illegal when applied."
NoFalseViolation == ~refused /\ ~badChange

\* In English: "At most one admitted message waits for recvLoop at a time."
AtMostOneAdmitted == Len(rq) <= 1

\* In English: "When nothing is in flight, both sides agree on the state."
ViewsAgreeWhenQuiet ==
    (toClient = <<>> /\ toServer = <<>> /\ rq = <<>>) => cur = pview
=============================================================================
