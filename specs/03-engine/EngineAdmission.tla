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
\* In English: "The keep-alive protocol's transitions."
\* Literally: "KATransitions is defined as the set containing these three
\*   tuples: <<"StClient", "MsgKeepAlive", "StServer">>, <<"StClient",
\*   "MsgDone", "StDone">>, and <<"StServer", "MsgKeepAliveResponse",
\*   "StClient">>."
KATransitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

\* [C1]
\* In English: "The chain-sync protocol's transitions."
\* Literally: "CSTransitions is defined as the set containing these ten tuples:
\*   <<"StIdle", "MsgRequestNext", "StCanAwait">>, <<"StIdle",
\*   "MsgFindIntersect", "StIntersect">>, <<"StIdle", "MsgDone", "StDone">>,
\*   <<"StCanAwait", "MsgAwaitReply", "StMustReply">>, <<"StCanAwait",
\*   "MsgRollForward", "StIdle">>, <<"StCanAwait", "MsgRollBackward",
\*   "StIdle">>, <<"StMustReply", "MsgRollForward", "StIdle">>, <<"StMustReply",
\*   "MsgRollBackward", "StIdle">>, <<"StIntersect", "MsgIntersectFound",
\*   "StIdle">>, and <<"StIntersect", "MsgIntersectNotFound", "StIdle">>."
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
\* In English: "The block-fetch protocol's transitions."
\* Literally: "BFTransitions is defined as the set containing these six tuples:
\*   <<"StIdle", "MsgRequestRange", "StBusy">>, <<"StIdle", "MsgClientDone",
\*   "StDone">>, <<"StBusy", "MsgNoBlocks", "StIdle">>, <<"StBusy",
\*   "MsgStartBatch", "StStreaming">>, <<"StStreaming", "MsgBlock",
\*   "StStreaming">>, and <<"StStreaming", "MsgBatchDone", "StIdle">>."
BFTransitions ==
    { <<"StIdle",      "MsgRequestRange", "StBusy">>,
      <<"StIdle",      "MsgClientDone",   "StDone">>,
      <<"StBusy",      "MsgNoBlocks",     "StIdle">>,
      <<"StBusy",      "MsgStartBatch",   "StStreaming">>,
      <<"StStreaming", "MsgBlock",        "StStreaming">>,
      <<"StStreaming", "MsgBatchDone",    "StIdle">> }

\* In English: "the transitions, initial state, and client-agency states of
\* the protocol being checked."
\* Literally: "Transitions is defined as: in the case Proto equals "KeepAlive",
\*   KATransitions; in the case Proto equals "ChainSync", CSTransitions; in the
\*   case Proto equals "BlockFetch", BFTransitions."
Transitions == CASE Proto = "KeepAlive"  -> KATransitions
               []   Proto = "ChainSync"  -> CSTransitions
               []   Proto = "BlockFetch" -> BFTransitions

\* Literally: "Initial is defined as: if Proto equals "KeepAlive" then
\*   "StClient", else "StIdle"."
Initial == IF Proto = "KeepAlive" THEN "StClient" ELSE "StIdle"

\* Literally: "ClientStates is defined as: if Proto equals "KeepAlive" then the
\*   set containing "StClient", else the set containing "StIdle"."
ClientStates == IF Proto = "KeepAlive" THEN {"StClient"} ELSE {"StIdle"}

\* In English: "who may send in state s: the client in its states, nobody in
\* StDone, the server everywhere else" ([K1][C1][B1] agency tables).
\* Literally: "Agency of s is defined as: if s is a member of ClientStates then
\*   "Client", else if s equals "StDone" then "Nobody", else "Server"."
Agency(s) == IF s \in ClientStates THEN "Client"
             ELSE IF s = "StDone" THEN "Nobody"
             ELSE "Server"

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

\* In English: "m is how the client ends the protocol."
\* Literally: "IsDone of m is defined as: m is a member of the set containing
\*   "MsgDone" and "MsgClientDone"."
IsDone(m) == m \in {"MsgDone", "MsgClientDone"}

\* In English: "m keeps the server talking" - a message the server may send
\* several of in a row, which the model bounds with MaxStreak.
\* Literally: "KeepsPeerTalking of s and m is defined as: IsLegal of s and m,
\*   and Agency of After of s and m equals "Server"."
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

\* Literally: "vars is defined as the tuple of all fourteen variables."
vars == <<cur, gen, reserved, rq, rl, snapState, snapGen, requests, toClient,
          toServer, pview, streak, refused, badChange>>

\* In English: "The variables of our side's engine."
\* Literally: "engineVars is defined as the tuple of cur, gen, reserved, rq, rl,
\*   snapState and snapGen."
engineVars == <<cur, gen, reserved, rq, rl, snapState, snapGen>>

\* In English: "Both sides start in the initial state, with nothing sent."
\* Literally: "Init is defined as: cur equals Initial, and gen equals 0, and
\*   reserved equals FALSE, and rq equals the empty sequence, and rl equals
\*   "idle", and snapState equals Initial, and snapGen equals 0, and requests
\*   equals 0, and toClient equals the empty sequence, and toServer equals the
\*   empty sequence, and pview equals Initial, and streak equals 0, and refused
\*   equals FALSE, and badChange equals FALSE."
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
\* Literally: "LocalSend of m is defined as: Agency of cur equals "Client", and
\*   IsLegal of cur and m, and if IsDone of m then requests equals MaxRequests,
\*   else requests is less than MaxRequests, and cur in the next state equals
\*   After of cur and m, and gen in the next state equals gen plus 1, and
\*   reserved in the next state equals FALSE, and toServer in the next state
\*   equals toServer with m appended, and requests in the next state equals: if
\*   IsDone of m then requests, else requests plus 1, and rq, rl, snapState,
\*   snapGen, toClient, pview, streak, refused and badChange are unchanged."
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
\* Literally: "ReadStart is defined as: rl equals "idle", and toClient does not
\*   equal the empty sequence, and snapState in the next state equals cur, and
\*   snapGen in the next state equals gen, and rl in the next state equals
\*   "started", and cur, gen, reserved, rq, requests, toClient, toServer, pview,
\*   streak, refused and badChange are unchanged."
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
\* Literally: "GenerationOK is defined as: gen equals snapGen, or
\*   (ContinuesPeerAgency is true, and gen equals snapGen plus 1, and Agency of
\*   snapState equals "Server")."
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
\* Literally: "Admit is defined as: rl equals "started", and, letting m be the
\*   head of toClient: if Agency of cur equals "Server", then (if GenerationOK
\*   is not true, then refused in the next state equals TRUE and rl in the next
\*   state equals "stopped" and rq, reserved and toClient are unchanged; else if
\*   ReserveOne is true and reserved is true, then FALSE; else rq in the next
\*   state equals rq with m appended, and reserved in the next state equals
\*   TRUE, and toClient in the next state equals the tail of toClient, and rl in
\*   the next state equals "idle", and refused is unchanged); else if Agency of
\*   cur equals "Nobody", then toClient in the next state equals the tail of
\*   toClient, and rl in the next state equals "idle", and rq, reserved and
\*   refused are unchanged; else refused in the next state equals TRUE, and rl
\*   in the next state equals "stopped", and rq, reserved and toClient are
\*   unchanged; and cur, gen, snapState, snapGen, requests, toServer, pview,
\*   streak and badChange are unchanged."
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
\* Literally: "Handle is defined as: rq does not equal the empty sequence, and
\*   Agency of cur equals "Server", and, letting m be the head of rq: if IsLegal
\*   of cur and m, then cur in the next state equals After of cur and m, and gen
\*   in the next state equals gen plus 1, and reserved in the next state equals
\*   FALSE, and badChange is unchanged; else badChange in the next state equals
\*   TRUE, and cur, gen and reserved are unchanged; and rq in the next state
\*   equals the tail of rq, and rl, snapState, snapGen, requests, toClient,
\*   toServer, pview, streak and refused are unchanged."
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
\* Literally: "PeerRecv is defined as: toServer does not equal the empty
\*   sequence, and pview in the next state equals After of pview and the head of
\*   toServer, and toServer in the next state equals the tail of toServer, and
\*   streak in the next state equals 0, and engineVars is unchanged, and
\*   requests, toClient, refused and badChange are unchanged."
PeerRecv ==
    /\ toServer /= <<>>
    /\ pview' = After(pview, Head(toServer))
    /\ toServer' = Tail(toServer)
    /\ streak' = 0
    /\ UNCHANGED engineVars
    /\ UNCHANGED <<requests, toClient, refused, badChange>>

\* In English: "When the peer believes it has agency, it sends any legal
\* message; one that keeps it talking only while its streak allows."
\* Literally: "PeerSend of m is defined as: Agency of pview equals "Server", and
\*   IsLegal of pview and m, and if KeepsPeerTalking of pview and m, then streak
\*   is less than MaxStreak, and pview in the next state equals After of pview
\*   and m, and toClient in the next state equals toClient with m appended, and
\*   streak in the next state equals streak plus 1, and engineVars is unchanged,
\*   and requests, toServer, refused and badChange are unchanged."
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

\* In English: "Every message type that appears in some transition."
\* Literally: "Messages is defined as the set of element 2 of t, for every t
\*   that is a member of Transitions."
Messages == {t[2] : t \in Transitions}

\* In English: "Everything is finished: we ended the protocol and every
\* message has been read and handled." Anything else where no step is
\* possible is a deadlock.
\* Literally: "Finished is defined as: (cur equals "StDone", and toClient equals
\*   the empty sequence, and toServer equals the empty sequence, and rq equals
\*   the empty sequence), or refused is true, or badChange is true; and vars is
\*   unchanged."
Finished ==
    /\ \/ /\ cur = "StDone"
          /\ toClient = <<>> /\ toServer = <<>> /\ rq = <<>>
       \/ refused \/ badChange
    /\ UNCHANGED vars

\* In English: "A step is a send by either side, a read, an admission, a handled
\* message, a peer read, or being finished."
\* Literally: "Next is defined as: there exists an m in Messages such that
\*   LocalSend of m or PeerSend of m; or ReadStart, or Admit, or Handle, or
\*   PeerRecv; or Finished."
Next ==
    \/ \E m \in Messages : LocalSend(m) \/ PeerSend(m)
    \/ ReadStart \/ Admit \/ Handle \/ PeerRecv
    \/ Finished

\* In English: "Start in Init, and take only Next steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "An honest peer is never refused, and nothing admitted is
\* ever illegal when applied."
\* Literally: "NoFalseViolation is defined as: refused is not true, and
\*   badChange is not true."
NoFalseViolation == ~refused /\ ~badChange

\* In English: "At most one admitted message waits for recvLoop at a time."
\* Literally: "AtMostOneAdmitted is defined as: the length of rq is less than or
\*   equal to 1."
AtMostOneAdmitted == Len(rq) <= 1

\* In English: "When nothing is in flight, both sides agree on the state."
\* Literally: "ViewsAgreeWhenQuiet is defined as: if toClient equals the empty
\*   sequence and toServer equals the empty sequence and rq equals the empty
\*   sequence, then cur equals pview."
ViewsAgreeWhenQuiet ==
    (toClient = <<>> /\ toServer = <<>> /\ rq = <<>>) => cur = pview
=============================================================================
