------------------------------ MODULE DmqRestart ------------------------------
(***************************************************************************)
(* Model 11, part 4: the DMQ servers after MsgDone.                        *)
(*                                                                         *)
(* A mini-protocol run ends when the client sends MsgDone (MsgClientDone   *)
(* in local message notification). The connection stays open, and the     *)
(* client may start a new run of the same protocol on it. The rule for    *)
(* the server's side is the inbound governor's: a responder that ended     *)
(* cleanly is restarted in its initial state, so the new run's first       *)
(* message is read and answered. gOuroboros d8f5bc2a does not do this for  *)
(* the three DMQ servers: each stays in StDone, and the new run's first    *)
(* message is never read.                                                  *)
(*                                                                         *)
(* One module serves the three protocols. Proto picks the protocol, and    *)
(* with it the state table both peers follow. Each peer sends, while its   *)
(* own view gives it agency, any message its table allows; each reads the *)
(* other's messages in order and judges them against its own view.         *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NewRunServed  a message waiting for the server can be read.           *)
(*   NoViolation   no side receives a message its state forbids.           *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [S5] ouroboros-network 5f356486ab3e, docs/network-spec/               *)
(*        connection-manager.tex 492-496: the server side of a             *)
(*        mini-protocol "should be restarted in its initial state in case  *)
(*        the client wishes to use the protocol again later".              *)
(*   [R11] ouroboros-network 5f356486ab3e, ouroboros-network/framework/    *)
(*        lib/Ouroboros/Network/InboundGovernor.hs 455-470: a responder    *)
(*        that terminated without error is run again                       *)
(*        (TrResponderRestarted); lib/Ouroboros/Network/Diffusion.hs       *)
(*        402-418: the node-to-client server runs under an inbound         *)
(*        governor too.                                                    *)
(*   [R12] dmq-node a267003c, dmq-node/app/Main.hs 270: dmq-node runs      *)
(*        Ouroboros.Network.Diffusion.run, so [R11] applies to its         *)
(*        node-to-node and node-to-client responders.                      *)
(*   [R6] dmq-node/src/DMQ/NodeToNode.hs: in V1 the initiator runs the     *)
(*        outbound (the client here), the responder the inbound (the       *)
(*        server, which receives MsgDone).                                 *)
(*   [C2][C4][C5] CIP-0137 03387471: the V1, local submission and local    *)
(*        notification state tables.                                      *)
(*   [G1][G2][G3] gOuroboros d8f5bc2a: the StateMaps in                    *)
(*        protocol/messagesubmission/messagesubmission.go (stateMapV1),    *)
(*        localmessagesubmission/localmessagesubmission.go,                *)
(*        localmessagenotification/localmessagenotification.go; each       *)
(*        server.go's Done handler only logs (or, for notification, shuts  *)
(*        the server down).                                                *)
(*                                                                         *)
(* Not modelled: message contents, the window rules (MessageSubmission.tla *)
(* has them), V2 (whose MsgDone comes from the server).                    *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Proto,          \* "LocalSubmission", "LocalNotification" or "SubmissionV1"
    MaxRuns,        \* how many runs the client may start on one connection
    MaxMsgs,        \* how many messages may be sent in all (keeps the model finite)
    ServerRestarts  \* TRUE: the server restarts after MsgDone [S5][R11]
                    \* FALSE: gOuroboros d8f5bc2a, which stays in StDone

Roles == {"Client", "Server"}
Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Each protocol's rows <<from-state, message, to-state>>, and
\* who has agency in each state." [C2][C4][C5], the same in [G1][G2][G3].
\*   Local submission: from StIdle the client submits (to StBusy) or ends;
\*     from StBusy the server accepts or rejects (back to StIdle).
\*   Local notification: from StIdle the client asks, blocking or not, or
\*     ends; the server answers each kind of request with its own reply.
\*   Submission V1: from StInit the client sends MsgInit; from StIdle the
\*     server asks for ids (blocking or not) or for messages; the client
\*     answers, and may end only in place of a reply to a blocking request.
Rows ==
    CASE Proto = "LocalSubmission" ->
           { <<"StIdle", "MsgSubmitMessage", "StBusy">>,
             <<"StIdle", "MsgDone",          "StDone">>,
             <<"StBusy", "MsgAcceptMessage", "StIdle">>,
             <<"StBusy", "MsgRejectMessage", "StIdle">> }
      [] Proto = "LocalNotification" ->
           { <<"StIdle",         "MsgRequestNonBlocking", "StBusyNonBlock">>,
             <<"StIdle",         "MsgRequestBlocking",    "StBusyBlock">>,
             <<"StIdle",         "MsgClientDone",         "StDone">>,
             <<"StBusyNonBlock", "MsgReplyNonBlocking",   "StIdle">>,
             <<"StBusyBlock",    "MsgReplyBlocking",      "StIdle">> }
      [] Proto = "SubmissionV1" ->
           { <<"StInit",       "MsgInit",               "StIdle">>,
             <<"StIdle",       "MsgRequestIdsBlocking", "StIdsBlock">>,
             <<"StIdle",       "MsgRequestIdsNonBlock", "StIdsNonBlock">>,
             <<"StIdle",       "MsgRequestMessages",    "StMessages">>,
             <<"StIdsBlock",   "MsgReplyIds",           "StIdle">>,
             <<"StIdsBlock",   "MsgDone",               "StDone">>,
             <<"StIdsNonBlock", "MsgReplyIds",          "StIdle">>,
             <<"StMessages",   "MsgReplyMessages",      "StIdle">> }

\* In English: "Where a run starts."
InitState == IF Proto = "SubmissionV1" THEN "StInit" ELSE "StIdle"

\* In English: "The client has agency in the states it sends from: the
\* first state of each local protocol's rows, and V1's StInit and reply
\* states. The server has the rest, and nobody has it in StDone."
ClientStates ==
    CASE Proto = "SubmissionV1" -> {"StInit", "StIdsBlock", "StIdsNonBlock", "StMessages"}
      [] OTHER                  -> {"StIdle"}
States == {tr[1] : tr \in Rows} \cup {"StDone"}
Agency(s) == IF s = "StDone" THEN "Nobody"
             ELSE IF s \in ClientStates THEN "Client" ELSE "Server"

\* In English: "Message m is legal in state s if some row starts with s and
\* m; After(s, m) is where that row leads."
IsLegal(s, m) == \E tr \in Rows : tr[1] = s /\ tr[2] = m
After(s, m)   == (CHOOSE tr \in Rows : tr[1] = s /\ tr[2] = m)[3]

\* In English: "A run's end message, which only the client sends."
IsDone(m) == m \in {"MsgDone", "MsgClientDone"}

VARIABLES
    view,   \* view[r]: the state side r believes the protocol is in, or "Violation"
    inbox,  \* inbox[r]: messages sent to r that r has not read yet
    runs,   \* client runs started so far on this connection
    sent    \* messages sent so far, by either side

vars == <<view, inbox, runs, sent>>

\* In English: "Both sides start in the protocol's first state, with
\* nothing in flight, in the first run."
Init ==
    /\ view = [r \in Roles |-> InitState]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ runs = 1
    /\ sent = 0

\* In English: "Side r, holding agency in its own view, sends m, which its
\* table allows there, and moves its view along the row."
Send(r, m) ==
    /\ view[r] \in States
    /\ Agency(view[r]) = r
    /\ IsLegal(view[r], m)
    /\ sent < MaxMsgs
    /\ view' = [view EXCEPT ![r] = After(view[r], m)]
    /\ inbox' = [inbox EXCEPT ![Peer(r)] = Append(@, m)]
    /\ sent' = sent + 1
    /\ UNCHANGED runs

\* In English: "Side r may read when it waits for its peer in its own
\* view, or when it is the server, its run is over, and it restarts. A
\* restarted server judges the message from the protocol's first state.
\* A message with no row from that state is a violation [S1]."
CanRead(r) ==
    \/ view[r] \in States /\ Agency(view[r]) = Peer(r)
    \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts

Recv(r) ==
    /\ inbox[r] /= <<>>
    /\ CanRead(r)
    /\ LET m == Head(inbox[r])
           s == IF view[r] = "StDone" THEN InitState ELSE view[r]
       IN  view' = [view EXCEPT ![r] = IF IsLegal(s, m) THEN After(s, m)
                                                         ELSE "Violation"]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<runs, sent>>

\* In English: "Once its run is over, the client may start another on the
\* same connection, up to MaxRuns."
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = InitState]
    /\ runs' = runs + 1
    /\ UNCHANGED <<inbox, sent>>

\* In English: "The model stops when the message budget is spent, or when
\* a side has hung up, or when both runs are over and nothing is in flight."
Over ==
    \/ sent = MaxMsgs
    \/ \E r \in Roles : view[r] = "Violation"
    \/ /\ view["Client"] = "StDone" /\ runs = MaxRuns
       /\ view["Server"] = "StDone" /\ inbox["Server"] = <<>>

Next ==
    \/ \E r \in Roles : \E tr \in Rows : Send(r, tr[2])
    \/ \E r \in Roles : Recv(r)
    \/ ClientRestart
    \/ Over /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
    /\ view \in [Roles -> States \cup {"Violation"}]
    /\ runs \in 1..MaxRuns
    /\ sent \in 0..MaxMsgs

\* In English: "No side has received a message its state forbids."
NoViolation == \A r \in Roles : view[r] /= "Violation"

\* In English: "A message waiting for the server can be read: the server
\* is never left holding a client message it will not read." It fails
\* when a client starts a second run and the server stayed in StDone.
NewRunServed ==
    (inbox["Server"] /= <<>> /\ NoViolation) => ENABLED Recv("Server")

\* Probe, EXPECTED to be violated: "The client never starts a second run."
ProbeNoSecondRun == runs = 1
=============================================================================
