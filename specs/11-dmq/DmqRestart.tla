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

\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles == {"Client", "Server"}
\* In English: "The peer of the client is the server, and vice versa."
\* Literally: "Peer of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
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
\* Literally: "Rows is defined as: in the case Proto equals "LocalSubmission",
\*   the set containing these four tuples: <<"StIdle", "MsgSubmitMessage",
\*   "StBusy">>, <<"StIdle", "MsgDone", "StDone">>, <<"StBusy",
\*   "MsgAcceptMessage", "StIdle">>, and <<"StBusy", "MsgRejectMessage",
\*   "StIdle">>; in the case Proto equals "LocalNotification", the set
\*   containing these five tuples: <<"StIdle", "MsgRequestNonBlocking",
\*   "StBusyNonBlock">>, <<"StIdle", "MsgRequestBlocking", "StBusyBlock">>,
\*   <<"StIdle", "MsgClientDone", "StDone">>, <<"StBusyNonBlock",
\*   "MsgReplyNonBlocking", "StIdle">>, and <<"StBusyBlock",
\*   "MsgReplyBlocking", "StIdle">>; in the case Proto equals "SubmissionV1",
\*   the set containing these eight tuples: <<"StInit", "MsgInit", "StIdle">>,
\*   <<"StIdle", "MsgRequestIdsBlocking", "StIdsBlock">>, <<"StIdle",
\*   "MsgRequestIdsNonBlock", "StIdsNonBlock">>, <<"StIdle",
\*   "MsgRequestMessages", "StMessages">>, <<"StIdsBlock", "MsgReplyIds",
\*   "StIdle">>, <<"StIdsBlock", "MsgDone", "StDone">>, <<"StIdsNonBlock",
\*   "MsgReplyIds", "StIdle">>, and <<"StMessages", "MsgReplyMessages",
\*   "StIdle">>."
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
\* Literally: "InitState is defined as: if Proto equals "SubmissionV1" then
\*   "StInit", else "StIdle"."
InitState == IF Proto = "SubmissionV1" THEN "StInit" ELSE "StIdle"

\* In English: "The client has agency in the states it sends from: the
\* first state of each local protocol's rows, and V1's StInit and reply
\* states. The server has the rest, and nobody has it in StDone."
\* Literally: "ClientStates is defined as: in the case Proto equals
\*   "SubmissionV1", the set containing "StInit", "StIdsBlock", "StIdsNonBlock"
\*   and "StMessages"; in every other case, the set containing "StIdle"."
ClientStates ==
    CASE Proto = "SubmissionV1" -> {"StInit", "StIdsBlock", "StIdsNonBlock", "StMessages"}
      [] OTHER                  -> {"StIdle"}
\* In English: "Every state some row starts from, and StDone."
\* Literally: "States is defined as the union of the set of element 1 of tr,
\*   for every tr that is a member of Rows, and the set containing "StDone"."
States == {tr[1] : tr \in Rows} \cup {"StDone"}
\* In English: "Nobody may send in StDone; the client may send in its states;
\* the server in the rest."
\* Literally: "Agency of s is defined as: if s equals "StDone" then "Nobody";
\*   else if s is a member of ClientStates then "Client", else "Server"."
Agency(s) == IF s = "StDone" THEN "Nobody"
             ELSE IF s \in ClientStates THEN "Client" ELSE "Server"

\* In English: "Message m is legal in state s if some row starts with s and
\* m; After(s, m) is where that row leads."
\* Literally: "IsLegal of s and m is defined as: there exists a tr that is a
\*   member of Rows such that element 1 of tr equals s and element 2 of tr
\*   equals m."
IsLegal(s, m) == \E tr \in Rows : tr[1] = s /\ tr[2] = m
\* Literally: "After of s and m is defined as element 3 of the tr, chosen from
\*   Rows, such that element 1 of tr equals s and element 2 of tr equals m."
After(s, m)   == (CHOOSE tr \in Rows : tr[1] = s /\ tr[2] = m)[3]

\* In English: "A run's end message, which only the client sends."
\* Literally: "IsDone of m is defined as: m is a member of the set containing
\*   "MsgDone" and "MsgClientDone"."
IsDone(m) == m \in {"MsgDone", "MsgClientDone"}

VARIABLES
    view,   \* view[r]: the state side r believes the protocol is in, or "Violation"
    inbox,  \* inbox[r]: messages sent to r that r has not read yet
    runs,   \* client runs started so far on this connection
    sent    \* messages sent so far, by either side

\* Literally: "vars is defined as the tuple of view, inbox, runs and sent."
vars == <<view, inbox, runs, sent>>

\* In English: "Both sides start in the protocol's first state, with
\* nothing in flight, in the first run."
\* Literally: "Init is defined as: view equals the function that maps every r
\*   in Roles to InitState, and inbox equals the function that maps every r in
\*   Roles to the empty sequence, and runs equals 1, and sent equals 0."
Init ==
    /\ view = [r \in Roles |-> InitState]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ runs = 1
    /\ sent = 0

\* In English: "Side r, holding agency in its own view, sends m, which its
\* table allows there, and moves its view along the row."
\* Literally: "Send of r and m is defined as: view of r is a member of States,
\*   and Agency of view of r equals r, and IsLegal of view of r and m, and sent
\*   is less than MaxMsgs, and view in the next state equals view except that
\*   its r entry is After of view of r and m, and inbox in the next state
\*   equals inbox except that its Peer of r entry is the old entry with m
\*   appended, and sent in the next state equals sent plus 1, and runs is
\*   unchanged."
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
\* Literally: "CanRead of r is defined as: view of r is a member of States and
\*   Agency of view of r equals Peer of r; or r equals "Server" and view of r
\*   equals "StDone" and ServerRestarts is true."
CanRead(r) ==
    \/ view[r] \in States /\ Agency(view[r]) = Peer(r)
    \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts

\* In English: "Side r reads its oldest message and moves along the row it
\* names, or to a violation if there is none."
\* Literally: "Recv of r is defined as: inbox of r does not equal the empty
\*   sequence, and CanRead of r, and, letting m be the head of inbox of r and s
\*   be (if view of r equals "StDone" then InitState, else view of r): view in
\*   the next state equals view except that its r entry is (if IsLegal of s and
\*   m then After of s and m, else "Violation"); and inbox in the next state
\*   equals inbox except that its r entry is the tail of the old entry, and
\*   runs and sent are unchanged."
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
\* Literally: "ClientRestart is defined as: view of "Client" equals "StDone",
\*   and runs is less than MaxRuns, and view in the next state equals view
\*   except that its "Client" entry is InitState, and runs in the next state
\*   equals runs plus 1, and inbox and sent are unchanged."
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = InitState]
    /\ runs' = runs + 1
    /\ UNCHANGED <<inbox, sent>>

\* In English: "The model stops when the message budget is spent, or when
\* a side has hung up, or when both runs are over and nothing is in flight."
\* Literally: "Over is defined as: sent equals MaxMsgs; or there exists an r in
\*   Roles such that view of r equals "Violation"; or view of "Client" equals
\*   "StDone" and runs equals MaxRuns, and view of "Server" equals "StDone" and
\*   inbox of "Server" equals the empty sequence."
Over ==
    \/ sent = MaxMsgs
    \/ \E r \in Roles : view[r] = "Violation"
    \/ /\ view["Client"] = "StDone" /\ runs = MaxRuns
       /\ view["Server"] = "StDone" /\ inbox["Server"] = <<>>

\* In English: "A step is some side sending some message, some side reading, a
\* client restart, or, once the model is over, nothing."
\* Literally: "Next is defined as: there exists an r in Roles such that there
\*   exists a tr in Rows such that Send of r and element 2 of tr; or there
\*   exists an r in Roles such that Recv of r; or ClientRestart; or Over is
\*   true and vars is unchanged."
Next ==
    \/ \E r \in Roles : \E tr \in Rows : Send(r, tr[2])
    \/ \E r \in Roles : Recv(r)
    \/ ClientRestart
    \/ Over /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "view, runs and sent hold the kind of value they should."
\* Literally: "TypeOK is defined as: view is a member of the set of functions
\*   from Roles to the union of States and the set containing "Violation", and
\*   runs is a member of 1 through MaxRuns, and sent is a member of 0 through
\*   MaxMsgs."
TypeOK ==
    /\ view \in [Roles -> States \cup {"Violation"}]
    /\ runs \in 1..MaxRuns
    /\ sent \in 0..MaxMsgs

\* In English: "No side has received a message its state forbids."
\* Literally: "NoViolation is defined as: for all r in Roles, view of r does
\*   not equal "Violation"."
NoViolation == \A r \in Roles : view[r] /= "Violation"

\* In English: "A message waiting for the server can be read: the server
\* is never left holding a client message it will not read." It fails
\* when a client starts a second run and the server stayed in StDone.
\* Literally: "NewRunServed is defined as: if inbox of "Server" does not equal
\*   the empty sequence and NoViolation is true, then Recv of "Server" is
\*   enabled."
NewRunServed ==
    (inbox["Server"] /= <<>> /\ NoViolation) => ENABLED Recv("Server")

\* Probe, EXPECTED to be violated: "The client never starts a second run."
\* Literally: "ProbeNoSecondRun is defined as: runs equals 1."
ProbeNoSecondRun == runs = 1
=============================================================================
