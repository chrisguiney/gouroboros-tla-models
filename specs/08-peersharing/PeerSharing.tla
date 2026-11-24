---------------------------- MODULE PeerSharing ----------------------------
(***************************************************************************)
(* The peer-sharing mini-protocol: states, agency, the requested amount,   *)
(* the reply's size, the StBusy timeout, and runs that end and restart on  *)
(* the same connection.                                                    *)
(*                                                                         *)
(* A client asks "send me up to N peers" (MsgShareRequest N) and the       *)
(* server answers with a list (MsgSharePeers). The list may be shorter     *)
(* than N, never longer, and must fit the state's size limit.             *)
(*                                                                         *)
(* Every rule follows the specification. Where the specification is       *)
(* silent, the model follows the reference implementation and says so.    *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e;            *)
(* specs/08-peersharing/README.md has links and quotes.                    *)
(*   Specification (docs/network-spec/):                                   *)
(*   [S1] miniprotocols.tex 27-36, 96-98: one side has agency at a time;   *)
(*        an unexpected message aborts the connection.                     *)
(*   [S2] miniprotocols.tex 1653-1708: peer-sharing states, transitions,   *)
(*        agency, messages; "It is a protocol error to send more peers     *)
(*        than it was requested" (1702).                                   *)
(*   [S3] miniprotocols.tex 1710-1743: size limit 5760 bytes in StIdle and *)
(*        StBusy; timeout none in StIdle, 60 s in StBusy; a violation      *)
(*        SHOULD tear the connection down.                                 *)
(*   [S7] connection-manager.tex 489-503: a server-side mini-protocol that *)
(*        terminates cleanly is restarted in its initial state.            *)
(*   Reference implementation (ouroboros-network/protocols/lib/Ouroboros/  *)
(*   Network/Protocol/PeerSharing/ unless noted):                          *)
(*   [R1] Type.hs 26-31, 74-93: the amount is a Word8; the three messages; *)
(*        StDone = NobodyAgency.                                           *)
(*   [R2] Codec.hs 58-77: a message is decoded against the reader's state; *)
(*        any other key fails ("unexpected key"); 123-161: 4 * 1440 bytes *)
(*        in StIdle and StBusy; StIdle waitForever, StBusy longWait (60s). *)
(*   [R3] ouroboros-network/lib/Ouroboros/Network/PeerSharing.hs 126-130: *)
(*        the client throws PeerSharingProtocolViolation on a reply longer *)
(*        than its request; 229-237: the server takes at most             *)
(*        min(policy maximum, amount) peers.                              *)
(*   [R4] the receive rules of specs/01-keepalive (its S4, S6, S8): a side *)
(*        reads only while its peer has agency; a finished run's unread    *)
(*        bytes are kept for the next run.                                 *)
(*                                                                         *)
(* The gOuroboros code it is compared with is protocol/peersharing/        *)
(* peersharing.go (StateMap, MaxSharedPeers), client.go (GetPeers,         *)
(* handleSharePeers), and server.go (handleShareRequest, handleDone).      *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend in specs/01-keepalive/          *)
(* KeepAlive.tla. This module uses nothing that legend does not explain.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences     \* numbers, and lists (Append, Head, ...)

CONSTANTS
    Amounts,        \* the amounts the client may ask for, e.g. {0, 1, 2}
    ByteCap,        \* the most peers a reply can carry within 5760 bytes [S3]
    Available,      \* how many peers the server's peer source returns
    MaxRequests,    \* how many requests the client may send (keeps it finite)
    MaxRuns,        \* how many runs the client may start on one connection
    RogueMessages,  \* how many arbitrary messages a misbehaving peer may inject
    UseTimeouts,    \* TRUE: the StBusy timeout of [S3] is in force
    SlowPeers,      \* TRUE: a server may be slower than the timeout allows
    \* Each switch below is TRUE in gOuroboros and in the reference; FALSE
    \* removes one safeguard to show that an invariant notices (*Bug.cfg).
    ClampToAmount,      \* the server sends at most the amount asked for [S2][R3]
    ClampToCap,         \* the server sends at most ByteCap peers (MaxSharedPeers)
    ClientChecksCount,  \* the client refuses a reply longer than its request [R3]
    ServerRestarts      \* the server restarts after MsgDone [S7]

\* In English: "the smaller of a and b". (A user-defined operator, like a
\* small Go function.)
\* Literally: "Min of a and b is defined as: if a is less than b then a, else
\*   b."
Min(a, b) == IF a < b THEN a ELSE b

\* In English: "The largest number in the non-empty set S."
\* Literally: "MaxOf of S is defined as the x, chosen from S, such that for all
\*   y in S, y is less than or equal to x."
MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

\* The largest list a rogue peer bothers to send: one more than anything
\* honest, so "longer than requested" is always possible.
\* Literally: "MaxCount is defined as MaxOf of the union of Amounts and the set
\*   containing Available and ByteCap, plus 1."
MaxCount == MaxOf(Amounts \cup {Available, ByteCap}) + 1

\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles    == {"Client", "Server"}
\* Literally: "States is defined as the set containing "StIdle", "StBusy" and
\*   "StDone"."
States   == {"StIdle", "StBusy", "StDone"}
\* Literally: "MsgTypes is defined as the set containing "MsgShareRequest",
\*   "MsgSharePeers" and "MsgDone"."
MsgTypes == {"MsgShareRequest", "MsgSharePeers", "MsgDone"}

\* A message is a record. `amount` is the requested amount (only for
\* MsgShareRequest), `count` the number of peers in the list (only for
\* MsgSharePeers), and `oversized` marks a message over the state's
\* 5760-byte limit [S3]. The model does not need actual bytes.
\* In English: "Msg(t, a, c, big) is the message of type t, amount a,
\* count c, and oversized flag big."
\* Literally: "Msg of t, a, c and big is defined as the record whose field type
\*   is t, whose field amount is a, whose field count is c, and whose field
\*   oversized is big."
Msg(t, a, c, big) == [type |-> t, amount |-> a, count |-> c, oversized |-> big]

\* In English: "A reply listing c peers. It is oversized exactly when c is
\* more than fits in the size limit."
\* Literally: "Reply of c is defined as Msg of "MsgSharePeers", 0, c, and c is
\*   greater than ByteCap."
Reply(c) == Msg("MsgSharePeers", 0, c, c > ByteCap)

\* In English: "Every message a peer could put on the wire: a request for
\* any amount the wire can carry, a reply of any length, done, and any of
\* these padded past the size limit."
\* Literally: "Messages is defined as the set of Msg of "MsgShareRequest", a, 0
\*   and big, for every a that is a member of 0 through MaxCount and every big
\*   that is a member of BOOLEAN; union the set of Msg of "MsgSharePeers", 0, c
\*   and big, for every c that is a member of 0 through MaxCount and every big
\*   that is a member of BOOLEAN; union the set of Msg of "MsgDone", 0, 0 and
\*   big, for every big that is a member of BOOLEAN."
Messages ==
    {Msg("MsgShareRequest", a, 0, big) : a \in 0..MaxCount, big \in BOOLEAN}
    \cup {Msg("MsgSharePeers", 0, c, big) : c \in 0..MaxCount, big \in BOOLEAN}
    \cup {Msg("MsgDone", 0, 0, big) : big \in BOOLEAN}

\* Where a side can end up besides a protocol state: it detected a protocol
\* violation, or it waited too long. Either way the connection is torn
\* down [S1][S3].
\* Literally: "Failures is defined as the set containing "Violation" and
\*   "TimedOut"."
Failures == {"Violation", "TimedOut"}

\* In English: "In StIdle the client may send; in StBusy the server may
\* send; in StDone nobody may." [S2] agency table; [R1] for StDone.
\* Literally: "Agency of s is defined as: in the case s equals "StIdle",
\*   "Client"; in the case s equals "StBusy", "Server"; in the case s equals
\*   "StDone", "Nobody"."
Agency(s) == CASE s = "StIdle" -> "Client"
             []   s = "StBusy" -> "Server"
             []   s = "StDone" -> "Nobody"

\* The protocol as <<from-state, message, to-state>> rows ([S2] figure).
\* In English:
\*   "In StIdle, MsgShareRequest moves to StBusy.
\*    In StIdle, MsgDone moves to StDone.
\*    In StBusy, MsgSharePeers moves back to StIdle."
\* Literally: "Transitions is defined as the set containing these three tuples:
\*   <<"StIdle", "MsgShareRequest", "StBusy">>, <<"StIdle", "MsgDone",
\*   "StDone">>, and <<"StBusy", "MsgSharePeers", "StIdle">>."
Transitions ==
    { <<"StIdle", "MsgShareRequest", "StBusy">>,
      <<"StIdle", "MsgDone",         "StDone">>,
      <<"StBusy", "MsgSharePeers",   "StIdle">> }

\* In English: "Message type t is legal in state s if a row starts with s, t."
\* Literally: "IsLegal of s and t is defined as: there exists a tr that is a
\*   member of Transitions such that element 1 of tr equals s and element 2 of
\*   tr equals t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t

\* In English: "The state that t moves to from s."
\* Literally: "After of s and t is defined as element 3 of the tr, chosen from
\*   Transitions, such that element 1 of tr equals s and element 2 of tr equals
\*   t."
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

\* In English: "The peer of the client is the server, and vice versa."
\* Literally: "Peer of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s."
\* Literally: "Awaiting of r and s is defined as: s is a member of the set
\*   containing "StIdle" and "StBusy", and Agency of s equals Peer of r."
Awaiting(r, s) == s \in {"StIdle", "StBusy"} /\ Agency(s) = Peer(r)

(***************************************************************************)
(* JUDGING A MESSAGE. What side r does when it reads message m in state s. *)
(* `requested` is the amount of the client's last request.                *)
(*   - Over the size limit: tear down [S3][R2].                            *)
(*   - Not legal in s: abort [S1][R2].                                     *)
(*   - A reply longer than the request: protocol error [S2 1702][R3].      *)
(*   - Otherwise follow the transition [S2].                               *)
(***************************************************************************)
\* Literally: "Judge of r, s, m and requested is defined as: if m's oversized
\*   field is true then "Violation"; else if IsLegal of s and m's type is not
\*   true then "Violation"; else if ClientChecksCount is true and m's type
\*   equals "MsgSharePeers" and m's count is greater than requested then
\*   "Violation"; else After of s and m's type."
Judge(r, s, m, requested) ==
    IF m.oversized                     THEN "Violation"  \* too big: hang up
    ELSE IF ~IsLegal(s, m.type)        THEN "Violation"  \* not legal here: hang up
    ELSE IF /\ ClientChecksCount
            /\ m.type = "MsgSharePeers"
            /\ m.count > requested     THEN "Violation"  \* more peers than asked for: hang up
    ELSE After(s, m.type)                                \* otherwise: move on

\* In English: "A new run starts in StIdle [S2]; otherwise a run keeps its
\* state." Used when a server whose run ended reads a new message [S7].
\* Literally: "RunState of s is defined as: if s equals "StDone" then "StIdle",
\*   else s."
RunState(s) == IF s = "StDone" THEN "StIdle" ELSE s

\* In English: "How many peers the server puts in its reply to a request
\* for a: what its peer source has, cut to a, then cut to what fits."
\* gOuroboros: min(len(peers), Amount, MaxSharedPeers) in handleShareRequest.
\* Reference: min(policy maximum 10, amount) [R3]; 10 addresses always fit.
\* Literally: "ServerReplyCount of a is defined as: letting toAmount be (if
\*   ClampToAmount is true then Min of Available and a, else Available): if
\*   ClampToCap is true then Min of toAmount and ByteCap, else toAmount."
ServerReplyCount(a) ==
    LET toAmount == IF ClampToAmount THEN Min(Available, a) ELSE Available
    IN  IF ClampToCap THEN Min(toAmount, ByteCap) ELSE toAmount

(***************************************************************************)
(* THE RECEIVE TABLE, printed by PeerSharingTable.tla. The gOuroboros test *)
(* protocol/peersharing/statemap_model_test.go holds the same cells. The   *)
(* client's last request asked for 1 peer.                                 *)
(*   "Waits": r holds agency, so it does not read yet [R4]; the message is *)
(*            judged when r next waits for its peer.                       *)
(*   "Held":  the client's run is over and no new run reads it [R4].       *)
(* After MsgDone the server restarts and judges in StIdle [S7].            *)
(***************************************************************************)
\* Literally: "Kinds is defined as the set containing "MsgShareRequest",
\*   "MsgSharePeers", "OverCountSharePeers", "MsgDone" and "Oversized"."
Kinds == {"MsgShareRequest", "MsgSharePeers", "OverCountSharePeers",
          "MsgDone", "Oversized"}

\* In English: "The amount the client's last request asked for, in the table."
\* Literally: "TableRequested is defined as 1."
TableRequested == 1

\* In English: "The concrete message each kind stands for."
\* Literally: "KindMsg of k is defined as: in the case k equals
\*   "MsgShareRequest", Msg of "MsgShareRequest", 1, 0 and FALSE; in the case k
\*   equals "MsgSharePeers", Msg of "MsgSharePeers", 0, TableRequested and
\*   FALSE; in the case k equals "OverCountSharePeers", Msg of "MsgSharePeers",
\*   0, TableRequested plus 1, and FALSE; in the case k equals "MsgDone", Msg
\*   of "MsgDone", 0, 0 and FALSE; in the case k equals "Oversized", Msg of
\*   "MsgShareRequest", 1, 0 and TRUE."
KindMsg(k) ==
    CASE k = "MsgShareRequest"     -> Msg("MsgShareRequest", 1, 0, FALSE)
    []   k = "MsgSharePeers"       -> Msg("MsgSharePeers", 0, TableRequested, FALSE)      \* as many as asked
    []   k = "OverCountSharePeers" -> Msg("MsgSharePeers", 0, TableRequested + 1, FALSE)  \* one more than asked
    []   k = "MsgDone"             -> Msg("MsgDone", 0, 0, FALSE)
    []   k = "Oversized"           -> Msg("MsgShareRequest", 1, 0, TRUE)                 \* padded past 5760 bytes

\* In English: "If the run is over: a restarting server judges the message
\* as a new run, a client leaves it Held. If r holds agency: it Waits.
\* Otherwise judge it now."
\* Literally: "ReceiveTable of r, s and k is defined as: if s equals "StDone",
\*   then (if r equals "Server" and ServerRestarts is true, then Judge of r,
\*   "StIdle", KindMsg of k, and TableRequested; else "Held"); else if Agency
\*   of s equals r, then "Waits"; else Judge of r, s, KindMsg of k, and
\*   TableRequested."
ReceiveTable(r, s, k) ==
    IF s = "StDone"
        THEN IF r = "Server" /\ ServerRestarts
                 THEN Judge(r, "StIdle", KindMsg(k), TableRequested)
                 ELSE "Held"
    ELSE IF Agency(s) = r THEN "Waits"
    ELSE Judge(r, s, KindMsg(k), TableRequested)

-----------------------------------------------------------------------------

VARIABLES
    view,        \* view[r]: the state side r believes the protocol is in
    inbox,       \* inbox[r]: messages sent to r that r has not read yet
    requests,    \* requests the client has sent so far
    requested,   \* the amount of the client's last request
    served,      \* the amount of the last request the server read
    runs,        \* client runs started so far on this connection
    rogueLeft,   \* rogue messages the misbehaving peer may still inject
    overTaken    \* TRUE once the client has accepted a reply longer than its request

\* Literally: "vars is defined as the tuple of all eight variables."
vars == <<view, inbox, requests, requested, served, runs, rogueLeft, overTaken>>

\* In English: "At the start both sides think StIdle, nothing is in flight,
\* nothing has been sent, this is run 1, and the rogue peer has its full
\* allowance."
\* Literally: "Init is defined as: view equals the function that maps every r
\*   in Roles to "StIdle", and inbox equals the function that maps every r in
\*   Roles to the empty sequence, and requests equals 0, and requested equals
\*   0, and served equals 0, and runs equals 1, and rogueLeft equals
\*   RogueMessages, and overTaken equals FALSE."
Init ==
    /\ view = [r \in Roles |-> "StIdle"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ requests = 0
    /\ requested = 0
    /\ served = 0
    /\ runs = 1
    /\ rogueLeft = RogueMessages
    /\ overTaken = FALSE

\* In English: "The client has finished for good: its run is over and it
\* may start no other."
\* Literally: "ClientFinished is defined as: view of "Client" equals "StDone",
\*   and runs equals MaxRuns."
ClientFinished == view["Client"] = "StDone" /\ runs = MaxRuns

\* In English: "The connection is over when someone has hung up, or the
\* client has finished for good and the server waits in StIdle (or StDone)
\* with nothing to read." Waiting in StIdle forever is allowed: StIdle has
\* no timeout [S3][R2], and the reference's client runs for the whole
\* connection, so a server is normally idle between requests.
\* Literally: "Ended is defined as: there exists an r in Roles such that view
\*   of r is a member of Failures; or ClientFinished is true, and view of
\*   "Server" is a member of the set containing "StIdle" and "StDone", and
\*   inbox of "Server" equals the empty sequence."
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ /\ ClientFinished
       /\ view["Server"] \in {"StIdle", "StDone"}
       /\ inbox["Server"] = <<>>

\* --- Honest sends. Each needs the sender to hold agency [S1][S2]. -------

\* In English: "When the client believes StIdle and has requests left, it
\* can ask for a peers. It then believes StBusy, the request is in the
\* server's inbox, and the client remembers a."
\* Literally: "ClientRequest of a is defined as: view of "Client" equals
\*   "StIdle", and requests is less than MaxRequests, and view in the next
\*   state equals view except that its "Client" entry is "StBusy", and inbox in
\*   the next state equals inbox except that its "Server" entry is the old
\*   entry with Msg of "MsgShareRequest", a, 0 and FALSE appended, and requests
\*   in the next state equals requests plus 1, and requested in the next state
\*   equals a, and served, runs, rogueLeft and overTaken are unchanged."
ClientRequest(a) ==
    /\ view["Client"] = "StIdle"                        \* the client may send
    /\ requests < MaxRequests                           \* and has requests left
    /\ view' = [view EXCEPT !["Client"] = "StBusy"]     \* next, it believes StBusy
    /\ inbox' = [inbox EXCEPT !["Server"] =
                     Append(@, Msg("MsgShareRequest", a, 0, FALSE))]  \* the request is on its way
    /\ requests' = requests + 1
    /\ requested' = a                                   \* the client remembers a
    /\ UNCHANGED <<served, runs, rogueLeft, overTaken>>

\* In English: "When the server believes StBusy, it answers the request it
\* read with ServerReplyCount peers, and believes StIdle again."
\* Literally: "ServerRespond is defined as: view of "Server" equals "StBusy",
\*   and view in the next state equals view except that its "Server" entry is
\*   "StIdle", and inbox in the next state equals inbox except that its
\*   "Client" entry is the old entry with Reply of ServerReplyCount of served
\*   appended, and requests, requested, served, runs, rogueLeft and overTaken
\*   are unchanged."
ServerRespond ==
    /\ view["Server"] = "StBusy"                        \* the server may send
    /\ view' = [view EXCEPT !["Server"] = "StIdle"]     \* next, it believes StIdle
    /\ inbox' = [inbox EXCEPT !["Client"] =
                     Append(@, Reply(ServerReplyCount(served)))]  \* the reply is on its way
    /\ UNCHANGED <<requests, requested, served, runs, rogueLeft, overTaken>>

\* In English: "When the client believes StIdle it can send done, and then
\* believes StDone." The reference client sends it when told to terminate
\* [R3 115-125]; nothing in the gOuroboros client API sends it.
\* Literally: "ClientDone is defined as: view of "Client" equals "StIdle", and
\*   view in the next state equals view except that its "Client" entry is
\*   "StDone", and inbox in the next state equals inbox except that its
\*   "Server" entry is the old entry with Msg of "MsgDone", 0, 0 and FALSE
\*   appended, and requests, requested, served, runs, rogueLeft and overTaken
\*   are unchanged."
ClientDone ==
    /\ view["Client"] = "StIdle"
    /\ view' = [view EXCEPT !["Client"] = "StDone"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0, 0, FALSE))]
    /\ UNCHANGED <<requests, requested, served, runs, rogueLeft, overTaken>>

\* In English: "An honest send is a request for some amount, or a reply, or
\* done."
\* Literally: "Send is defined as: there exists an a in Amounts such that
\*   ClientRequest of a, or ServerRespond, or ClientDone."
Send == \/ \E a \in Amounts : ClientRequest(a)
        \/ ServerRespond
        \/ ClientDone

\* --- Reading. -----------------------------------------------------------

\* In English: "Side r can read the oldest message in its inbox when it is
\* waiting for its peer, or when it is a restarting server whose run is
\* over. It judges the message and moves to the result. A server reading a
\* request remembers its amount. A client that accepts a reply longer than
\* its request records that it did."
\* Literally: "Recv of r is defined as: inbox of r does not equal the empty
\*   sequence, and (Awaiting of r and view of r, or r equals "Server" and view
\*   of r equals "StDone" and ServerRestarts is true), and, letting m be the
\*   head of inbox of r and outcome be Judge of r, RunState of view of r, m,
\*   and requested: view in the next state equals view except that its r entry
\*   is outcome; and served in the next state equals (if r equals "Server" and
\*   m's type equals "MsgShareRequest" then m's amount, else served); and
\*   overTaken in the next state equals overTaken, or (r equals "Client" and
\*   m's type equals "MsgSharePeers" and outcome is not a member of Failures
\*   and m's count is greater than requested); and inbox in the next state
\*   equals inbox except that its r entry is the tail of the old entry; and
\*   requests, requested, runs and rogueLeft are unchanged."
Recv(r) ==
    /\ inbox[r] /= <<>>                                 \* r has something to read
    /\ \/ Awaiting(r, view[r])                          \* and r is waiting for its peer
       \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts  \* or r restarts
    /\ LET m       == Head(inbox[r])
           outcome == Judge(r, RunState(view[r]), m, requested)
       IN  /\ view' = [view EXCEPT ![r] = outcome]      \* next, r is wherever m takes it
           /\ served' = IF r = "Server" /\ m.type = "MsgShareRequest"
                            THEN m.amount ELSE served   \* a server remembers the amount
           /\ overTaken' = \/ overTaken
                           \/ /\ r = "Client"
                              /\ m.type = "MsgSharePeers"
                              /\ outcome \notin Failures
                              /\ m.count > requested     \* the client took too many
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]           \* next, m is no longer in r's inbox
    /\ UNCHANGED <<requests, requested, runs, rogueLeft>>

\* In English: "When the client's run is over and it may start another, it
\* does: it believes StIdle, and one more run has started."
\* Literally: "ClientRestart is defined as: view of "Client" equals "StDone",
\*   and runs is less than MaxRuns, and view in the next state equals view
\*   except that its "Client" entry is "StIdle", and runs in the next state
\*   equals runs plus 1, and inbox, requests, requested, served, rogueLeft and
\*   overTaken are unchanged."
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ runs' = runs + 1
    /\ UNCHANGED <<inbox, requests, requested, served, rogueLeft, overTaken>>

\* In English: "While it has allowance left, the rogue peer can put any
\* message m into r's inbox at any time."
\* Literally: "Inject of r and m is defined as: rogueLeft is greater than 0,
\*   and inbox in the next state equals inbox except that its r entry is the
\*   old entry with m appended, and rogueLeft in the next state equals
\*   rogueLeft minus 1, and view, requests, requested, served, runs and
\*   overTaken are unchanged."
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, requests, requested, served, runs, overTaken>>

\* In English: "Progress is possible: some honest send, a restart, or some side
\* reading."
\* Literally: "Progress is defined as: Send, or ClientRestart, or there exists
\*   an r in Roles such that Recv of r."
Progress == Send \/ ClientRestart \/ \E r \in Roles : Recv(r)

\* --- Timeouts. ----------------------------------------------------------
\* [S3][R2]: StBusy has a 60 s limit (the client waiting); StIdle has none
\* (the server may wait for ever). No clock: with SlowPeers the client may
\* give up whenever it waits; without, only when nothing else can happen.
\*
\* In English: "If timeouts are on, the connection is not over, and the
\* client waits in StBusy, it can give up, provided the server may be slow
\* or nothing else can happen."
\* Literally: "Timeout is defined as: UseTimeouts is true, and Ended is not
\*   true, and view of "Client" equals "StBusy", and (SlowPeers is true, or
\*   Progress is not enabled), and view in the next state equals view except
\*   that its "Client" entry is "TimedOut", and inbox, requests, requested,
\*   served, runs, rogueLeft and overTaken are unchanged."
Timeout ==
    /\ UseTimeouts
    /\ ~Ended
    /\ view["Client"] = "StBusy"
    /\ SlowPeers \/ ~ENABLED Progress
    /\ view' = [view EXCEPT !["Client"] = "TimedOut"]
    /\ UNCHANGED <<inbox, requests, requested, served, runs, rogueLeft, overTaken>>

\* In English: "A step is an honest send, a client restart, a read, a
\* timeout, a rogue injection, or, once the connection is over, nothing."
\* Literally: "Next is defined as: Send, or ClientRestart, or there exists an r
\*   in Roles such that Recv of r, or Timeout, or there exists an r in Roles
\*   and an m in Messages such that Inject of r and m, or Ended is true and
\*   vars is unchanged."
Next ==
    \/ Send
    \/ ClientRestart
    \/ \E r \in Roles : Recv(r)
    \/ Timeout
    \/ \E r \in Roles, m \in Messages : Inject(r, m)
    \/ Ended /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants: must hold in every reachable state. *)

\* In English: "Every variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: view is a member of the set of functions
\*   from Roles to the union of States and Failures, and inbox is a member of
\*   the set of functions from Roles to the set of sequences of members of
\*   Messages, and requests is a member of 0 through MaxRequests, and requested
\*   is a member of the union of Amounts and the set containing 0, and served
\*   is a member of 0 through MaxCount, and runs is a member of 1 through
\*   MaxRuns, and rogueLeft is a member of 0 through RogueMessages, and
\*   overTaken is a member of BOOLEAN."
TypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ requests \in 0..MaxRequests
    /\ requested \in Amounts \cup {0}
    /\ served \in 0..MaxCount
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages
    /\ overTaken \in BOOLEAN

\* In English: "No side has hung up."
\* Literally: "NoFailures is defined as: for all r in Roles, view of r is not a
\*   member of Failures."
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "No side has seen a protocol violation." Slow honest peers
\* may time out, never violate.
\* Literally: "NoViolations is defined as: for all r in Roles, view of r does
\*   not equal "Violation"."
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* THE AMOUNT RULE [S2 1702]. In English: "Every reply waiting for the
\* client lists at most the amount it asked for." With an honest server.
\* Literally: "RepliesWithinRequest is defined as: for all i in 1 through the
\*   length of inbox of "Client", if element i of inbox of "Client"'s type
\*   equals "MsgSharePeers", then element i of inbox of "Client"'s count is
\*   less than or equal to requested."
RepliesWithinRequest ==
    \A i \in 1..Len(inbox["Client"]) :
        inbox["Client"][i].type = "MsgSharePeers" =>
            inbox["Client"][i].count <= requested

\* THE SIZE RULE [S3]. In English: "No reply waiting for the client is over
\* the size limit." With an honest server.
\* Literally: "RepliesFit is defined as: for all i in 1 through the length of
\*   inbox of "Client", element i of inbox of "Client"'s oversized field is not
\*   true."
RepliesFit ==
    \A i \in 1..Len(inbox["Client"]) : ~inbox["Client"][i].oversized

\* In English: "The client has never accepted a reply longer than its
\* request." Must hold even against a rogue server.
\* Literally: "NeverTakesTooMany is defined as: overTaken is not true."
NeverTakesTooMany == ~overTaken

\* Literally: "IsDoneMsg of m is defined as: m's type equals "MsgDone"."
IsDoneMsg(m) == m.type = "MsgDone"

\* In English: "In each inbox every message but the newest is an earlier
\* run's done, and at most one inbox ends in something other than done."
\* (Same reasoning as specs/01-keepalive: a client may send MsgDone, start
\* a new run and send a request before the server reads the MsgDone.)
\* Literally: "OneMessageInFlightPerRun is defined as: for all r in Roles, for
\*   all i in 1 through the length of inbox of r minus 1, IsDoneMsg of element
\*   i of inbox of r; and, for all r1 and r2 in Roles, if (inbox of r1 does not
\*   equal the empty sequence, and inbox of r2 does not equal the empty
\*   sequence, and IsDoneMsg of the last element of inbox of r1 is not true,
\*   and IsDoneMsg of the last element of inbox of r2 is not true), then r1
\*   equals r2."
OneMessageInFlightPerRun ==
    /\ \A r \in Roles :
           \A i \in 1..(Len(inbox[r]) - 1) : IsDoneMsg(inbox[r][i])
    /\ \A r1, r2 \in Roles :
           (/\ inbox[r1] /= <<>> /\ inbox[r2] /= <<>>
            /\ ~IsDoneMsg(inbox[r1][Len(inbox[r1])])
            /\ ~IsDoneMsg(inbox[r2][Len(inbox[r2])])) => r1 = r2

\* In English: "Never do both sides believe they may send."
\* Literally: "NeverBothHaveAgency is defined as: it is not the case that (view
\*   of "Client" is a member of States and Agency of view of "Client" equals
\*   "Client", and view of "Server" is a member of States and Agency of view of
\*   "Server" equals "Server")."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "With nothing in flight, both sides believe the same state,
\* except a server that ended a run while the client started the next."
\* Literally: "ViewsAgreeWhenQuiet is defined as: if, for all r in Roles, inbox
\*   of r equals the empty sequence, then view of "Client" equals view of
\*   "Server", or (ServerRestarts is true, and view of "Server" equals
\*   "StDone", and view of "Client" equals "StIdle")."
ViewsAgreeWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>>) =>
        \/ view["Client"] = view["Server"]
        \/ /\ ServerRestarts
           /\ view["Server"] = "StDone"
           /\ view["Client"] = "StIdle"

-----------------------------------------------------------------------------
(* Properties about steps. *)

\* THE STATES THAT CANNOT BE ENTERED. In English: "A side's state changes
\* only to a failure, from StDone to a new run, or along a table row."
\* Literally: "OnlyLegalMoves is defined as: always, every step is a step in
\*   which, for all r in Roles, if view in the next state of r does not equal
\*   view of r, then view in the next state of r is a member of Failures, or
\*   (view of r equals "StDone" and view in the next state of r equals
\*   "StIdle"), or there exists a tr in Transitions such that element 1 of tr
\*   equals RunState of view of r and element 3 of tr equals view in the next
\*   state of r; or a step that leaves vars unchanged."
OnlyLegalMoves ==
    [][\A r \in Roles :
         view'[r] /= view[r] =>
             \/ view'[r] \in Failures
             \/ view[r] = "StDone" /\ view'[r] = "StIdle"
             \/ \E tr \in Transitions :
                    tr[1] = RunState(view[r]) /\ tr[3] = view'[r]]_vars

\* In English: "A side that has hung up stays hung up."
\* Literally: "FailuresAreFinal is defined as: always, every step is a step in
\*   which, for all r in Roles, if view of r is a member of Failures, then view
\*   in the next state of r equals view of r; or a step that leaves vars
\*   unchanged."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

-----------------------------------------------------------------------------
(* REACHABILITY PROBES. Each claims something never happens; each must be *)
(* VIOLATED (the *ProbeBug.cfg configs), or the passing invariants above  *)
(* could be passing only because the model never gets near the edge.     *)

\* In English: "The client never receives a non-empty reply."
\* Literally: "ProbeNoPeersDelivered is defined as: it is not the case that
\*   there exists an i in 1 through the length of inbox of "Client" such that
\*   element i of inbox of "Client"'s count is greater than 0."
ProbeNoPeersDelivered ==
    ~ \E i \in 1..Len(inbox["Client"]) : inbox["Client"][i].count > 0

\* In English: "The server never has more peers than were asked for, so it
\* never has to cut its list." Violated = the amount clamp does work.
\* Literally: "ProbeNeverClampsToAmount is defined as: it is not the case that
\*   (view of "Server" equals "StBusy" and Available is greater than served)."
ProbeNeverClampsToAmount ==
    ~ (view["Server"] = "StBusy" /\ Available > served)

\* In English: "The server never cuts a reply to fit the size limit."
\* Literally: "ProbeNeverClampsToCap is defined as: it is not the case that
\*   (view of "Server" equals "StBusy" and Min of Available and served is
\*   greater than ByteCap)."
ProbeNeverClampsToCap ==
    ~ (view["Server"] = "StBusy" /\ Min(Available, served) > ByteCap)

\* In English: "The server never starts a second run."
\* Literally: "ProbeNeverRestarts is defined as: it is not the case that (runs
\*   equals MaxRuns and view of "Server" equals "StBusy")."
ProbeNeverRestarts ==
    ~ (runs = MaxRuns /\ view["Server"] = "StBusy")

\* In English: "The connection never settles with the server idle for ever."
\* Literally: "ProbeNeverIdleForever is defined as: it is not the case that
\*   (ClientFinished is true, and view of "Server" equals "StIdle", and inbox
\*   of "Server" equals the empty sequence)."
ProbeNeverIdleForever ==
    ~ (ClientFinished /\ view["Server"] = "StIdle" /\ inbox["Server"] = <<>>)

\* DELIBERATELY WRONG, for PeerSharingRogueBug.cfg. In English: "A rogue
\* message can never make a side hang up."
\* Literally: "NoFailuresEvenWithRogue is defined as NoFailures."
NoFailuresEvenWithRogue == NoFailures
=============================================================================
