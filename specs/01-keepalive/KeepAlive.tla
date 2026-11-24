----------------------------- MODULE KeepAlive -----------------------------
(***************************************************************************)
(* The keep-alive mini-protocol: states, agency, cookies, size limits,     *)
(* timeouts, and runs that end and restart on the same connection.         *)
(*                                                                         *)
(* Every rule follows the specification. Where the specification is       *)
(* silent, the model follows the reference implementation and says so.    *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e unless      *)
(* noted; specs/01-keepalive/README.md has links and quotes.               *)
(*   Specification (docs/network-spec/):                                   *)
(*   [S1] miniprotocols.tex 27-36, 96-98: one side has agency at a time;   *)
(*        an unexpected message aborts the connection.                     *)
(*   [S2] miniprotocols.tex 1560-1650: keep-alive states, transitions,     *)
(*        agency, cookie rule, size limits, timeouts.                      *)
(*   [S7] connection-manager.tex 489-503: a server-side mini-protocol that *)
(*        terminates cleanly is restarted in its initial state.            *)
(*   Reference implementation, used only where the specification is silent:*)
(*   [S3] .../Protocol/KeepAlive/Type.hs 89-106: StDone = NobodyAgency.    *)
(*   [S4] network-mux/src/Network/Mux.hs 362-378, 512: a finished run's    *)
(*        unread bytes are kept for the next run.                          *)
(*   [S5] network-mux/src/Network/Mux.hs 846-852: a finished mini-protocol *)
(*        may be started again on the same connection.                     *)
(*   [S6] .../InboundGovernor.hs 433-475: the server restart of [S7].      *)
(*   [S8] IntersectMBO/typed-protocols 8fa4ed2f (1.2.2.0),                 *)
(*        typed-protocols/src/Network/TypedProtocol/Driver.hs 145-176: a   *)
(*        side reads only when its peer has agency.                        *)
(*   [S9] .../Protocol/KeepAlive/Codec.hs 58-116: a message is decoded     *)
(*        against the reader's state when it is read.                      *)
(*                                                                         *)
(* The gOuroboros code it is compared with is protocol/keepalive/          *)
(* keepalive.go (StateMap), client.go, server.go, and the receive checks   *)
(* in protocol/protocol.go.                                                *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS (see also specs/00-hello/Hello.tla)             *)
(*   ==  "is defined as"        /\  "and"        \/  "or"      ~  "not"    *)
(*   x'  "x in the next state"  =>  "implies"    \in "is one of"           *)
(*   \E x \in S : P   "there is some x in S for which P is true"           *)
(*   \A x \in S : P   "for every x in S, P is true"                        *)
(*   IF a THEN b ELSE c          like Go's if/else, but it produces a value *)
(*   CASE a -> x [] b -> y       like Go's switch                          *)
(*   LET n == e IN body          "let n stand for e inside body"           *)
(*   CHOOSE x \in S : P          "the x in S for which P is true"          *)
(*   <<a, b, c>>                 a tuple (or sequence); t[1] is its first  *)
(*   {a, b}                      a set                                     *)
(*   {f(x) : x \in S}            "every f(x), for x in S"                  *)
(*   [k \in S |-> v]             a function: like a Go map with keys S     *)
(*   [S -> T]                    "every function from S to T"              *)
(*   [a |-> 1, b |-> 2]          a record: like a Go struct; r.a reads it  *)
(*   [f EXCEPT ![k] = v]         "f, but with key k set to v"; inside,     *)
(*                               @ means "the old value of f[k]"           *)
(*   UNCHANGED x                 "x stays the same" (x' = x)               *)
(*   ENABLED A                   "step A could happen right now"           *)
(*   Seq(S)                      "every finite list of things in S"        *)
(*   Append(s, x)  Head(s)  Tail(s)  Len(s)                                *)
(*                 add to end, first item, all but first, length           *)
(***************************************************************************)
EXTENDS Naturals, Sequences     \* numbers, and lists (Append, Head, ...)

\* Constants are the knobs: each .cfg file sets them. Changing them asks a
\* different question of the same model.
CONSTANTS
    MaxPings,       \* how many pings the client may send (keeps the model finite)
    MaxRuns,        \* how many runs the client may start on one connection
    RogueMessages,  \* how many arbitrary messages a misbehaving peer may inject
    UseTimeouts,    \* TRUE: the state timeouts of [S2] are in force
    SlowPeers,      \* TRUE: a peer may be slower than the timeout allows
    ServerRestarts  \* TRUE: the server restarts after MsgDone [S7]. FALSE: gOuroboros today

\* The two sides, the protocol states, and the message types, as sets.
\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles     == {"Client", "Server"}
\* Literally: "States is defined as the set containing "StClient", "StServer" and
\*   "StDone"."
States    == {"StClient", "StServer", "StDone"}
\* Literally: "MsgTypes is defined as the set containing "MsgKeepAlive",
\*   "MsgKeepAliveResponse" and "MsgDone"."
MsgTypes  == {"MsgKeepAlive", "MsgKeepAliveResponse", "MsgDone"}

\* Cookies are 16-bit numbers [S2]. Two values are enough to tell a matching
\* cookie from a wrong one, and keep the model small.
\* Literally: "Cookies is defined as the set containing 0 and 1."
Cookies   == {0, 1}

\* A message is a record: like a Go struct with three fields. `oversized`
\* marks one larger than the state's size limit (65535 bytes [S2]); the
\* model does not need actual sizes.
\* In English: "Msg(t, c, big) is the message of type t, cookie c, and
\* oversized flag big."
\* Literally: "Msg of t, c and big is defined as the record whose field type
\*   is t, whose field cookie is c, and whose field oversized is big."
Msg(t, c, big) == [type |-> t, cookie |-> c, oversized |-> big]

\* In English: "Messages is every possible message: every type, with every
\* cookie, oversized or not."
\* Literally: "Messages is defined as the set of Msg of t, c and big, for
\*   every t that is a member of MsgTypes, every c that is a member of Cookies,
\*   and every big that is a member of BOOLEAN."
Messages == {Msg(t, c, big) : t \in MsgTypes, c \in Cookies, big \in BOOLEAN}

\* Where a side can end up besides a protocol state: it detected a protocol
\* violation and closed the connection, or it waited too long and gave up.
\* Either way the connection is torn down [S1][S2].
\* Literally: "Failures is defined as the set containing "Violation" and "TimedOut"."
Failures == {"Violation", "TimedOut"}

\* In English: "In StClient the client may send; in StServer the server
\* may send; in StDone nobody may." This is "agency". [S2] agency table;
\* [S1] and [S3] for StDone.
\* Literally: "Agency of s is defined as: in the case s equals "StClient",
\*   "Client"; in the case s equals "StServer", "Server"; in the case s equals
\*   "StDone", "Nobody"."
Agency(s) == CASE s = "StClient" -> "Client"
             []   s = "StServer" -> "Server"
             []   s = "StDone"   -> "Nobody"

\* The whole protocol, as a set of <<from-state, message, to-state>> tuples
\* ([S2] state-machine figure). In English:
\*   "In StClient, MsgKeepAlive moves to StServer.
\*    In StClient, MsgDone moves to StDone.
\*    In StServer, MsgKeepAliveResponse moves to StClient."
\* Literally: "Transitions is defined as the set containing these three
\*   tuples: <<"StClient", "MsgKeepAlive", "StServer">>,
\*   <<"StClient", "MsgDone", "StDone">>, and
\*   <<"StServer", "MsgKeepAliveResponse", "StClient">>."
Transitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

\* In English: "Message type t is legal in state s if some row of the
\* table starts with s and t."
\* Literally: "IsLegal of s and t is defined as: there exists a tr that
\*   is a member of Transitions such that element 1 of tr equals s and element 2
\*   of tr equals t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t

\* In English: "After(s, t) is the state you move to when t is sent in s":
\* pick the row that starts with s and t, and take its third column.
\* Literally: "After of s and t is defined as element 3 of the tr,
\*   chosen from Transitions, such that element 1 of tr equals s and element 2 of
\*   tr equals t."
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

\* In English: "The peer of the client is the server, and vice versa."
\* Literally: "Peer of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s: s is an active
\* state, and the peer is the one allowed to send."
\* Literally: "Awaiting of r and s is defined as: s is a member of the
\*   set {"StClient", "StServer"}, and Agency of s equals Peer of r."
Awaiting(r, s) == s \in {"StClient", "StServer"} /\ Agency(s) = Peer(r)

(***************************************************************************)
(* JUDGING A MESSAGE. What side r does when it reads message m in state s, *)
(* while waiting for its peer. `expected` is the cookie of the client's    *)
(* last ping.                                                              *)
(*   - Too big for the state: tear down [S2 size limits].                  *)
(*   - Not a legal message in s: abort [S1].                               *)
(*   - A response with the wrong cookie: "a protocol error" [S2].          *)
(*   - Otherwise follow the transition [S2].                               *)
(* Every message in r's inbox was sent by r's peer, so "who sent it" needs *)
(* no check; WHEN it is read matters, and Recv below decides that.         *)
(***************************************************************************)
\* Literally: "Judge of r, s, m and expected is defined as: if m's
\*   oversized field is true then "Violation"; else if IsLegal of s and m's type
\*   is not true then "Violation"; else if m's type equals "MsgKeepAliveResponse"
\*   and m's cookie does not equal expected then "Violation"; else After of s and
\*   m's type."
Judge(r, s, m, expected) ==
    IF m.oversized                     THEN "Violation"  \* if it is too big: hang up
    ELSE IF ~IsLegal(s, m.type)        THEN "Violation"  \* if it is not legal here: hang up
    ELSE IF m.type = "MsgKeepAliveResponse" /\ m.cookie /= expected
                                       THEN "Violation"  \* if it is a response with the wrong cookie: hang up
    ELSE After(s, m.type)                                \* otherwise: move to the next state

\* In English: "A new run starts in StClient [S2]; otherwise the run keeps
\* its state." Used when a server that finished a run reads a new message.
\* Literally: "RunState of s is defined as: if s equals "StDone" then
\*   "StClient", else s."
RunState(s) == IF s = "StDone" THEN "StClient" ELSE s

(***************************************************************************)
(* THE RECEIVE TABLE: the outcome for every role, state, and kind of       *)
(* message, printed by `make keepalive-table`. The gOuroboros tests check  *)
(* against it. Kinds stand for concrete messages; the client's last ping   *)
(* used cookie 0.                                                          *)
(*   "Waits": r holds agency, so it does not read yet [S8]. The message is *)
(*            judged when r next waits for its peer, against that state.   *)
(*   "Held":  the client's run is over and no new run reads it [S4].       *)
(* After MsgDone the server restarts and judges in StClient [S7].          *)
(***************************************************************************)
\* Literally: "Kinds is defined as the set of these five strings."
Kinds == {"MsgKeepAlive", "MsgKeepAliveResponse", "WrongCookieResponse",
          "MsgDone", "Oversized"}

\* In English: "The concrete message each kind stands for."
\* Literally: "KindMsg of k is defined as: in the case k equals
\*   "WrongCookieResponse", Msg of "MsgKeepAliveResponse", 1 and FALSE; in the
\*   case k equals "Oversized", Msg of "MsgKeepAlive", 0 and TRUE; in every
\*   other case, Msg of k, 0 and FALSE."
KindMsg(k) ==
    CASE k = "WrongCookieResponse" -> Msg("MsgKeepAliveResponse", 1, FALSE)  \* a response with cookie 1, not 0
    []   k = "Oversized"           -> Msg("MsgKeepAlive", 0, TRUE)          \* a ping that is too big
    []   OTHER                     -> Msg(k, 0, FALSE)                      \* the plain message of that type

\* In English: "If the run is over: a server judges the message as a new
\* run, a client leaves it Held. If side r holds agency: the message Waits.
\* Otherwise: judge it now."
\* Literally: "ReceiveTable of r, s and k is defined as: if s equals
\*   "StDone", then (if r equals "Server" and ServerRestarts is true, then Judge
\*   of r, "StClient", KindMsg of k, and 0; else "Held"); else if Agency of s
\*   equals r, then "Waits"; else Judge of r, s, KindMsg of k, and 0."
ReceiveTable(r, s, k) ==
    IF s = "StDone"
        THEN IF r = "Server" /\ ServerRestarts
                 THEN Judge(r, "StClient", KindMsg(k), 0)
                 ELSE "Held"
    ELSE IF Agency(s) = r THEN "Waits"
    ELSE Judge(r, s, KindMsg(k), 0)

-----------------------------------------------------------------------------

VARIABLES
    view,        \* view[r]: the state side r believes the protocol is in
    inbox,       \* inbox[r]: messages sent to r that r has not read yet
    pings,       \* pings sent so far
    sentCookie,  \* the cookie of the client's last ping
    pingCookie,  \* the cookie of the last ping the server read
    runs,        \* client runs started so far on this connection
    rogueLeft    \* rogue messages the misbehaving peer may still inject

\* Literally: "vars is defined as the tuple of all seven variables."
vars == <<view, inbox, pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "At the start, both sides think it is StClient, nothing is in
\* flight, nothing has been sent, this is run 1, and the rogue peer has its
\* full allowance."
\* Literally: "Init is defined as: view equals the function that maps every
\*   r in Roles to "StClient", and inbox equals the function that maps every r in
\*   Roles to the empty sequence, and pings equals 0, and sentCookie equals 0,
\*   and pingCookie equals 0, and runs equals 1, and rogueLeft equals
\*   RogueMessages."
Init ==
    /\ view = [r \in Roles |-> "StClient"]  \* both sides believe: StClient
    /\ inbox = [r \in Roles |-> <<>>]       \* both inboxes are empty
    /\ pings = 0                            \* no pings sent
    /\ sentCookie = 0
    /\ pingCookie = 0
    /\ runs = 1                             \* this is the first run
    /\ rogueLeft = RogueMessages            \* the rogue peer has its full allowance

\* In English: "The connection is over when someone has hung up, or both
\* sides are done."
\* Literally: "Ended is defined as: there exists an r in Roles such that
\*   view of r is a member of Failures, or, for all r in Roles, view of r equals
\*   "StDone"."
Ended ==
    \/ \E r \in Roles : view[r] \in Failures    \* some side hung up
    \/ \A r \in Roles : view[r] = "StDone"      \* or every side is done

\* --- Honest sends. Each needs the sender to hold agency [S1][S2]. -------

\* In English: "When the client believes it is StClient and has pings left,
\* it can send a ping with cookie c. It then believes it is StServer, the
\* ping is added to the server's inbox, one more ping has been sent, and the
\* client remembers c."
\* Literally: "ClientPing of c is defined as: view of "Client" equals
\*   "StClient", and pings is less than MaxPings, and view in the next state
\*   equals view except that its "Client" entry is "StServer", and inbox in the
\*   next state equals inbox except that its "Server" entry is the old entry with
\*   Msg of "MsgKeepAlive", c and FALSE appended, and pings in the next state
\*   equals pings plus 1, and sentCookie in the next state equals c, and
\*   pingCookie, runs and rogueLeft are unchanged."
ClientPing(c) ==
    /\ view["Client"] = "StClient"                  \* the client may send
    /\ pings < MaxPings                             \* and has pings left
    /\ view' = [view EXCEPT !["Client"] = "StServer"]   \* next, the client believes: StServer
    /\ inbox' = [inbox EXCEPT !["Server"] =
                     Append(@, Msg("MsgKeepAlive", c, FALSE))]  \* next, the ping is in the server's inbox
    /\ pings' = pings + 1                           \* next, one more ping has been sent
    /\ sentCookie' = c                              \* next, the client remembers cookie c
    /\ UNCHANGED <<pingCookie, runs, rogueLeft>>    \* and nothing else changes

\* In English: "When the server believes it is StServer, it can send a
\* response echoing the cookie of the ping it read [S2]. It then believes it
\* is StClient, and the response is added to the client's inbox."
\* Literally: "ServerRespond is defined as: view of "Server" equals
\*   "StServer", and view in the next state equals view except that its "Server"
\*   entry is "StClient", and inbox in the next state equals inbox except that
\*   its "Client" entry is the old entry with Msg of "MsgKeepAliveResponse",
\*   pingCookie and FALSE appended, and pings, sentCookie, pingCookie, runs and
\*   rogueLeft are unchanged."
ServerRespond ==
    /\ view["Server"] = "StServer"                  \* the server may send
    /\ view' = [view EXCEPT !["Server"] = "StClient"]   \* next, the server believes: StClient
    /\ inbox' = [inbox EXCEPT !["Client"] =
                     Append(@, Msg("MsgKeepAliveResponse", pingCookie, FALSE))]  \* next, the response is in the client's inbox
    /\ UNCHANGED <<pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "When the client believes it is StClient, it can send done.
\* It then believes it is StDone, and done is added to the server's inbox."
\* Literally: "ClientDone is defined as: view of "Client" equals
\*   "StClient", and view in the next state equals view except that its "Client"
\*   entry is "StDone", and inbox in the next state equals inbox except that its
\*   "Server" entry is the old entry with Msg of "MsgDone", 0 and FALSE appended,
\*   and the other five variables are unchanged."
ClientDone ==
    /\ view["Client"] = "StClient"                  \* the client may send
    /\ view' = [view EXCEPT !["Client"] = "StDone"]     \* next, the client believes: StDone
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0, FALSE))]  \* next, done is in the server's inbox
    /\ UNCHANGED <<pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "An honest send is a ping with some cookie, or a response,
\* or done."
\* Literally: "Send is defined as: there exists a c in Cookies such that
\*   ClientPing of c, or ServerRespond, or ClientDone."
Send == \/ \E c \in Cookies : ClientPing(c)
        \/ ServerRespond
        \/ ClientDone

\* --- Reading. -----------------------------------------------------------

\* In English: "Side r can read the oldest message in its inbox when it is
\* waiting for its peer, or when it is a restartable server whose run is
\* over. It judges the message, moves to the result, and removes the
\* message from its inbox. A server reading a ping remembers its cookie."
\*
\* Why only then: a side reads only while its peer has agency [S8]; a
\* message that arrived earlier waits until then and is judged against the
\* state at that moment [S9]. A server whose run ended restarts and reads in
\* StClient [S7]. A client whose run ended reads nothing until a new run
\* starts [S4][S5].
\* Literally: "Recv of r is defined as: inbox of r does not equal the empty
\*   sequence, and (Awaiting of r and view of r, or r equals "Server" and view of
\*   r equals "StDone" and ServerRestarts is true), and, letting m be the head of
\*   inbox of r: view in the next state equals view except that its r entry is
\*   Judge of r, RunState of view of r, m, and sentCookie; and pingCookie in the
\*   next state equals m's cookie if r equals "Server" and m's type equals
\*   "MsgKeepAlive", else pingCookie; and inbox in the next state equals inbox
\*   except that its r entry is the tail of the old entry; and pings, sentCookie,
\*   runs and rogueLeft are unchanged."
Recv(r) ==
    /\ inbox[r] /= <<>>                             \* r has something to read
    /\ \/ Awaiting(r, view[r])                      \* and r is waiting for its peer
       \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts  \* or r is a server that restarts
    /\ LET m == Head(inbox[r]) IN                   \* let m be the oldest message
         /\ view' = [view EXCEPT ![r] = Judge(r, RunState(view[r]), m, sentCookie)]  \* next, r is wherever judging m takes it
         /\ pingCookie' = IF r = "Server" /\ m.type = "MsgKeepAlive"
                              THEN m.cookie ELSE pingCookie  \* next, a server remembers a ping's cookie
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]       \* next, m is no longer in r's inbox
    /\ UNCHANGED <<pings, sentCookie, runs, rogueLeft>>

\* In English: "When the client's run is over and it may start another, it
\* can: it then believes it is StClient, and one more run has started [S5]."
\* Literally: "ClientRestart is defined as: view of "Client" equals
\*   "StDone", and runs is less than MaxRuns, and view in the next state equals
\*   view except that its "Client" entry is "StClient", and runs in the next
\*   state equals runs plus 1, and the other five variables are unchanged."
ClientRestart ==
    /\ view["Client"] = "StDone"                    \* the client's run is over
    /\ runs < MaxRuns                               \* and it may start another
    /\ view' = [view EXCEPT !["Client"] = "StClient"]   \* next, the client believes: StClient
    /\ runs' = runs + 1                             \* next, one more run has started
    /\ UNCHANGED <<inbox, pings, sentCookie, pingCookie, rogueLeft>>

\* In English: "While the rogue peer has allowance left, it can put any
\* message m into r's inbox, at any time, using up one of its allowance."
\* Literally: "Inject of r and m is defined as: rogueLeft is greater than
\*   0, and inbox in the next state equals inbox except that its r entry is the
\*   old entry with m appended, and rogueLeft in the next state equals rogueLeft
\*   minus 1, and the other five variables are unchanged."
Inject(r, m) ==
    /\ rogueLeft > 0                                \* the rogue peer has allowance left
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]  \* next, m is in r's inbox
    /\ rogueLeft' = rogueLeft - 1                   \* next, it has one less
    /\ UNCHANGED <<view, pings, sentCookie, pingCookie, runs>>

\* In English: "Progress is possible: some honest send, a restart, or some
\* side reading." (Everything except a timeout or a rogue injection.)
\* Literally: "Progress is defined as: Send, or ClientRestart, or there
\*   exists an r in Roles such that Recv of r."
Progress == Send \/ ClientRestart \/ \E r \in Roles : Recv(r)

\* --- Timeouts. ----------------------------------------------------------
\* [S2] "Timeouts per state" bound how long a side waits for its peer: 97s
\* in StClient (the server waiting), 60s in StServer (the client waiting),
\* after which "the connection SHOULD be torn down". The model has no clock:
\* with SlowPeers a timeout may fire whenever a side is waiting, because the
\* peer may be too slow; without it, a timeout fires only when nothing could
\* ever arrive, because a peer that is not stuck answers in time.
\*
\* In English: "If timeouts are on, the connection is not over, and side r
\* is waiting for its peer, then r can give up, provided peers may be slow,
\* or nothing else can ever happen."
\* Literally: "Timeout of r is defined as: UseTimeouts is true, and Ended
\*   is not true, and Awaiting of r and view of r, and (SlowPeers is true, or
\*   Progress is not enabled), and view in the next state equals view except
\*   that its r entry is "TimedOut", and the other six variables are unchanged."
Timeout(r) ==
    /\ UseTimeouts                                  \* timeouts are on
    /\ ~Ended                                       \* and the connection is not over
    /\ Awaiting(r, view[r])                         \* and r is waiting for its peer
    /\ SlowPeers \/ ~ENABLED Progress               \* and peers may be slow, or nothing else can happen
    /\ view' = [view EXCEPT ![r] = "TimedOut"]      \* next, r has given up
    /\ UNCHANGED <<inbox, pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "A step is an honest send, or a client restart, or some side
\* reading or timing out, or the rogue peer injecting some message, or,
\* once the connection is over, nothing changing."
\* Literally: "Next is defined as: Send, or ClientRestart, or there exists an
\*   r in Roles such that Recv of r or Timeout of r, or there exists an r in Roles
\*   and an m in Messages such that Inject of r and m, or Ended is true and vars
\*   is unchanged."
Next ==
    \/ Send
    \/ ClientRestart
    \/ \E r \in Roles : Recv(r) \/ Timeout(r)
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
\*   from Roles to the union of States and Failures, and inbox is a member of the
\*   set of functions from Roles to sequences of Messages, and pings is a member
\*   of 0 through MaxPings, and sentCookie and pingCookie are members of Cookies,
\*   and runs is a member of 1 through MaxRuns, and rogueLeft is a member of 0
\*   through RogueMessages."
TypeOK ==
    /\ view \in [Roles -> States \cup Failures]     \* each side believes a state, or has hung up
    /\ inbox \in [Roles -> Seq(Messages)]           \* each inbox is a list of messages
    /\ pings \in 0..MaxPings
    /\ sentCookie \in Cookies
    /\ pingCookie \in Cookies
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages

\* In English: "No side has hung up." With honest peers that answer in
\* time, this must always hold.
\* Literally: "NoFailures is defined as: for all r in Roles, view of r is
\*   not a member of Failures."
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "No side has seen a protocol violation." With honest but slow
\* peers, a timeout is possible but a violation is not.
\* Literally: "NoViolations is defined as: for all r in Roles, view of r
\*   does not equal "Violation"."
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* In English: "Every response waiting in the client's inbox carries the
\* cookie the client is waiting for [S2]."
\* Literally: "ResponsesEchoCookies is defined as: for all i in 1
\*   through the length of inbox of "Client", if element i's type equals
\*   "MsgKeepAliveResponse", then element i's cookie equals sentCookie."
ResponsesEchoCookies ==
    \A i \in 1..Len(inbox["Client"]) :              \* for every position i in the client's inbox:
        inbox["Client"][i].type = "MsgKeepAliveResponse" =>     \* if the message there is a response,
            inbox["Client"][i].cookie = sentCookie              \* then its cookie is the one sent

\* Agency means only one message per run is on the wire at a time [S1]
\* "At any time, only one side has the agency". Across runs there can be
\* more: a client may send MsgDone, start a new run, and send MsgKeepAlive
\* before the server reads the MsgDone; that is why [S4] keeps a run's
\* trailing bytes.
\* Literally: "IsDoneMsg of m is defined as: m's type equals "MsgDone"."
IsDoneMsg(m) == m.type = "MsgDone"

\* In English: "In each inbox, every message except the newest is an
\* earlier run's done, and at most one inbox ends in something other than
\* done."
\* Literally: "OneMessageInFlightPerRun is defined as: for all r
\*   in Roles, for all i in 1 through the length of inbox of r minus 1,
\*   IsDoneMsg of element i of inbox of r; and, for all r1 and r2 in Roles, if
\*   inbox of r1 and inbox of r2 are both non-empty and the last element of each
\*   is not a done message, then r1 equals r2."
OneMessageInFlightPerRun ==
    /\ \A r \in Roles :
           \A i \in 1..(Len(inbox[r]) - 1) : IsDoneMsg(inbox[r][i])     \* all but the newest are done
    /\ \A r1, r2 \in Roles :                                            \* for any two sides:
           (/\ inbox[r1] /= <<>> /\ inbox[r2] /= <<>>                   \* if both inboxes are non-empty
            /\ ~IsDoneMsg(inbox[r1][Len(inbox[r1])])                    \* and both end in something
            /\ ~IsDoneMsg(inbox[r2][Len(inbox[r2])])) => r1 = r2        \* other than done, they are the same side

\* In English: "It is never the case that the client believes it may send
\* AND the server believes it may send."
\* Literally: "NeverBothHaveAgency is defined as: it is not the case
\*   that (view of "Client" is a member of States and Agency of it equals
\*   "Client", and view of "Server" is a member of States and Agency of it equals
\*   "Server")."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "When both inboxes are empty, both sides believe the same
\* state, except that a server that ended a run agrees with a client
\* starting the next one (it will restart on the client's first message)."
\* Literally: "ViewsAgreeWhenQuiet is defined as: if, for all r in
\*   Roles, inbox of r equals the empty sequence, then view of "Client" equals
\*   view of "Server", or (ServerRestarts is true, and view of "Server" equals
\*   "StDone", and view of "Client" equals "StClient")."
ViewsAgreeWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>>) =>           \* if nothing is in flight, then
        \/ view["Client"] = view["Server"]          \* both sides agree,
        \/ /\ ServerRestarts                        \* or the server will restart
           /\ view["Server"] = "StDone"             \*   from StDone
           /\ view["Client"] = "StClient"           \*   for a client starting a new run

-----------------------------------------------------------------------------
(* Properties about steps rather than states. [][P]_vars means "every step *)
(* satisfies P"; view' is the value after the step.                      *)

\* THE STATES THAT CANNOT BE ENTERED.
\* In English: "In every step, for every side: if its state changes, then
\* it changed to a failure, or from StDone to the start of a new run, or
\* along some row of the transition table."
\* Literally: "OnlyLegalMoves is defined as: always, for every step,
\*   for all r in Roles, if view of r in the next state does not equal view of r,
\*   then view of r in the next state is a member of Failures, or (view of r
\*   equals "StDone" and view of r in the next state equals "StClient"), or there
\*   exists a tr in Transitions such that element 1 of tr equals RunState of view
\*   of r and element 3 of tr equals view of r in the next state."
OnlyLegalMoves ==
    [][\A r \in Roles :
         view'[r] /= view[r] =>                                     \* if r's state changes, then
             \/ view'[r] \in Failures                               \* it is a failure,
             \/ view[r] = "StDone" /\ view'[r] = "StClient"         \* or a new run,
             \/ \E tr \in Transitions :
                    tr[1] = RunState(view[r]) /\ tr[3] = view'[r]]_vars  \* or a legal transition

\* In English: "In every step, a side that has hung up stays hung up."
\* Literally: "FailuresAreFinal is defined as: always, for every step,
\*   for all r in Roles, if view of r is a member of Failures, then view of r in
\*   the next state equals view of r."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

\* DELIBERATELY WRONG, used by KeepAliveRogueBug.cfg. In English: "A rogue
\* message can never make a side hang up." TLC shows the shortest
\* counterexample.
\* Literally: "NoFailuresEvenWithRogue is defined as NoFailures."
NoFailuresEvenWithRogue == NoFailures
=============================================================================
