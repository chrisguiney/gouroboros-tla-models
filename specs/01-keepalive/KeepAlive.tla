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
Roles     == {"Client", "Server"}
States    == {"StClient", "StServer", "StDone"}
MsgTypes  == {"MsgKeepAlive", "MsgKeepAliveResponse", "MsgDone"}

\* Cookies are 16-bit numbers [S2]. Two values are enough to tell a matching
\* cookie from a wrong one, and keep the model small.
Cookies   == {0, 1}

\* A message is a record: like a Go struct with three fields. `oversized`
\* marks one larger than the state's size limit (65535 bytes [S2]); the
\* model does not need actual sizes.
\* In English: "Msg(t, c, big) is the message of type t, cookie c, and
\* oversized flag big."
Msg(t, c, big) == [type |-> t, cookie |-> c, oversized |-> big]

\* In English: "Messages is every possible message: every type, with every
\* cookie, oversized or not."
Messages == {Msg(t, c, big) : t \in MsgTypes, c \in Cookies, big \in BOOLEAN}

\* Where a side can end up besides a protocol state: it detected a protocol
\* violation and closed the connection, or it waited too long and gave up.
\* Either way the connection is torn down [S1][S2].
Failures == {"Violation", "TimedOut"}

\* In English: "In StClient the client may send; in StServer the server
\* may send; in StDone nobody may." This is "agency". [S2] agency table;
\* [S1] and [S3] for StDone.
Agency(s) == CASE s = "StClient" -> "Client"
             []   s = "StServer" -> "Server"
             []   s = "StDone"   -> "Nobody"

\* The whole protocol, as a set of <<from-state, message, to-state>> tuples
\* ([S2] state-machine figure). In English:
\*   "In StClient, MsgKeepAlive moves to StServer.
\*    In StClient, MsgDone moves to StDone.
\*    In StServer, MsgKeepAliveResponse moves to StClient."
Transitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

\* In English: "Message type t is legal in state s if some row of the
\* table starts with s and t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t

\* In English: "After(s, t) is the state you move to when t is sent in s":
\* pick the row that starts with s and t, and take its third column.
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

\* In English: "The peer of the client is the server, and vice versa."
Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s: s is an active
\* state, and the peer is the one allowed to send."
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
Judge(r, s, m, expected) ==
    IF m.oversized                     THEN "Violation"  \* if it is too big: hang up
    ELSE IF ~IsLegal(s, m.type)        THEN "Violation"  \* if it is not legal here: hang up
    ELSE IF m.type = "MsgKeepAliveResponse" /\ m.cookie /= expected
                                       THEN "Violation"  \* if it is a response with the wrong cookie: hang up
    ELSE After(s, m.type)                                \* otherwise: move to the next state

\* In English: "A new run starts in StClient [S2]; otherwise the run keeps
\* its state." Used when a server that finished a run reads a new message.
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
Kinds == {"MsgKeepAlive", "MsgKeepAliveResponse", "WrongCookieResponse",
          "MsgDone", "Oversized"}

\* In English: "The concrete message each kind stands for."
KindMsg(k) ==
    CASE k = "WrongCookieResponse" -> Msg("MsgKeepAliveResponse", 1, FALSE)  \* a response with cookie 1, not 0
    []   k = "Oversized"           -> Msg("MsgKeepAlive", 0, TRUE)          \* a ping that is too big
    []   OTHER                     -> Msg(k, 0, FALSE)                      \* the plain message of that type

\* In English: "If the run is over: a server judges the message as a new
\* run, a client leaves it Held. If side r holds agency: the message Waits.
\* Otherwise: judge it now."
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

vars == <<view, inbox, pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "At the start, both sides think it is StClient, nothing is in
\* flight, nothing has been sent, this is run 1, and the rogue peer has its
\* full allowance."
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
Ended ==
    \/ \E r \in Roles : view[r] \in Failures    \* some side hung up
    \/ \A r \in Roles : view[r] = "StDone"      \* or every side is done

\* --- Honest sends. Each needs the sender to hold agency [S1][S2]. -------

\* In English: "When the client believes it is StClient and has pings left,
\* it can send a ping with cookie c. It then believes it is StServer, the
\* ping is added to the server's inbox, one more ping has been sent, and the
\* client remembers c."
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
ServerRespond ==
    /\ view["Server"] = "StServer"                  \* the server may send
    /\ view' = [view EXCEPT !["Server"] = "StClient"]   \* next, the server believes: StClient
    /\ inbox' = [inbox EXCEPT !["Client"] =
                     Append(@, Msg("MsgKeepAliveResponse", pingCookie, FALSE))]  \* next, the response is in the client's inbox
    /\ UNCHANGED <<pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "When the client believes it is StClient, it can send done.
\* It then believes it is StDone, and done is added to the server's inbox."
ClientDone ==
    /\ view["Client"] = "StClient"                  \* the client may send
    /\ view' = [view EXCEPT !["Client"] = "StDone"]     \* next, the client believes: StDone
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0, FALSE))]  \* next, done is in the server's inbox
    /\ UNCHANGED <<pings, sentCookie, pingCookie, runs, rogueLeft>>

\* In English: "An honest send is a ping with some cookie, or a response,
\* or done."
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
ClientRestart ==
    /\ view["Client"] = "StDone"                    \* the client's run is over
    /\ runs < MaxRuns                               \* and it may start another
    /\ view' = [view EXCEPT !["Client"] = "StClient"]   \* next, the client believes: StClient
    /\ runs' = runs + 1                             \* next, one more run has started
    /\ UNCHANGED <<inbox, pings, sentCookie, pingCookie, rogueLeft>>

\* In English: "While the rogue peer has allowance left, it can put any
\* message m into r's inbox, at any time, using up one of its allowance."
Inject(r, m) ==
    /\ rogueLeft > 0                                \* the rogue peer has allowance left
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]  \* next, m is in r's inbox
    /\ rogueLeft' = rogueLeft - 1                   \* next, it has one less
    /\ UNCHANGED <<view, pings, sentCookie, pingCookie, runs>>

\* In English: "Progress is possible: some honest send, a restart, or some
\* side reading." (Everything except a timeout or a rogue injection.)
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
Next ==
    \/ Send
    \/ ClientRestart
    \/ \E r \in Roles : Recv(r) \/ Timeout(r)
    \/ \E r \in Roles, m \in Messages : Inject(r, m)
    \/ Ended /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants: must hold in every reachable state. *)

\* In English: "Every variable holds the kind of value it should."
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
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "No side has seen a protocol violation." With honest but slow
\* peers, a timeout is possible but a violation is not.
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* In English: "Every response waiting in the client's inbox carries the
\* cookie the client is waiting for [S2]."
ResponsesEchoCookies ==
    \A i \in 1..Len(inbox["Client"]) :              \* for every position i in the client's inbox:
        inbox["Client"][i].type = "MsgKeepAliveResponse" =>     \* if the message there is a response,
            inbox["Client"][i].cookie = sentCookie              \* then its cookie is the one sent

\* Agency means only one message per run is on the wire at a time [S1]
\* "At any time, only one side has the agency". Across runs there can be
\* more: a client may send MsgDone, start a new run, and send MsgKeepAlive
\* before the server reads the MsgDone; that is why [S4] keeps a run's
\* trailing bytes.
IsDoneMsg(m) == m.type = "MsgDone"

\* In English: "In each inbox, every message except the newest is an
\* earlier run's done, and at most one inbox ends in something other than
\* done."
OneMessageInFlightPerRun ==
    /\ \A r \in Roles :
           \A i \in 1..(Len(inbox[r]) - 1) : IsDoneMsg(inbox[r][i])     \* all but the newest are done
    /\ \A r1, r2 \in Roles :                                            \* for any two sides:
           (/\ inbox[r1] /= <<>> /\ inbox[r2] /= <<>>                   \* if both inboxes are non-empty
            /\ ~IsDoneMsg(inbox[r1][Len(inbox[r1])])                    \* and both end in something
            /\ ~IsDoneMsg(inbox[r2][Len(inbox[r2])])) => r1 = r2        \* other than done, they are the same side

\* In English: "It is never the case that the client believes it may send
\* AND the server believes it may send."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "When both inboxes are empty, both sides believe the same
\* state, except that a server that ended a run agrees with a client
\* starting the next one (it will restart on the client's first message)."
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
OnlyLegalMoves ==
    [][\A r \in Roles :
         view'[r] /= view[r] =>                                     \* if r's state changes, then
             \/ view'[r] \in Failures                               \* it is a failure,
             \/ view[r] = "StDone" /\ view'[r] = "StClient"         \* or a new run,
             \/ \E tr \in Transitions :
                    tr[1] = RunState(view[r]) /\ tr[3] = view'[r]]_vars  \* or a legal transition

\* In English: "In every step, a side that has hung up stays hung up."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

\* DELIBERATELY WRONG, used by KeepAliveRogueBug.cfg. In English: "A rogue
\* message can never make a side hang up." TLC shows the shortest
\* counterexample.
NoFailuresEvenWithRogue == NoFailures
=============================================================================
