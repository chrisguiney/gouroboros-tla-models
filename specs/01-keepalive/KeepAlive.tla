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
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxPings,       \* how many pings the client may send (keeps the model finite)
    MaxRuns,        \* how many runs the client may start on one connection
    RogueMessages,  \* how many arbitrary messages a misbehaving peer may inject
    UseTimeouts,    \* TRUE: the state timeouts of [S2] are in force
    SlowPeers,      \* TRUE: a peer may be slower than the timeout allows
    ServerRestarts  \* TRUE: the server restarts after MsgDone [S7]. FALSE: gOuroboros today

Roles     == {"Client", "Server"}
States    == {"StClient", "StServer", "StDone"}
MsgTypes  == {"MsgKeepAlive", "MsgKeepAliveResponse", "MsgDone"}

\* Cookies are 16-bit numbers [S2]. Two values are enough to tell a matching
\* cookie from a wrong one, and keep the model small.
Cookies   == {0, 1}

\* A message is a record: like a Go struct. `oversized` marks one larger than
\* the state's size limit (65535 bytes [S2]); the model does not need sizes.
\* [a |-> x, b |-> y] builds a record; m.a reads a field.
Msg(t, c, big) == [type |-> t, cookie |-> c, oversized |-> big]
Messages == {Msg(t, c, big) : t \in MsgTypes, c \in Cookies, big \in BOOLEAN}

\* Where a side can end up besides a protocol state: it detected a protocol
\* violation and closed the connection, or it waited too long and gave up.
\* Either way the connection is torn down [S1][S2].
Failures == {"Violation", "TimedOut"}

\* Who may send in each state. This is "agency". [S2] agency table; [S1]
\* and [S3] for StDone, where nobody has it. CASE is like a Go switch.
Agency(s) == CASE s = "StClient" -> "Client"
             []   s = "StServer" -> "Server"
             []   s = "StDone"   -> "Nobody"

\* The whole protocol, as a set of <<from-state, message, to-state>> tuples.
\* [S2] state-machine figure.
Transitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* Side r is waiting for its peer in state s: the peer has agency.
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
    IF m.oversized                     THEN "Violation"
    ELSE IF ~IsLegal(s, m.type)        THEN "Violation"
    ELSE IF m.type = "MsgKeepAliveResponse" /\ m.cookie /= expected
                                       THEN "Violation"
    ELSE After(s, m.type)

\* A new run starts in the initial state, StClient [S2].
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

KindMsg(k) ==
    CASE k = "WrongCookieResponse" -> Msg("MsgKeepAliveResponse", 1, FALSE)
    []   k = "Oversized"           -> Msg("MsgKeepAlive", 0, TRUE)
    []   OTHER                     -> Msg(k, 0, FALSE)

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

Init ==
    /\ view = [r \in Roles |-> "StClient"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ pings = 0
    /\ sentCookie = 0
    /\ pingCookie = 0
    /\ runs = 1
    /\ rogueLeft = RogueMessages

\* The connection is over: someone hung up, or both sides are done.
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ \A r \in Roles : view[r] = "StDone"

\* Honest sends. Each needs the sender to hold agency [S1][S2].
\* [f EXCEPT ![k] = v] is "f with key k set to v"; @ means "the old value".
ClientPing(c) ==
    /\ view["Client"] = "StClient"
    /\ pings < MaxPings
    /\ view' = [view EXCEPT !["Client"] = "StServer"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgKeepAlive", c, FALSE))]
    /\ pings' = pings + 1
    /\ sentCookie' = c
    /\ UNCHANGED <<pingCookie, runs, rogueLeft>>

\* "The cookie value ... allows to match requests with responses" [S2]: the
\* server echoes the cookie of the ping it is answering.
ServerRespond ==
    /\ view["Server"] = "StServer"
    /\ view' = [view EXCEPT !["Server"] = "StClient"]
    /\ inbox' = [inbox EXCEPT !["Client"] =
                     Append(@, Msg("MsgKeepAliveResponse", pingCookie, FALSE))]
    /\ UNCHANGED <<pings, sentCookie, pingCookie, runs, rogueLeft>>

ClientDone ==
    /\ view["Client"] = "StClient"
    /\ view' = [view EXCEPT !["Client"] = "StDone"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0, FALSE))]
    /\ UNCHANGED <<pings, sentCookie, pingCookie, runs, rogueLeft>>

Send == \/ \E c \in Cookies : ClientPing(c)
        \/ ServerRespond
        \/ ClientDone

\* Side r reads the oldest message in its inbox. It reads only while waiting
\* for its peer [S8]; a message that arrived earlier waits until then and is
\* judged against the state at that moment [S9]. A server whose run ended
\* restarts and reads in StClient [S7]. A client whose run ended reads
\* nothing until a new run starts [S4][S5].
Recv(r) ==
    /\ inbox[r] /= <<>>
    /\ \/ Awaiting(r, view[r])
       \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts
    /\ LET m == Head(inbox[r]) IN
         /\ view' = [view EXCEPT ![r] = Judge(r, RunState(view[r]), m, sentCookie)]
         /\ pingCookie' = IF r = "Server" /\ m.type = "MsgKeepAlive"
                              THEN m.cookie ELSE pingCookie
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<pings, sentCookie, runs, rogueLeft>>

\* The client starts a new run on the same connection [S5].
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StClient"]
    /\ runs' = runs + 1
    /\ UNCHANGED <<inbox, pings, sentCookie, pingCookie, rogueLeft>>

\* A misbehaving peer slips any message into r's inbox, at any time.
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, pings, sentCookie, pingCookie, runs>>

\* Anything other than a timeout or an injection that could happen now.
Progress == Send \/ ClientRestart \/ \E r \in Roles : Recv(r)

\* [S2] "Timeouts per state" bound how long a side waits for its peer: 97s
\* in StClient (the server waiting), 60s in StServer (the client waiting),
\* after which "the connection SHOULD be torn down". The model has no clock:
\* with SlowPeers a timeout may fire whenever a side is waiting, because the
\* peer may be too slow; without it, a timeout fires only when nothing could
\* ever arrive, because a peer that is not stuck answers in time.
\* ENABLED A is true when action A could happen in the current state.
Timeout(r) ==
    /\ UseTimeouts
    /\ ~Ended
    /\ Awaiting(r, view[r])
    /\ SlowPeers \/ ~ENABLED Progress
    /\ view' = [view EXCEPT ![r] = "TimedOut"]
    /\ UNCHANGED <<inbox, pings, sentCookie, pingCookie, runs, rogueLeft>>

Next ==
    \/ Send
    \/ ClientRestart
    \/ \E r \in Roles : Recv(r) \/ Timeout(r)
    \/ \E r \in Roles, m \in Messages : Inject(r, m)
    \/ Ended /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants: must hold in every reachable state. *)

TypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ pings \in 0..MaxPings
    /\ sentCookie \in Cookies
    /\ pingCookie \in Cookies
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages

\* With honest peers that answer in time, nobody ever hangs up.
NoFailures == \A r \in Roles : view[r] \notin Failures

\* With honest peers, a slow peer can cause a timeout but never a
\* protocol violation.
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* Every response on its way to the client echoes the cookie the client is
\* waiting for [S2].
ResponsesEchoCookies ==
    \A i \in 1..Len(inbox["Client"]) :
        inbox["Client"][i].type = "MsgKeepAliveResponse" =>
            inbox["Client"][i].cookie = sentCookie

\* Agency means only one message per run is on the wire at a time [S1]
\* "At any time, only one side has the agency". Across runs there can be
\* more: a client may send MsgDone, start a new run, and send MsgKeepAlive
\* before the server reads the MsgDone; that is why [S4] keeps a run's
\* trailing bytes. So every queued message except the newest is an earlier
\* run's MsgDone, and only one message overall is something else.
\* \A i \in 1..n : P(i) checks P for each position i from 1 to n.
IsDoneMsg(m) == m.type = "MsgDone"
OneMessageInFlightPerRun ==
    /\ \A r \in Roles :
           \A i \in 1..(Len(inbox[r]) - 1) : IsDoneMsg(inbox[r][i])
    /\ \A r1, r2 \in Roles :
           (/\ inbox[r1] /= <<>> /\ inbox[r2] /= <<>>
            /\ ~IsDoneMsg(inbox[r1][Len(inbox[r1])])
            /\ ~IsDoneMsg(inbox[r2][Len(inbox[r2])])) => r1 = r2

\* The two sides never both believe it is their own turn to talk.
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* Once every message has been read, both sides agree on the state. A server
\* that has ended a run agrees with a client starting the next one, because
\* it will restart on the client's first message.
ViewsAgreeWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>>) =>
        \/ view["Client"] = view["Server"]
        \/ /\ ServerRestarts
           /\ view["Server"] = "StDone"
           /\ view["Client"] = "StClient"

-----------------------------------------------------------------------------
(* Properties about steps rather than states. [][P]_vars means "every step *)
(* satisfies P"; view' is the value after the step.                      *)

\* THE STATES THAT CANNOT BE ENTERED: a side's state only ever moves along
\* a row of Transitions (in a new run, if the last one ended), to a failure,
\* or from StDone to the start of a new run. No other move exists.
OnlyLegalMoves ==
    [][\A r \in Roles :
         view'[r] /= view[r] =>
             \/ view'[r] \in Failures
             \/ view[r] = "StDone" /\ view'[r] = "StClient"
             \/ \E tr \in Transitions :
                    tr[1] = RunState(view[r]) /\ tr[3] = view'[r]]_vars

\* A side that hung up stays hung up.
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

\* DELIBERATELY WRONG, used by KeepAliveRogueBug.cfg: claims a rogue message
\* can never make a side hang up. TLC shows the shortest counterexample.
NoFailuresEvenWithRogue == NoFailures
=============================================================================
