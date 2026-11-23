----------------------------- MODULE KeepAlive -----------------------------
(***************************************************************************)
(* The keep-alive mini-protocol, at the state-machine level, including     *)
(* what happens when a run ends and a new one starts on the same           *)
(* connection.                                                             *)
(*                                                                         *)
(* Sources, all at IntersectMBO/ouroboros-network commit 5f356486ab3e.     *)
(* specs/01-keepalive/README.md has links and quotes.                      *)
(*   [S1] docs/network-spec/miniprotocols.tex 27-36, 96-98: one side has   *)
(*        agency at a time; an unexpected message aborts the connection.   *)
(*   [S2] docs/network-spec/miniprotocols.tex 1560-1650: keep-alive states,*)
(*        transitions, agency, cookie rule, timeouts.                      *)
(*   [S3] .../Protocol/KeepAlive/Type.hs 89-106: message types, and        *)
(*        StateAgency StDone = NobodyAgency.                               *)
(*   [S4] network-mux/src/Network/Mux.hs 362-378, 512: a run that ends     *)
(*        puts its unread bytes back in the queue for the next run; the    *)
(*        mux does not restart it.                                         *)
(*   [S5] network-mux/src/Network/Mux.hs 846-852: a finished mini-protocol *)
(*        may be started again on the same connection.                     *)
(*   [S6] ouroboros-network/framework/lib/Ouroboros/Network/               *)
(*        InboundGovernor.hs 433-475: a responder (server) that ends       *)
(*        cleanly is restarted.                                            *)
(*                                                                         *)
(* The gOuroboros code it is compared with is protocol/keepalive/          *)
(* keepalive.go (StateMap), protocol/keepalive/server.go, and the receive  *)
(* checks in protocol/protocol.go.                                         *)
(*                                                                         *)
(* Unlike the hello model, each side keeps ITS OWN copy of the protocol    *)
(* state, and messages travel through an inbox. That is what lets the      *)
(* model show the two sides agreeing, or disagreeing.                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxPings,       \* how many pings the client may send (keeps the model finite)
    MaxRuns,        \* how many runs the client may start on one connection
    RogueMessages,  \* how many arbitrary messages a misbehaving peer may inject
    UseTimeouts,    \* TRUE: a side stuck waiting for its peer gives up
    ServerRestarts  \* TRUE: reference behavior [S6]. FALSE: gOuroboros today

Roles    == {"Client", "Server"}
States   == {"StClient", "StServer", "StDone"}
Messages == {"MsgKeepAlive", "MsgKeepAliveResponse", "MsgDone"}

\* Where a side can end up besides a protocol state: it detected a protocol
\* violation and closed the connection, or it waited too long and gave up.
Failures == {"Violation", "TimedOut"}

\* Who may send in each state. This is "agency". [S2] agency table, and
\* [S3] StateAgency for StDone. CASE is like a Go switch statement.
Agency(s) == CASE s = "StClient" -> "Client"
             []   s = "StServer" -> "Server"
             []   s = "StDone"   -> "Nobody"

\* The whole protocol, as a set of <<from-state, message, to-state>> tuples.
\* <<a, b, c>> is a tuple; t[1] is its first element.
\* [S2] state-machine figure; [S3] the three Message constructors.
Transitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

IsLegal(s, m) == \E t \in Transitions : t[1] = s /\ t[2] = m

\* CHOOSE picks the (only) matching tuple; [3] takes its to-state.
After(s, m) == (CHOOSE t \in Transitions : t[1] = s /\ t[2] = m)[3]

Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* WITHIN A RUN: what side r must do when message m arrives from its peer
\* while r believes the state is s. [S1]: "If either side receives a message
\* that is not expected according to the mini-protocol the communication is
\* aborted (the connection is closed)."
Receive(r, s, m) ==
    IF Agency(s) = Peer(r) /\ IsLegal(s, m)
        THEN After(s, m)      \* the peer was allowed to say that: accept it
        ELSE "Violation"      \* wrong speaker or wrong message: hang up

\* A new run starts in the initial state, StClient [S2].
RunState(s) == IF s = "StDone" THEN "StClient" ELSE s

(***************************************************************************)
(* THE RECEIVE TABLE. What happens to message m arriving at side r in      *)
(* state s, including after a run ended (StDone). The gOuroboros tests     *)
(* check against this, cell by cell (run `make keepalive-table`).          *)
(*                                                                         *)
(* After StDone no run is reading. The server restarts and the new run     *)
(* reads the message [S6]; the client's bytes wait for a next run that may *)
(* never come [S4], shown as "Held".                                       *)
(***************************************************************************)
ReceiveTable(r, s, m) ==
    IF s /= "StDone"                 THEN Receive(r, s, m)
    ELSE IF r = "Server" /\ ServerRestarts THEN Receive(r, "StClient", m)
    ELSE "Held"

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in
    inbox,      \* inbox[r]: messages sent to r that r has not read yet
    pings,      \* pings sent so far
    runs,       \* client runs started so far on this connection
    rogueLeft   \* rogue messages the misbehaving peer may still inject

vars == <<view, inbox, pings, runs, rogueLeft>>

Init ==
    /\ view = [r \in Roles |-> "StClient"]  \* a function: like a Go map
    /\ inbox = [r \in Roles |-> <<>>]       \* <<>> is the empty sequence
    /\ pings = 0
    /\ runs = 1
    /\ rogueLeft = RogueMessages

\* The connection is over: someone hung up, or both sides are done.
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ \A r \in Roles : view[r] = "StDone"

\* An honest side sends a message it is allowed to send.
\* [f EXCEPT ![k] = v] is "f with key k set to v"; @ means "the old value".
Send(r, m) ==
    /\ view[r] \in {"StClient", "StServer"}
    /\ Agency(view[r]) = r
    /\ IsLegal(view[r], m)
    /\ m = "MsgKeepAlive" => pings < MaxPings
    /\ view' = [view EXCEPT ![r] = After(view[r], m)]
    /\ inbox' = [inbox EXCEPT ![Peer(r)] = Append(@, m)]
    /\ pings' = IF m = "MsgKeepAlive" THEN pings + 1 ELSE pings
    /\ UNCHANGED <<runs, rogueLeft>>

\* Some run of side r is reading: an active run, or a server that restarts
\* because a message arrived after its last run ended [S6].
Reading(r) ==
    \/ view[r] \in {"StClient", "StServer"}
    \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts

\* Side r reads the oldest message in its inbox. With no run reading, the
\* message just stays in the inbox [S4].
Recv(r) ==
    /\ Reading(r)
    /\ inbox[r] /= <<>>
    /\ view' = [view EXCEPT ![r] = Receive(r, RunState(view[r]), Head(inbox[r]))]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<pings, runs, rogueLeft>>

\* The client starts a new run on the same connection [S5].
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StClient"]
    /\ runs' = runs + 1
    /\ UNCHANGED <<inbox, pings, rogueLeft>>

\* A misbehaving peer slips any message into r's inbox, at any time.
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, pings, runs>>

\* Anything other than a timeout or an injection that could happen now.
Progress ==
    \/ ClientRestart
    \/ \E r \in Roles : Recv(r) \/ \E m \in Messages : Send(r, m)

\* Side r is waiting for its peer, and nothing can ever arrive: it gives up.
\* [S2] "Timeouts per state": 97s in StClient, 60s in StServer, after which
\* "the connection SHOULD be torn down". The model has no clock, so it only
\* lets a timeout fire when waiting longer could never help.
\* ENABLED A is true when action A could happen in the current state.
Timeout(r) ==
    /\ UseTimeouts
    /\ ~Ended
    /\ ~ENABLED Progress
    /\ view[r] \in {"StClient", "StServer"}
    /\ Agency(view[r]) = Peer(r)
    /\ view' = [view EXCEPT ![r] = "TimedOut"]
    /\ UNCHANGED <<inbox, pings, runs, rogueLeft>>

Next ==
    \/ \E r \in Roles, m \in Messages : Send(r, m) \/ Inject(r, m)
    \/ \E r \in Roles : Recv(r) \/ Timeout(r)
    \/ ClientRestart
    \/ Ended /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants: must hold in every reachable state. *)

TypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ pings \in 0..MaxPings
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages

\* With honest peers, nobody ever hangs up or times out.
NoFailures == \A r \in Roles : view[r] \notin Failures

\* Agency means only one message per run is on the wire at a time. [S1] "At
\* any time, only one side has the agency". Across runs there can be more: a
\* client may send MsgDone, start a new run, and send MsgKeepAlive before the
\* server reads the MsgDone; that is why [S4] keeps a run's trailing bytes.
\* So every queued message except the newest must be an earlier run's
\* MsgDone, and only one message overall can be something else.
\* \A i \in 1..n : P(i) checks P for each position i from 1 to n.
OneMessageInFlightPerRun ==
    /\ \A r \in Roles :
           \A i \in 1..(Len(inbox[r]) - 1) : inbox[r][i] = "MsgDone"
    /\ \A r1, r2 \in Roles :
           (/\ inbox[r1] /= <<>> /\ inbox[r2] /= <<>>
            /\ inbox[r1][Len(inbox[r1])] /= "MsgDone"
            /\ inbox[r2][Len(inbox[r2])] /= "MsgDone") => r1 = r2

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
             \/ \E t \in Transitions :
                    t[1] = RunState(view[r]) /\ t[3] = view'[r]]_vars

\* A side that hung up stays hung up.
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

\* DELIBERATELY WRONG, used by KeepAliveRogueBug.cfg: claims a rogue message
\* can never make a side hang up. TLC shows the shortest counterexample.
NoFailuresEvenWithRogue == NoFailures
=============================================================================
