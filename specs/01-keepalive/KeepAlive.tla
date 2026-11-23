----------------------------- MODULE KeepAlive -----------------------------
(***************************************************************************)
(* The keep-alive mini-protocol, at the state-machine level.               *)
(*                                                                         *)
(* Sources, all at IntersectMBO/ouroboros-network commit 5f356486ab3e:     *)
(*   [S1] docs/network-spec/miniprotocols.tex, section "Protocols as State *)
(*        Machines" (lines 27-36, 96-98): one side has agency at a time;   *)
(*        an unexpected message aborts the connection.                     *)
(*   [S2] docs/network-spec/miniprotocols.tex, section "Keep Alive Mini    *)
(*        Protocol" (lines 1560-1650): states, transitions, agency,        *)
(*        cookie rule, timeouts.                                           *)
(*   [S3] ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/      *)
(*        KeepAlive/Type.hs (lines 89-106): the reference implementation's *)
(*        message types and StateAgency, including StDone = NobodyAgency.  *)
(* specs/01-keepalive/README.md has full links. The gOuroboros code it is  *)
(* compared with is protocol/keepalive/keepalive.go (StateMap) and the     *)
(* receive checks in protocol/protocol.go.                                 *)
(*                                                                         *)
(* Unlike the hello model, each side keeps ITS OWN copy of the protocol    *)
(* state, and messages travel through an inbox. That is what lets the      *)
(* model show the two sides agreeing, or disagreeing.                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxPings,       \* how many pings the client may send (keeps the model finite)
    RogueMessages,  \* how many arbitrary messages a misbehaving peer may inject
    UseTimeouts     \* TRUE: a side stuck waiting for its peer gives up (as gOuroboros does)

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
\* [S2] state-machine figure; [S3] the three Message constructors.
\* <<a, b, c>> is a tuple; t[1] is its first element.
Transitions ==
    { <<"StClient", "MsgKeepAlive",         "StServer">>,
      <<"StClient", "MsgDone",              "StDone">>,
      <<"StServer", "MsgKeepAliveResponse", "StClient">> }

IsLegal(s, m) == \E t \in Transitions : t[1] = s /\ t[2] = m

\* CHOOSE picks the (only) matching tuple; [3] takes its to-state.
After(s, m) == (CHOOSE t \in Transitions : t[1] = s /\ t[2] = m)[3]

Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

(***************************************************************************)
(* THE RECEIVE RULE. What side r must do when message m arrives from its   *)
(* peer while r believes the state is s. The Go tests check gOuroboros     *)
(* against this operator, cell by cell (run `make keepalive-table`).       *)
(*                                                                         *)
(* The accept and Violation branches are [S1]: "If either side receives a  *)
(* message that is not expected according to the mini-protocol the         *)
(* communication is aborted (the connection is closed)."                   *)
(*                                                                         *)
(* UNSOURCED: the StDone branch. No source says a message after MsgDone is *)
(* ignored; it copies what gOuroboros does. Read literally, [S1] makes it  *)
(* a Violation. See "Open question" in specs/01-keepalive/README.md.       *)
(***************************************************************************)
Receive(r, s, m) ==
    IF s = "StDone"
        THEN "StDone"         \* conversation over: later messages are ignored
    ELSE IF Agency(s) = Peer(r) /\ IsLegal(s, m)
        THEN After(s, m)      \* the peer was allowed to say that: accept it
    ELSE "Violation"          \* wrong speaker or wrong message: hang up

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in
    inbox,      \* inbox[r]: messages sent to r that r has not read yet
    pings,      \* pings sent so far
    rogueLeft   \* rogue messages the misbehaving peer may still inject

vars == <<view, inbox, pings, rogueLeft>>

Init ==
    /\ view = [r \in Roles |-> "StClient"]  \* a function: like a Go map
    /\ inbox = [r \in Roles |-> <<>>]       \* <<>> is the empty sequence
    /\ pings = 0
    /\ rogueLeft = RogueMessages

\* The connection is over: both sides are done, or someone hung up.
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ /\ \A r \in Roles : view[r] = "StDone"
       /\ \A r \in Roles : inbox[r] = <<>>

\* An honest side sends a message it is allowed to send.
\* [f EXCEPT ![k] = v] is "f with key k set to v"; @ means "the old value".
Send(r, m) ==
    /\ view[r] \in States
    /\ Agency(view[r]) = r
    /\ IsLegal(view[r], m)
    /\ m = "MsgKeepAlive" => pings < MaxPings
    /\ view' = [view EXCEPT ![r] = After(view[r], m)]
    /\ inbox' = [inbox EXCEPT ![Peer(r)] = Append(@, m)]
    /\ pings' = IF m = "MsgKeepAlive" THEN pings + 1 ELSE pings
    /\ UNCHANGED rogueLeft

\* Side r reads the oldest message in its inbox and applies the receive rule.
Recv(r) ==
    /\ view[r] \in States
    /\ inbox[r] /= <<>>
    /\ view' = [view EXCEPT ![r] = Receive(r, view[r], Head(inbox[r]))]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<pings, rogueLeft>>

\* A misbehaving peer slips any message into r's inbox, at any time.
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, pings>>

\* Anything other than a timeout or an injection that could happen now.
Progress == \E r \in Roles : Recv(r) \/ \E m \in Messages : Send(r, m)

\* Side r is waiting for its peer, and nothing can ever arrive: it gives up.
\* [S2] "Timeouts per state": 97s in StClient, 60s in StServer, after which
\* "the connection SHOULD be torn down". The model has no clock, so it only
\* lets a timeout fire when waiting longer could never help.
\* ENABLED A is true when action A could happen in the current state.
Timeout(r) ==
    /\ UseTimeouts
    /\ ~Ended
    /\ ~ENABLED Progress
    /\ view[r] \in States
    /\ Agency(view[r]) = Peer(r)
    /\ view' = [view EXCEPT ![r] = "TimedOut"]
    /\ UNCHANGED <<inbox, pings, rogueLeft>>

Next ==
    \/ \E r \in Roles, m \in Messages : Send(r, m) \/ Inject(r, m)
    \/ \E r \in Roles : Recv(r) \/ Timeout(r)
    \/ Ended /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants: must hold in every reachable state. *)

TypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ pings \in 0..MaxPings
    /\ rogueLeft \in 0..RogueMessages

\* With honest peers, nobody ever hangs up or times out.
NoFailures == \A r \in Roles : view[r] \notin Failures

\* Agency means only one message is ever on the wire at a time. [S1] "At any
\* time, only one side has the agency".
OneMessageInFlight == Len(inbox["Client"]) + Len(inbox["Server"]) <= 1

\* The two sides never both believe it is their own turn to talk.
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* Once every message has been read, both sides agree on the state.
ViewsAgreeWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>>) => view["Client"] = view["Server"]

-----------------------------------------------------------------------------
(* Properties about steps rather than states. [][P]_vars means "every step *)
(* satisfies P"; view' is the value after the step.                      *)

\* THE STATES THAT CANNOT BE ENTERED: a side's state only ever moves along
\* a row of Transitions, or to a failure. No other move exists.
OnlyLegalMoves ==
    [][\A r \in Roles :
         view'[r] /= view[r] =>
             \/ view'[r] \in Failures
             \/ \E t \in Transitions : t[1] = view[r] /\ t[3] = view'[r]]_vars

\* StDone and the failures are dead ends: nothing leaves them.
EndingsAreFinal ==
    [][\A r \in Roles :
         view[r] \in {"StDone"} \cup Failures => view'[r] = view[r]]_vars

\* DELIBERATELY WRONG, used by KeepAliveRogueBug.cfg: claims a rogue message
\* can never make a side hang up. TLC shows the shortest counterexample.
NoFailuresEvenWithRogue == NoFailures
=============================================================================
