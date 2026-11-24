---------------------------- MODULE EngineTimer ----------------------------
(***************************************************************************)
(* Model 03, slice 3: when the engine arms a state's timeout.              *)
(*                                                                         *)
(* What the code does (protocol/protocol.go):                              *)
(*   stateLoop's setState arms a timer for the state just entered, if it   *)
(*   has a Timeout. recvLoop takes the next queued message, asks stateLoop *)
(*   to transition (transitionInboundState), and only then runs the        *)
(*   protocol's MessageHandlerFunc (BlockFunc, RollForwardFunc, ...). A    *)
(*   message this side sends goes through transitionState from sendLoop.   *)
(*   When the timer fires, the protocol fails with "timeout waiting on     *)
(*   transition".                                                          *)
(*                                                                         *)
(* The rule [S1][R1]: a state's time limit bounds how long the side       *)
(* without agency waits for the peer's message. The reference applies it  *)
(* only around recvMessage, so neither the time this side holds agency    *)
(* nor the time its own code spends on a received message counts.         *)
(*                                                                         *)
(* Sources (README has links):                                             *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/               *)
(*        miniprotocols.tex: time limits are how long the receiver waits. *)
(*   [R1] typed-protocols 8fa4ed2f5bfe Network/TypedProtocol/Driver.hs    *)
(*        and ouroboros-network runPeerWithLimits: the timeout wraps      *)
(*        recvMessage only.                                                *)
(*   [G] gOuroboros: stateLoop setState (the timer), recvLoop (transition *)
(*       then MessageHandlerFunc), requestStateTransition.                *)
(*                                                                         *)
(* One side is modelled, with an abstract peer. Time is not modelled: the *)
(* timer may fire at any step while armed, which covers a handler or a    *)
(* peer of any speed. Symbols are explained in                            *)
(* specs/01-keepalive/KeepAlive.tla's header.                             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Msgs,      \* how many messages the peer sends (keeps the model finite)
    \* Where the engine arms a state's timer:
    \*   "everyState"   gOuroboros d0b95845: on entering any state with a
    \*                  timeout, including one where this side has agency.
    \*   "atTransition" PR #3159 at c0a5ca9c: only when the peer has agency,
    \*                  but at the inbound transition, before the handler.
    \*   "afterHandler" the fix: while MessageHandlerFunc runs, no
    \*                  transition arms a timer, whether inbound or sent by
    \*                  the handler; when it returns, recvLoop tells
    \*                  stateLoop, which arms the timer of the state current
    \*                  then if the peer has agency in it.
    \*   "never"        a mutation that arms no timer after a handler.
    TimerArm

ASSUME TimerArm \in {"everyState", "atTransition", "afterHandler", "never"}

VARIABLES
    agency,    \* who holds agency in the current state: "local" or "peer"
    phase,     \* recvLoop: "idle" (waiting for a message) or "handling"
               \* (MessageHandlerFunc runs)
    inbox,     \* the peer's message is queued and not yet handled
    sent,      \* how many messages the peer has sent
    timer,     \* "off" or "armed"
    stopped,   \* the timer fired and the protocol stopped
    blamed     \* the timer fired while this side, not the peer, was busy

vars == <<agency, phase, inbox, sent, timer, stopped, blamed>>

\* In English: "Where an inbound transition into state agency a leaves the
\* timer."
ArmAtTransition(a) ==
    CASE TimerArm = "everyState"   -> "armed"
      [] TimerArm = "atTransition" -> IF a = "peer" THEN "armed" ELSE "off"
      [] OTHER                     -> "off"

Init ==
    /\ agency = "local"          \* this side starts with agency
    /\ phase = "idle"
    /\ inbox = FALSE
    /\ sent = 0
    /\ timer = "off"
    /\ stopped = FALSE
    /\ blamed = FALSE

\* In English: "This side sends a message that hands agency to the peer
\* (transitionState from sendLoop). It may do so from inside a handler.
\* This side now waits for the peer, so the timer is armed, except with the
\* fix while a handler runs: recvLoop cannot take the peer's answer until
\* the handler returns."
LocalSend ==
    /\ ~stopped /\ agency = "local" /\ sent < Msgs
    /\ agency' = "peer"
    /\ timer' = IF TimerArm = "afterHandler" /\ phase = "handling"
                  THEN "off" ELSE "armed"
    /\ UNCHANGED <<phase, inbox, sent, stopped, blamed>>

\* In English: "The peer, holding agency, sends its message; the read loop
\* queues it."
PeerSend ==
    /\ ~stopped /\ agency = "peer" /\ ~inbox /\ sent < Msgs
    /\ inbox' = TRUE
    /\ sent' = sent + 1
    /\ UNCHANGED <<agency, phase, timer, stopped, blamed>>

\* In English: "recvLoop takes the queued message and transitions. The next
\* state may leave agency with the peer (block-fetch MsgBlock in Streaming)
\* or give it to this side. Then MessageHandlerFunc starts."
RecvTransition ==
    /\ ~stopped /\ phase = "idle" /\ inbox /\ agency = "peer"
    /\ \E next \in {"local", "peer"} :
          /\ agency' = next
          /\ timer' = ArmAtTransition(next)
    /\ inbox' = FALSE
    /\ phase' = "handling"
    /\ UNCHANGED <<sent, stopped, blamed>>

\* In English: "MessageHandlerFunc returns. With the fix, recvLoop tells
\* stateLoop, which arms the current state's timer if the peer has agency."
HandlerDone ==
    /\ ~stopped /\ phase = "handling"
    /\ phase' = "idle"
    /\ timer' = IF TimerArm = "afterHandler" /\ agency = "peer" THEN "armed"
                                                                ELSE timer
    /\ UNCHANGED <<agency, inbox, sent, stopped, blamed>>

\* In English: "The timer fires and the protocol stops. It is this side's
\* fault, not the peer's, if this side holds agency or is still handling
\* the peer's last message."
Fire ==
    /\ ~stopped /\ timer = "armed"
    /\ stopped' = TRUE
    /\ blamed' = (agency = "local" \/ phase = "handling")
    /\ timer' = "off"
    /\ UNCHANGED <<agency, phase, inbox, sent>>

\* In English: "Nothing is left to do: the run is over, or stopped."
Quiet ==
    /\ stopped \/ (sent = Msgs /\ ~inbox /\ phase = "idle")
    /\ UNCHANGED vars

Next ==
    \/ LocalSend \/ PeerSend \/ RecvTransition \/ HandlerDone \/ Fire
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "A timeout never fires while this side holds agency or is
\* still handling the peer's message: only the peer's slowness counts."
OnlyThePeerIsTimed == ~blamed

\* In English: "Whenever this side is only waiting for the peer, the state's
\* timer runs: the fix still times the peer."
PeerWaitIsTimed ==
    (~stopped /\ agency = "peer" /\ phase = "idle" /\ ~inbox /\ sent < Msgs)
        => timer = "armed"

\* Probe, EXPECTED to be violated: "The timer never fires." Violated = a
\* slow peer is still timed out.
ProbeTimerNeverFires == ~stopped

\* Probe, EXPECTED to be violated: "No handler runs in a state where the peer
\* keeps agency." Violated = the case the fix is about is reached.
ProbeNeverHandlingWhilePeerHasAgency == ~(phase = "handling" /\ agency = "peer")
=============================================================================
