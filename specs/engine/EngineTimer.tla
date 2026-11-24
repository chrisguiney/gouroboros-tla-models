---------------------------- MODULE EngineTimer ----------------------------
(***************************************************************************)
(* Model `engine`, slice 3: when the engine arms a state's timeout.              *)
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
(* specs/keepalive/KeepAlive.tla's header.                             *)
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

\* Literally: "vars is defined as the tuple of all seven variables."
vars == <<agency, phase, inbox, sent, timer, stopped, blamed>>

\* In English: "Where an inbound transition into state agency a leaves the
\* timer."
\* Literally: "ArmAtTransition of a is defined as: in the case TimerArm equals
\*   "everyState", "armed"; in the case TimerArm equals "atTransition", if a
\*   equals "peer" then "armed", else "off"; in every other case, "off"."
ArmAtTransition(a) ==
    CASE TimerArm = "everyState"   -> "armed"
      [] TimerArm = "atTransition" -> IF a = "peer" THEN "armed" ELSE "off"
      [] OTHER                     -> "off"

\* In English: "At the start this side holds agency, recvLoop is idle, nothing
\* is queued or sent, the timer is off, and nothing has stopped or been blamed."
\* Literally: "Init is defined as: agency equals "local", and phase equals
\*   "idle", and inbox equals FALSE, and sent equals 0, and timer equals "off",
\*   and stopped equals FALSE, and blamed equals FALSE."
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
\* Literally: "LocalSend is defined as: stopped is not true, and agency equals
\*   "local", and sent is less than Msgs, and agency in the next state equals
\*   "peer", and timer in the next state equals: if TimerArm equals
\*   "afterHandler" and phase equals "handling", then "off", else "armed", and
\*   phase, inbox, sent, stopped and blamed are unchanged."
LocalSend ==
    /\ ~stopped /\ agency = "local" /\ sent < Msgs
    /\ agency' = "peer"
    /\ timer' = IF TimerArm = "afterHandler" /\ phase = "handling"
                  THEN "off" ELSE "armed"
    /\ UNCHANGED <<phase, inbox, sent, stopped, blamed>>

\* In English: "The peer, holding agency, sends its message; the read loop
\* queues it."
\* Literally: "PeerSend is defined as: stopped is not true, and agency equals
\*   "peer", and inbox is not true, and sent is less than Msgs, and inbox in the
\*   next state equals TRUE, and sent in the next state equals sent plus 1, and
\*   agency, phase, timer, stopped and blamed are unchanged."
PeerSend ==
    /\ ~stopped /\ agency = "peer" /\ ~inbox /\ sent < Msgs
    /\ inbox' = TRUE
    /\ sent' = sent + 1
    /\ UNCHANGED <<agency, phase, timer, stopped, blamed>>

\* In English: "recvLoop takes the queued message and transitions. The next
\* state may leave agency with the peer (block-fetch MsgBlock in Streaming)
\* or give it to this side. Then MessageHandlerFunc starts."
\* Literally: "RecvTransition is defined as: stopped is not true, and phase
\*   equals "idle", and inbox is true, and agency equals "peer", and there
\*   exists a next in the set containing "local" and "peer" such that agency in
\*   the next state equals next and timer in the next state equals
\*   ArmAtTransition of next, and inbox in the next state equals FALSE, and
\*   phase in the next state equals "handling", and sent, stopped and blamed are
\*   unchanged."
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
\* Literally: "HandlerDone is defined as: stopped is not true, and phase equals
\*   "handling", and phase in the next state equals "idle", and timer in the
\*   next state equals: if TimerArm equals "afterHandler" and agency equals
\*   "peer", then "armed", else timer, and agency, inbox, sent, stopped and
\*   blamed are unchanged."
HandlerDone ==
    /\ ~stopped /\ phase = "handling"
    /\ phase' = "idle"
    /\ timer' = IF TimerArm = "afterHandler" /\ agency = "peer" THEN "armed"
                                                                ELSE timer
    /\ UNCHANGED <<agency, inbox, sent, stopped, blamed>>

\* In English: "The timer fires and the protocol stops. It is this side's
\* fault, not the peer's, if this side holds agency or is still handling
\* the peer's last message."
\* Literally: "Fire is defined as: stopped is not true, and timer equals
\*   "armed", and stopped in the next state equals TRUE, and blamed in the next
\*   state equals (agency equals "local" or phase equals "handling"), and timer
\*   in the next state equals "off", and agency, phase, inbox and sent are
\*   unchanged."
Fire ==
    /\ ~stopped /\ timer = "armed"
    /\ stopped' = TRUE
    /\ blamed' = (agency = "local" \/ phase = "handling")
    /\ timer' = "off"
    /\ UNCHANGED <<agency, phase, inbox, sent>>

\* In English: "Nothing is left to do: the run is over, or stopped."
\* Literally: "Quiet is defined as: stopped is true, or (sent equals Msgs and
\*   inbox is not true and phase equals "idle"); and vars is unchanged."
Quiet ==
    /\ stopped \/ (sent = Msgs /\ ~inbox /\ phase = "idle")
    /\ UNCHANGED vars

\* In English: "A step is a local send, a peer send, a receive, a handler
\* returning, the timer firing, or nothing left to do."
\* Literally: "Next is defined as: LocalSend or PeerSend or RecvTransition or
\*   HandlerDone or Fire or Quiet."
Next ==
    \/ LocalSend \/ PeerSend \/ RecvTransition \/ HandlerDone \/ Fire
    \/ Quiet

\* In English: "Start in Init, and take only Next steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "A timeout never fires while this side holds agency or is
\* still handling the peer's message: only the peer's slowness counts."
\* Literally: "OnlyThePeerIsTimed is defined as: blamed is not true."
OnlyThePeerIsTimed == ~blamed

\* In English: "Whenever this side is only waiting for the peer, the state's
\* timer runs: the fix still times the peer."
\* Literally: "PeerWaitIsTimed is defined as: if stopped is not true and agency
\*   equals "peer" and phase equals "idle" and inbox is not true and sent is
\*   less than Msgs, then timer equals "armed"."
PeerWaitIsTimed ==
    (~stopped /\ agency = "peer" /\ phase = "idle" /\ ~inbox /\ sent < Msgs)
        => timer = "armed"

\* Probe, EXPECTED to be violated: "The timer never fires." Violated = a
\* slow peer is still timed out.
\* Literally: "ProbeTimerNeverFires is defined as: stopped is not true."
ProbeTimerNeverFires == ~stopped

\* Probe, EXPECTED to be violated: "No handler runs in a state where the peer
\* keeps agency." Violated = the case the fix is about is reached.
\* Literally: "ProbeNeverHandlingWhilePeerHasAgency is defined as: (phase equals
\*   "handling" and agency equals "peer") is not true."
ProbeNeverHandlingWhilePeerHasAgency == ~(phase = "handling" /\ agency = "peer")
=============================================================================
