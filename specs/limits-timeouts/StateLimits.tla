----------------------------- MODULE StateLimits -----------------------------
(***************************************************************************)
(* Model `limits-timeouts`: which side a state's timer runs on, what it is *)
(* set to, and what a message over a state's byte limit does, for one side *)
(* of one mini-protocol (LimitsTables.tla) against an abstract peer.       *)
(*                                                                         *)
(* What the code does (gOuroboros 7cd17437, protocol/protocol.go):         *)
(*   stateLoop's setState arms the entered state's Timeout only when the   *)
(*   peer holds agency there, never in the initial state (Protocol-        *)
(*   Config.InitialStateTimeout is unset for every protocol here), and not *)
(*   while recvLoop runs MessageHandlerFunc; when the handler returns,     *)
(*   stateLoop arms the current state's timer if the peer holds agency.    *)
(*   The read loop refuses a message larger than the active state's        *)
(*   PendingMessageByteLimit with ErrProtocolViolationQueueExceeded, which *)
(*   ends the protocol. This is EngineTimer.tla's "afterHandler" rule      *)
(*   (specs/engine), applied to each protocol's table.                     *)
(*                                                                         *)
(* The rule [S1][R0]: a state's time limit bounds only how long the side   *)
(* without agency waits; the reference's byte limit bounds each message    *)
(* the side receives in that state. Sources are listed in LimitsTables.tla *)
(* and README.md.                                                          *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex *)
(*   [R0] typed-protocols 8fa4ed2f5bfe Network/TypedProtocol/Driver.hs and *)
(*        ouroboros-network runPeerWithLimits.                             *)
(*                                                                         *)
(* Time is not modelled: an armed timer may fire at any step. The timer    *)
(* variable holds the duration armed, so the tables' values are checked.   *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Integers, LimitsTables

CONSTANTS
    Msgs,      \* how many messages the peer sends (keeps the model finite)
    \* Where the engine arms a timer:
    \*   "afterHandler" gOuroboros 7cd17437 (EngineTimer.tla's fix).
    \*   "everyState"   a mutation: on entering any state with a timeout.
    TimerArm,
    \* What the read loop does with a message over the state's limit:
    \*   "refuse" gOuroboros 7cd17437: the protocol ends with an error.
    \*   "wait"   a mutation: it is held, as a PendingReceiveByteBudget
    \*            holds a message until the queue drains, but nothing drains.
    \*   "accept" a mutation: the limit is not checked.
    OverLimit,
    \* Recorded differences from the reference that are not defects, per
    \* side (DRIFT.md rows). A state listed here is skipped by the
    \* invariant named.
    TimeoutDeviations,  \* skipped by TimedAsReference
    LimitDeviations     \* skipped by NoLooserThanReference

ASSUME Side \in Sides
ASSUME TimerArm \in {"afterHandler", "everyState"}
ASSUME OverLimit \in {"refuse", "wait", "accept"}

VARIABLES
    st,        \* the state this side is in
    phase,     \* recvLoop: "idle" or "handling" (MessageHandlerFunc runs)
    inbox,     \* size in bytes of the peer's queued message; 0 = none
    sent,      \* how many messages the peer has sent
    timer,     \* the duration armed, in seconds; 0 = no timer
    left,      \* this side has left its initial state
    outcome,   \* "run", "done", "refused", "timedOut", "cancelled"
    silent,    \* the peer has stopped sending for good
    accSize,   \* size of the last message accepted; 0 = none yet
    accIn,     \* the state it was accepted in
    blamed     \* the timer fired while this side was not waiting

vars == <<st, phase, inbox, sent, timer, left, outcome, silent, accSize,
          accIn, blamed>>

\* In English: "The sizes the peer may send in state s: one byte, each limit,
\* and one byte past each limit."
Sizes(s) ==
    {1} \cup {x \in {GoLimit(s), GoLimit(s) + 1, RefLimit(s),
                     RefLimit(s) + 1} : x > 0}

\* In English: "The timer the engine arms on entering state s (handling:
\* whether a handler is running). With afterHandler: only if the peer holds
\* agency, no handler runs, and s is not the initial state's first entry."
Arm(s, handling, first) ==
    IF first THEN 0
    ELSE CASE TimerArm = "everyState" -> GoTimeout(s)
           [] OTHER -> IF Agency(s) = "peer" /\ ~handling
                         THEN GoTimeout(s) ELSE 0

\* In English: "The run starts in the initial state, nothing queued or sent,
\* no timer (the initial state is never timed)."
Init ==
    /\ st = InitState
    /\ phase = "idle"
    /\ inbox = 0
    /\ sent = 0
    /\ timer = 0
    /\ left = FALSE
    /\ outcome = "run"
    /\ silent = FALSE
    /\ accSize = 0
    /\ accIn = InitState
    /\ blamed = FALSE

Running == outcome = "run"

\* In English: "This side, holding agency, sends a message (from a caller or
\* from inside a handler) and enters the next state."
LocalSend ==
    /\ Running /\ Agency(st) = "local"
    /\ \E s \in NextStates(st) :
          /\ st' = s                                    \* the new state
          /\ timer' = Arm(s, phase = "handling", FALSE) \* armed or not
          /\ outcome' = IF Agency(s) = "none" THEN "done" ELSE "run"
    /\ left' = TRUE
    /\ UNCHANGED <<phase, inbox, sent, silent, accSize, accIn, blamed>>

\* In English: "The peer, holding agency, sends a message of some size."
PeerSend ==
    /\ Running /\ Agency(st) = "peer" /\ inbox = 0 /\ ~silent /\ sent < Msgs
    /\ \E n \in Sizes(st) : inbox' = n                  \* queued
    /\ sent' = sent + 1
    /\ UNCHANGED <<st, phase, timer, left, outcome, silent, accSize, accIn,
                   blamed>>

\* In English: "The peer stops sending for good (a slow, stuck or hostile
\* peer)."
PeerGoesSilent ==
    /\ Running /\ ~silent
    /\ silent' = TRUE
    /\ UNCHANGED <<st, phase, inbox, sent, timer, left, outcome, accSize,
                   accIn, blamed>>

\* In English: "The message is over the state's limit."
Over(n, s) == GoLimit(s) > 0 /\ n > GoLimit(s)

\* In English: "The read loop refuses an over-limit message: the protocol
\* ends with an error."
Refuse ==
    /\ Running /\ phase = "idle" /\ inbox > 0
    /\ OverLimit = "refuse" /\ Over(inbox, st)
    /\ outcome' = "refused"                             \* protocol error
    /\ timer' = 0
    /\ UNCHANGED <<st, phase, inbox, sent, left, silent, accSize, accIn,
                   blamed>>

\* In English: "recvLoop takes a message within the limit (or any message,
\* in the accept mutation), transitions, and starts the handler."
Recv ==
    /\ Running /\ phase = "idle" /\ inbox > 0
    /\ OverLimit = "accept" \/ ~Over(inbox, st)
    /\ \E s \in NextStates(st) :
          /\ st' = s
          /\ timer' = Arm(s, TRUE, FALSE)
          /\ outcome' = IF Agency(s) = "none" THEN "done" ELSE "run"
    /\ accSize' = inbox                                 \* accepted
    /\ accIn' = st
    /\ inbox' = 0
    /\ phase' = "handling"
    /\ left' = TRUE
    /\ UNCHANGED <<sent, silent, blamed>>

\* In English: "The handler returns; stateLoop arms the current state's timer
\* if the peer holds agency and none is armed."
HandlerDone ==
    /\ Running /\ phase = "handling"
    /\ phase' = "idle"
    /\ timer' = IF TimerArm = "afterHandler" /\ timer = 0
                   /\ Agency(st) = "peer"
                  THEN GoTimeout(st) ELSE timer
    /\ UNCHANGED <<st, inbox, sent, left, outcome, silent, accSize, accIn,
                   blamed>>

\* In English: "The timer fires and the protocol ends. It is this side's
\* fault if it holds agency or is still handling the peer's last message."
Fire ==
    /\ Running /\ timer > 0
    /\ outcome' = "timedOut"
    /\ blamed' = (Agency(st) = "local" \/ phase = "handling")
    /\ timer' = 0
    /\ UNCHANGED <<st, phase, inbox, sent, left, silent, accSize, accIn>>

\* In English: "LeiosFetch only: the caller's context ends while it waits for
\* a block or block transactions reply; the request fails."
CallerCancel ==
    /\ Running /\ CtxBound(st) /\ phase = "idle"
    /\ outcome' = "cancelled"
    /\ UNCHANGED <<st, phase, inbox, sent, timer, left, silent, accSize,
                   accIn, blamed>>

\* In English: "Nothing is left to do: the run ended, the peer sent all it
\* will, or this side legitimately waits forever for a silent peer."
Quiet ==
    /\ \/ ~Running
       \/ phase = "idle" /\ inbox = 0 /\ Agency(st) = "peer"
          /\ (silent \/ sent = Msgs)
       \/ phase = "idle" /\ Agency(st) = "local" /\ sent = Msgs
    /\ UNCHANGED vars

Next ==
    \/ LocalSend \/ PeerSend \/ PeerGoesSilent \/ Refuse \/ Recv
    \/ HandlerDone \/ Fire \/ CallerCancel \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "A timer never fires while this side holds agency or is still
\* handling the peer's message." (EngineTimer.tla OnlyThePeerIsTimed)
OnlyThePeerIsTimed == ~blamed

\* In English: "An armed timer is never in a state where this side holds
\* agency."
TimerOnlyWhileWaiting == timer > 0 => Agency(st) = "peer"

\* In English: "No message over the state's limit is ever handled."
NeverAcceptsOverLimit == accSize > 0 => ~Over(accSize, accIn)

\* In English: "No message the reference would refuse in that state is
\* handled, except where a difference is recorded."
NoLooserThanReference ==
    (accSize > 0 /\ RefLimit(accIn) > 0 /\ accIn \notin LimitDeviations)
        => accSize <= RefLimit(accIn)

\* In English: "Where the reference bounds this side's wait for the peer,
\* gOuroboros bounds it too: a timer runs, or the caller's context does."
WaitIsBounded ==
    (Running /\ Agency(st) = "peer" /\ phase = "idle" /\ inbox = 0 /\ left
     /\ RefTimeout(st) > 0)
        => (timer > 0 \/ CtxBound(st))

\* In English: "An armed timer has the reference's duration, unless the
\* reference has no row for the state or a difference is recorded. A
\* reference waitForever (0) means no timer at all."
TimedAsReference ==
    (timer > 0 /\ RefTimeout(st) >= 0 /\ st \notin TimeoutDeviations)
        => timer = RefTimeout(st)

\* In English: "Where a caller passed a timeout option for a wait on this
\* side, that wait is timed with the caller's value."
OptionsTakeEffect ==
    (OptionValue > 0 /\ st \in OptionIntent /\ Running /\ left
     /\ Agency(st) = "peer" /\ phase = "idle")
        => timer = OptionValue

\* Probe, EXPECTED to be violated where a state is timed: "No timer fires."
ProbeTimerNeverFires == outcome # "timedOut"

\* Probe, EXPECTED to be violated where a state has a limit: "No message is
\* refused."
ProbeNeverRefused == outcome # "refused"
=============================================================================
