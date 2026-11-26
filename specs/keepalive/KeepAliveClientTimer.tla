------------------------ MODULE KeepAliveClientTimer ------------------------
(***************************************************************************)
(* The gOuroboros keep-alive CLIENT's ping timer, at the level of its      *)
(* goroutines and of an abstract clock. KeepAlive.tla says which messages  *)
(* may follow which; EngineTimer.tla says which side a state's time limit  *)
(* times. This module checks the client's own timer                        *)
(* (protocol/keepalive/client.go, gOuroboros 7cd17437):                    *)
(*                                                                         *)
(*   cb       sendKeepAlive, run once by Start and then by each            *)
(*            time.AfterFunc callback: under cookieMutex, skip the ping if *)
(*            one is in flight, else mark it in flight; SendMessage, which *)
(*            fails once the protocol is stopping; startTimer: an unlocked *)
(*            IsStopping check, then under timerMutex a second check and   *)
(*            AfterFunc(Period, sendKeepAlive).                             *)
(*   stopper  Client.Stop: Protocol.Stop as a signal, then under           *)
(*            timerMutex timer.Stop and timer = nil, then the join of the  *)
(*            protocol's loops. Or the connection's shutdown, which only   *)
(*            calls Protocol.Stop on the client's instance and joins its   *)
(*            loops through the muxer (connection.go stopProtocols).       *)
(*   watcher  the goroutine Start leaves behind: <-DoneChan, then under    *)
(*            timerMutex timer.Stop.                                       *)
(*   recv     the protocol's receive loop running the response handler:    *)
(*            under cookieMutex, a response whose cookie is the expected   *)
(*            one clears inFlight and moves to the next cookie; any other  *)
(*            cookie is a protocol error, which stops the protocol.        *)
(*   peer     the server: answers the ping with its cookie (honest), with  *)
(*            another cookie (rogue), or never (silent).                    *)
(*                                                                         *)
(* Time. `now` counts abstract units; a Tick moves it on only when nothing *)
(* is due at the current instant, and the callback's own steps take no     *)
(* time. A timer armed at t fires at t + Period. The server's limit on the *)
(* client's next ping [S2] (97 s, ClientTimeout) starts when it answers,   *)
(* since the server does not time the initial state; the client's limit on *)
(* the answer (StServer, config.Timeout) starts when the ping is sent      *)
(* (EngineTimer.tla: the engine times only the side without agency).       *)
(* Durations are small integers that keep their order: PeerLimit stands    *)
(* for 97 s, Period and Timeout for the configured values.                 *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S2] ouroboros-network 5f356486ab3e docs/network-spec/               *)
(*        miniprotocols.tex 1560-1650: keep-alive states and time limits   *)
(*        (97 s in StClient, 60 s in StServer).                           *)
(*   [G]  gOuroboros 7cd17437 protocol/keepalive/client.go (Start,         *)
(*        sendKeepAlive, startTimer, Stop, handleKeepAliveResponse),       *)
(*        keepalive.go (NewConfig defaults, StateMap), protocol/protocol.go *)
(*        (enqueueMessage refuses once stopChan is closed; armTimeout arms *)
(*        nothing for a zero Timeout).                                     *)
(*   UNSOURCED: a zero or negative Period or Timeout. Neither the          *)
(*        specification nor the reference has an unset duration; the       *)
(*        reference's keepAliveInterval and timeLimitsKeepAlive are always *)
(*        positive. The model asks what gOuroboros does with one.          *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Period,           \* config.Period, in time units; 0 is a zero Config
    Timeout,          \* config.Timeout, in time units; 0 is a zero Config
    DefaultPeriod,    \* NewConfig's Period (60 s)
    DefaultTimeout,   \* NewConfig's Timeout (10 s)
    PeerLimit,        \* the server's limit on the next ping (97 s) [S2]
    MaxTime,          \* the clock stops here (keeps the model finite)
    PeerKinds,        \* how the server may behave, a subset of
                      \* {"honest", "rogue", "silent"}
    StopKind,         \* who stops the client: "client" (Client.Stop),
                      \* "connection" (shutdown's Protocol.Stop), "none"
    Fix,              \* a subset of {"defaultPeriod", "defaultTimeout"}:
                      \* "defaultPeriod": NewClient uses DefaultPeriod for a
                      \*   Period that is not positive;
                      \* "defaultTimeout": NewClient uses DefaultTimeout for
                      \*   a Timeout that is not positive.
    Mutation          \* a subset of {"clearFirst", "noInFlightGuard"}:
                      \* "clearFirst": Client.Stop clears the timer before
                      \*   it signals (the order before the A11 fix);
                      \* "noInFlightGuard": sendKeepAlive pings even with a
                      \*   ping in flight.

ASSUME Fix \subseteq {"defaultPeriod", "defaultTimeout"}
ASSUME Mutation \subseteq {"clearFirst", "noInFlightGuard"}
ASSUME StopKind \in {"client", "connection", "none"}
ASSUME PeerKinds \subseteq {"honest", "rogue", "silent"} /\ PeerKinds # {}

\* In English: "The period the timer uses: the configured one, or the
\* default when the fix applies to a period that is not positive."
\* Literally: "EffPeriod is defined as: if "defaultPeriod" is in Fix and
\*   Period equals 0, then DefaultPeriod, else Period."
EffPeriod == IF "defaultPeriod" \in Fix /\ Period = 0 THEN DefaultPeriod ELSE Period

\* In English: "The time limit on the server's answer: the configured one,
\* or the default when the fix applies; 0 arms no timer (armTimeout)."
\* Literally: "EffTimeout is defined as: if "defaultTimeout" is in Fix and
\*   Timeout equals 0, then DefaultTimeout, else Timeout."
EffTimeout == IF "defaultTimeout" \in Fix /\ Timeout = 0 THEN DefaultTimeout ELSE Timeout

VARIABLES
    now,          \* the abstract clock
    timerArmed,   \* an AfterFunc timer is pending
    timerAt,      \* when it fires
    cb,           \* sendKeepAlive's next step: "idle", "check", "send",
                  \*   "fast" (unlocked check), "lock" (locked check and arm)
    inFlight,     \* c.inFlight
    onWire,       \* pings sent and not yet answered
    sentAt,       \* when the last ping was sent
    peer,         \* the server's behaviour, chosen at the start
    peerWaiting,  \* the server answered and waits for the next ping
    peerSince,    \* when it answered
    peerTimedOut, \* the server's limit passed with no ping: it hangs up
    stopped,      \* the protocol is stopping (stopChan closed)
    loopsDone,    \* the protocol's loops have returned (DoneChan closed)
    stopper,      \* the stopper's next step: "idle", "signal", "clear",
                  \*   "join", "done"
    watcher,      \* the DoneChan watcher: "wait" or "done"
    firesNow,     \* timer fires at the current instant
    firesAfterStop, \* timer fires once the stopper has returned
    sentAfterStop   \* a ping went out once the stopper had returned

vars == <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt, peer,
          peerWaiting, peerSince, peerTimedOut, stopped, loopsDone, stopper,
          watcher, firesNow, firesAfterStop, sentAfterStop>>

\* In English: "The first step of the stopper: the connection's shutdown
\* only signals; Client.Stop signals first, or clears first under the
\* clearFirst mutation."
FirstStopStep == IF StopKind = "connection" THEN "signal"
                 ELSE IF "clearFirst" \in Mutation THEN "clear" ELSE "signal"

\* In English: "At the start Start has just called sendKeepAlive: no ping is
\* in flight, no timer is armed, the server may be any of PeerKinds."
\* Literally: "Init is defined as: now equals 0, and timerArmed is false, and
\*   timerAt equals 0, and cb equals "check", and inFlight is false, and onWire
\*   equals 0, and sentAt equals 0, and peer is one of PeerKinds, and the
\*   server waits for nothing, and nothing is stopped, and the stopper is
\*   idle, and the watcher waits, and every counter is 0 or false."
Init ==
    /\ now = 0
    /\ timerArmed = FALSE /\ timerAt = 0
    /\ cb = "check"                 \* Start calls sendKeepAlive directly
    /\ inFlight = FALSE
    /\ onWire = 0 /\ sentAt = 0
    /\ peer \in PeerKinds           \* TLC tries every behaviour
    /\ peerWaiting = FALSE /\ peerSince = 0 /\ peerTimedOut = FALSE
    /\ stopped = FALSE /\ loopsDone = FALSE
    /\ stopper = "idle"
    /\ watcher = "wait"
    /\ firesNow = 0
    /\ firesAfterStop = 0
    /\ sentAfterStop = FALSE

-----------------------------------------------------------------------------
(* sendKeepAlive, one locked block or call per step [G]. *)

\* In English: "Under cookieMutex: with a ping in flight, skip to
\* startTimer; otherwise mark one in flight and go on to send it."
CbCheck ==
    /\ cb = "check"
    /\ IF inFlight /\ "noInFlightGuard" \notin Mutation
          THEN /\ cb' = "fast"                  \* skip the ping
               /\ UNCHANGED inFlight
          ELSE /\ cb' = "send"
               /\ inFlight' = TRUE              \* c.inFlight = true
    /\ UNCHANGED <<now, timerArmed, timerAt, onWire, sentAt, peer, peerWaiting,
                   peerSince, peerTimedOut, stopped, loopsDone, stopper,
                   watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "SendMessage: once the protocol is stopping it fails, and
\* the ping is no longer in flight; otherwise the ping goes out, the server
\* stops waiting, and the engine starts timing the answer."
CbSend ==
    /\ cb = "send"
    /\ cb' = "fast"
    /\ IF stopped \/ loopsDone
          THEN /\ inFlight' = FALSE             \* ErrProtocolShuttingDown
               /\ UNCHANGED <<onWire, sentAt, peerWaiting, sentAfterStop>>
          ELSE /\ onWire' = onWire + 1          \* the ping is on the wire
               /\ sentAt' = now
               /\ peerWaiting' = FALSE          \* the server got its ping
               /\ sentAfterStop' = (sentAfterStop \/ stopper = "done")
               /\ UNCHANGED inFlight
    /\ UNCHANGED <<now, timerArmed, timerAt, peer, peerSince, peerTimedOut,
                   stopped, loopsDone, stopper, watcher, firesNow,
                   firesAfterStop>>

\* In English: "startTimer's unlocked check: a stopping protocol arms
\* nothing."
CbFast ==
    /\ cb = "fast"
    /\ cb' = IF stopped THEN "idle" ELSE "lock"
    /\ UNCHANGED <<now, timerArmed, timerAt, inFlight, onWire, sentAt, peer,
                   peerWaiting, peerSince, peerTimedOut, stopped, loopsDone,
                   stopper, watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "Under timerMutex: check again, then stop the old timer and
\* arm a new one Period from now. The callback then returns."
CbLock ==
    /\ cb = "lock"
    /\ cb' = "idle"
    /\ IF stopped
          THEN UNCHANGED <<timerArmed, timerAt>>
          ELSE /\ timerArmed' = TRUE            \* time.AfterFunc(Period, ...)
               /\ timerAt' = now + EffPeriod
    /\ UNCHANGED <<now, inFlight, onWire, sentAt, peer, peerWaiting, peerSince,
                   peerTimedOut, stopped, loopsDone, stopper, watcher, firesNow,
                   firesAfterStop, sentAfterStop>>

\* In English: "The timer fires at its time and runs sendKeepAlive on a new
\* goroutine. (A callback arms the next timer as its last step, so one
\* callback runs at a time.)"
Fire ==
    /\ timerArmed /\ timerAt = now /\ cb = "idle"
    /\ timerArmed' = FALSE
    /\ cb' = "check"
    /\ firesNow' = firesNow + 1
    /\ firesAfterStop' = IF stopper = "done" THEN firesAfterStop + 1
                                             ELSE firesAfterStop
    /\ UNCHANGED <<now, timerAt, inFlight, onWire, sentAt, peer, peerWaiting,
                   peerSince, peerTimedOut, stopped, loopsDone, stopper,
                   watcher, sentAfterStop>>

-----------------------------------------------------------------------------
(* The server and the response handler. *)

\* In English: "An honest server answers the ping with its cookie; the
\* handler, under cookieMutex, clears inFlight. The server then waits for
\* the next ping, timed from now."
PeerAnswers ==
    /\ peer = "honest" /\ onWire > 0 /\ ~stopped
    /\ onWire' = onWire - 1
    /\ inFlight' = FALSE                        \* cookie matched
    /\ peerWaiting' = TRUE
    /\ peerSince' = now
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, sentAt, peer, peerTimedOut,
                   stopped, loopsDone, stopper, watcher, firesNow,
                   firesAfterStop, sentAfterStop>>

\* In English: "A rogue server answers with another cookie: the handler
\* returns an error and the protocol stops."
PeerRogue ==
    /\ peer = "rogue" /\ onWire > 0 /\ ~stopped
    /\ onWire' = onWire - 1
    /\ stopped' = TRUE                          \* SendError stops it
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, sentAt, peer,
                   peerWaiting, peerSince, peerTimedOut, loopsDone, stopper,
                   watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "The server's limit on the next ping passes: it hangs up."
PeerLimitPasses ==
    /\ peerWaiting /\ ~stopped /\ ~peerTimedOut
    /\ now >= peerSince + PeerLimit
    /\ peerTimedOut' = TRUE
    /\ stopped' = TRUE                          \* the connection goes down
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt,
                   peer, peerWaiting, peerSince, loopsDone, stopper, watcher,
                   firesNow, firesAfterStop, sentAfterStop>>

\* In English: "The client's limit on the answer passes (only with a
\* positive Timeout): the engine fails the protocol."
ClientLimitPasses ==
    /\ onWire > 0 /\ ~stopped /\ EffTimeout > 0
    /\ now >= sentAt + EffTimeout
    /\ stopped' = TRUE
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt,
                   peer, peerWaiting, peerSince, peerTimedOut, loopsDone,
                   stopper, watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

-----------------------------------------------------------------------------
(* Stopping. *)

\* In English: "Someone begins to stop the client."
StopBegin ==
    /\ StopKind # "none" /\ stopper = "idle"
    /\ stopper' = FirstStopStep
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt,
                   peer, peerWaiting, peerSince, peerTimedOut, stopped,
                   loopsDone, watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "Protocol.Stop as a signal: stopChan closes."
StopSignal ==
    /\ stopper = "signal"
    /\ stopped' = TRUE
    /\ stopper' = IF StopKind = "connection" THEN "join"
                  ELSE IF "clearFirst" \in Mutation THEN "join" ELSE "clear"
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt,
                   peer, peerWaiting, peerSince, peerTimedOut, loopsDone,
                   watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "Client.Stop, under timerMutex: timer.Stop and timer = nil."
StopClear ==
    /\ stopper = "clear"
    /\ timerArmed' = FALSE
    /\ stopper' = IF "clearFirst" \in Mutation THEN "signal" ELSE "join"
    /\ UNCHANGED <<now, timerAt, cb, inFlight, onWire, sentAt, peer,
                   peerWaiting, peerSince, peerTimedOut, stopped, loopsDone,
                   watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "The join: the protocol's loops have returned. The timer
\* callback is not one of them."
StopJoin ==
    /\ stopper = "join" /\ loopsDone
    /\ stopper' = "done"
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt,
                   peer, peerWaiting, peerSince, peerTimedOut, stopped,
                   loopsDone, watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "A stopping protocol's loops return and DoneChan closes."
LoopsExit ==
    /\ stopped /\ ~loopsDone
    /\ loopsDone' = TRUE
    /\ UNCHANGED <<now, timerArmed, timerAt, cb, inFlight, onWire, sentAt,
                   peer, peerWaiting, peerSince, peerTimedOut, stopped,
                   stopper, watcher, firesNow, firesAfterStop,
                   sentAfterStop>>

\* In English: "The watcher sees DoneChan closed and, under timerMutex,
\* stops the timer."
WatcherStops ==
    /\ watcher = "wait" /\ loopsDone
    /\ watcher' = "done"
    /\ timerArmed' = FALSE
    /\ UNCHANGED <<now, timerAt, cb, inFlight, onWire, sentAt, peer,
                   peerWaiting, peerSince, peerTimedOut, stopped, loopsDone,
                   stopper, firesNow, firesAfterStop,
                   sentAfterStop>>

-----------------------------------------------------------------------------
(* The clock. *)

\* In English: "Something must happen at this instant: a timer or a limit
\* that is due, or a callback still running."
Due ==
    \/ cb # "idle"
    \/ timerArmed /\ timerAt <= now
    \/ peerWaiting /\ ~stopped /\ ~peerTimedOut /\ now >= peerSince + PeerLimit
    \/ onWire > 0 /\ ~stopped /\ EffTimeout > 0 /\ now >= sentAt + EffTimeout

\* In English: "Time moves on by one unit when nothing is due now."
Tick ==
    /\ now < MaxTime /\ ~Due
    /\ now' = now + 1
    /\ firesNow' = 0
    /\ UNCHANGED <<timerArmed, timerAt, cb, inFlight, onWire, sentAt, peer,
                   peerWaiting, peerSince, peerTimedOut, stopped, loopsDone,
                   stopper, watcher, firesAfterStop,
                   sentAfterStop>>

\* In English: "The clock has run out, or everything has stopped."
Quiet ==
    /\ (now = MaxTime \/ (stopped /\ loopsDone /\ watcher = "done"))
    /\ UNCHANGED vars

Next ==
    \/ CbCheck \/ CbSend \/ CbFast \/ CbLock \/ Fire
    \/ PeerAnswers \/ PeerRogue \/ PeerLimitPasses \/ ClientLimitPasses
    \/ StopBegin \/ StopSignal \/ StopClear \/ StopJoin \/ LoopsExit
    \/ WatcherStops \/ Tick \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every variable holds a value of the right kind."
TypeOK ==
    /\ now \in 0..MaxTime
    /\ timerArmed \in BOOLEAN /\ timerAt \in Nat
    /\ cb \in {"idle", "check", "send", "fast", "lock"}
    /\ inFlight \in BOOLEAN /\ onWire \in Nat
    /\ stopper \in {"idle", "signal", "clear", "join", "done"}
    /\ watcher \in {"wait", "done"}

\* In English: "At most one ping is ever unanswered (the cookie rule [S2]
\* needs the client to wait for the answer before the next ping)."
AtMostOneInFlight == onWire <= 1

\* In English: "The timer fires at most once at any instant: every fire is
\* separated from the next by time passing."
FiresBounded == firesNow <= 1

\* In English: "A client that keeps answering pings is never hung up on
\* by the server for being silent."
PeerNeverTimesOut == ~peerTimedOut

\* In English: "An unanswered ping is noticed: once its time limit has
\* passed (DefaultTimeout when none is set), the protocol is stopping. A
\* client that never times the answer fails this."
SilentPeerNoticed ==
    LET limit == IF EffTimeout > 0 THEN EffTimeout ELSE DefaultTimeout
    IN (onWire > 0 /\ now > sentAt + limit) => stopped

\* In English: "Once Client.Stop has returned no timer is armed."
StopLeavesNoTimer == (StopKind = "client" /\ stopper = "done") => ~timerArmed

\* In English: "No ping goes out after the stopper has returned."
NoSendAfterStop == ~sentAfterStop

\* In English: "After the stopper has returned, the timer fires at most
\* once more (the connection's shutdown leaves the timer to the watcher,
\* which it does not join)."
ExtraFiresAfterStopAtMostOne == firesAfterStop <= 1

\* In English: "Once everything has stopped, no timer is left armed."
NoTimerWhenQuiescent ==
    (stopped /\ loopsDone /\ watcher = "done" /\ cb = "idle") => ~timerArmed
=============================================================================
