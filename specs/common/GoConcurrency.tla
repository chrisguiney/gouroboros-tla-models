---------------------------- MODULE GoConcurrency ----------------------------
(***************************************************************************)
(* Go's concurrency primitives, as values a spec keeps in its own          *)
(* variables. Every operator returns the next value of a primitive, so a   *)
(* spec writes ch' = Send(ch, m) or mu' = Lock(mu, "sd"), and every spec   *)
(* that EXTENDS or INSTANCEs this module names the same object the same    *)
(* way. Each goroutine stays a process of the spec that uses the module:   *)
(* the module only says when a step on a primitive is enabled and what it  *)
(* leaves behind.                                                          *)
(*                                                                         *)
(* Semantics follow the Go memory model and the runtime                    *)
(* (https://go.dev/ref/spec#Channel_types, #Send_statements,               *)
(* #Receive_operator, #Select_statements; package sync; time.Timer.Stop):  *)
(*   - a send on a buffered channel blocks while the buffer is full; an    *)
(*     unbuffered channel (capacity 0) is a rendezvous, which a spec       *)
(*     writes as one step taken by both goroutines (Rendezvous);           *)
(*   - a receive blocks while the channel is empty and open; on a closed,  *)
(*     empty channel it returns the zero value at once (ok = FALSE);       *)
(*   - a send on a closed channel and a close of a closed channel panic.   *)
(*     A spec makes these reachable error states (SendPanics, ClosePanics) *)
(*     and checks an invariant that they never happen;                     *)
(*   - a select picks any enabled case; its default case is enabled        *)
(*     exactly when no other case is (DefaultEnabled);                     *)
(*   - a channel closed to wake every waiter ("broadcast") and replaced is *)
(*     a generation counter: a waiter that read generation g is woken by   *)
(*     any later close (Woken);                                            *)
(*   - Mutex, RWMutex (writer preference), WaitGroup, Once and Timer as    *)
(*     below.                                                              *)
(*                                                                         *)
(* How to read the symbols: see specs/keepalive/KeepAlive.tla's header.   *)
(* The record syntax [buf |-> ...] builds a record, r.buf reads a field,   *)
(* and [r EXCEPT !.buf = e] is r with one field replaced                   *)
(* (Specifying Systems, section 5.2; docs/glossary.md "record").           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

-----------------------------------------------------------------------------
(* Channels *)

\* In English: "A new, empty, open channel that holds at most cap values."
Chan(cap) == [buf |-> <<>>, cap |-> cap, closed |-> FALSE]

\* In English: "A send on c can complete now: c is open and its buffer has
\* room. (A send on a closed channel is enabled too, but it panics: see
\* SendPanics.)"
CanSend(c) == ~c.closed /\ Len(c.buf) < c.cap

\* In English: "A send on c at this moment would panic: c is closed."
SendPanics(c) == c.closed

\* In English: "c after m is appended to its buffer."
Send(c, m) == [c EXCEPT !.buf = Append(@, m)]

\* In English: "A receive on c can complete now: c holds a value, or c is
\* closed (and the receive yields the zero value)."
CanRecv(c) == Len(c.buf) > 0 \/ c.closed

\* In English: "The receive's ok result: TRUE when a value was taken, FALSE
\* when the channel was closed and empty."
RecvOk(c) == Len(c.buf) > 0

\* In English: "The value a receive on c yields: the oldest buffered value,
\* or zero when c is closed and empty."
RecvVal(c, zero) == IF Len(c.buf) > 0 THEN Head(c.buf) ELSE zero

\* In English: "c after a receive: the oldest value is gone (a receive on a
\* closed, empty channel changes nothing)."
Recv(c) == IF Len(c.buf) > 0 THEN [c EXCEPT !.buf = Tail(@)] ELSE c

\* In English: "c after close(c). Values still buffered can be received."
Close(c) == [c EXCEPT !.closed = TRUE]

\* In English: "close(c) at this moment would panic: c is already closed."
ClosePanics(c) == c.closed

\* In English: "How many values c holds (Go's len(c))."
ChanLen(c) == Len(c.buf)

\* In English: "An unbuffered send and receive meet: both goroutines are at
\* their step and the channel is open. The spec moves both in one step."
Rendezvous(c, senderReady, receiverReady) ==
    c.cap = 0 /\ ~c.closed /\ senderReady /\ receiverReady

\* In English: "A select's default case is enabled exactly when none of its
\* other cases is. cases is the set of the other cases' enabling conditions,
\* each a Boolean."
DefaultEnabled(cases) == \A e \in cases : ~e

-----------------------------------------------------------------------------
(* A chan struct{} that is only ever closed, to signal: a Boolean.         *)
(* Receiving from it is enabled once it is TRUE. Closing it twice panics,  *)
(* so a spec closes it with SignalClose and checks SignalClosePanics.      *)

\* In English: "close(s) on a signal channel s: it is now closed."
SignalClose(s) == TRUE

\* In English: "close(s) at this moment would panic."
SignalClosePanics(s) == s

-----------------------------------------------------------------------------
(* Broadcast: a channel closed and replaced under a lock to wake every     *)
(* waiter. A waiter reads the current generation, unlocks, then waits on   *)
(* the channel it read: two steps, so a close between them is a wakeup    *)
(* the waiter still sees, and a waiter that reads after the close waits    *)
(* for the next one.                                                       *)

\* In English: "Close the current channel and make a new one."
Bump(gen) == gen + 1

\* In English: "A waiter that read generation g has been woken."
Woken(gen, g) == gen > g

-----------------------------------------------------------------------------
(* sync.Mutex: the holder, or Free. Lock is enabled only when it is free;  *)
(* Go mutexes are not reentrant, so a holder that locks again blocks for   *)
(* ever, which TLC reports as a deadlock.                                  *)

Free == "free"

\* In English: "g may take mu now: nobody holds it."
CanLock(mu) == mu = Free

\* In English: "mu after g takes it."
Lock(mu, g) == g

\* In English: "mu after its holder releases it."
Unlock(mu) == Free

\* In English: "TryLock: TRUE and taken if free, FALSE and unchanged if not."
TryLock(mu, g) == IF mu = Free THEN g ELSE mu

-----------------------------------------------------------------------------
(* sync.RWMutex with writer preference: a reader cannot join while a      *)
(* writer waits, so a reader that re-locks for reading while a writer      *)
(* waits deadlocks (the sync documentation forbids recursive read locks).  *)

RW == [w |-> Free, r |-> {}, wantW |-> {}]

\* In English: "Reader g may take rw now: no writer holds or waits for it."
CanRLock(rw) == rw.w = Free /\ rw.wantW = {}

RLock(rw, g) == [rw EXCEPT !.r = @ \cup {g}]

RUnlock(rw, g) == [rw EXCEPT !.r = @ \ {g}]

\* In English: "Writer g announces it waits; readers that come later block."
WantLock(rw, g) == [rw EXCEPT !.wantW = @ \cup {g}]

\* In English: "Writer g may take rw now: it announced itself, and nobody
\* holds rw."
CanWLock(rw, g) == g \in rw.wantW /\ rw.w = Free /\ rw.r = {}

WLock(rw, g) == [rw EXCEPT !.w = g, !.wantW = @ \ {g}]

WUnlock(rw) == [rw EXCEPT !.w = Free]

-----------------------------------------------------------------------------
(* sync.WaitGroup: a counter. Wait is enabled at zero. An Add from zero   *)
(* must happen before the Wait it is meant to delay (sync documentation); *)
(* a spec records a late Add as an error state with AddAfterWait.          *)

\* In English: "Wait may return now: the counter is zero."
CanWait(wg) == wg = 0

WgAdd(wg, n) == wg + n

\* In English: "Done: the counter drops by one. Below zero Go panics; a
\* spec checks wg >= 0 as an invariant by keeping the counter in Nat."
WgDone(wg) == wg - 1

\* In English: "An Add from zero while a Wait may already have returned:
\* the Add is not ordered before the Wait, so nothing joins the goroutine."
AddAfterWait(wg, waitReturned) == wg = 0 /\ waitReturned

-----------------------------------------------------------------------------
(* sync.Once: "idle", "running" (the first caller runs the function; a    *)
(* second caller blocks until it returns) or "done".                       *)

OnceIdle == "idle"
OnceRunning == "running"
OnceDone == "done"

-----------------------------------------------------------------------------
(* time.Timer and time.AfterFunc: "idle", "armed", "fired" or "stopped". *)
(* An armed timer fires at any moment (wall-clock time is not modelled).   *)
(* Stop reports TRUE only if it prevented the fire; it does not wait for   *)
(* an AfterFunc callback already running, which is a goroutine of its own. *)

TimerIdle == "idle"
TimerArmed == "armed"
TimerFired == "fired"
TimerStopped == "stopped"

\* In English: "The timer may fire now."
CanFire(t) == t = TimerArmed

\* In English: "What t.Stop() returns: TRUE if it stopped an armed timer."
StopPrevents(t) == t = TimerArmed

\* In English: "t after t.Stop()."
StopTimer(t) == IF t = TimerArmed THEN TimerStopped ELSE t

=============================================================================
