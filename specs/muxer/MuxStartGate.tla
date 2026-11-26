---------------------------- MODULE MuxStartGate ----------------------------
(***************************************************************************)
(* The muxer's start gate (muxer/muxer.go: Start, StartOnce, readLoop).    *)
(*                                                                         *)
(* New starts the read loop at once, but it reads nothing until the gate   *)
(* opens. StartOnce admits one segment (the handshake reply); Start admits *)
(* every segment from then on. The gate is not part of the reference mux,  *)
(* which runs the handshake before it starts the mux that carries the      *)
(* other mini-protocols [R1]; it is gOuroboros's way of running the        *)
(* handshake on the same muxer.                                            *)
(*   main:  startChan has one slot, and Start and StartOnce both make a    *)
(*          non-blocking send into it (true and false). A Start called     *)
(*          while StartOnce's false is still in the slot is dropped: the   *)
(*          read loop takes the false, reads one segment and waits at the  *)
(*          gate until Stop.                                               *)
(*   fix:   Start closes a channel of its own, once, and the gate selects  *)
(*          on it as well as on the one-slot StartOnce channel.            *)
(*                                                                         *)
(* Writes are not gated: Send never looks at the gate, so the handshake    *)
(* client can write its proposal before any read. WriteBeforeGateProbeBug *)
(* shows that this is reachable, as it should be.                          *)
(*                                                                         *)
(* Granularity: each Start or StartOnce call is one step; the read loop's  *)
(* gate select is one step, and reading one segment is one step.           *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `loop` is the read loop's program counter.                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Fixed,      \* TRUE: Start closes its own channel; FALSE: main
    MaxOnce,    \* how many times the user may call StartOnce
    MaxReads,   \* how many segments the peer sends
    GateSkipped \* mutation: the read loop reads without passing the gate

VARIABLES
    slot,       \* startChan's one slot: "empty", "once" or "start"
    started,    \* Fixed only: Start has closed its channel
    onceCalls,  \* StartOnce calls so far
    startCalls, \* Start calls so far (0 or 1 is enough)
    stopped,    \* doneChan is closed
    loop,       \* "gate", "read" (one admitted segment), "reading" (Start seen), "exited"
    reads,      \* segments the read loop has read
    writes      \* segments the user has written with Send

\* In English: "all the variables."
vars == <<slot, started, onceCalls, startCalls, stopped, loop, reads, writes>>

\* In English: "Just after New: nothing called, the read loop waits at the
\* gate."
\* Literally: "Init is defined as: slot is "empty", started is false, the
\*   call counts, reads and writes are 0, stopped is false, and loop is
\*   "gate"."
Init ==
    /\ slot = "empty" /\ started = FALSE
    /\ onceCalls = 0 /\ startCalls = 0
    /\ stopped = FALSE
    /\ loop = "gate"
    /\ reads = 0 /\ writes = 0

\* In English: "StartOnce sends a token into the slot if it is empty, and
\* otherwise does nothing."
\* Literally: "StartOnce is defined as: onceCalls is below MaxOnce, onceCalls
\*   goes up by one, and slot becomes "once" if it was "empty", else is
\*   unchanged."
StartOnce ==
    /\ onceCalls < MaxOnce
    /\ onceCalls' = onceCalls + 1
    /\ slot' = IF slot = "empty" THEN "once" ELSE slot   \* select { case startChan <- ...: default: }
    /\ UNCHANGED <<started, startCalls, stopped, loop, reads, writes>>

\* In English: "Start: on main it sends true into the slot if the slot is
\* empty and is dropped otherwise; with the fix it closes its own channel."
\* Literally: "Start is defined as: startCalls is 0, startCalls becomes 1,
\*   and if Fixed then started becomes true and slot is unchanged, else
\*   slot becomes "start" if it was "empty", else is unchanged."
Start ==
    /\ startCalls = 0
    /\ startCalls' = 1
    /\ IF Fixed
         THEN started' = TRUE /\ UNCHANGED slot          \* onceStart.Do(close(startedChan))
         ELSE slot' = (IF slot = "empty" THEN "start" ELSE slot) /\ UNCHANGED started
    /\ UNCHANGED <<onceCalls, stopped, loop, reads, writes>>

\* In English: "Stop closes doneChan."
\* Literally: "Stop is defined as: stopped is false and becomes true."
Stop ==
    /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED <<slot, started, onceCalls, startCalls, loop, reads, writes>>

\* In English: "The user's protocol writes a segment. Send checks only
\* doneChan."
\* Literally: "Write is defined as: stopped is false, writes is below
\*   MaxReads, and writes goes up by one."
Write ==
    /\ ~stopped /\ writes < MaxReads
    /\ writes' = writes + 1
    /\ UNCHANGED <<slot, started, onceCalls, startCalls, stopped, loop, reads>>

\* In English: "At the gate the read loop takes whichever case of its select
\* is ready: doneChan ends it, Start's closed channel (fix) or a true token
\* (main) lets it read from then on, and a StartOnce token lets it read one
\* segment."
\* Literally: "Gate is defined as: loop is "gate", and either stopped and
\*   loop becomes "exited"; or Fixed, started, and loop becomes "reading";
\*   or slot is "start", slot becomes "empty" and loop becomes "reading";
\*   or slot is "once", slot becomes "empty" and loop becomes "read"; or
\*   GateSkipped and loop becomes "read"."
Gate ==
    /\ loop = "gate"
    /\ \/ stopped /\ loop' = "exited" /\ UNCHANGED <<slot>>
       \/ Fixed /\ started /\ loop' = "reading" /\ UNCHANGED <<slot>>
       \/ slot = "start" /\ slot' = "empty" /\ loop' = "reading"
       \/ slot = "once" /\ slot' = "empty" /\ loop' = "read"
       \/ GateSkipped /\ loop' = "read" /\ UNCHANGED <<slot>>
    /\ UNCHANGED <<started, onceCalls, startCalls, stopped, reads, writes>>

\* In English: "Admitted for one segment, the read loop reads it (or ends,
\* if stopped) and goes back to the gate."
\* Literally: "ReadOne is defined as: loop is "read", and if stopped then
\*   loop becomes "exited", else reads is below MaxReads, reads goes up by
\*   one and loop becomes "gate"."
ReadOne ==
    /\ loop = "read"
    /\ IF stopped
         THEN loop' = "exited" /\ UNCHANGED reads
         ELSE reads < MaxReads /\ reads' = reads + 1 /\ loop' = "gate"
    /\ UNCHANGED <<slot, started, onceCalls, startCalls, stopped, writes>>

\* In English: "Started, the read loop reads every segment the peer sends,
\* until stopped."
\* Literally: "ReadOn is defined as: loop is "reading", and if stopped then
\*   loop becomes "exited", else reads is below MaxReads and goes up by one."
ReadOn ==
    /\ loop = "reading"
    /\ IF stopped
         THEN loop' = "exited" /\ UNCHANGED reads
         ELSE reads < MaxReads /\ reads' = reads + 1 /\ UNCHANGED loop
    /\ UNCHANGED <<slot, started, onceCalls, startCalls, stopped, writes>>

\* In English: "any step."
Progress ==
    \/ StartOnce \/ Start \/ Stop \/ Write \/ Gate \/ ReadOne \/ ReadOn

\* In English: "Once nothing can move, nothing changes."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is any step, or resting once none can move."
Next == Progress \/ Rest

\* In English: "start in Init; every later step is a Next step."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "no step can be taken."
Quiescent == ~ENABLED Progress

\* In English: "Before Start, the read loop has read at most one segment
\* per StartOnce call."
\* Literally: "NoReadBeforeGate is defined as: if startCalls is 0 then reads
\*   is at most onceCalls."
NoReadBeforeGate == startCalls = 0 => reads <= onceCalls

\* In English: "Once Start has been called and the muxer is still running,
\* the gate never holds the read loop again: whenever the read loop is at
\* the gate, it can pass it." This is what Start promises its caller. A
\* safety form: a later StartOnce could rescue a read loop stuck at the gate,
\* so a "nothing can move" form would not catch the drop.
\* Literally: "StartIsSticky is defined as: if startCalls is 1, stopped is
\*   false and loop is "gate", then the Gate step is enabled."
StartIsSticky ==
    (startCalls = 1 /\ ~stopped /\ loop = "gate") => ENABLED Gate

\* In English: "Once stopped and nothing can move, the read loop has ended,
\* whether or not the gate was ever opened."
\* Literally: "StoppedAtGate is defined as: if Quiescent and stopped, then
\*   loop is "exited"."
StoppedAtGate == (Quiescent /\ stopped) => loop = "exited"

\* In English: "Probe: nothing is written before the gate first opens."
\* Expected to be violated: Send is not gated, by design.
NoWriteBeforeGate == (onceCalls = 0 /\ startCalls = 0) => writes = 0

\* In English: "each variable holds the kind of value it should."
TypeOK ==
    /\ slot \in {"empty", "once", "start"}
    /\ started \in BOOLEAN /\ stopped \in BOOLEAN
    /\ onceCalls \in 0..MaxOnce /\ startCalls \in 0..1
    /\ loop \in {"gate", "read", "reading", "exited"}
    /\ reads \in 0..MaxReads /\ writes \in 0..MaxReads
=============================================================================
