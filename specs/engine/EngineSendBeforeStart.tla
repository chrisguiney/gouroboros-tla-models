------------------------ MODULE EngineSendBeforeStart ------------------------
(***************************************************************************)
(* A message sent to a gOuroboros protocol instance before, or while, it   *)
(* starts (protocol/protocol.go: New, Start, enqueueMessage, muxerDone).    *)
(*                                                                         *)
(* enqueueMessage puts the encoded message on `sendQueueChan`, which       *)
(* sendLoop drains once the instance has started, and also selects on the  *)
(* muxer's done channel `muxerDoneChan`.                                   *)
(*   main:  Start makes `sendQueueChan` and registration sets              *)
(*          `muxerDoneChan`, both under lifecycleMu, while a sender reads   *)
(*          both with no lock. A sender that runs before Start reads a nil *)
(*          queue: a send on a nil channel never proceeds, even after      *)
(*          Start makes the queue, so the sender waits until its context   *)
(*          ends and the message is never written (hazard A9). A sender    *)
(*          that runs during Start races with the writes.                  *)
(*   fix:   New makes the queue, so the field is never written after New;  *)
(*          the muxer's done channel is read under lifecycleMu.            *)
(*                                                                         *)
(* Granularity: Start's locked block is two steps (take the lock and       *)
(* write; release), the sender's read of the fields is one step, and its   *)
(* select on the queue is one step.                                        *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `sender` and `start` are program counters.                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Fixed,      \* TRUE: fix/protocol-send-before-start; FALSE: main
    WithStop    \* TRUE: the instance may be stopped as well

VARIABLES
    queue,      \* the sendQueueChan field: "nil" or "made"
    muxDone,    \* the muxerDoneChan field: "nil" or "set"
    start,      \* Start: "idle", "writing" (holds lifecycleMu), "done"
    stopped,    \* the instance was stopped
    sender,     \* "read", "select", "queued", "ctxErr", "shutdown"
    snap,       \* the queue channel the sender's select uses
    written,    \* sendLoop wrote the message
    racedRead   \* the sender read a field while Start was writing it

\* In English: "all the variables."
\* Literally: "vars is defined as the tuple of all eight variables."
vars == <<queue, muxDone, start, stopped, sender, snap, written, racedRead>>

\* In English: "Just after New: with the fix the queue exists; on main it
\* does not. The sender is about to send."
\* Literally: "Init is defined as: queue equals "made" if Fixed else "nil",
\*   muxDone equals "nil", start equals "idle", stopped is false, sender
\*   equals "read", snap equals "nil", written is false, and racedRead is
\*   false."
Init ==
    /\ queue = IF Fixed THEN "made" ELSE "nil"     \* New makes it (fix only)
    /\ muxDone = "nil"
    /\ start = "idle"
    /\ stopped = FALSE
    /\ sender = "read"
    /\ snap = "nil"
    /\ written = FALSE
    /\ racedRead = FALSE

\* In English: "Start takes lifecycleMu and writes the fields: on main it
\* makes the queue; in both it registers with the muxer, which sets the
\* muxer's done channel."
\* Literally: "StartWrite is defined as: start equals "idle", stopped is
\*   false, start becomes "writing", queue becomes "made", and muxDone
\*   becomes "set"."
StartWrite ==
    /\ start = "idle" /\ ~stopped
    /\ start' = "writing"
    /\ queue' = "made"                          \* main: p.sendQueueChan = make(...)
    /\ muxDone' = "set"                         \* ensureRegistered
    /\ UNCHANGED <<stopped, sender, snap, written, racedRead>>

\* In English: "Start releases lifecycleMu; the loops run."
\* Literally: "StartUnlock is defined as: start equals "writing", and start
\*   becomes "done"."
StartUnlock ==
    /\ start = "writing"
    /\ start' = "done"
    /\ UNCHANGED <<queue, muxDone, stopped, sender, snap, written, racedRead>>

\* In English: "The sender reads the queue and the muxer's done channel. On
\* main both reads take no lock, so a read during Start's write races. With
\* the fix the queue is never written after New, and the muxer's done
\* channel is read under lifecycleMu, so the read waits for Start's unlock."
\* Literally: "SenderRead is defined as: sender equals "read", and (not
\*   Fixed or start is not "writing"), and sender becomes "select", snap
\*   becomes queue, and racedRead becomes (not Fixed and start equals
\*   "writing")."
SenderRead ==
    /\ sender = "read"
    /\ ~Fixed \/ start # "writing"              \* fix: muxerDone() takes lifecycleMu
    /\ sender' = "select"
    /\ snap' = queue
    /\ racedRead' = (~Fixed /\ start = "writing")
    /\ UNCHANGED <<queue, muxDone, start, stopped, written>>

\* In English: "The send on the queue it read proceeds; on a nil channel it
\* never does."
\* Literally: "SenderQueue is defined as: sender equals "select", snap equals
\*   "made", and sender becomes "queued"."
SenderQueue ==
    /\ sender = "select" /\ snap = "made"
    /\ sender' = "queued"
    /\ UNCHANGED <<queue, muxDone, start, stopped, snap, written, racedRead>>

\* In English: "The sender's context ends while it waits in the select: it
\* returns the context's error and the message is dropped."
\* Literally: "SenderCtxEnds is defined as: sender equals "select", and
\*   sender becomes "ctxErr"."
SenderCtxEnds ==
    /\ sender = "select"
    /\ sender' = "ctxErr"
    /\ UNCHANGED <<queue, muxDone, start, stopped, snap, written, racedRead>>

\* In English: "The instance is stopped; a sender waiting in the select
\* returns ErrProtocolShuttingDown."
\* Literally: "Stop is defined as: WithStop, stopped is false, start is not
\*   "writing", stopped becomes true, and sender becomes "shutdown" if it
\*   was "select", else is unchanged."
Stop ==
    /\ WithStop /\ ~stopped /\ start # "writing"
    /\ stopped' = TRUE
    /\ sender' = IF sender = "select" THEN "shutdown" ELSE sender
    /\ UNCHANGED <<queue, muxDone, start, snap, written, racedRead>>

\* In English: "sendLoop, running once Start is done and until Stop, takes
\* the queued message and writes it."
\* Literally: "SendLoop is defined as: start equals "done", stopped is false,
\*   sender equals "queued", written is false, and written becomes true."
SendLoop ==
    /\ start = "done" /\ ~stopped
    /\ sender = "queued" /\ ~written
    /\ written' = TRUE
    /\ UNCHANGED <<queue, muxDone, start, stopped, sender, snap, racedRead>>

\* In English: "any step."
\* Literally: "Progress is defined as: StartWrite, or StartUnlock, or
\*   SenderRead, or SenderQueue, or SenderCtxEnds, or Stop, or SendLoop."
Progress ==
    \/ StartWrite \/ StartUnlock \/ SenderRead \/ SenderQueue
    \/ SenderCtxEnds \/ Stop \/ SendLoop

\* In English: "Once nothing can move, nothing changes."
\* Literally: "Rest is defined as: Progress is not enabled, and vars is
\*   unchanged."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is any step, or resting once none can move."
\* Literally: "Next is defined as: Progress or Rest."
Next == Progress \/ Rest

\* In English: "start in Init; every later step is a Next step."
\* Literally: "Spec is defined as: Init, and always every step is a Next step
\*   or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "no step can be taken."
\* Literally: "Quiescent is defined as: Progress is not enabled."
Quiescent == ~ENABLED Progress

\* In English: "A message sent before Start, to an instance that started
\* and was never stopped, is written, or its sender gave up only because the
\* send could have proceeded and its context ended first." The reference
\* queues a message on its channel (ouroboros-network-framework
\* `Network.Mux` egress queue) whatever moment it is sent at.
\* Literally: "SentBeforeStartIsWritten is defined as: if Quiescent and
\*   start equals "done" and stopped is false, then written is true or
\*   (sender equals "ctxErr" and snap equals "made")."
SentBeforeStartIsWritten ==
    (Quiescent /\ start = "done" /\ ~stopped) =>
        \/ written
        \/ sender = "ctxErr" /\ snap = "made"

\* In English: "The sender never reads a field while Start is writing it."
\* Literally: "NoRacingRead is defined as: racedRead is false."
NoRacingRead == ~racedRead

\* In English: "Each variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: queue is "nil" or "made", muxDone is
\*   "nil" or "set", start is "idle", "writing" or "done", and stopped,
\*   written and racedRead are booleans."
TypeOK ==
    /\ queue \in {"nil", "made"} /\ muxDone \in {"nil", "set"}
    /\ start \in {"idle", "writing", "done"}
    /\ stopped \in BOOLEAN /\ written \in BOOLEAN /\ racedRead \in BOOLEAN
=============================================================================
