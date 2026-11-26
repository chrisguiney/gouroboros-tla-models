------------------------- MODULE EngineSendDrained -------------------------
(***************************************************************************)
(* Protocol.WaitSendQueueDrained (protocol/protocol.go 804-833 at          *)
(* gOuroboros 7cd17437) against the send path it watches. Dingo's          *)
(* block-fetch server calls it between blocks to pace its sends.           *)
(*                                                                         *)
(* A message passes through these stages:                                  *)
(*   [G1] enqueueMessage 1032-1105: add its bytes to pendingSendBytes      *)
(*        under pendingBytesMu, then send it on sendQueueChan;             *)
(*   [G2] sendLoop 1540-1632: receive it, append it to the loop's payload  *)
(*        buffer and subtract its bytes from pendingSendBytes;            *)
(*   [G3] sendLoop 1666-1707: hand the segment to the muxer's per-protocol *)
(*        channel;                                                         *)
(*   [G4] muxer 1292-1320: the protocol's sender goroutine writes it to   *)
(*        the bearer, which blocks while the peer does not read, then      *)
(*        reports delivery.                                                *)
(* The waiter polls every 2 ms: shutdown (stopChan, doneChan) means "not   *)
(* drained"; pendingSendBytes = 0 and an empty sendQueueChan mean          *)
(* "drained"; past the deadline, "not drained".                            *)
(*                                                                         *)
(* Defect (Fixed = FALSE): pendingSendBytes drops at [G2], before the      *)
(* bytes reach the bearer, so the waiter reports drained while the last    *)
(* message is still in the payload buffer, in the muxer's channel, or in a *)
(* write the bearer is blocking.                                           *)
(* Fix (Fixed = TRUE): [G2] moves the bytes to an unwritten count in the   *)
(* same critical section, the muxer's report of a successful write at [G4] *)
(* subtracts them, and the waiter also requires the unwritten count to be *)
(* zero. A failed or abandoned write (the protocol unregistered on Stop)  *)
(* subtracts nothing: counting it would let a waiter that passed the      *)
(* shutdown check just before Stop answer drained for bytes never written *)
(* (the counterexample TLC finds when Report also covers abandoned        *)
(* segments).                                                              *)
(*                                                                         *)
(* Message counts stand for byte counts. A segment carries every message  *)
(* moved into the buffer so far. Not modelled: the enqueue rollback after  *)
(* shutdown (the waiter already answers "not drained" then); pipelined     *)
(* messages held for agency (their bytes stay in pendingSendBytes).        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    N,          \* messages the application sends
    Fixed,      \* TRUE: the fix; FALSE: gOuroboros 7cd17437
    Mutation    \* "None"; "ReportOnHandoff": the fix's unwritten count
                \* drops when the segment is handed to the muxer;
                \* "CountFailed": it also drops for a segment the muxer
                \* abandons on Stop

ASSUME Mutation \in {"None", "ReportOnHandoff", "CountFailed"}

VARIABLES
    enq,       \* messages counted in pendingSendBytes so far [G1]
    pushed,    \* messages sent on sendQueueChan
    deq,       \* messages sendLoop received
    moved,     \* messages appended to the buffer, bytes subtracted [G2]
    handed,    \* messages handed to the muxer [G3]
    written,   \* messages the bearer has taken [G4]
    reported,  \* messages whose delivery was reported (the fix's count)
    blocked,   \* the bearer blocks writes (the peer does not read)
    stopped,   \* the instance is stopping
    wpc,       \* the waiter: "idle", "stopchk", "readPending", "readQueue",
               \*   "returned"
    owed,      \* messages counted before the waiter was called
    seenZero,  \* the waiter's read of the byte counts found them zero
    result     \* what the waiter returned

vars == <<enq, pushed, deq, moved, handed, written, reported, blocked,
          stopped, wpc, owed, seenZero, result>>

\* In English: "pendingSendBytes, the send queue's length, and the fix's
\* unwritten count."
Pending == enq - moved
QueueLen == pushed - deq
Unwritten == moved - reported

Init ==
    /\ enq = 0 /\ pushed = 0 /\ deq = 0 /\ moved = 0 /\ handed = 0
    /\ written = 0 /\ reported = 0
    /\ blocked \in BOOLEAN
    /\ stopped = FALSE
    /\ wpc = "idle" /\ owed = 0 /\ seenZero = FALSE /\ result = FALSE

\* In English: "[G1] the sender counts a message's bytes, then queues it."
Count ==
    /\ enq < N /\ enq = pushed
    /\ enq' = enq + 1
    /\ UNCHANGED <<pushed, deq, moved, handed, written, reported, blocked,
                   stopped, wpc, owed, seenZero, result>>

Push ==
    /\ pushed < enq /\ ~stopped
    /\ pushed' = pushed + 1
    /\ UNCHANGED <<enq, deq, moved, handed, written, reported, blocked,
                   stopped, wpc, owed, seenZero, result>>

\* In English: "[G2] sendLoop receives a message, then appends it to its
\* buffer and subtracts its bytes."
Dequeue ==
    /\ deq < pushed /\ ~stopped
    /\ deq' = deq + 1
    /\ UNCHANGED <<enq, pushed, moved, handed, written, reported, blocked,
                   stopped, wpc, owed, seenZero, result>>

Move ==
    /\ moved < deq
    /\ moved' = moved + 1
    /\ UNCHANGED <<enq, pushed, deq, handed, written, reported, blocked,
                   stopped, wpc, owed, seenZero, result>>

\* In English: "[G3] sendLoop hands the buffer to the muxer as a segment.
\* Under ReportOnHandoff the unwritten count drops here."
Handoff ==
    /\ handed < moved /\ ~stopped
    /\ handed' = moved
    /\ reported' = IF Mutation = "ReportOnHandoff" THEN moved ELSE reported
    /\ UNCHANGED <<enq, pushed, deq, moved, written, blocked, stopped, wpc,
                   owed, seenZero, result>>

\* In English: "[G4] the muxer writes the segment once the bearer takes it,
\* then reports delivery."
Write ==
    /\ written < handed /\ ~blocked /\ ~stopped
    /\ written' = handed
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, reported, blocked,
                   stopped, wpc, owed, seenZero, result>>

Report ==
    /\ reported < written
    /\ reported' = written
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, blocked,
                   stopped, wpc, owed, seenZero, result>>

\* In English: "Under CountFailed, the muxer's failure report for a segment
\* abandoned on Stop subtracts its bytes too."
Abandon ==
    /\ Mutation = "CountFailed" /\ stopped /\ reported < handed
    /\ reported' = handed
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, blocked,
                   stopped, wpc, owed, seenZero, result>>

Unblock ==
    /\ blocked
    /\ blocked' = FALSE
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   stopped, wpc, owed, seenZero, result>>

Stop ==
    /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   blocked, wpc, owed, seenZero, result>>

\* In English: "The application calls WaitSendQueueDrained once; it owes
\* every message already counted."
Call ==
    /\ wpc = "idle"
    /\ wpc' = "stopchk"
    /\ owed' = enq
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   blocked, stopped, seenZero, result>>

\* In English: "The waiter's poll: a shutdown returns not drained; then
\* the counts under pendingBytesMu; then the queue's length."
StopCheck ==
    /\ wpc = "stopchk"
    /\ IF stopped
         THEN /\ wpc' = "returned" /\ result' = FALSE
         ELSE /\ wpc' = "readPending" /\ result' = result
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   blocked, stopped, owed, seenZero>>

ReadPending ==
    /\ wpc = "readPending"
    /\ seenZero' = (Pending = 0 /\ (~Fixed \/ Unwritten = 0))
    /\ wpc' = "readQueue"
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   blocked, stopped, owed, result>>

\* In English: "Drained when both reads found zero; otherwise sleep and
\* poll again, or, past the deadline, return not drained."
ReadQueue ==
    /\ wpc = "readQueue"
    /\ IF seenZero /\ QueueLen = 0
         THEN /\ wpc' = "returned" /\ result' = TRUE
         ELSE /\ wpc' = "stopchk" /\ result' = result
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   blocked, stopped, owed, seenZero>>

Timeout ==
    /\ wpc = "readQueue" /\ ~(seenZero /\ QueueLen = 0)
    /\ wpc' = "returned" /\ result' = FALSE
    /\ UNCHANGED <<enq, pushed, deq, moved, handed, written, reported,
                   blocked, stopped, owed, seenZero>>

Waiter == StopCheck \/ ReadPending \/ ReadQueue

Next ==
    \/ Count \/ Push \/ Dequeue \/ Move \/ Handoff \/ Write \/ Report
    \/ Abandon \/ Unblock \/ Stop \/ Call \/ Waiter \/ Timeout

\* The send path and the waiter make progress; the peer, Stop and the
\* deadline are not assumed to.
Spec == Init /\ [][Next]_vars
        /\ WF_vars(Waiter) /\ WF_vars(Dequeue) /\ WF_vars(Move)
        /\ WF_vars(Handoff) /\ WF_vars(Report) /\ WF_vars(Push)

TypeOK ==
    /\ reported <= moved /\ written <= handed /\ handed <= moved
    /\ moved <= deq /\ deq <= pushed /\ pushed <= enq /\ enq <= N

\* In English: "A drained answer means every message counted before the
\* call has been written to the bearer."
\* Literally: "DrainedMeansWritten is defined as: if wpc is "returned" and
\*   result is true, then written is at least owed."
DrainedMeansWritten == (wpc = "returned" /\ result) => written >= owed

\* In English: "Once the instance stops, a waiting call returns."
ReturnsAfterStop == (stopped /\ wpc \notin {"idle"}) ~> (wpc = "returned")

\* In English: "Probe: the waiter can answer drained. Violated (as
\* expected) in every configuration where the peer reads."
ProbeNeverDrained == ~(wpc = "returned" /\ result)
=============================================================================
