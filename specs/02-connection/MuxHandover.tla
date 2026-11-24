---------------------------- MODULE MuxHandover ----------------------------
(***************************************************************************)
(* Model 02, part 1: does every message reach the right server instance    *)
(* when a mini-protocol restarts in the middle of a byte stream?           *)
(*                                                                         *)
(* A client sends keep-alive messages through the multiplexer. Messages    *)
(* travel as bytes, cut into segments that may split a message or carry    *)
(* parts of two. When the client sends MsgDone, the gOuroboros server      *)
(* stops that instance and starts a new one, while more bytes keep         *)
(* arriving. The property: every message the client sends is processed    *)
(* exactly once, in the order it was sent, across any number of restarts.  *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e:            *)
(*   [M1] docs/network-spec/mux.tex 36-58: the bearer delivers a           *)
(*        mini-protocol's segments in order and reliably; the mux          *)
(*        reassembles each mini-protocol's byte stream, so a mini-protocol *)
(*        is written "as if it would only communicate with its instance on *)
(*        the remote end".                                                 *)
(*   [M2] docs/network-spec/mux.tex 113-121: the mux may split a message   *)
(*        across segments or merge several into one segment.               *)
(*   [S4] network-mux/src/Network/Mux.hs 362-378: a finished run's unread  *)
(*        bytes are kept for the next run.                                 *)
(*   [S7] docs/network-spec/connection-manager.tex 489-503: a server that  *)
(*        terminates cleanly is restarted in its initial state.            *)
(*   [S8] IntersectMBO/typed-protocols 8fa4ed2f, Driver.hs 145-176: "one   *)
(*        protocols to be run after another on the same channel"; the      *)
(*        first message of the next run may share a chunk with the last    *)
(*        message of the previous one.                                     *)
(*                                                                         *)
(* The gOuroboros code it follows (all read, not guessed):                 *)
(*   protocol/protocol.go readLoop - takes a segment off the muxer channel *)
(*     and appends it to readBuffer in one step; admits one message at a   *)
(*     time while the peer has agency (reserveInboundAdmission); a server  *)
(*     stops reading at the first message after Done, leaving it in       *)
(*     readBuffer (carryOnExit); on a restart, readBuffer becomes          *)
(*     carriedIngress.                                                     *)
(*   protocol/protocol.go stop(restart) - waits for readLoop to finish,    *)
(*     then SuspendProtocol with carriedIngress.                           *)
(*   muxer/muxer.go - a suspended receiver keeps its queue and channel;    *)
(*     RegisterProtocol resumes it; TakeCarriedIngress hands the carried   *)
(*     bytes to the new instance, whose readLoop consumes them first       *)
(*     (handoverIngress).                                                  *)
(*   protocol/keepalive/server.go handleDone - StopForRestart, then a new  *)
(*     instance, then Start.                                               *)
(*                                                                         *)
(* Not modelled: Stop and connection shutdown (KeepAliveLifecycle.tla has *)
(* them), byte-size limits, timeouts, and the server-to-client direction,  *)
(* which is shortened to a single step.                                    *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxPings,           \* how many pings the client may send in total
    MaxRuns,            \* how many runs the client may start
    CarryReadBuffer,    \* TRUE (gOuroboros): unprocessed bytes go to the next instance
    AdmitOneAtATime,    \* TRUE (gOuroboros): a message waits until the last one is handled
    ResumeReceiver      \* TRUE (gOuroboros): the new instance gets the old receiver back

\* The protocol, as in KeepAlive.tla.
Agency(s) == CASE s = "StClient" -> "Client"
             []   s = "StServer" -> "Server"
             []   s = "StDone"   -> "Nobody"

\* In English: "The state after message type t in state s."
After(s, t) ==
    CASE s = "StClient" /\ t = "MsgKeepAlive"         -> "StServer"
    []   s = "StClient" /\ t = "MsgDone"              -> "StDone"
    []   s = "StServer" /\ t = "MsgKeepAliveResponse" -> "StClient"

\* A message is two bytes on the wire, so a segment can end halfway through
\* one [M2]. In English: "Bytes(id, t) is the two bytes of message id, of
\* type t: part 1, then part 2."
Bytes(id, t) == << [id |-> id, type |-> t, part |-> 1],
                   [id |-> id, type |-> t, part |-> 2] >>

\* In English: "buf starts with a whole message: its first byte is part 1
\* and its second byte is part 2 of the same message."
StartsWithMessage(buf) ==
    /\ Len(buf) >= 2
    /\ buf[1].part = 1
    /\ buf[2].id = buf[1].id

\* In English: "Drop the first n bytes of buf."
Drop(buf, n) == SubSeq(buf, n + 1, Len(buf))

VARIABLES
    \* --- the client ---
    cview,      \* the state the client believes the protocol is in
    pings,      \* pings sent so far
    runs,       \* client runs started so far
    nextId,     \* the number the next message gets
    out,        \* bytes the client has sent but not yet cut into segments
    sent,       \* every message id, in the order the client sent it
    \* --- the muxer ---
    rx,         \* segments waiting in the server's receiver, oldest first
    \* --- the current server instance ---
    ps,         \* the state the server instance believes the protocol is in
    rb,         \* its readBuffer: bytes read from the muxer, not yet parsed
    reading,    \* TRUE while its readLoop runs
    rq,         \* messages its readLoop admitted, for its recvLoop to handle
    reserved,   \* TRUE while an admitted message is waiting to be handled
    \* --- the restart ---
    restart,    \* the restart's next step: "idle", "stop", "suspend", "start"
    stopping,   \* TRUE once StopForRestart has asked the readLoop to stop
    carry,      \* bytes the old instance hands to the new one
    \* --- what the server processed ---
    delivered,  \* every message id the server's recvLoops handled, in order
    violation   \* TRUE if a server instance refused a message

vars == <<cview, pings, runs, nextId, out, sent, rx, ps, rb, reading, rq,
          reserved, restart, stopping, carry, delivered, violation>>

\* In English: "At the start, client and server are in StClient, nothing has
\* been sent, and the server instance is reading."
Init ==
    /\ cview = "StClient"
    /\ pings = 0
    /\ runs = 1
    /\ nextId = 1
    /\ out = <<>>
    /\ sent = <<>>
    /\ rx = <<>>
    /\ ps = "StClient"
    /\ rb = <<>>
    /\ reading = TRUE
    /\ rq = <<>>
    /\ reserved = FALSE
    /\ restart = "idle"
    /\ stopping = FALSE
    /\ carry = <<>>
    /\ delivered = <<>>
    /\ violation = FALSE

serverVars == <<ps, rb, reading, rq, reserved, restart, stopping, carry,
                delivered, violation>>

-----------------------------------------------------------------------------
(* The client. It follows the protocol, as an honest peer does. *)

\* In English: "When the client may send and has pings left, it sends a ping:
\* its two bytes go out, it remembers the id, and it waits for the server."
ClientPing ==
    /\ cview = "StClient"                       \* the client may send
    /\ pings < MaxPings                         \* and has pings left
    /\ out' = out \o Bytes(nextId, "MsgKeepAlive")  \* next, the ping's bytes are queued
    /\ sent' = Append(sent, nextId)             \* next, the ping is recorded as sent
    /\ nextId' = nextId + 1
    /\ pings' = pings + 1
    /\ cview' = "StServer"                      \* next, it waits for the server
    /\ UNCHANGED <<runs, rx>> /\ UNCHANGED serverVars

\* In English: "When the client may send, it sends done and its run ends."
ClientDone ==
    /\ cview = "StClient"
    /\ out' = out \o Bytes(nextId, "MsgDone")
    /\ sent' = Append(sent, nextId)
    /\ nextId' = nextId + 1
    /\ cview' = "StDone"
    /\ UNCHANGED <<pings, runs, rx>> /\ UNCHANGED serverVars

\* In English: "When the client's run is over and it may start another, it
\* starts one at once" - without waiting for the server, so the new run's
\* bytes can follow the old run's MsgDone in the same stream [S8].
ClientRestart ==
    /\ cview = "StDone"
    /\ runs < MaxRuns
    /\ cview' = "StClient"
    /\ runs' = runs + 1
    /\ UNCHANGED <<pings, nextId, out, sent, rx>> /\ UNCHANGED serverVars

\* In English: "The client's mux cuts the next 1 or 2 bytes into a segment
\* and the bearer delivers it, in order, to the server's receiver" [M1][M2].
SendSegment(n) ==
    /\ Len(out) >= n
    /\ rx' = Append(rx, SubSeq(out, 1, n))      \* next, a segment of n bytes is waiting
    /\ out' = Drop(out, n)                      \* next, those bytes have left the client
    /\ UNCHANGED <<cview, pings, runs, nextId, sent>> /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* The current server instance: its readLoop and its recvLoop. *)

\* In English: "While the readLoop runs, it can take the oldest segment from
\* the receiver and append it to readBuffer" - in one step, so a stop can
\* never lose a segment taken but not yet appended.
ReadSegment ==
    /\ reading
    /\ rx /= <<>>
    /\ rb' = rb \o Head(rx)
    /\ rx' = Tail(rx)
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, ps, reading, rq,
                   reserved, restart, stopping, carry, delivered, violation>>

\* In English: "While the readLoop runs, has bytes, and (in gOuroboros) no
\* earlier message is still waiting to be handled:
\*   - if the instance's run is over, it stops reading and keeps the bytes
\*     for the next instance (carryOnExit);
\*   - otherwise, if a whole message is at the front and the client has
\*     agency, it admits that message for the recvLoop;
\*   - otherwise, a whole message from a peer without agency is refused."
Parse ==
    /\ reading
    /\ rb /= <<>>
    /\ AdmitOneAtATime => ~reserved             \* gOuroboros waits for the last message
    /\ IF ps = "StDone"
          THEN /\ carry' = IF CarryReadBuffer THEN rb ELSE <<>>  \* keep the bytes, or lose them
               /\ rb' = <<>>
               /\ reading' = FALSE              \* the readLoop stops
               /\ UNCHANGED <<rq, reserved, violation>>
       ELSE IF StartsWithMessage(rb) /\ Agency(ps) = "Client"
          THEN /\ rq' = Append(rq, [id |-> rb[1].id, type |-> rb[1].type])  \* admit the message
               /\ rb' = Drop(rb, 2)
               /\ reserved' = TRUE
               /\ UNCHANGED <<reading, carry, violation>>
       ELSE IF StartsWithMessage(rb)
          THEN /\ violation' = TRUE             \* a message out of turn: refuse it
               /\ reading' = FALSE
               /\ UNCHANGED <<rb, rq, reserved, carry>>
          ELSE FALSE                            \* half a message: wait for more bytes
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, rx, ps, restart,
                   stopping, delivered>>

\* In English: "When no restart is in progress, the recvLoop handles the
\* oldest admitted message: the message is delivered, the state moves on,
\* and if it was MsgDone, handleDone starts the restart."
Handle ==
    /\ rq /= <<>>
    /\ restart = "idle"
    /\ LET m == Head(rq) IN
         /\ delivered' = Append(delivered, m.id)    \* next, m has been processed
         /\ ps' = After(ps, m.type)                 \* next, the state follows m
         /\ restart' = IF m.type = "MsgDone" THEN "stop" ELSE "idle"
    /\ rq' = Tail(rq)
    /\ reserved' = FALSE                            \* the next message may be admitted
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, rx, rb, reading,
                   stopping, carry, violation>>

\* In English: "When the server has agency, it answers the ping, and the
\* client receives the answer." (The reverse direction, shortened.)
Respond ==
    /\ ps = "StServer"
    /\ cview = "StServer"
    /\ ps' = "StClient"
    /\ cview' = "StClient"
    /\ UNCHANGED <<pings, runs, nextId, out, sent, rx, rb, reading, rq,
                   reserved, restart, stopping, carry, delivered, violation>>

-----------------------------------------------------------------------------
(* The restart, run by handleDone in the old instance's recvLoop. *)

\* Step 1, StopForRestart. In English: "Ask the readLoop to stop."
StopForRestart ==
    /\ restart = "stop"
    /\ stopping' = TRUE
    /\ restart' = "suspend"
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, rx, ps, rb, reading,
                   rq, reserved, carry, delivered, violation>>

\* In English: "A readLoop asked to stop exits, keeping what it has read for
\* the next instance (in gOuroboros)." It may also have exited already, at
\* the first message after Done (Parse).
ReadLoopExits ==
    /\ stopping
    /\ reading
    /\ reading' = FALSE
    /\ carry' = IF CarryReadBuffer THEN rb ELSE <<>>
    /\ rb' = <<>>
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, rx, ps, rq, reserved,
                   restart, stopping, delivered, violation>>

\* Still step 1: stop(restart) waits for the readLoop, then suspends the
\* receiver with the carried bytes. In English: "Once the readLoop has
\* exited, the receiver is suspended."
Suspend ==
    /\ restart = "suspend"
    /\ ~reading
    /\ restart' = "start"
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, rx, ps, rb, reading,
                   rq, reserved, stopping, carry, delivered, violation>>

\* Steps 2 and 3, a new instance starts. In English: "A fresh instance starts
\* in StClient with nothing admitted; its readBuffer begins with the carried
\* bytes; it gets the old receiver back (gOuroboros), or a new, empty one."
StartNew ==
    /\ restart = "start"
    /\ ps' = "StClient"
    /\ rb' = carry                              \* the handover comes first
    /\ carry' = <<>>
    /\ rq' = <<>>                               \* anything the old instance admitted is gone
    /\ reserved' = FALSE
    /\ reading' = TRUE
    /\ stopping' = FALSE
    /\ rx' = IF ResumeReceiver THEN rx ELSE <<>>
    /\ restart' = "idle"
    /\ UNCHANGED <<cview, pings, runs, nextId, out, sent, delivered, violation>>

-----------------------------------------------------------------------------

\* In English: "Everything is finished: the client is done for good, every
\* byte has been delivered and handled, and no restart is in progress."
\* Any other state where nothing can happen is a deadlock, and TLC reports
\* it: a message the server will never see.
AllDone ==
    /\ cview = "StDone" /\ runs = MaxRuns
    /\ out = <<>> /\ rx = <<>> /\ rq = <<>>
    /\ restart = "idle"
    /\ Len(delivered) = Len(sent)

Next ==
    \/ ClientPing \/ ClientDone \/ ClientRestart
    \/ \E n \in 1..2 : SendSegment(n)
    \/ ReadSegment \/ Parse \/ Handle \/ Respond
    \/ StopForRestart \/ ReadLoopExits \/ Suspend \/ StartNew
    \/ AllDone /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "What the server handled is the start of what the client
\* sent, in the same order": nothing lost, nothing twice, nothing swapped.
DeliveredInOrder ==
    /\ Len(delivered) <= Len(sent)
    /\ \A i \in 1..Len(delivered) : delivered[i] = sent[i]

\* In English: "No server instance ever refuses a message from this honest
\* client."
NoViolation == ~violation

\* In English: "At most one message is admitted and waiting at a time."
AtMostOneAdmitted == Len(rq) <= 1
=============================================================================
