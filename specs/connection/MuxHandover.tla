---------------------------- MODULE MuxHandover ----------------------------
(***************************************************************************)
(* Model `connection`, parts 1 and 2: does every message reach the right server      *)
(* instance when a mini-protocol restarts in the middle of a byte stream,  *)
(* and does Stop or a connection shutdown during a restart leave anything  *)
(* behind?                                                                 *)
(*                                                                         *)
(* A client sends keep-alive messages through the multiplexer. Messages    *)
(* travel as bytes, cut into segments that may split a message or carry    *)
(* parts of two. When the client sends MsgDone, the gOuroboros server      *)
(* stops that instance and starts a new one, while more bytes keep         *)
(* arriving. Optionally, something stops the server at the same time.      *)
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
(*     then SuspendProtocol with carriedIngress. Stop (not a restart)      *)
(*     unregisters instead, and its readBuffer is dropped.                 *)
(*   muxer/muxer.go - a suspended receiver keeps its queue and channel;    *)
(*     RegisterProtocol resumes it; TakeCarriedIngress hands the carried   *)
(*     bytes to the new instance, whose readLoop consumes them first       *)
(*     (handoverIngress). Bytes for an unregistered role are dropped       *)
(*     (protocolTombstones), and so is everything once the muxer stops.    *)
(*   protocol/keepalive/server.go handleDone and Stop - StopForRestart;    *)
(*     under protocolMu, if Stop was requested, unregister and stop;       *)
(*     otherwise install a new instance; then Start it.                    *)
(*   connection.go stopProtocols - calls each restarting server's Stop    *)
(*     (restartingServersLocked), then the muxer is stopped. Before the    *)
(*     fix for issue 3085 it read ProtocolInstance() and stopped only that *)
(*     instance (ShutdownStopsServer = FALSE).                             *)
(*                                                                         *)
(* Not modelled: byte-size limits, timeouts, and the server-to-client      *)
(* direction, which is shortened to a single step.                         *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxPings,           \* how many pings the client may send in total
    MaxRuns,            \* how many runs the client may start
    CarryReadBuffer,    \* TRUE (gOuroboros): unprocessed bytes go to the next instance
    AdmitOneAtATime,    \* TRUE (gOuroboros): a message waits until the last one is handled
    ResumeReceiver,     \* TRUE (gOuroboros): the new instance gets the old receiver back
    Stopper,            \* "None", "Server" (Server.Stop), or "Connection" (shutdown)
    ShutdownStopsServer \* TRUE (gOuroboros since the fix for issue 3085): connection
                        \* shutdown calls the server's Stop. FALSE (before it): shutdown
                        \* stops only the instance it reads, and records no request.

\* The protocol, as in KeepAlive.tla.
\* In English: "In StClient the client may send; in StServer the server may
\* send; in StDone nobody may."
\* Literally: "Agency of s is defined as: in the case s equals "StClient",
\*   "Client"; in the case s equals "StServer", "Server"; in the case s equals
\*   "StDone", "Nobody"."
Agency(s) == CASE s = "StClient" -> "Client"
             []   s = "StServer" -> "Server"
             []   s = "StDone"   -> "Nobody"

\* In English: "The state after message type t in state s."
\* Literally: "After of s and t is defined as: in the case s equals "StClient"
\*   and t equals "MsgKeepAlive", "StServer"; in the case s equals "StClient"
\*   and t equals "MsgDone", "StDone"; in the case s equals "StServer" and t
\*   equals "MsgKeepAliveResponse", "StClient"."
After(s, t) ==
    CASE s = "StClient" /\ t = "MsgKeepAlive"         -> "StServer"
    []   s = "StClient" /\ t = "MsgDone"              -> "StDone"
    []   s = "StServer" /\ t = "MsgKeepAliveResponse" -> "StClient"

\* A message is two bytes on the wire, so a segment can end halfway through
\* one [M2]. In English: "Bytes(id, t) is the two bytes of message id, of
\* type t: part 1, then part 2."
\* Literally: "Bytes of id and t is defined as the tuple of the record whose
\*   field id is id, field type is t and field part is 1, and the record whose
\*   field id is id, field type is t and field part is 2."
Bytes(id, t) == << [id |-> id, type |-> t, part |-> 1],
                   [id |-> id, type |-> t, part |-> 2] >>

\* In English: "buf starts with a whole message: its first byte is part 1
\* and its second byte is part 2 of the same message."
\* Literally: "StartsWithMessage of buf is defined as: the length of buf is
\*   greater than or equal to 2, and element 1 of buf's part equals 1, and
\*   element 2 of buf's id equals element 1 of buf's id."
StartsWithMessage(buf) ==
    /\ Len(buf) >= 2
    /\ buf[1].part = 1
    /\ buf[2].id = buf[1].id

\* In English: "Drop the first n bytes of buf."
\* Literally: "Drop of buf and n is defined as the subsequence of buf from
\*   element n plus 1 through element the length of buf."
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
    muxer,      \* "running" or "stopped"
    slot,       \* the server's receiver: "registered", "suspended", or "empty"
    rx,         \* segments waiting in that receiver, oldest first
    \* --- the server instances ---
    inst,       \* the number of the current instance (s.Protocol)
    stoppedTo,  \* every instance up to this number has been stopped
    ps,         \* the state the current instance believes the protocol is in
    rb,         \* its readBuffer: bytes read from the muxer, not yet parsed
    reading,    \* TRUE while its readLoop runs
    rq,         \* messages its readLoop admitted, for its recvLoop to handle
    reserved,   \* TRUE while an admitted message is waiting to be handled
    \* --- the restart ---
    restart,    \* the restart's next step: "idle", "stop", "suspend", "install", "start"
    stopping,   \* TRUE once StopForRestart has asked the readLoop to stop
    carry,      \* bytes the old instance hands to the new one
    \* --- the stopper ---
    stopper,    \* the stopper's next step: "idle", "act", "muxer", "done"
    stopReq,    \* the flag Server.Stop sets
    snap,       \* the instance the stopper read
    cutoff,     \* messages sent before the stop finished; later ones must not be handled
    \* --- what the server processed ---
    delivered,  \* every message id the server's recvLoops handled, in order
    violation   \* TRUE if a server instance refused a message

\* Literally: "vars is defined as the tuple of all twenty-five variables."
vars == <<cview, pings, runs, nextId, out, sent, muxer, slot, rx, inst,
          stoppedTo, ps, rb, reading, rq, reserved, restart, stopping, carry,
          stopper, stopReq, snap, cutoff, delivered, violation>>

\* In English: "At the start, client and server are in StClient, nothing has
\* been sent, instance 1 is reading with its receiver registered, and the
\* stopper has not started (with no stopper, it never will)."
\* Literally: "Init is defined as: cview equals "StClient", and pings equals 0,
\*   and runs equals 1, and nextId equals 1, and out equals the empty sequence,
\*   and sent equals the empty sequence, and muxer equals "running", and slot
\*   equals "registered", and rx equals the empty sequence, and inst equals 1,
\*   and stoppedTo equals 0, and ps equals "StClient", and rb equals the empty
\*   sequence, and reading equals TRUE, and rq equals the empty sequence, and
\*   reserved equals FALSE, and restart equals "idle", and stopping equals
\*   FALSE, and carry equals the empty sequence, and stopper equals (if Stopper
\*   equals "None" then "done", else "idle"), and stopReq equals FALSE, and
\*   snap equals 0, and cutoff equals 0, and delivered equals the empty
\*   sequence, and violation equals FALSE."
Init ==
    /\ cview = "StClient"
    /\ pings = 0
    /\ runs = 1
    /\ nextId = 1
    /\ out = <<>>
    /\ sent = <<>>
    /\ muxer = "running"
    /\ slot = "registered"
    /\ rx = <<>>
    /\ inst = 1
    /\ stoppedTo = 0
    /\ ps = "StClient"
    /\ rb = <<>>
    /\ reading = TRUE
    /\ rq = <<>>
    /\ reserved = FALSE
    /\ restart = "idle"
    /\ stopping = FALSE
    /\ carry = <<>>
    /\ stopper = IF Stopper = "None" THEN "done" ELSE "idle"
    /\ stopReq = FALSE
    /\ snap = 0
    /\ cutoff = 0
    /\ delivered = <<>>
    /\ violation = FALSE

\* In English: "The client's variables."
\* Literally: "clientVars is defined as the tuple of cview, pings, runs,
\*   nextId, out and sent."
clientVars == <<cview, pings, runs, nextId, out, sent>>
\* In English: "The server instances' and the restart's variables, and what the
\* server processed."
\* Literally: "serverVars is defined as the tuple of inst, stoppedTo, ps, rb,
\*   reading, rq, reserved, restart, stopping, carry, delivered and violation."
serverVars == <<inst, stoppedTo, ps, rb, reading, rq, reserved, restart,
                stopping, carry, delivered, violation>>
\* In English: "The stopper's variables."
\* Literally: "stopVars is defined as the tuple of stopper, stopReq, snap and
\*   cutoff."
stopVars   == <<stopper, stopReq, snap, cutoff>>

-----------------------------------------------------------------------------
(* The client. It follows the protocol, as an honest peer does. *)

\* In English: "When the client may send and has pings left, it sends a ping:
\* its two bytes go out, it remembers the id, and it waits for the server."
\* Literally: "ClientPing is defined as: cview equals "StClient", and pings is
\*   less than MaxPings, and out in the next state equals out concatenated with
\*   Bytes of nextId and "MsgKeepAlive", and sent in the next state equals sent
\*   with nextId appended, and nextId in the next state equals nextId plus 1,
\*   and pings in the next state equals pings plus 1, and cview in the next
\*   state equals "StServer", and runs is unchanged, and muxer, slot and rx are
\*   unchanged, and serverVars is unchanged, and stopVars is unchanged."
ClientPing ==
    /\ cview = "StClient"                       \* the client may send
    /\ pings < MaxPings                         \* and has pings left
    /\ out' = out \o Bytes(nextId, "MsgKeepAlive")  \* next, the ping's bytes are queued
    /\ sent' = Append(sent, nextId)             \* next, the ping is recorded as sent
    /\ nextId' = nextId + 1
    /\ pings' = pings + 1
    /\ cview' = "StServer"                      \* next, it waits for the server
    /\ UNCHANGED runs
    /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED serverVars /\ UNCHANGED stopVars

\* In English: "When the client may send, it sends done and its run ends."
\* Literally: "ClientDone is defined as: cview equals "StClient", and out in
\*   the next state equals out concatenated with Bytes of nextId and "MsgDone",
\*   and sent in the next state equals sent with nextId appended, and nextId in
\*   the next state equals nextId plus 1, and cview in the next state equals
\*   "StDone", and pings and runs are unchanged, and muxer, slot and rx are
\*   unchanged, and serverVars is unchanged, and stopVars is unchanged."
ClientDone ==
    /\ cview = "StClient"
    /\ out' = out \o Bytes(nextId, "MsgDone")
    /\ sent' = Append(sent, nextId)
    /\ nextId' = nextId + 1
    /\ cview' = "StDone"
    /\ UNCHANGED <<pings, runs>>
    /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED serverVars /\ UNCHANGED stopVars

\* In English: "When the client's run is over and it may start another, it
\* starts one at once" - without waiting for the server, so the new run's
\* bytes can follow the old run's MsgDone in the same stream [S8].
\* Literally: "ClientRestart is defined as: cview equals "StDone", and runs is
\*   less than MaxRuns, and cview in the next state equals "StClient", and runs
\*   in the next state equals runs plus 1, and pings, nextId, out and sent are
\*   unchanged, and muxer, slot and rx are unchanged, and serverVars is
\*   unchanged, and stopVars is unchanged."
ClientRestart ==
    /\ cview = "StDone"
    /\ runs < MaxRuns
    /\ cview' = "StClient"
    /\ runs' = runs + 1
    /\ UNCHANGED <<pings, nextId, out, sent>>
    /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED serverVars /\ UNCHANGED stopVars

\* In English: "The client's mux cuts the next 1 or 2 bytes into a segment
\* and the bearer delivers it, in order [M1][M2]. The server's muxer queues
\* it if a receiver is registered or suspended, and drops it otherwise."
\* Literally: "SendSegment of n is defined as: the length of out is greater
\*   than or equal to n, and rx in the next state equals (if muxer equals
\*   "running" and slot does not equal "empty", then rx with the subsequence of
\*   out from element 1 through element n appended, else rx), and out in the
\*   next state equals Drop of out and n, and cview, pings, runs, nextId, sent,
\*   muxer and slot are unchanged, and serverVars is unchanged, and stopVars is
\*   unchanged."
SendSegment(n) ==
    /\ Len(out) >= n
    /\ rx' = IF muxer = "running" /\ slot /= "empty"
                THEN Append(rx, SubSeq(out, 1, n))     \* queued for the server
                ELSE rx                                \* dropped
    /\ out' = Drop(out, n)                      \* next, those bytes have left the client
    /\ UNCHANGED <<cview, pings, runs, nextId, sent, muxer, slot>>
    /\ UNCHANGED serverVars /\ UNCHANGED stopVars

-----------------------------------------------------------------------------
(* The current server instance: its readLoop and its recvLoop. *)

\* In English: "While the readLoop runs, it can take the oldest segment from
\* the receiver and append it to readBuffer" - in one step, so a stop can
\* never lose a segment taken but not yet appended.
\* Literally: "ReadSegment is defined as: reading is true, and rx does not
\*   equal the empty sequence, and rb in the next state equals rb concatenated
\*   with the head of rx, and rx in the next state equals the tail of rx, and
\*   clientVars is unchanged, and muxer and slot are unchanged, and stopVars is
\*   unchanged, and inst, stoppedTo, ps, reading, rq, reserved, restart,
\*   stopping, carry, delivered and violation are unchanged."
ReadSegment ==
    /\ reading
    /\ rx /= <<>>
    /\ rb' = rb \o Head(rx)
    /\ rx' = Tail(rx)
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, slot>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, ps, reading, rq, reserved, restart,
                   stopping, carry, delivered, violation>>

\* In English: "While the readLoop runs, has bytes, and (in gOuroboros) no
\* earlier message is still waiting to be handled:
\*   - if the instance's run is over, it stops reading and keeps the bytes
\*     for the next instance (carryOnExit);
\*   - otherwise, if a whole message is at the front and the client has
\*     agency, it admits that message for the recvLoop;
\*   - otherwise, a whole message from a peer without agency is refused."
\* Literally: "Parse is defined as: reading is true, and rb does not equal the
\*   empty sequence, and if AdmitOneAtATime is true, then reserved is not true;
\*   and if ps equals "StDone", then (carry in the next state equals (if
\*   CarryReadBuffer then rb, else the empty sequence), and rb in the next
\*   state equals the empty sequence, and reading in the next state equals
\*   FALSE, and rq, reserved and violation are unchanged); else if
\*   StartsWithMessage of rb and Agency of ps equals "Client", then (rq in the
\*   next state equals rq with the record whose field id is element 1 of rb's
\*   id and field type is element 1 of rb's type appended, and rb in the next
\*   state equals Drop of rb and 2, and reserved in the next state equals TRUE,
\*   and reading, carry and violation are unchanged); else if StartsWithMessage
\*   of rb, then (violation in the next state equals TRUE, and reading in the
\*   next state equals FALSE, and rb, rq, reserved and carry are unchanged);
\*   else FALSE; and clientVars is unchanged, and muxer, slot and rx are
\*   unchanged, and stopVars is unchanged, and inst, stoppedTo, ps, restart,
\*   stopping and delivered are unchanged."
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
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, ps, restart, stopping, delivered>>

\* In English: "When no restart is in progress and the instance has not
\* been stopped, the recvLoop handles the oldest admitted message: the
\* message is delivered, the state moves on, and if it was MsgDone,
\* handleDone starts the restart."
\* Literally: "Handle is defined as: rq does not equal the empty sequence, and
\*   restart equals "idle", and inst is greater than stoppedTo, and, letting m
\*   be the head of rq: delivered in the next state equals delivered with m's
\*   id appended, and ps in the next state equals After of ps and m's type, and
\*   restart in the next state equals (if m's type equals "MsgDone" then
\*   "stop", else "idle"); and rq in the next state equals the tail of rq, and
\*   reserved in the next state equals FALSE, and clientVars is unchanged, and
\*   muxer, slot and rx are unchanged, and stopVars is unchanged, and inst,
\*   stoppedTo, rb, reading, stopping, carry and violation are unchanged."
Handle ==
    /\ rq /= <<>>
    /\ restart = "idle"
    /\ inst > stoppedTo                             \* this instance is not stopped
    /\ LET m == Head(rq) IN
         /\ delivered' = Append(delivered, m.id)    \* next, m has been processed
         /\ ps' = After(ps, m.type)                 \* next, the state follows m
         /\ restart' = IF m.type = "MsgDone" THEN "stop" ELSE "idle"
    /\ rq' = Tail(rq)
    /\ reserved' = FALSE                            \* the next message may be admitted
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, rb, reading, stopping, carry, violation>>

\* In English: "When the server has agency, it answers the ping, and the
\* client receives the answer." (The reverse direction, shortened.)
\* Literally: "Respond is defined as: ps equals "StServer", and cview equals
\*   "StServer", and inst is greater than stoppedTo, and ps in the next state
\*   equals "StClient", and cview in the next state equals "StClient", and
\*   pings, runs, nextId, out and sent are unchanged, and muxer, slot and rx
\*   are unchanged, and stopVars is unchanged, and inst, stoppedTo, rb,
\*   reading, rq, reserved, restart, stopping, carry, delivered and violation
\*   are unchanged."
Respond ==
    /\ ps = "StServer"
    /\ cview = "StServer"
    /\ inst > stoppedTo                             \* a stopped instance answers nothing
    /\ ps' = "StClient"
    /\ cview' = "StClient"
    /\ UNCHANGED <<pings, runs, nextId, out, sent>>
    /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, rb, reading, rq, reserved, restart,
                   stopping, carry, delivered, violation>>

-----------------------------------------------------------------------------
(* The restart, run by handleDone in the old instance's recvLoop. *)

\* Step 1, StopForRestart. In English: "If this instance was not stopped
\* already, mark it stopped and ask its readLoop to stop."
\* Literally: "StopForRestart is defined as: restart equals "stop", and if inst
\*   is greater than stoppedTo, then (stoppedTo in the next state equals inst,
\*   and stopping in the next state equals TRUE), else stoppedTo and stopping
\*   are unchanged; and restart in the next state equals "suspend", and
\*   clientVars is unchanged, and muxer, slot and rx are unchanged, and
\*   stopVars is unchanged, and inst, ps, rb, reading, rq, reserved, carry,
\*   delivered and violation are unchanged."
StopForRestart ==
    /\ restart = "stop"
    /\ IF inst > stoppedTo
          THEN /\ stoppedTo' = inst
               /\ stopping' = TRUE
          ELSE UNCHANGED <<stoppedTo, stopping>>    \* Stop got there first: no-op
    /\ restart' = "suspend"
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, ps, rb, reading, rq, reserved, carry, delivered,
                   violation>>

\* In English: "A readLoop asked to stop exits, keeping what it has read for
\* the next instance (in gOuroboros)." It may also have exited already, at
\* the first message after Done (Parse).
\* Literally: "ReadLoopExits is defined as: stopping is true, and reading is
\*   true, and reading in the next state equals FALSE, and carry in the next
\*   state equals (if CarryReadBuffer then rb, else the empty sequence), and rb
\*   in the next state equals the empty sequence, and clientVars is unchanged,
\*   and muxer, slot and rx are unchanged, and stopVars is unchanged, and inst,
\*   stoppedTo, ps, rq, reserved, restart, stopping, delivered and violation
\*   are unchanged."
ReadLoopExits ==
    /\ stopping
    /\ reading
    /\ reading' = FALSE
    /\ carry' = IF CarryReadBuffer THEN rb ELSE <<>>
    /\ rb' = <<>>
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, ps, rq, reserved, restart, stopping,
                   delivered, violation>>

\* Still step 1: once the readLoop has exited, the receiver is suspended with
\* the carried bytes - if it is still registered. (If Stop already removed
\* it, there is nothing to suspend.)
\* In English: "Once the readLoop has exited, suspend a still-registered
\* receiver, and go to step 2."
\* Literally: "Suspend is defined as: restart equals "suspend", and reading is
\*   not true, and slot in the next state equals (if slot equals "registered"
\*   then "suspended", else slot), and restart in the next state equals
\*   "install", and clientVars is unchanged, and muxer and rx are unchanged,
\*   and stopVars is unchanged, and inst, stoppedTo, ps, rb, reading, rq,
\*   reserved, stopping, carry, delivered and violation are unchanged."
Suspend ==
    /\ restart = "suspend"
    /\ ~reading
    /\ slot' = IF slot = "registered" THEN "suspended" ELSE slot
    /\ restart' = "install"
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, rx>> /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, ps, rb, reading, rq, reserved, stopping,
                   carry, delivered, violation>>

\* Step 2, under protocolMu. In English: "If Server.Stop was requested,
\* unregister the receiver (dropping its bytes) and stop here. Otherwise
\* install a new instance, which becomes current."
\* Literally: "Install is defined as: restart equals "install", and if stopReq
\*   is true, then (slot in the next state equals "empty", and rx in the next
\*   state equals the empty sequence, and carry in the next state equals the
\*   empty sequence, and restart in the next state equals "idle", and inst is
\*   unchanged), else (inst in the next state equals inst plus 1, and restart
\*   in the next state equals "start", and slot, rx and carry are unchanged);
\*   and clientVars is unchanged, and muxer is unchanged, and stopVars is
\*   unchanged, and stoppedTo, ps, rb, reading, rq, reserved, stopping,
\*   delivered and violation are unchanged."
Install ==
    /\ restart = "install"
    /\ IF stopReq
          THEN /\ slot' = "empty"
               /\ rx' = <<>>
               /\ carry' = <<>>
               /\ restart' = "idle"
               /\ UNCHANGED inst
          ELSE /\ inst' = inst + 1
               /\ restart' = "start"
               /\ UNCHANGED <<slot, rx, carry>>
    /\ UNCHANGED clientVars /\ UNCHANGED muxer /\ UNCHANGED stopVars
    /\ UNCHANGED <<stoppedTo, ps, rb, reading, rq, reserved, stopping,
                   delivered, violation>>

\* Step 3, Start. In English: "If the new instance was stopped before it
\* started, or the muxer has stopped, nothing starts. Otherwise a fresh
\* instance starts in StClient with nothing admitted; its readBuffer begins
\* with the carried bytes, and it gets the old receiver back (gOuroboros)
\* or a new, empty one."
\* Literally: "StartNew is defined as: restart equals "start", and if inst is
\*   greater than stoppedTo and muxer equals "running", then (ps in the next
\*   state equals "StClient", and rb in the next state equals carry, and rq in
\*   the next state equals the empty sequence, and reserved in the next state
\*   equals FALSE, and reading in the next state equals TRUE, and slot in the
\*   next state equals "registered", and rx in the next state equals (if
\*   ResumeReceiver then rx, else the empty sequence)), else ps, rb, rq,
\*   reserved, reading, slot and rx are unchanged; and carry in the next state
\*   equals the empty sequence, and stopping in the next state equals FALSE,
\*   and restart in the next state equals "idle", and clientVars is unchanged,
\*   and muxer is unchanged, and stopVars is unchanged, and inst, stoppedTo,
\*   delivered and violation are unchanged."
StartNew ==
    /\ restart = "start"
    /\ IF inst > stoppedTo /\ muxer = "running"
          THEN /\ ps' = "StClient"
               /\ rb' = carry                   \* the handover comes first
               /\ rq' = <<>>                    \* anything the old instance admitted is gone
               /\ reserved' = FALSE
               /\ reading' = TRUE
               /\ slot' = "registered"
               /\ rx' = IF ResumeReceiver THEN rx ELSE <<>>
          ELSE UNCHANGED <<ps, rb, rq, reserved, reading, slot, rx>>
    /\ carry' = <<>>
    /\ stopping' = FALSE
    /\ restart' = "idle"
    /\ UNCHANGED clientVars /\ UNCHANGED muxer /\ UNCHANGED stopVars
    /\ UNCHANGED <<inst, stoppedTo, delivered, violation>>

-----------------------------------------------------------------------------
(* The stopper: Server.Stop, or connection shutdown. *)

\* In English: "Read the current instance. Server.Stop also records that
\* Stop was requested, under the same lock; so does connection shutdown,
\* once it calls Server.Stop (ShutdownStopsServer)."
\* Literally: "StopRead is defined as: stopper equals "idle", and snap in the
\*   next state equals inst, and stopReq in the next state equals (Stopper
\*   equals "Server" or ShutdownStopsServer is true), and stopper in the next
\*   state equals "act", and cutoff is unchanged, and clientVars is unchanged,
\*   and muxer, slot and rx are unchanged, and serverVars is unchanged."
StopRead ==
    /\ stopper = "idle"
    /\ snap' = inst
    /\ stopReq' = (Stopper = "Server" \/ ShutdownStopsServer)
    /\ stopper' = "act"
    /\ UNCHANGED cutoff
    /\ UNCHANGED clientVars /\ UNCHANGED <<muxer, slot, rx>> /\ UNCHANGED serverVars

\* In English: "Stop the instance read, if nobody has stopped it yet: it
\* stops reading, its unread bytes and admitted messages are dropped, and
\* its receiver is unregistered. Then record which messages were sent
\* before the stop finished. Connection shutdown goes on to stop the muxer."
\* Literally: "StopAct is defined as: stopper equals "act", and if snap is
\*   greater than stoppedTo, then (stoppedTo in the next state equals snap, and
\*   if snap equals inst, then (reading in the next state equals FALSE, and rb
\*   in the next state equals the empty sequence, and rq in the next state
\*   equals the empty sequence), else reading, rb and rq are unchanged; and
\*   slot in the next state equals "empty", and rx in the next state equals the
\*   empty sequence), else stoppedTo, reading, rb, rq, slot and rx are
\*   unchanged; and cutoff in the next state equals the length of sent, and
\*   stopper in the next state equals (if Stopper equals "Connection" then
\*   "muxer", else "done"), and stopReq and snap are unchanged, and clientVars
\*   is unchanged, and muxer is unchanged, and inst, ps, reserved, restart,
\*   stopping, carry, delivered and violation are unchanged."
StopAct ==
    /\ stopper = "act"
    /\ IF snap > stoppedTo
          THEN /\ stoppedTo' = snap
               /\ IF snap = inst
                     THEN /\ reading' = FALSE
                          /\ rb' = <<>>
                          /\ rq' = <<>>
                     ELSE UNCHANGED <<reading, rb, rq>>
               /\ slot' = "empty"
               /\ rx' = <<>>
          ELSE UNCHANGED <<stoppedTo, reading, rb, rq, slot, rx>>
    /\ cutoff' = Len(sent)
    /\ stopper' = IF Stopper = "Connection" THEN "muxer" ELSE "done"
    /\ UNCHANGED <<stopReq, snap>> /\ UNCHANGED clientVars /\ UNCHANGED muxer
    /\ UNCHANGED <<inst, ps, reserved, restart, stopping, carry, delivered,
                   violation>>

\* In English: "Connection shutdown stops the muxer: every receiver and its
\* bytes are gone, and the current instance stops reading."
\* Literally: "MuxerStop is defined as: stopper equals "muxer", and muxer in
\*   the next state equals "stopped", and slot in the next state equals
\*   "empty", and rx in the next state equals the empty sequence, and reading
\*   in the next state equals FALSE, and stopper in the next state equals
\*   "done", and stopReq, snap and cutoff are unchanged, and clientVars is
\*   unchanged, and inst, stoppedTo, ps, rb, rq, reserved, restart, stopping,
\*   carry, delivered and violation are unchanged."
MuxerStop ==
    /\ stopper = "muxer"
    /\ muxer' = "stopped"
    /\ slot' = "empty"
    /\ rx' = <<>>
    /\ reading' = FALSE
    /\ stopper' = "done"
    /\ UNCHANGED <<stopReq, snap, cutoff>> /\ UNCHANGED clientVars
    /\ UNCHANGED <<inst, stoppedTo, ps, rb, rq, reserved, restart, stopping,
                   carry, delivered, violation>>

-----------------------------------------------------------------------------

\* In English: "Everything is finished: either nothing stopped the server,
\* the client is done for good, and every message was handled; or the
\* server was stopped and no restart is in progress." Any other state where
\* nothing can happen is a deadlock, and TLC reports it: a message the
\* server will never see.
\* Literally: "AllDone is defined as: either (Stopper equals "None", and cview
\*   equals "StDone", and runs equals MaxRuns, and out equals the empty
\*   sequence, and rx equals the empty sequence, and rq equals the empty
\*   sequence, and restart equals "idle", and the length of delivered equals
\*   the length of sent), or (Stopper does not equal "None", and stopper equals
\*   "done", and restart equals "idle")."
AllDone ==
    \/ /\ Stopper = "None"
       /\ cview = "StDone" /\ runs = MaxRuns
       /\ out = <<>> /\ rx = <<>> /\ rq = <<>>
       /\ restart = "idle"
       /\ Len(delivered) = Len(sent)
    \/ /\ Stopper /= "None"
       /\ stopper = "done"
       /\ restart = "idle"

\* In English: "A step is any one step of the client, the bearer, the server,
\* the restart or the stopper, or, once everything is finished, nothing
\* changing."
\* Literally: "Next is defined as: ClientPing, or ClientDone, or ClientRestart,
\*   or there exists an n in 1 through 2 such that SendSegment of n, or
\*   ReadSegment, or Parse, or Handle, or Respond, or StopForRestart, or
\*   ReadLoopExits, or Suspend, or Install, or StartNew, or StopRead, or
\*   StopAct, or MuxerStop, or AllDone and vars is unchanged."
Next ==
    \/ ClientPing \/ ClientDone \/ ClientRestart
    \/ \E n \in 1..2 : SendSegment(n)
    \/ ReadSegment \/ Parse \/ Handle \/ Respond
    \/ StopForRestart \/ ReadLoopExits \/ Suspend \/ Install \/ StartNew
    \/ StopRead \/ StopAct \/ MuxerStop
    \/ AllDone /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "What the server handled is the start of what the client
\* sent, in the same order": nothing lost, nothing twice, nothing swapped.
\* (With a stopper, later messages may never be handled; that is a prefix
\* too.)
\* Literally: "DeliveredInOrder is defined as: the length of delivered is less
\*   than or equal to the length of sent, and for all i in 1 through the length
\*   of delivered, element i of delivered equals element i of sent."
DeliveredInOrder ==
    /\ Len(delivered) <= Len(sent)
    /\ \A i \in 1..Len(delivered) : delivered[i] = sent[i]

\* In English: "No server instance ever refuses a message from this honest
\* client."
\* Literally: "NoViolation is defined as: violation is not true."
NoViolation == ~violation

\* In English: "At most one message is admitted and waiting at a time."
\* Literally: "AtMostOneAdmitted is defined as: the length of rq is less than
\*   or equal to 1."
AtMostOneAdmitted == Len(rq) <= 1

\* In English: "Once the stop has finished, no message sent after it is
\* ever handled."
\* Literally: "NothingHandledAfterStop is defined as: if stopper equals "done"
\*   and Stopper does not equal "None", then for all i in 1 through the length
\*   of delivered, element i of delivered is less than or equal to cutoff."
NothingHandledAfterStop ==
    stopper = "done" /\ Stopper /= "None" =>
        \A i \in 1..Len(delivered) : delivered[i] <= cutoff

\* In English: "Once Server.Stop has finished and no restart is in
\* progress, no instance is reading and no receiver is left registered or
\* suspended."
\* Literally: "StopLeavesNothing is defined as: if Stopper equals "Server" and
\*   stopper equals "done" and restart equals "idle", then reading is not true
\*   and slot equals "empty"."
StopLeavesNothing ==
    (Stopper = "Server" /\ stopper = "done" /\ restart = "idle") =>
        /\ ~reading
        /\ slot = "empty"
=============================================================================
