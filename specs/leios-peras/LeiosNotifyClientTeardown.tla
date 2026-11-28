--------------------- MODULE LeiosNotifyClientTeardown ---------------------
(***************************************************************************)
(* The gOuroboros LeiosNotify client's goroutines at teardown              *)
(* (protocol/leiosnotify/client.go, v0.222.0 0c00b799; the engine is       *)
(* protocol/protocol.go at the same commit).                               *)
(*                                                                         *)
(* Goroutines, one program counter each:                                   *)
(*   rl      the engine's recvLoop, which runs the message handler. A      *)
(*           notification handler (handleBlockAnnouncement and its three   *)
(*           siblings) sends the message on the unbuffered                 *)
(*           notificationChan, in a select whose other case is DoneChan.   *)
(*   nl      notificationLoop, started by Sync through RunLoop. It takes   *)
(*           one notification, runs NotificationFunc, and asks for more    *)
(*           (sendRequests) once no pipelined request is owed. If the      *)
(*           callback returns ErrStopNotificationProcess it drains the     *)
(*           owed notifications and returns; any other error (or a panic,  *)
(*           which RunLoop turns into the same stop) calls SendError and   *)
(*           returns at once.                                              *)
(*   sl      the engine's sendLoop; it ends once StopChan closes.          *)
(*   closer  the goroutine Start runs: <-DoneChan, then                    *)
(*           close(notificationChan).                                      *)
(*   stopper a user's Stop: sets quitting under sendMutex (MsgQuit is      *)
(*           sent and bounded by a 250 ms context, so it is not a step     *)
(*           here), then Protocol.Stop: close StopChan and join the loops  *)
(*           (recvLoop, sendLoop, notificationLoop).                       *)
(* The engine closes DoneChan only once recvLoop and sendLoop have both    *)
(* returned (Protocol.Start's watcher goroutine, folded into one step).    *)
(* So a handler blocked in its send cannot be released by DoneChan: only   *)
(* notificationLoop can take the message. When notificationLoop has        *)
(* returned through the error path with a later pipelined notification     *)
(* already in recvLoop, nothing ever receives it: recvLoop never returns,  *)
(* DoneChan never closes, and Stop (and the connection's Close, which      *)
(* joins the same loops) waits for ever.                                   *)
(*                                                                         *)
(* Fixed = TRUE models the fix: the handler's select also ends on          *)
(* StopChan, which SendError, recoverLoop and Stop all close.              *)
(*                                                                         *)
(* The reference client (ouroboros-consensus LeiosNotify client, run as a  *)
(* typed-protocols pipelined peer) runs the callback on the protocol's own *)
(* thread and collects each pipelined reply there, so there is no second   *)
(* goroutine to hand a reply to; a callback exception ends the whole       *)
(* mini-protocol thread. gOuroboros splits receive and callback across two *)
(* goroutines and an unbuffered channel, which is where this comes from.   *)
(*                                                                         *)
(* Primitives are written in place with the names a shared module would    *)
(* use (a channel's `closed`, a WaitGroup-style join over the loops); see  *)
(* the README.                                                             *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. A step is enabled only when the Go line it stands for could    *)
(*   run.                                                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    PipelineLimit,  \* Config.PipelineLimit (requests per sendRequests)
    MaxRequests,    \* bound on requests sent, to keep the state space finite
    Outcomes,       \* what NotificationFunc may return: subset of {"ok","stop","err"}
    Fixed,          \* TRUE: the handler's select also ends on StopChan
    CloseOnStop     \* mutation: the closer waits for StopChan, not DoneChan

VARIABLES
    owed,       \* requests sent whose answer the server has not yet sent
    total,      \* requests sent so far (bounded by MaxRequests)
    recvQ,      \* answers queued for recvLoop: "n" notification, "c" MsgCanceled
    rl,         \* recvLoop: "loop", "handler", "exited"
    nl,         \* notificationLoop: "wait", "cb", "send", "drain", "exited"
    pnext,      \* pipelinedRequestNext
    drainLeft,  \* notifications drainPipelinedMessages still takes
    quitting,   \* c.quitting
    stopChan,   \* the protocol's StopChan is closed
    sl,         \* sendLoop: "running", "exited"
    doneChan,   \* the protocol's DoneChan is closed
    closed,     \* notificationChan is closed
    closer,     \* the closer goroutine: "wait", "exited"
    stopper,    \* the user's Stop: "idle", "stopping", "join", "returned"
    panicked    \* a send on the closed notificationChan happened

vars == <<owed, total, recvQ, rl, nl, pnext, drainLeft, quitting, stopChan,
          sl, doneChan, closed, closer, stopper, panicked>>

\* In English: "Sync has sent one request and started notificationLoop."
Init ==
    /\ owed = 1 /\ total = 1 /\ recvQ = <<>>
    /\ rl = "loop" /\ nl = "wait" /\ pnext = 0 /\ drainLeft = 0
    /\ quitting = FALSE /\ stopChan = FALSE /\ sl = "running"
    /\ doneChan = FALSE /\ closed = FALSE /\ closer = "wait"
    /\ stopper = "idle" /\ panicked = FALSE

\* In English: "The loops a Stop joins have all returned."
LoopsJoined == rl = "exited" /\ nl = "exited" /\ sl = "exited"

-----------------------------------------------------------------------------
\* The server.

\* In English: "The server answers an owed request with a notification, or,
\* once the client has quit, with MsgCanceled."
ServerAnswer ==
    /\ owed > 0
    /\ owed' = owed - 1
    /\ \E kind \in IF quitting THEN {"n", "c"} ELSE {"n"} :
           recvQ' = Append(recvQ, kind)
    /\ UNCHANGED <<total, rl, nl, pnext, drainLeft, quitting, stopChan, sl,
                   doneChan, closed, closer, stopper, panicked>>

-----------------------------------------------------------------------------
\* recvLoop (protocol.go recvLoop) and the handler it runs.

\* In English: "recvLoop's select: StopChan is closed, so it returns; or it
\* takes the oldest queued answer. A notification starts the handler;
\* MsgCanceled after quit is accepted with nothing to deliver. Both cases
\* may be ready at once, and Go picks either."
RecvStop ==
    /\ rl = "loop" /\ stopChan
    /\ rl' = "exited"
    /\ UNCHANGED <<owed, total, recvQ, nl, pnext, drainLeft, quitting,
                   stopChan, sl, doneChan, closed, closer, stopper, panicked>>

RecvTake ==
    /\ rl = "loop" /\ recvQ /= <<>>
    /\ recvQ' = Tail(recvQ)
    /\ rl' = IF Head(recvQ) = "n" THEN "handler" ELSE "loop"
    /\ UNCHANGED <<owed, total, nl, pnext, drainLeft, quitting, stopChan, sl,
                   doneChan, closed, closer, stopper, panicked>>

\* In English: "The handler's select ends on DoneChan, or (fixed) on
\* StopChan, and returns to recvLoop without delivering."
HandlerGiveUp ==
    /\ rl = "handler"
    /\ doneChan \/ (Fixed /\ stopChan)
    /\ rl' = "loop"
    /\ UNCHANGED <<owed, total, recvQ, nl, pnext, drainLeft, quitting,
                   stopChan, sl, doneChan, closed, closer, stopper, panicked>>

\* In English: "The handler's send case on a closed notificationChan is a
\* panic. It is never enabled while the closer waits for DoneChan, since
\* DoneChan needs recvLoop to have returned."
HandlerSendClosed ==
    /\ rl = "handler" /\ closed
    /\ panicked' = TRUE
    /\ rl' = "exited"
    /\ UNCHANGED <<owed, total, recvQ, nl, pnext, drainLeft, quitting,
                   stopChan, sl, doneChan, closed, closer, stopper>>

-----------------------------------------------------------------------------
\* notificationLoop.

\* In English: "The unbuffered send meets notificationLoop's receive, in its
\* main select or in the drain: one step for both goroutines."
Rendezvous ==
    /\ rl = "handler" /\ ~closed
    /\ nl \in {"wait", "drain"}
    /\ rl' = "loop"
    /\ IF nl = "wait"
       THEN nl' = "cb" /\ UNCHANGED drainLeft
       ELSE /\ drainLeft' = drainLeft - 1
            /\ nl' = IF drainLeft - 1 = 0 THEN "exited" ELSE "drain"
    /\ UNCHANGED <<owed, total, recvQ, pnext, quitting, stopChan, sl,
                   doneChan, closed, closer, stopper, panicked>>

\* In English: "notificationLoop's select (or the drain's) ends: the channel
\* is closed, or DoneChan is."
LoopEnds ==
    /\ nl \in {"wait", "drain"}
    /\ closed \/ doneChan
    /\ nl' = "exited"
    /\ UNCHANGED <<owed, total, recvQ, rl, pnext, drainLeft, quitting,
                   stopChan, sl, doneChan, closed, closer, stopper, panicked>>

\* In English: "NotificationFunc returns. ok: take the next owed
\* notification, or ask for more when none is owed. stop: drain the owed
\* ones and return. err (or a panic): SendError closes StopChan and the loop
\* returns. ok is only offered while the request budget allows it."
Callback ==
    /\ nl = "cb"
    /\ LET okAllowed == pnext > 0 \/ total + PipelineLimit <= MaxRequests
           choices == IF okAllowed THEN Outcomes ELSE Outcomes \ {"ok"}
           cs == IF choices = {} THEN {"stop"} ELSE choices
       IN \E out \in cs :
           CASE out = "ok" ->
                   /\ IF pnext > 0
                      THEN pnext' = pnext - 1 /\ nl' = "wait"
                      ELSE nl' = "send" /\ UNCHANGED pnext
                   /\ UNCHANGED <<drainLeft, stopChan>>
             [] out = "stop" ->
                   /\ drainLeft' = pnext /\ pnext' = 0
                   /\ nl' = IF pnext = 0 THEN "exited" ELSE "drain"
                   /\ UNCHANGED stopChan
             [] out = "err" ->
                   /\ stopChan' = TRUE /\ nl' = "exited"
                   /\ UNCHANGED <<pnext, drainLeft>>
    /\ UNCHANGED <<owed, total, recvQ, rl, quitting, sl, doneChan, closed,
                   closer, stopper, panicked>>

\* In English: "sendRequests under sendMutex: if quitting, or the protocol is
\* stopping (SendMessage refuses), the loop returns; otherwise it sends
\* PipelineLimit requests and owes PipelineLimit - 1 more answers after the
\* next."
SendRequests ==
    /\ nl = "send"
    /\ IF quitting \/ stopChan
       THEN /\ nl' = "exited"
            /\ UNCHANGED <<owed, total, pnext>>
       ELSE /\ owed' = owed + PipelineLimit
            /\ total' = total + PipelineLimit
            /\ pnext' = PipelineLimit - 1
            /\ nl' = "wait"
    /\ UNCHANGED <<recvQ, rl, drainLeft, quitting, stopChan, sl, doneChan,
                   closed, closer, stopper, panicked>>

-----------------------------------------------------------------------------
\* sendLoop, the engine's DoneChan watcher, and the closer goroutine.

\* In English: "sendLoop returns once StopChan is closed."
SendLoopExit ==
    /\ sl = "running" /\ stopChan
    /\ sl' = "exited"
    /\ UNCHANGED <<owed, total, recvQ, rl, nl, pnext, drainLeft, quitting,
                   stopChan, doneChan, closed, closer, stopper, panicked>>

\* In English: "DoneChan closes once recvLoop and sendLoop have returned."
CloseDone ==
    /\ ~doneChan /\ rl = "exited" /\ sl = "exited"
    /\ doneChan' = TRUE
    /\ UNCHANGED <<owed, total, recvQ, rl, nl, pnext, drainLeft, quitting,
                   stopChan, sl, closed, closer, stopper, panicked>>

\* In English: "The closer goroutine wakes on DoneChan (the mutation: on
\* StopChan) and closes notificationChan."
Closer ==
    /\ closer = "wait" /\ IF CloseOnStop THEN stopChan ELSE doneChan
    /\ closed' = TRUE /\ closer' = "exited"
    /\ UNCHANGED <<owed, total, recvQ, rl, nl, pnext, drainLeft, quitting,
                   stopChan, sl, doneChan, stopper, panicked>>

-----------------------------------------------------------------------------
\* The user's Stop.

\* In English: "Stop sets quitting under sendMutex and queues MsgQuit."
StopQuit ==
    /\ stopper = "idle"
    /\ quitting' = TRUE /\ stopper' = "stopping"
    /\ UNCHANGED <<owed, total, recvQ, rl, nl, pnext, drainLeft, stopChan,
                   sl, doneChan, closed, closer, panicked>>

\* In English: "Protocol.Stop closes StopChan (if SendError has not)."
StopSignal ==
    /\ stopper = "stopping"
    /\ stopChan' = TRUE /\ stopper' = "join"
    /\ UNCHANGED <<owed, total, recvQ, rl, nl, pnext, drainLeft, quitting,
                   sl, doneChan, closed, closer, panicked>>

\* In English: "Protocol.Stop returns once the loops it joins have returned."
StopJoin ==
    /\ stopper = "join" /\ LoopsJoined
    /\ stopper' = "returned"
    /\ UNCHANGED <<owed, total, recvQ, rl, nl, pnext, drainLeft, quitting,
                   stopChan, sl, doneChan, closed, closer, panicked>>

-----------------------------------------------------------------------------

\* In English: "Everything has ended: Stop returned and every goroutine,
\* the closer included, has returned. The only honest end state."
Finished ==
    /\ stopper = "returned" /\ LoopsJoined /\ closer = "exited"

Next ==
    \/ ServerAnswer
    \/ RecvStop \/ RecvTake \/ HandlerGiveUp \/ HandlerSendClosed
    \/ Rendezvous \/ LoopEnds \/ Callback \/ SendRequests
    \/ SendLoopExit \/ CloseDone \/ Closer
    \/ StopQuit \/ StopSignal \/ StopJoin
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Each goroutine progresses whenever its step stays enabled; the server
\* answers owed requests. The user's Stop is always eventually called.
FairSpec ==
    /\ Spec
    /\ WF_vars(ServerAnswer)
    /\ WF_vars(RecvStop) /\ WF_vars(RecvTake) /\ WF_vars(HandlerGiveUp)
    /\ WF_vars(Rendezvous) /\ WF_vars(LoopEnds) /\ WF_vars(Callback)
    /\ WF_vars(SendRequests) /\ WF_vars(SendLoopExit) /\ WF_vars(CloseDone)
    /\ WF_vars(Closer)
    /\ WF_vars(StopQuit) /\ WF_vars(StopSignal) /\ WF_vars(StopJoin)

-----------------------------------------------------------------------------

TypeOK ==
    /\ owed \in Nat /\ total \in 0..(MaxRequests + PipelineLimit)
    /\ rl \in {"loop", "handler", "exited"}
    /\ nl \in {"wait", "cb", "send", "drain", "exited"}
    /\ stopper \in {"idle", "stopping", "join", "returned"}

\* In English: "notificationChan is never sent on after it is closed."
NoSendOnClosed == ~panicked

\* In English: "Once Stop has returned, every goroutine has returned,
\* including the closer." The closer is not joined by Stop: it runs after
\* DoneChan, which closes after the join. A probe, not a defect: liveness
\* (AllGoroutinesExit) shows it always ends.
NothingOutlivesStop == stopper = "returned" => closer = "exited"

\* In English: "Stop eventually returns."
StopReturns == <>(stopper = "returned")

\* In English: "Every goroutine eventually returns."
AllGoroutinesExit == <>(LoopsJoined /\ closer = "exited")
=============================================================================
