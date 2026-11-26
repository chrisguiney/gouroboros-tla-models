--------------------------- MODULE MuxReceiverStop ---------------------------
(***************************************************************************)
(* The receive side of the muxer and how it stops (muxer/muxer.go:         *)
(* readLoop and its exit sweep, segmentChannel.enqueue, forward, stop and  *)
(* callMetrics, RegisterProtocol, UnregisterProtocol, Stop and the cleanup *)
(* goroutine).                                                             *)
(*                                                                         *)
(* One mini-protocol role. Each RegisterProtocol makes a receiver: a queue *)
(* the read loop appends to, and a forward goroutine that waits on the     *)
(* receiver's sync.Cond while the queue is empty, hands each segment to    *)
(* the protocol, and reports metrics callbacks. The read loop also runs a  *)
(* metrics callback after each enqueue. Stop closes doneChan and waits for *)
(* the cleanup goroutine, which waits on the muxer's WaitGroup: the read   *)
(* loop and every forwarder. The reference mux runs its muxer and demuxer  *)
(* in a job pool and does not return until both have ended [R3].           *)
(*                                                                         *)
(*   main:  (1) readLoop calls waitGroup.Done before its exit sweep, so    *)
(*          Stop can return while the sweep still runs and holds           *)
(*          protocolReceiversMutex. (2) A second RegisterProtocol of a     *)
(*          role that is still registered replaces its receiver in the map *)
(*          and nothing stops the old one: the sweep finds only mapped     *)
(*          receivers, so the old forwarder waits on the Cond for ever and *)
(*          Stop never returns.                                            *)
(*   fix:   Done after the sweep (JoinFix); RegisterProtocol stops the     *)
(*          receiver and sender it replaces (ReplaceFix).                  *)
(*                                                                         *)
(* Granularity: a step is one critical section of segmentChannel.mu or     *)
(* callbackMu, one channel operation, or a callback starting or returning. *)
(* segmentChannel.stop's three locked updates (stopping under callbackMu,  *)
(* close(done), closed and Broadcast under mu) are one step, MarkStop:     *)
(* forward reads them only under those locks or from that channel, and     *)
(* each order of them ends the same way. A sync.Cond wait is modelled with *)
(* a flag: forward checks its predicate and parks under mu in one step     *)
(* (clearing `woken`), Broadcast under mu sets `woken`, and a parked       *)
(* forward can move only once `woken` is set.                              *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `rl`, `fwd[r]`, `user` and `cleanup` are program counters.     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    NRecv,              \* how many receivers RegisterProtocol may make
    QMax,               \* queue bound per receiver
    JoinFix,            \* TRUE: readLoop's Done comes after its sweep
    ReplaceFix,         \* TRUE: RegisterProtocol stops what it replaces
    DoubleRegister,     \* the user may register a role that is registered
    \* Mutations, each TRUE for gOuroboros:
    BroadcastOnStop,    \* stop broadcasts after setting closed
    BroadcastOnEnqueue, \* enqueue broadcasts after appending
    StopWaits           \* Stop waits for the cleanup goroutine

\* In English: "the receivers RegisterProtocol may make, numbered from 1."
R == 1..NRecv
\* In English: "no receiver."
None == 0

VARIABLES
    rl,         \* readLoop: "loop", "rcb", "exit", "sweep", "sweepWait", "exited"
    rlTarget,   \* the receiver readLoop's callback or sweep is on
    rlDone,     \* readLoop has called waitGroup.Done
    mapped,     \* the receiver in protocolReceivers for the role, or None
    nextR,      \* the next receiver RegisterProtocol makes
    fwd,        \* per receiver: "none", "check", "wait", "report", "cb", "send", "exiting", "exited"
    queue,      \* per receiver: segments queued
    woken,      \* per receiver: a Broadcast came since forward parked
    closed,     \* per receiver: segmentChannel.closed
    stopping,   \* per receiver: segmentChannel.stopping
    callbacks,  \* per receiver: metrics callbacks admitted and running
    needWait,   \* per receiver: its stopper waits for forwarderDone
    doneCh,     \* the muxer's doneChan is closed
    user,       \* "idle", "regWait", "unregWait", "stopWait", "returned"
    userTarget, \* the receiver the user's stop waits for
    cleanup     \* "waitDone", "wait", "finished"

\* In English: "all the variables."
vars == <<rl, rlTarget, rlDone, mapped, nextR, fwd, queue, woken, closed,
          stopping, callbacks, needWait, doneCh, user, userTarget, cleanup>>

\* In English: "the per-receiver variables."
recvVars == <<fwd, queue, woken, closed, stopping, callbacks, needWait>>

\* In English: "the state just after New."
Init ==
    /\ rl = "loop" /\ rlTarget = None /\ rlDone = FALSE
    /\ mapped = None /\ nextR = 1
    /\ fwd = [r \in R |-> "none"]
    /\ queue = [r \in R |-> 0]
    /\ woken = [r \in R |-> FALSE]
    /\ closed = [r \in R |-> FALSE]
    /\ stopping = [r \in R |-> FALSE]
    /\ callbacks = [r \in R |-> 0]
    /\ needWait = [r \in R |-> FALSE]
    /\ doneCh = FALSE
    /\ user = "idle" /\ userTarget = None
    /\ cleanup = "waitDone"

\* In English: "segmentChannel.stop's effect on receiver r: no new callback
\* is admitted, its stopper will wait for forward only if no callback is
\* running, closed is set, and (unless mutated) waiters are woken."
\* Literally: "MarkStop(r) is defined as: stopping[r], closed[r] become
\*   true, needWait[r] becomes callbacks[r] = 0, woken[r] becomes true if
\*   BroadcastOnStop. The caller says what happens to fwd, queue and
\*   callbacks."
MarkStop(r) ==
    /\ stopping' = [stopping EXCEPT ![r] = TRUE]            \* muxer.go stop: callbackMu
    /\ needWait' = [needWait EXCEPT ![r] = (callbacks[r] = 0)]
    /\ closed' = [closed EXCEPT ![r] = TRUE]                \* closed = true
    /\ woken' = IF BroadcastOnStop
                  THEN [woken EXCEPT ![r] = TRUE]           \* cond.Broadcast()
                  ELSE woken

\* In English: "Can a stopper of r stop waiting: r's forward has exited, or
\* it was not waited for because a callback was running."
StopperMayGo(r) == fwd[r] = "exited" \/ ~needWait[r]

-----------------------------------------------------------------------------
(* The user's goroutine. *)

\* In English: "RegisterProtocol, before Stop: a new receiver with its
\* forward goroutine goes into the map. If one was mapped, on main it is
\* just dropped from the map; with ReplaceFix it is stopped and the call
\* waits for it."
\* Literally: "Register is defined as: user is "idle", doneCh is false,
\*   nextR is a receiver, mapped is None or DoubleRegister; r is nextR,
\*   old is mapped; mapped becomes r, nextR goes up, fwd[r] becomes "check";
\*   and if old is a receiver and ReplaceFix then MarkStop(old) on top of
\*   that and user becomes "regWait" on old."
Register ==
    /\ user = "idle" /\ ~doneCh /\ nextR \in R
    /\ mapped = None \/ DoubleRegister
    /\ LET r == nextR
           old == mapped
       IN /\ mapped' = r
          /\ nextR' = nextR + 1
          /\ IF old # None /\ ReplaceFix
               THEN /\ MarkStop(old) /\ fwd' = [fwd EXCEPT ![r] = "check"]
                    /\ UNCHANGED <<queue, callbacks>>
                    /\ user' = "regWait" /\ userTarget' = old
               ELSE /\ fwd' = [fwd EXCEPT ![r] = "check"]  \* waitGroup.Go(forward)
                    /\ UNCHANGED <<queue, woken, closed, stopping, callbacks, needWait,
                                   user, userTarget>>
    /\ UNCHANGED <<rl, rlTarget, rlDone, doneCh, cleanup>>

\* In English: "UnregisterProtocol: the mapped receiver leaves the map and is
\* stopped; the call waits for it."
Unregister ==
    /\ user = "idle" /\ mapped # None
    /\ MarkStop(mapped) /\ UNCHANGED <<fwd, queue, callbacks>>
    /\ mapped' = None
    /\ user' = "unregWait" /\ userTarget' = mapped
    /\ UNCHANGED <<rl, rlTarget, rlDone, nextR, doneCh, cleanup>>

\* In English: "The user's stop of a receiver returns once its stopper may
\* go."
UserStopReturns ==
    /\ user \in {"regWait", "unregWait"} /\ StopperMayGo(userTarget)
    /\ user' = "idle" /\ userTarget' = None
    /\ UNCHANGED <<rl, rlTarget, rlDone, mapped, nextR, recvVars, doneCh, cleanup>>

\* In English: "Muxer.Stop closes doneChan; it then waits for the cleanup
\* goroutine (unless mutated not to)."
Stop ==
    /\ user = "idle"
    /\ doneCh' = TRUE
    /\ user' = IF StopWaits THEN "stopWait" ELSE "returned"
    /\ UNCHANGED <<rl, rlTarget, rlDone, mapped, nextR, recvVars, userTarget, cleanup>>

\* In English: "Stop returns once the cleanup goroutine has finished."
StopReturns ==
    /\ user = "stopWait" /\ cleanup = "finished"
    /\ user' = "returned"
    /\ UNCHANGED <<rl, rlTarget, rlDone, mapped, nextR, recvVars, doneCh, userTarget, cleanup>>

-----------------------------------------------------------------------------
(* The read loop. *)

\* In English: "A segment for the role arrives: the read loop appends it to
\* the mapped receiver's queue and broadcasts, then runs the depth callback
\* if the receiver admits one. A segment for a closed receiver is dropped."
\* Literally: "Enqueue is defined as: rl is "loop", doneCh is false, mapped
\*   is a receiver r that is not closed with queue below QMax; queue[r] goes
\*   up, woken[r] becomes true if BroadcastOnEnqueue, and if r is not
\*   stopping its callbacks go up and rl becomes "rcb" on r."
Enqueue ==
    /\ rl = "loop" /\ ~doneCh /\ mapped # None
    /\ LET r == mapped IN
       /\ ~closed[r] /\ queue[r] < QMax
       /\ queue' = [queue EXCEPT ![r] = @ + 1]
       /\ woken' = IF BroadcastOnEnqueue THEN [woken EXCEPT ![r] = TRUE] ELSE woken
       /\ IF stopping[r]
            THEN UNCHANGED <<callbacks, rl, rlTarget>>
            ELSE /\ callbacks' = [callbacks EXCEPT ![r] = @ + 1]   \* callMetrics admits
                 /\ rl' = "rcb" /\ rlTarget' = r
    /\ UNCHANGED <<rlDone, mapped, nextR, fwd, closed, stopping, needWait,
                   doneCh, user, userTarget, cleanup>>

\* In English: "The read loop's callback returns."
ReadCallbackReturns ==
    /\ rl = "rcb"
    /\ callbacks' = [callbacks EXCEPT ![rlTarget] = @ - 1]
    /\ rl' = "loop" /\ rlTarget' = None
    /\ UNCHANGED <<rlDone, mapped, nextR, fwd, queue, woken, closed, stopping,
                   needWait, doneCh, user, userTarget, cleanup>>

\* In English: "A bearer error: sendError closes doneChan and the read loop
\* leaves its loop. Or it sees doneChan already closed."
ReadLoopEnds ==
    /\ rl = "loop"
    /\ doneCh' = TRUE                                    \* sendError -> stop, or already closed
    /\ rl' = "exit"
    /\ UNCHANGED <<rlTarget, rlDone, mapped, nextR, recvVars, user, userTarget, cleanup>>

\* In English: "On main the deferred function calls waitGroup.Done first;
\* with JoinFix it goes straight to the sweep."
ReadLoopExit ==
    /\ rl = "exit"
    /\ rlDone' = ~JoinFix
    /\ rl' = "sweep"
    /\ UNCHANGED <<rlTarget, mapped, nextR, recvVars, doneCh, user, userTarget, cleanup>>

\* In English: "The sweep stops the mapped receiver and removes it, or, with
\* nothing mapped, ends (calling Done here with JoinFix)."
Sweep ==
    /\ rl = "sweep"
    /\ IF mapped # None
         THEN /\ MarkStop(mapped) /\ UNCHANGED <<fwd, queue, callbacks>>
              /\ mapped' = None
              /\ rl' = "sweepWait" /\ rlTarget' = mapped
              /\ UNCHANGED rlDone
         ELSE /\ rl' = "exited"
              /\ rlDone' = TRUE
              /\ UNCHANGED <<mapped, rlTarget, recvVars>>
    /\ UNCHANGED <<nextR, doneCh, user, userTarget, cleanup>>

\* In English: "The sweep's stop returns once its stopper may go."
SweepWaitReturns ==
    /\ rl = "sweepWait" /\ StopperMayGo(rlTarget)
    /\ rl' = "sweep" /\ rlTarget' = None
    /\ UNCHANGED <<rlDone, mapped, nextR, recvVars, doneCh, user, userTarget, cleanup>>

-----------------------------------------------------------------------------
(* Each receiver's forward goroutine. *)

\* In English: "Under mu: take a queued segment; or, closed with nothing
\* queued, return; or park on the Cond."
\* Literally: "FwdCheck(r) is defined as: fwd[r] is "check", and if queue[r]
\*   is positive it goes down and fwd[r] becomes "report"; else if closed[r]
\*   fwd[r] becomes "exiting"; else fwd[r] becomes "wait" and woken[r]
\*   false."
FwdCheck(r) ==
    /\ fwd[r] = "check"
    /\ IF queue[r] > 0
         THEN /\ queue' = [queue EXCEPT ![r] = @ - 1]
              /\ fwd' = [fwd EXCEPT ![r] = "report"]
              /\ UNCHANGED woken
         ELSE IF closed[r]
         THEN /\ fwd' = [fwd EXCEPT ![r] = "exiting"]
              /\ UNCHANGED <<queue, woken>>
         ELSE /\ fwd' = [fwd EXCEPT ![r] = "wait"]       \* cond.Wait(): parks, releases mu
              /\ woken' = [woken EXCEPT ![r] = FALSE]
              /\ UNCHANGED queue
    /\ UNCHANGED <<closed, stopping, callbacks, needWait>>

\* In English: "A parked forward runs again only after a Broadcast."
FwdWake(r) ==
    /\ fwd[r] = "wait" /\ woken[r]
    /\ fwd' = [fwd EXCEPT ![r] = "check"]
    /\ UNCHANGED <<queue, woken, closed, stopping, callbacks, needWait>>

\* In English: "The depth report: a callback is admitted unless stopping."
FwdReport(r) ==
    /\ fwd[r] = "report"
    /\ IF stopping[r]
         THEN fwd' = [fwd EXCEPT ![r] = "send"] /\ UNCHANGED callbacks
         ELSE /\ callbacks' = [callbacks EXCEPT ![r] = @ + 1]
              /\ fwd' = [fwd EXCEPT ![r] = "cb"]
    /\ UNCHANGED <<queue, woken, closed, stopping, needWait>>

\* In English: "Its callback returns."
FwdCallbackReturns(r) ==
    /\ fwd[r] = "cb"
    /\ callbacks' = [callbacks EXCEPT ![r] = @ - 1]
    /\ fwd' = [fwd EXCEPT ![r] = "send"]
    /\ UNCHANGED <<queue, woken, closed, stopping, needWait>>

\* In English: "The segment goes to the protocol, or the receiver's done
\* channel ends the send and forward returns."
FwdSend(r) ==
    /\ fwd[r] = "send"
    /\ \/ fwd' = [fwd EXCEPT ![r] = "check"]             \* sc.ch <- seg
       \/ stopping[r] /\ fwd' = [fwd EXCEPT ![r] = "exiting"]   \* <-sc.done
    /\ UNCHANGED <<queue, woken, closed, stopping, callbacks, needWait>>

\* In English: "forward's deferred function waits for running callbacks,
\* closes the channel and forwarderDone, and calls Done."
FwdExit(r) ==
    /\ fwd[r] = "exiting" /\ callbacks[r] = 0
    /\ fwd' = [fwd EXCEPT ![r] = "exited"]
    /\ UNCHANGED <<queue, woken, closed, stopping, callbacks, needWait>>

\* In English: "any step of r's forward goroutine; nothing else moves."
FwdStep(r) ==
    /\ \/ FwdCheck(r) \/ FwdWake(r) \/ FwdReport(r)
       \/ FwdCallbackReturns(r) \/ FwdSend(r) \/ FwdExit(r)
    /\ UNCHANGED <<rl, rlTarget, rlDone, mapped, nextR, doneCh, user, userTarget, cleanup>>

-----------------------------------------------------------------------------
(* The cleanup goroutine. *)

\* In English: "After doneChan it waits for the WaitGroup: readLoop's Done
\* and every forward made."
Cleanup ==
    /\ \/ cleanup = "waitDone" /\ doneCh /\ cleanup' = "wait"
       \/ /\ cleanup = "wait" /\ rlDone
          /\ \A r \in R : r < nextR => fwd[r] = "exited"
          /\ cleanup' = "finished"                        \* close(errorChan), close(cleanupDone)
    /\ UNCHANGED <<rl, rlTarget, rlDone, mapped, nextR, recvVars, doneCh, user, userTarget>>

\* In English: "any step."
Progress ==
    \/ Register \/ Unregister \/ UserStopReturns \/ Stop \/ StopReturns
    \/ Enqueue \/ ReadCallbackReturns \/ ReadLoopEnds \/ ReadLoopExit
    \/ Sweep \/ SweepWaitReturns \/ Cleanup
    \/ \E r \in R : FwdStep(r)

\* In English: "once nothing can move, nothing changes."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is any step, or resting once none can move."
Next == Progress \/ Rest

\* In English: "start in Init; every later step is a Next step."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "no step can be taken."
Quiescent == ~ENABLED Progress

\* In English: "No lost wakeup: a parked forward that has not been woken has
\* nothing queued and is not closed, so its Cond predicate is still false."
\* Literally: "NoLostWakeup is defined as: for every receiver r, if fwd[r]
\*   is "wait" and woken[r] is false, then queue[r] is 0 and closed[r] is
\*   false."
NoLostWakeup ==
    \A r \in R : (fwd[r] = "wait" /\ ~woken[r]) => (queue[r] = 0 /\ ~closed[r])

\* In English: "No wait after stop: forward never parks on a closed
\* receiver." (Implied by the loop predicate; kept as its own line because
\* it is what the Cond's `for` re-check guarantees.)
NoWaitAfterStop == \A r \in R : fwd[r] = "wait" => ~closed[r] \/ woken[r]

\* In English: "Stop returns only after the read loop has ended, sweep
\* included."
StopJoinsReadLoop == user = "returned" /\ StopWaits => rl = "exited"

\* In English: "After Stop returns, no metrics callback is running."
NoCallbackAfterStop ==
    user = "returned" => (rl # "rcb" /\ \A r \in R : fwd[r] # "cb")

\* In English: "When nothing can move, Stop has returned, the read loop has
\* ended and every receiver made has exited: the receiver always exits on
\* Stop or on a bearer error, replaced ones included."
StopCompletes ==
    Quiescent =>
        /\ user = "returned" /\ rl = "exited"
        /\ \A r \in R : r < nextR => fwd[r] = "exited"

\* In English: "each variable holds the kind of value it should."
TypeOK ==
    /\ rl \in {"loop", "rcb", "exit", "sweep", "sweepWait", "exited"}
    /\ mapped \in R \cup {None}
    /\ fwd \in [R -> {"none", "check", "wait", "report", "cb", "send", "exiting", "exited"}]
    /\ queue \in [R -> 0..QMax]
    /\ callbacks \in [R -> 0..2]
    /\ user \in {"idle", "regWait", "unregWait", "stopWait", "returned"}
    /\ cleanup \in {"waitDone", "wait", "finished"}
=============================================================================
