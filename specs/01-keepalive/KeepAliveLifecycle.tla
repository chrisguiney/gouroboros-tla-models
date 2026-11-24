------------------------- MODULE KeepAliveLifecycle -------------------------
(***************************************************************************)
(* The gOuroboros keep-alive SERVER restart, at the level of its           *)
(* goroutines. KeepAlive.tla says WHAT must happen after MsgDone (a new    *)
(* run); this module checks HOW gOuroboros does it, while something else   *)
(* may be stopping the server at the same moment.                          *)
(*                                                                         *)
(* Each step below is one line or one locked block of gOuroboros code, so  *)
(* TLC tries every way the two goroutines can interleave:                  *)
(*                                                                         *)
(*   Restart: handleDone, run by the old instance's receive loop when       *)
(*   MsgDone arrives (protocol/keepalive/server.go):                       *)
(*     1. proto.StopForRestart()       stop the old instance               *)
(*     2. under protocolMu: install a new instance, or, if Stop was        *)
(*        requested (StopGuard), install nothing                           *)
(*     3. Start the new instance                                           *)
(*                                                                         *)
(*   Stopper, one of:                                                      *)
(*     "Server":     Server.Stop() - under protocolMu, record the request  *)
(*                   and read the current instance; then stop it.          *)
(*     "Connection": Connection shutdown (connection.go stopProtocols) -   *)
(*                   read ProtocolInstance(), stop it, then muxer.Stop().  *)
(*                                                                         *)
(* Facts about instances (protocol/protocol.go):                           *)
(*   - Stop and StopForRestart only act once per instance (onceStop).      *)
(*   - Start on a stopped instance does nothing.                           *)
(*   - Start after the muxer stopped fails to register, and reports        *)
(*     "could not register protocol with muxer" through SendError.         *)
(*   - A running instance's loops exit once the muxer stops.               *)
(*                                                                         *)
(* Facts about the muxer slot for the keep-alive server (muxer/muxer.go):  *)
(* the muxer keeps one receiver per protocol and role, and instances share *)
(* it one after another.                                                   *)
(*   - Stop unregisters it (UnregisterProtocol), even for an instance that *)
(*     never started.                                                      *)
(*   - StopForRestart suspends it (SuspendProtocol): it stays registered   *)
(*     and keeps buffering what arrives, for the next instance. With       *)
(*     nothing registered, it unregisters instead.                         *)
(*   - Start registers it (RegisterProtocol), resuming a suspended one.    *)
(*   - A stopped muxer holds no receivers.                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    MaxDones,           \* how many MsgDone the client sends (each triggers a restart)
    Stopper,            \* "Server" or "Connection": who stops the server
    StopGuard,          \* TRUE: Server.Stop sets a flag that a later restart honours
    CancelUnregisters   \* TRUE: a restart cancelled by the guard unregisters the slot

Instances == 1..(MaxDones + 1)

VARIABLES
    status,         \* status[i]: "unused", "new", "running", or "stopped"
    current,        \* the instance s.Protocol points at
    nextId,         \* the next instance number to hand out
    muxer,          \* "running" or "stopped"
    slot,           \* the keep-alive server's muxer receiver:
                    \*   "empty", "registered", or "suspended"
    restart,        \* the restart goroutine's next step
    old,            \* the instance the restart is replacing
    stopper,        \* the stopper's next step
    snap,           \* the instance the stopper read
    stopRequested,  \* the flag Server.Stop sets when StopGuard is on
    dones,          \* MsgDone received so far
    lateError       \* a restart failed to register after the muxer stopped

vars == <<status, current, nextId, muxer, slot, restart, old, stopper, snap,
          stopRequested, dones, lateError>>

Init ==
    /\ status = [i \in Instances |-> IF i = 1 THEN "running" ELSE "unused"]
    /\ current = 1
    /\ nextId = 2
    /\ muxer = "running"
    /\ slot = "registered"
    /\ restart = "idle"
    /\ old = 1
    /\ stopper = "idle"
    /\ snap = 1
    /\ stopRequested = FALSE
    /\ dones = 0
    /\ lateError = FALSE

\* Whether Stop or StopForRestart on instance i does anything: only the first
\* call on an instance acts.
Acts(i) == status[i] \in {"new", "running"}

-----------------------------------------------------------------------------
(* The restart goroutine. *)

\* The running instance reads MsgDone and calls handleDone.
RecvDone ==
    /\ restart = "idle"
    /\ dones < MaxDones
    /\ status[current] = "running"
    /\ restart' = "stopOld"
    /\ old' = current
    /\ dones' = dones + 1
    /\ UNCHANGED <<status, current, nextId, muxer, slot, stopper, snap,
                   stopRequested, lateError>>

\* 1. proto.StopForRestart(): suspend the slot, or unregister it if empty.
StopOld ==
    /\ restart = "stopOld"
    /\ IF Acts(old)
          THEN /\ status' = [status EXCEPT ![old] = "stopped"]
               /\ slot' = IF slot = "registered" THEN "suspended" ELSE "empty"
          ELSE UNCHANGED <<status, slot>>
    /\ restart' = "install"
    /\ UNCHANGED <<current, nextId, muxer, old, stopper, snap,
                   stopRequested, dones, lateError>>

\* 2. Under protocolMu: install a new instance. With StopGuard, a restart
\*    that sees Stop was requested installs nothing; with CancelUnregisters
\*    it also releases the slot StopForRestart left suspended.
Install ==
    /\ restart = "install"
    /\ IF StopGuard /\ stopRequested
          THEN /\ restart' = "idle"
               /\ slot' = IF CancelUnregisters THEN "empty" ELSE slot
               /\ UNCHANGED <<status, current, nextId>>
          ELSE /\ status' = [status EXCEPT ![nextId] = "new"]
               /\ current' = nextId
               /\ nextId' = nextId + 1
               /\ restart' = "start"
               /\ UNCHANGED slot
    /\ UNCHANGED <<muxer, old, stopper, snap, stopRequested, dones, lateError>>

\* 3. Start the new instance.
StartNew ==
    /\ restart = "start"
    /\ IF status[current] /= "new"
          THEN UNCHANGED <<status, slot, lateError>>   \* stopped already: no-op
       ELSE IF muxer = "stopped"
          THEN /\ status' = [status EXCEPT ![current] = "stopped"]
               /\ lateError' = TRUE                    \* registration failed
               /\ UNCHANGED slot
          ELSE /\ status' = [status EXCEPT ![current] = "running"]
               /\ slot' = "registered"
               /\ UNCHANGED lateError
    /\ restart' = "idle"
    /\ UNCHANGED <<current, nextId, muxer, old, stopper, snap,
                   stopRequested, dones>>

-----------------------------------------------------------------------------
(* The stopper. *)

\* Read the current instance under the lock. Server.Stop also records the
\* request; connection shutdown reads ProtocolInstance() and records nothing.
StopRead ==
    /\ stopper = "idle"
    /\ snap' = current
    /\ stopRequested' = (Stopper = "Server")
    /\ stopper' = "stop"
    /\ UNCHANGED <<status, current, nextId, muxer, slot, restart, old, dones,
                   lateError>>

\* Stop the instance read: it unregisters the slot, if it acts at all.
StopSnap ==
    /\ stopper = "stop"
    /\ IF Acts(snap)
          THEN /\ status' = [status EXCEPT ![snap] = "stopped"]
               /\ slot' = "empty"
          ELSE UNCHANGED <<status, slot>>
    /\ stopper' = IF Stopper = "Connection" THEN "muxer" ELSE "done"
    /\ UNCHANGED <<current, nextId, muxer, restart, old, snap,
                   stopRequested, dones, lateError>>

\* Connection shutdown then stops the muxer, which drops every receiver.
MuxerStop ==
    /\ stopper = "muxer"
    /\ muxer' = "stopped"
    /\ slot' = "empty"
    /\ stopper' = "done"
    /\ UNCHANGED <<status, current, nextId, restart, old, snap,
                   stopRequested, dones, lateError>>

\* A running instance's loops exit once the muxer has stopped.
LoopsExit ==
    /\ muxer = "stopped"
    /\ \E i \in Instances :
         /\ status[i] = "running"
         /\ status' = [status EXCEPT ![i] = "stopped"]
    /\ UNCHANGED <<current, nextId, muxer, slot, restart, old, stopper, snap,
                   stopRequested, dones, lateError>>

Finished ==
    /\ restart = "idle"
    /\ stopper = "done"
    /\ UNCHANGED vars

Next ==
    \/ RecvDone \/ StopOld \/ Install \/ StartNew
    \/ StopRead \/ StopSnap \/ MuxerStop \/ LoopsExit
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

Running == {i \in Instances : status[i] = "running"}

TypeOK ==
    /\ status \in [Instances -> {"unused", "new", "running", "stopped"}]
    /\ current \in Instances
    /\ muxer \in {"running", "stopped"}
    /\ slot \in {"empty", "registered", "suspended"}
    /\ lateError \in BOOLEAN

\* Never two keep-alive server instances reading the connection at once.
AtMostOneRunning == Cardinality(Running) <= 1

\* Once Stop has returned and no restart is in flight, nothing is still
\* serving keep-alive on a live muxer. Stop must mean stop.
StopIsEffective ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        Running = {}

\* ...and nothing is left registered in the muxer either: a suspended
\* receiver would keep buffering the client's bytes, charged against the
\* connection's ingress budget, until the connection closes.
StopReleasesSlot ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        slot = "empty"

\* A restart never starts an instance after the connection stopped the muxer.
\* The error it then raises is dropped: the connection stops reading protocol
\* errors before it stops the muxer (connection.go). The model shows the
\* window; whether it matters needs the connection in the model.
NoStartAfterClose == ~lateError
=============================================================================
