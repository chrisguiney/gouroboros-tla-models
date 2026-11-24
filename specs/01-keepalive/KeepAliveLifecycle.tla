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
(*     2. s.initProtocol()             install a new one under protocolMu  *)
(*     3. s.Start()                    start it                            *)
(*                                                                         *)
(*   Stopper, one of:                                                      *)
(*     "Server":     Server.Stop() - read the current instance under       *)
(*                   protocolMu, then stop it.                             *)
(*     "Connection": Connection shutdown (connection.go stopProtocols) -   *)
(*                   read ProtocolInstance(), stop it, then muxer.Stop().  *)
(*                                                                         *)
(* Facts about instances (protocol/protocol.go):                           *)
(*   - Stop and StopForRestart only act once per instance (onceStop).      *)
(*   - Start on a stopped instance does nothing.                           *)
(*   - Start after the muxer stopped fails to register, and reports        *)
(*     "could not register protocol with muxer" through SendError.         *)
(*   - A running instance's loops exit once the muxer stops.               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    MaxDones,   \* how many MsgDone the client sends (each triggers a restart)
    Stopper,    \* "Server" or "Connection": who stops the server
    StopGuard   \* TRUE: Server.Stop sets a flag that a later restart honours

Instances == 1..(MaxDones + 1)

VARIABLES
    status,         \* status[i]: "unused", "new", "running", or "stopped"
    current,        \* the instance s.Protocol points at
    nextId,         \* the next instance number to hand out
    muxer,          \* "running" or "stopped"
    restart,        \* the restart goroutine's next step
    old,            \* the instance the restart is replacing
    stopper,        \* the stopper's next step
    snap,           \* the instance the stopper read
    stopRequested,  \* the flag Server.Stop sets when StopGuard is on
    dones,          \* MsgDone received so far
    lateError       \* a restart failed to register after the muxer stopped

vars == <<status, current, nextId, muxer, restart, old, stopper, snap,
          stopRequested, dones, lateError>>

Init ==
    /\ status = [i \in Instances |-> IF i = 1 THEN "running" ELSE "unused"]
    /\ current = 1
    /\ nextId = 2
    /\ muxer = "running"
    /\ restart = "idle"
    /\ old = 1
    /\ stopper = "idle"
    /\ snap = 1
    /\ stopRequested = FALSE
    /\ dones = 0
    /\ lateError = FALSE

\* Stop or StopForRestart on instance i. Only the first call does anything.
StopInst(i) ==
    IF status[i] \in {"new", "running"}
        THEN [status EXCEPT ![i] = "stopped"]
        ELSE status

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
    /\ UNCHANGED <<status, current, nextId, muxer, stopper, snap,
                   stopRequested, lateError>>

\* 1. proto.StopForRestart()
StopOld ==
    /\ restart = "stopOld"
    /\ status' = StopInst(old)
    /\ restart' = "install"
    /\ UNCHANGED <<current, nextId, muxer, old, stopper, snap,
                   stopRequested, dones, lateError>>

\* 2. s.initProtocol(): build a new instance and install it under the lock.
\*    With StopGuard, a restart that sees Stop was requested installs nothing.
Install ==
    /\ restart = "install"
    /\ IF StopGuard /\ stopRequested
          THEN /\ restart' = "idle"
               /\ UNCHANGED <<status, current, nextId>>
          ELSE /\ status' = [status EXCEPT ![nextId] = "new"]
               /\ current' = nextId
               /\ nextId' = nextId + 1
               /\ restart' = "start"
    /\ UNCHANGED <<muxer, old, stopper, snap, stopRequested, dones, lateError>>

\* 3. s.Start()
StartNew ==
    /\ restart = "start"
    /\ IF status[current] /= "new"
          THEN UNCHANGED <<status, lateError>>       \* stopped already: no-op
       ELSE IF muxer = "stopped"
          THEN /\ status' = [status EXCEPT ![current] = "stopped"]
               /\ lateError' = TRUE                  \* registration failed
          ELSE /\ status' = [status EXCEPT ![current] = "running"]
               /\ UNCHANGED lateError
    /\ restart' = "idle"
    /\ UNCHANGED <<current, nextId, muxer, old, stopper, snap,
                   stopRequested, dones>>

-----------------------------------------------------------------------------
(* The stopper. *)

\* Read the current instance under the lock. Server.Stop also records the
\* request when StopGuard is on; connection shutdown reads ProtocolInstance()
\* and records nothing.
StopRead ==
    /\ stopper = "idle"
    /\ snap' = current
    /\ stopRequested' = (Stopper = "Server")
    /\ stopper' = "stop"
    /\ UNCHANGED <<status, current, nextId, muxer, restart, old, dones,
                   lateError>>

StopSnap ==
    /\ stopper = "stop"
    /\ status' = StopInst(snap)
    /\ stopper' = IF Stopper = "Connection" THEN "muxer" ELSE "done"
    /\ UNCHANGED <<current, nextId, muxer, restart, old, snap,
                   stopRequested, dones, lateError>>

\* Connection shutdown then stops the muxer.
MuxerStop ==
    /\ stopper = "muxer"
    /\ muxer' = "stopped"
    /\ stopper' = "done"
    /\ UNCHANGED <<status, current, nextId, restart, old, snap,
                   stopRequested, dones, lateError>>

\* A running instance's loops exit once the muxer has stopped.
LoopsExit ==
    /\ muxer = "stopped"
    /\ \E i \in Instances :
         /\ status[i] = "running"
         /\ status' = [status EXCEPT ![i] = "stopped"]
    /\ UNCHANGED <<current, nextId, muxer, restart, old, stopper, snap,
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
    /\ lateError \in BOOLEAN

\* Never two keep-alive server instances reading the connection at once.
AtMostOneRunning == Cardinality(Running) <= 1

\* Once Stop has returned and no restart is in flight, nothing is still
\* serving keep-alive on a live muxer. Stop must mean stop.
StopIsEffective ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        Running = {}

\* Closing a connection cleanly never makes a restart report an error.
NoErrorFromClose == ~lateError
=============================================================================
