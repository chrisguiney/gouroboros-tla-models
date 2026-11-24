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
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Each goroutine is a little program counter: `restart` and `stopper`   *)
(*   name the step each goroutine will run next, like a line number. A     *)
(*   step's first lines say which step it is ("restart = ..."); the rest   *)
(*   say what changes. Symbols are explained in KeepAlive.tla's header.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets    \* numbers, and Cardinality (the size of a set)

CONSTANTS
    MaxDones,           \* how many MsgDone the client sends (each triggers a restart)
    Stopper,            \* "Server" or "Connection": who stops the server
    StopGuard,          \* TRUE: Server.Stop sets a flag that a later restart honours
    CancelUnregisters   \* TRUE: a restart cancelled by the guard unregisters the slot

\* The instances that can exist: the first one, plus one per restart.
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

\* In English: "At the start, instance 1 is running and registered with a
\* running muxer, and both goroutines are idle."
Init ==
    /\ status = [i \in Instances |-> IF i = 1 THEN "running" ELSE "unused"]  \* only instance 1 exists, running
    /\ current = 1                  \* s.Protocol is instance 1
    /\ nextId = 2                   \* the next new instance will be 2
    /\ muxer = "running"
    /\ slot = "registered"          \* instance 1 holds the muxer slot
    /\ restart = "idle"             \* no restart in progress
    /\ old = 1
    /\ stopper = "idle"             \* nobody is stopping the server yet
    /\ snap = 1
    /\ stopRequested = FALSE
    /\ dones = 0
    /\ lateError = FALSE

\* In English: "Stop or StopForRestart on instance i does something only if
\* i has not been stopped already" (Go's sync.Once).
Acts(i) == status[i] \in {"new", "running"}

-----------------------------------------------------------------------------
(* The restart goroutine. *)

\* In English: "When no restart is in progress and the current instance is
\* running, it can read a MsgDone: the restart begins, remembering which
\* instance it is replacing."
RecvDone ==
    /\ restart = "idle"                 \* no restart in progress
    /\ dones < MaxDones                 \* and the client has a MsgDone left to send
    /\ status[current] = "running"      \* and the current instance is running
    /\ restart' = "stopOld"             \* next, the restart's first step is due
    /\ old' = current                   \* next, it remembers the instance it replaces
    /\ dones' = dones + 1
    /\ UNCHANGED <<status, current, nextId, muxer, slot, stopper, snap,
                   stopRequested, lateError>>

\* Step 1, proto.StopForRestart().
\* In English: "If the old instance was not stopped yet, stop it, and
\* suspend the muxer slot (or empty it, if nothing was registered)."
StopOld ==
    /\ restart = "stopOld"              \* this is step 1
    /\ IF Acts(old)                     \* if the old instance was not stopped yet
          THEN /\ status' = [status EXCEPT ![old] = "stopped"]           \* stop it
               /\ slot' = IF slot = "registered" THEN "suspended" ELSE "empty"  \* and suspend the slot
          ELSE UNCHANGED <<status, slot>>                               \* else: nothing happens
    /\ restart' = "install"             \* next, step 2 is due
    /\ UNCHANGED <<current, nextId, muxer, old, stopper, snap,
                   stopRequested, dones, lateError>>

\* Step 2, under protocolMu.
\* In English: "If the guard is on and Stop was requested: install nothing,
\* end the restart, and (with CancelUnregisters) empty the muxer slot.
\* Otherwise: create the next instance, make it current, and go to step 3."
Install ==
    /\ restart = "install"              \* this is step 2
    /\ IF StopGuard /\ stopRequested    \* if Stop was requested
          THEN /\ restart' = "idle"     \* the restart ends here
               /\ slot' = IF CancelUnregisters THEN "empty" ELSE slot   \* and maybe releases the slot
               /\ UNCHANGED <<status, current, nextId>>
          ELSE /\ status' = [status EXCEPT ![nextId] = "new"]   \* else: a new instance exists
               /\ current' = nextId                             \* and is now current
               /\ nextId' = nextId + 1
               /\ restart' = "start"                            \* next, step 3 is due
               /\ UNCHANGED slot
    /\ UNCHANGED <<muxer, old, stopper, snap, stopRequested, dones, lateError>>

\* Step 3, start the new instance.
\* In English: "If the new instance was already stopped, nothing happens.
\* Otherwise, if the muxer has stopped, registering fails and an error is
\* raised. Otherwise it runs and holds the muxer slot. Either way the
\* restart is over."
StartNew ==
    /\ restart = "start"                \* this is step 3
    /\ IF status[current] /= "new"
          THEN UNCHANGED <<status, slot, lateError>>   \* stopped already: no-op
       ELSE IF muxer = "stopped"
          THEN /\ status' = [status EXCEPT ![current] = "stopped"]  \* it cannot register,
               /\ lateError' = TRUE                                 \* and raises an error
               /\ UNCHANGED slot
          ELSE /\ status' = [status EXCEPT ![current] = "running"]  \* it runs
               /\ slot' = "registered"                              \* and holds the slot
               /\ UNCHANGED lateError
    /\ restart' = "idle"                \* the restart is over
    /\ UNCHANGED <<current, nextId, muxer, old, stopper, snap,
                   stopRequested, dones>>

-----------------------------------------------------------------------------
(* The stopper. *)

\* In English: "The stopper reads which instance is current. Server.Stop
\* also records that Stop was requested; connection shutdown records
\* nothing."
StopRead ==
    /\ stopper = "idle"                         \* the stopper has not started
    /\ snap' = current                          \* next, it holds the current instance
    /\ stopRequested' = (Stopper = "Server")    \* next, the flag is set if this is Server.Stop
    /\ stopper' = "stop"                        \* next, its second step is due
    /\ UNCHANGED <<status, current, nextId, muxer, slot, restart, old, dones,
                   lateError>>

\* In English: "Stop the instance it read: if that does anything, the
\* instance is stopped and the muxer slot is emptied. Connection shutdown
\* goes on to stop the muxer."
StopSnap ==
    /\ stopper = "stop"                         \* this is the stopper's second step
    /\ IF Acts(snap)
          THEN /\ status' = [status EXCEPT ![snap] = "stopped"]     \* the instance stops
               /\ slot' = "empty"                                   \* and releases the slot
          ELSE UNCHANGED <<status, slot>>                           \* else: nothing happens
    /\ stopper' = IF Stopper = "Connection" THEN "muxer" ELSE "done"
    /\ UNCHANGED <<current, nextId, muxer, restart, old, snap,
                   stopRequested, dones, lateError>>

\* In English: "Connection shutdown stops the muxer, which drops every
\* receiver."
MuxerStop ==
    /\ stopper = "muxer"
    /\ muxer' = "stopped"
    /\ slot' = "empty"
    /\ stopper' = "done"
    /\ UNCHANGED <<status, current, nextId, restart, old, snap,
                   stopRequested, dones, lateError>>

\* In English: "Once the muxer has stopped, any running instance's loops
\* exit, one instance at a time."
LoopsExit ==
    /\ muxer = "stopped"
    /\ \E i \in Instances :
         /\ status[i] = "running"
         /\ status' = [status EXCEPT ![i] = "stopped"]
    /\ UNCHANGED <<current, nextId, muxer, slot, restart, old, stopper, snap,
                   stopRequested, dones, lateError>>

\* In English: "When both goroutines are finished, nothing changes any
\* more." This tells TLC that this is an expected ending, not a deadlock.
Finished ==
    /\ restart = "idle"
    /\ stopper = "done"
    /\ UNCHANGED vars

\* In English: "A step is any one step of either goroutine, or loops
\* exiting, or staying finished."
Next ==
    \/ RecvDone \/ StopOld \/ Install \/ StartNew
    \/ StopRead \/ StopSnap \/ MuxerStop \/ LoopsExit
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "the set of instances that are running."
Running == {i \in Instances : status[i] = "running"}

TypeOK ==
    /\ status \in [Instances -> {"unused", "new", "running", "stopped"}]
    /\ current \in Instances
    /\ muxer \in {"running", "stopped"}
    /\ slot \in {"empty", "registered", "suspended"}
    /\ lateError \in BOOLEAN

\* In English: "At most one instance is running at any moment": never two
\* keep-alive servers reading the connection at once.
AtMostOneRunning == Cardinality(Running) <= 1

\* In English: "If the stopper has finished, no restart is in progress, and
\* the muxer is still running, then no instance is running." Stop must
\* mean stop.
StopIsEffective ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        Running = {}

\* In English: "...and in that same situation, the muxer slot is empty." A
\* suspended receiver would keep buffering the client's bytes, charged
\* against the connection's ingress budget, until the connection closes.
StopReleasesSlot ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        slot = "empty"

\* In English: "A restart never tries to start an instance after the muxer
\* has stopped." The error it would raise is dropped: the connection stops
\* reading protocol errors before it stops the muxer (connection.go). The
\* model shows the window; whether it matters needs the connection in the
\* model.
NoStartAfterClose == ~lateError
=============================================================================
