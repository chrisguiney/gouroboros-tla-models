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
(*     "Connection": Connection shutdown (connection.go stopProtocols),    *)
(*                   then muxer.Stop(). With ShutdownStopsServer it calls  *)
(*                   Server.Stop() like "Server" does; without, it read    *)
(*                   ProtocolInstance() and stopped only that instance.    *)
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
    CancelUnregisters,  \* TRUE: a restart cancelled by the guard unregisters the slot
    ShutdownStopsServer \* TRUE (gOuroboros since the fix for issue 3085): connection
                        \* shutdown calls the server's Stop. FALSE (before it): shutdown
                        \* stops only the instance it reads, and records no request.

\* The instances that can exist: the first one, plus one per restart.
\* Literally: "Instances is defined as 1 through MaxDones plus 1."
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

\* Literally: "vars is defined as the tuple of all twelve variables."
vars == <<status, current, nextId, muxer, slot, restart, old, stopper, snap,
          stopRequested, dones, lateError>>

\* In English: "At the start, instance 1 is running and registered with a
\* running muxer, and both goroutines are idle."
\* Literally: "Init is defined as: status equals the function that maps every i
\*   in Instances to (if i equals 1 then "running", else "unused"), and current
\*   equals 1, and nextId equals 2, and muxer equals "running", and slot equals
\*   "registered", and restart equals "idle", and old equals 1, and stopper
\*   equals "idle", and snap equals 1, and stopRequested equals FALSE, and
\*   dones equals 0, and lateError equals FALSE."
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
\* Literally: "Acts of i is defined as: status of i is a member of the set
\*   containing "new" and "running"."
Acts(i) == status[i] \in {"new", "running"}

-----------------------------------------------------------------------------
(* The restart goroutine. *)

\* In English: "When no restart is in progress and the current instance is
\* running, it can read a MsgDone: the restart begins, remembering which
\* instance it is replacing."
\* Literally: "RecvDone is defined as: restart equals "idle", and dones is less
\*   than MaxDones, and status of current equals "running", and restart in the
\*   next state equals "stopOld", and old in the next state equals current, and
\*   dones in the next state equals dones plus 1, and status, current, nextId,
\*   muxer, slot, stopper, snap, stopRequested and lateError are unchanged."
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
\* Literally: "StopOld is defined as: restart equals "stopOld", and if Acts of
\*   old, then (status in the next state equals status except that its old
\*   entry is "stopped", and slot in the next state equals (if slot equals
\*   "registered" then "suspended", else "empty")), else status and slot are
\*   unchanged; and restart in the next state equals "install", and current,
\*   nextId, muxer, old, stopper, snap, stopRequested, dones and lateError are
\*   unchanged."
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
\* Literally: "Install is defined as: restart equals "install", and if
\*   StopGuard is true and stopRequested is true, then (restart in the next
\*   state equals "idle", and slot in the next state equals (if
\*   CancelUnregisters then "empty", else slot), and status, current and nextId
\*   are unchanged), else (status in the next state equals status except that
\*   its nextId entry is "new", and current in the next state equals nextId,
\*   and nextId in the next state equals nextId plus 1, and restart in the next
\*   state equals "start", and slot is unchanged); and muxer, old, stopper,
\*   snap, stopRequested, dones and lateError are unchanged."
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
\* Literally: "StartNew is defined as: restart equals "start", and if status of
\*   current does not equal "new", then status, slot and lateError are
\*   unchanged; else if muxer equals "stopped", then (status in the next state
\*   equals status except that its current entry is "stopped", and lateError in
\*   the next state equals TRUE, and slot is unchanged); else (status in the
\*   next state equals status except that its current entry is "running", and
\*   slot in the next state equals "registered", and lateError is unchanged);
\*   and restart in the next state equals "idle", and current, nextId, muxer,
\*   old, stopper, snap, stopRequested and dones are unchanged."
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
\* also records that Stop was requested; so does connection shutdown, once
\* it calls Server.Stop (ShutdownStopsServer)."
\* Literally: "StopRead is defined as: stopper equals "idle", and snap in the
\*   next state equals current, and stopRequested in the next state equals
\*   (Stopper equals "Server" or ShutdownStopsServer is true), and stopper in
\*   the next state equals "stop", and status, current, nextId, muxer, slot,
\*   restart, old, dones and lateError are unchanged."
StopRead ==
    /\ stopper = "idle"                         \* the stopper has not started
    /\ snap' = current                          \* next, it holds the current instance
    /\ stopRequested' = (Stopper = "Server" \/ ShutdownStopsServer)  \* next, the flag is set if this is Server.Stop
    /\ stopper' = "stop"                        \* next, its second step is due
    /\ UNCHANGED <<status, current, nextId, muxer, slot, restart, old, dones,
                   lateError>>

\* In English: "Stop the instance it read: if that does anything, the
\* instance is stopped and the muxer slot is emptied. Connection shutdown
\* goes on to stop the muxer."
\* Literally: "StopSnap is defined as: stopper equals "stop", and if Acts of
\*   snap, then (status in the next state equals status except that its snap
\*   entry is "stopped", and slot in the next state equals "empty"), else
\*   status and slot are unchanged; and stopper in the next state equals (if
\*   Stopper equals "Connection" then "muxer", else "done"), and current,
\*   nextId, muxer, restart, old, snap, stopRequested, dones and lateError are
\*   unchanged."
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
\* Literally: "MuxerStop is defined as: stopper equals "muxer", and muxer in
\*   the next state equals "stopped", and slot in the next state equals
\*   "empty", and stopper in the next state equals "done", and status, current,
\*   nextId, restart, old, snap, stopRequested, dones and lateError are
\*   unchanged."
MuxerStop ==
    /\ stopper = "muxer"
    /\ muxer' = "stopped"
    /\ slot' = "empty"
    /\ stopper' = "done"
    /\ UNCHANGED <<status, current, nextId, restart, old, snap,
                   stopRequested, dones, lateError>>

\* In English: "Once the muxer has stopped, any running instance's loops
\* exit, one instance at a time."
\* Literally: "LoopsExit is defined as: muxer equals "stopped", and there
\*   exists an i in Instances such that status of i equals "running" and status
\*   in the next state equals status except that its i entry is "stopped"; and
\*   current, nextId, muxer, slot, restart, old, stopper, snap, stopRequested,
\*   dones and lateError are unchanged."
LoopsExit ==
    /\ muxer = "stopped"
    /\ \E i \in Instances :
         /\ status[i] = "running"
         /\ status' = [status EXCEPT ![i] = "stopped"]
    /\ UNCHANGED <<current, nextId, muxer, slot, restart, old, stopper, snap,
                   stopRequested, dones, lateError>>

\* In English: "When both goroutines are finished, nothing changes any
\* more." This tells TLC that this is an expected ending, not a deadlock.
\* Literally: "Finished is defined as: restart equals "idle", and stopper
\*   equals "done", and vars is unchanged."
Finished ==
    /\ restart = "idle"
    /\ stopper = "done"
    /\ UNCHANGED vars

\* In English: "A step is any one step of either goroutine, or loops
\* exiting, or staying finished."
\* Literally: "Next is defined as: RecvDone, or StopOld, or Install, or
\*   StartNew, or StopRead, or StopSnap, or MuxerStop, or LoopsExit, or
\*   Finished."
Next ==
    \/ RecvDone \/ StopOld \/ Install \/ StartNew
    \/ StopRead \/ StopSnap \/ MuxerStop \/ LoopsExit
    \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "the set of instances that are running."
\* Literally: "Running is defined as the set of every i in Instances such that
\*   status of i equals "running"."
Running == {i \in Instances : status[i] = "running"}

\* In English: "status, current, muxer, slot and lateError each hold the kind
\* of value they should."
\* Literally: "TypeOK is defined as: status is a member of the set of functions
\*   from Instances to the set containing "unused", "new", "running" and
\*   "stopped", and current is a member of Instances, and muxer is a member of
\*   the set containing "running" and "stopped", and slot is a member of the
\*   set containing "empty", "registered" and "suspended", and lateError is a
\*   member of BOOLEAN."
TypeOK ==
    /\ status \in [Instances -> {"unused", "new", "running", "stopped"}]
    /\ current \in Instances
    /\ muxer \in {"running", "stopped"}
    /\ slot \in {"empty", "registered", "suspended"}
    /\ lateError \in BOOLEAN

\* In English: "At most one instance is running at any moment": never two
\* keep-alive servers reading the connection at once.
\* Literally: "AtMostOneRunning is defined as: the number of members of Running
\*   is less than or equal to 1."
AtMostOneRunning == Cardinality(Running) <= 1

\* In English: "If the stopper has finished, no restart is in progress, and
\* the muxer is still running, then no instance is running." Stop must
\* mean stop.
\* Literally: "StopIsEffective is defined as: if stopper equals "done" and
\*   restart equals "idle" and muxer equals "running", then Running equals the
\*   empty set."
StopIsEffective ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        Running = {}

\* In English: "...and in that same situation, the muxer slot is empty." A
\* suspended receiver would keep buffering the client's bytes, charged
\* against the connection's ingress budget, until the connection closes.
\* Literally: "StopReleasesSlot is defined as: if stopper equals "done" and
\*   restart equals "idle" and muxer equals "running", then slot equals
\*   "empty"."
StopReleasesSlot ==
    (stopper = "done" /\ restart = "idle" /\ muxer = "running") =>
        slot = "empty"

\* In English: "A restart never tries to start an instance after the muxer
\* has stopped." The error it would raise is dropped: the connection stops
\* reading protocol errors before it stops the muxer (connection.go). The
\* model shows the window; whether it matters needs the connection in the
\* model.
\* Literally: "NoStartAfterClose is defined as: lateError is not true."
NoStartAfterClose == ~lateError
=============================================================================
