------------------------- MODULE BlockFetchBusyHandoff -------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 10: the busy lock of the one-at-a-time        *)
(* fetches (GetBlockRange, GetBlock) across Stop and Start.                *)
(*                                                                         *)
(* gOuroboros file: protocol/blockfetch/client.go (acquireBusy,            *)
(* releaseBusy, heldBusyToken, releaseBusyOnProtocolDone, GetBlockRange,   *)
(* GetBlock, awaitBlock, resolve, stop), at blinklabs-io/gouroboros        *)
(* 7cd17437.                                                               *)
(*                                                                         *)
(* What the code does [G1]:                                                *)
(*   acquireBusy locks busyMutex and, under busyStateMutex, records a new  *)
(*   token as the holder. releaseBusy(t) unlocks busyMutex only if t is    *)
(*   the holder's token, so a stale token releases nothing. The fetch then *)
(*   reads the client's current protocol instance and sends its request   *)
(*   on it; if that instance is already stopping, the send fails and the   *)
(*   fetch releases its own token. Otherwise its token is released when    *)
(*   the request resolves, or when that instance is done (the busy         *)
(*   releaser of GetBlockRange, the waits of GetBlock).                    *)
(*   Stop records the token held when it stops the protocol (heldBusyToken) *)
(*   and, once it has joined, releases it.                                 *)
(*   A client begins with an instance that is not started (clientStateNew).*)
(*   A send on it is queued: it neither fails nor is answered until the    *)
(*   instance is started or stopped. Stop in a state other than running    *)
(*   did not stop that instance; Start after it installs a new one.        *)
(*   Stopping an instance unregisters its role from the muxer, which        *)
(*   removes whichever instance is registered for that role.               *)
(*                                                                         *)
(* The fix (branch fix/blockfetch-busy-across-restart): Stop releases no   *)
(* token, and Stop of a never-started client stops that instance under    *)
(* lifecycleMutex, so a send on it fails and Start's later registration    *)
(* cannot be removed by it.                                                *)
(*                                                                         *)
(* Question: is at most one fetch in progress at a time, as GetBlockRange's *)
(* doc comment says ("a second call blocks until the first batch          *)
(* completes"), and is the lock always free in the end?                    *)
(*                                                                         *)
(* Sources: the busy lock is gOuroboros's own [G1]; the reference has no   *)
(* synchronous fetch. UNSOURCED in the network specification.              *)
(*   [G1] is 7cd17437; the never-started branch is stop() 609-640 and      *)
(*        Start 413-497 (initProtocol after clientStateStopped) at the fix. *)
(*   [G1] protocol/blockfetch/client.go 363-413 (acquireBusy, releaseBusy, *)
(*        heldBusyToken, releaseBusyOnProtocolDone), 604-702 (stop:        *)
(*        heldBusyToken at 617 and 669, releaseBusy at 636 and 689),       *)
(*        717-804 (GetBlockRange, GetBlock), 1142 (the instance read).     *)
(*                                                                         *)
(* One answer stands for a whole batch. Stop is the running branch and     *)
(* joins at once (BlockFetchRestart.tla covers what the join waits for).   *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `pc` is a program counter per fetch, `spc` for Stop.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Fetches,          \* the fetching goroutines, e.g. {1, 2}
    MaxGen,           \* generations (2: one restart)
    StopReleasesBusy,  \* TRUE on main: Stop releases the token it recorded;
                       \* FALSE: the fix, which leaves every token to its
                       \* own fetch
    StopsNeverStarted, \* TRUE: Stop of a never-started client stops that
                       \* instance (the fix); FALSE: it leaves it alone
    StopNewLocked      \* TRUE: that stop happens under lifecycleMutex
                       \* (the fix); FALSE: after the mutex is released

VARIABLES
    gen,     \* the client's current instance
    life,    \* "new" (never started), "running" or "stopped"
    started, \* started[g]: instance g was started, so it answers
    reg,     \* the instance registered with the muxer, 0 when none
    done,    \* done[g]: instance g is stopped
    holder,  \* the token busyStateMutex records as held, 0 when free
    next,    \* the last token handed out
    pc,      \* pc[f]: "idle", "acq" (holds a token, has not read the
             \* instance), "wait" (request on instance on[f]), "fin"
    tok,     \* tok[f]: f's token
    on,      \* on[f]: the instance f's request went out on
    spc,     \* Stop: "idle", "signal" (never-started instance still to
             \* stop, lifecycleMutex released), "joined"
    snap     \* the token Stop recorded

vars == <<gen, life, started, reg, done, holder, next, pc, tok, on, spc, snap>>

\* In English: "Release token t: only the holder's token unlocks."
\* Literally: "Release(t) is defined as: holder' equals 0 if holder equals t
\*   and t is not 0, and holder otherwise."
Release(t) == holder' = IF holder = t /\ t /= 0 THEN 0 ELSE holder

\* Literally: "Init is defined as: gen equals 1, life is "new" or
\*   "running", instance 1 is started and registered exactly when life is
\*   "running", no instance is done, holder and next are 0, every fetch is
\*   "idle" with token 0 on instance 0, spc equals "idle", and snap equals 0."
Init ==
    /\ gen = 1 /\ life \in {"new", "running"}
    /\ started = [g \in 1..MaxGen |-> g = 1 /\ life = "running"]
    /\ reg = IF life = "running" THEN 1 ELSE 0
    /\ done = [g \in 1..MaxGen |-> FALSE]
    /\ holder = 0 /\ next = 0
    /\ pc = [f \in Fetches |-> "idle"]
    /\ tok = [f \in Fetches |-> 0] /\ on = [f \in Fetches |-> 0]
    /\ spc = "idle" /\ snap = 0

\* In English: "Fetch f takes the busy lock with a new token."
\* Literally: "Acquire(f) is defined as: pc[f] equals "idle", and holder
\*   equals 0, and next' is next plus 1, and holder' and tok'[f] are next',
\*   and pc' maps f to "acq", and the other variables are unchanged."
Acquire(f) ==
    /\ pc[f] = "idle" /\ holder = 0
    /\ next' = next + 1
    /\ holder' = next + 1
    /\ tok' = [tok EXCEPT ![f] = next + 1]
    /\ pc' = [pc EXCEPT ![f] = "acq"]
    /\ UNCHANGED <<gen, life, started, reg, done, on, spc, snap>>

\* In English: "Fetch f reads the current instance and sends on it; a
\* stopped instance refuses, and f releases its own token. A never-started
\* instance takes the send and leaves it waiting."
\* Literally: "SendOn(f) is defined as: pc[f] equals "acq", and if done[gen]
\*   then Release(tok[f]) and pc' maps f to "fin" and on is unchanged, else
\*   on' maps f to gen and pc' maps f to "wait" and holder is unchanged; and
\*   the other variables are unchanged."
SendOn(f) ==
    /\ pc[f] = "acq"
    /\ IF done[gen]
          THEN /\ Release(tok[f])
               /\ pc' = [pc EXCEPT ![f] = "fin"]
               /\ UNCHANGED on
          ELSE /\ on' = [on EXCEPT ![f] = gen]
               /\ pc' = [pc EXCEPT ![f] = "wait"]
               /\ UNCHANGED holder
    /\ UNCHANGED <<gen, life, started, reg, done, next, tok, spc, snap>>

\* In English: "Fetch f's request resolves, by its answer (its instance
\* was started) or because its instance is done; f's token is released."
\* Literally: "Finish(f) is defined as: pc[f] equals "wait", and instance
\*   on[f] is started or done, and Release(tok[f]), and pc' maps f to "fin",
\*   and the other variables are unchanged."
Finish(f) ==
    /\ pc[f] = "wait"
    /\ started[on[f]] \/ done[on[f]]
    /\ Release(tok[f])
    /\ pc' = [pc EXCEPT ![f] = "fin"]
    /\ UNCHANGED <<gen, life, started, reg, done, next, tok, on, spc, snap>>

\* In English: "Stop of the running client: it records the held token and
\* stops the instance, which unregisters the role; the join completes."
\* Literally: "StopJoin is defined as: spc equals "idle", and life equals
\*   "running", and life' equals "stopped", and done' maps gen to TRUE, and
\*   reg' equals 0, and snap' equals holder, and spc' equals "joined", and
\*   the other variables are unchanged."
StopJoin ==
    /\ spc = "idle" /\ life = "running"
    /\ life' = "stopped"
    /\ done' = [done EXCEPT ![gen] = TRUE]
    /\ reg' = 0
    /\ snap' = holder
    /\ spc' = "joined"
    /\ UNCHANGED <<gen, started, holder, next, pc, tok, on>>

\* In English: "Stop of a never-started client, under lifecycleMutex: it
\* records the held token and marks the client stopped. With
\* StopsNeverStarted and StopNewLocked it also stops the instance here;
\* with StopsNeverStarted alone it stops it after releasing the mutex."
\* Literally: "StopNew is defined as: spc equals "idle", and life equals
\*   "new", and life' equals "stopped", and snap' equals holder, and if
\*   StopsNeverStarted and StopNewLocked then done' maps gen to TRUE and
\*   reg' equals 0 and spc' equals "joined"; if StopsNeverStarted alone then
\*   spc' equals "signal" and done and reg are unchanged; otherwise spc'
\*   equals "joined" and done and reg are unchanged; and the other
\*   variables are unchanged."
StopNew ==
    /\ spc = "idle" /\ life = "new"
    /\ life' = "stopped"
    /\ snap' = holder
    /\ IF StopsNeverStarted /\ StopNewLocked
          THEN /\ done' = [done EXCEPT ![gen] = TRUE]
               /\ reg' = 0
               /\ spc' = "joined"
          ELSE /\ spc' = IF StopsNeverStarted THEN "signal" ELSE "joined"
               /\ UNCHANGED <<done, reg>>
    /\ UNCHANGED <<gen, started, holder, next, pc, tok, on>>

\* In English: "With lifecycleMutex released, Stop stops the never-started
\* instance 1 (the only one a client starts out with); unregistering its
\* role removes whatever is registered, which may be the instance a
\* concurrent Start installed."
\* Literally: "StopSignal is defined as: spc equals "signal", and done'
\*   maps 1 to TRUE, and reg' equals 0, and spc' equals "joined", and the
\*   other variables are unchanged."
StopSignal ==
    /\ spc = "signal"
    /\ done' = [done EXCEPT ![1] = TRUE]
    /\ reg' = 0
    /\ spc' = "joined"
    /\ UNCHANGED <<gen, life, started, holder, next, pc, tok, on, snap>>

\* In English: "Stop releases the token it recorded (main), or nothing
\* (the fix), and returns."
\* Literally: "StopRelease is defined as: spc equals "joined", and if
\*   StopReleasesBusy then Release(snap) else holder is unchanged, and spc'
\*   equals "idle", and the other variables are unchanged."
StopRelease ==
    /\ spc = "joined"
    /\ IF StopReleasesBusy THEN Release(snap) ELSE UNCHANGED holder
    /\ spc' = "idle"
    /\ UNCHANGED <<gen, life, started, reg, done, next, pc, tok, on, snap>>

\* In English: "Start of a new client starts its instance; Start of a
\* stopped client installs the next one. Either way the started instance
\* is registered."
\* Literally: "Start is defined as: life equals "new" and gen' equals gen,
\*   or life equals "stopped" and gen is less than MaxGen and gen' is gen
\*   plus 1; and life' equals "running", and started' maps gen' to TRUE,
\*   and reg' equals gen', and the other variables are unchanged."
Start ==
    /\ \/ life = "new" /\ gen' = gen
       \/ life = "stopped" /\ gen < MaxGen /\ gen' = gen + 1
    /\ life' = "running"
    /\ started' = [started EXCEPT ![gen'] = TRUE]
    /\ reg' = gen'
    /\ UNCHANGED <<done, holder, next, pc, tok, on, spc, snap>>

\* In English: "Nothing left to do: every fetch finished or never started,
\* Stop is not mid-way, and the lock is free."
\* Literally: "Finished is defined as: every fetch is "idle" or "fin", spc
\*   equals "idle", holder equals 0, and the variables are unchanged."
Finished ==
    /\ \A f \in Fetches : pc[f] \in {"idle", "fin"}
    /\ spc = "idle" /\ holder = 0
    /\ UNCHANGED vars

\* Literally: "Next is defined as: some fetch f takes Acquire(f), SendOn(f)
\*   or Finish(f), or StopJoin, StopNew, StopSignal, StopRelease or Start
\*   is a step, or Finished."
Next ==
    \/ \E f \in Fetches : Acquire(f) \/ SendOn(f) \/ Finish(f)
    \/ StopJoin \/ StopNew \/ StopSignal \/ StopRelease \/ Start
    \/ Finished

Spec == Init /\ [][Next]_vars

\* In English: "Every enabled step but a new Acquire is eventually taken.
\* Start and Stop are bounded by MaxGen, so their fairness only says a
\* client is not left new forever."
FairSpec ==
    /\ Spec
    /\ \A f \in Fetches : WF_vars(SendOn(f)) /\ WF_vars(Finish(f))
    /\ WF_vars(StopJoin) /\ WF_vars(StopNew) /\ WF_vars(StopSignal)
    /\ WF_vars(StopRelease) /\ WF_vars(Start)

\* In English: "Each variable holds a value of the right kind."
TypeOK ==
    /\ gen \in 1..MaxGen /\ life \in {"new", "running", "stopped"}
    /\ started \in [1..MaxGen -> BOOLEAN] /\ reg \in 0..MaxGen
    /\ pc \in [Fetches -> {"idle", "acq", "wait", "fin"}]
    /\ holder \in 0..next /\ spc \in {"idle", "signal", "joined"}

\* In English: "At most one fetch is in progress (holding a token it has
\* not yet given back)."
\* Literally: "OneFetchAtATime is defined as: the number of fetches whose pc
\*   is "acq" or "wait" is at most 1."
OneFetchAtATime ==
    Cardinality({f \in Fetches : pc[f] \in {"acq", "wait"}}) <= 1

\* In English: "The recorded holder is a fetch in progress, if any."
\* Literally: "HolderIsInProgress is defined as: holder equals 0, or some
\*   fetch f in "acq" or "wait" has token holder."
HolderIsInProgress ==
    holder = 0 \/ \E f \in Fetches : pc[f] \in {"acq", "wait"} /\ tok[f] = holder

\* In English: "While the client runs, its current instance is the one
\* registered: no Stop removed the registration Start installed."
\* Literally: "RegisteredWhileRunning is defined as: if life equals
\*   "running" then reg equals gen."
RegisteredWhileRunning == life = "running" => reg = gen

\* In English: "A fetch that holds the lock eventually gives it back."
\* Literally: "CallerAlwaysReleased is defined as: for every fetch f, f in
\*   "acq" or "wait" leads to f in "fin"."
CallerAlwaysReleased ==
    \A f \in Fetches : pc[f] \in {"acq", "wait"} ~> pc[f] = "fin"

\* In English: "The busy lock is eventually free."
BusyEventuallyFree == <>[](holder = 0)

\* Probe, EXPECTED to be violated (reachability).
\* In English: "No fetch sends on a later instance than the one current when
\* it took the lock." Violated = a fetch outlives a restart before sending.
\* Literally: "ProbeNoFetchAcrossRestart is defined as: for every fetch f
\*   that is "wait", on[f] equals 1."
ProbeNoFetchAcrossRestart == \A f \in Fetches : pc[f] = "wait" => on[f] = 1
=============================================================================
