-------------------------- MODULE BlockFetchRestart --------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 5: starting the block-fetch client again      *)
(* while the previous protocol instance still has a goroutine running a    *)
(* callback (hazard B3, "Start and a second generation").                  *)
(*                                                                         *)
(* gOuroboros file: protocol/blockfetch/client.go (Start, stop,            *)
(* joinProtocol, startShutdownWatcher, failOutstandingOnProtocolDone,      *)
(* watchRangeDeadline) and protocol/blockfetch/goroutines.go, at           *)
(* blinklabs-io/gouroboros 7cd17437.                                       *)
(*                                                                         *)
(* What the code does [G1]:                                                *)
(*   Each protocol instance (a "generation") has two goroutines that run   *)
(*   RangeDoneFunc for its ranges once it is stopping:                     *)
(*   - the shutdown watcher, a loop of the protocol instance (RunLoop),    *)
(*     which waits for DoneChan and resolves what is still queued;         *)
(*   - a range deadline watcher, in the client's own goroutine group,      *)
(*     which, when the range's timer fires, takes the range out of the     *)
(*     queue, stops the protocol (SendError) and resolves it.              *)
(*   Stop marks the client stopped, signals the protocol, releases         *)
(*   lifecycleMutex, then joins the protocol's loops and the group, unless *)
(*   its context ends first, when it returns ctx.Err() and shutdown goes   *)
(*   on without it.                                                        *)
(*   Start, finding the client stopped, waits for the old instance's       *)
(*   loops (oldProto.Stop(context.Background()) and DoneChan) and then     *)
(*   installs a new instance. On main it does not wait for the old         *)
(*   group; with the fix (StartJoinsGroup) it does.                        *)
(*                                                                         *)
(* Question: can a callback of generation g run once generation g+1 has    *)
(* been started? (NoOldGenCallbackAfterStart, proposed for hazard B3 in    *)
(* CONCURRENCY.md.)                                                        *)
(*                                                                         *)
(* Sources: there is no rule in the specification or the reference for     *)
(* this; it is gOuroboros's own contract. [G1] Start's comment, "ensure    *)
(* the old instance is fully stopped before re-registering", and Stop's    *)
(* doc comment, "no callback of the stopped protocol is still running".    *)
(* UNSOURCED in the network specification: the reference fetch client has *)
(* no completion callback and no restart of a client on one connection.    *)
(*                                                                         *)
(* One range per generation, armed when the generation starts. A range is  *)
(* resolved by exactly one of the two watchers: whichever takes it out of  *)
(* the queue under queueMutex first (BlockFetchBusyDelivery.tla checks     *)
(* that part, RangeDoneOnce).                                              *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `stopPc` and `startPc` are program counters.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    MaxGen,          \* generations the client may run (2: one restart)
    StopCtxMayExpire,\* TRUE: Stop's context may end before its join
    ConcurrentStart, \* TRUE: Start may run while a Stop is still joining
    StartJoinsGroup, \* TRUE: the fix, Start also waits for the old group
    CbRestarts       \* TRUE: a deadline callback stops the client with its
                     \* own context and then calls Start (documented as not
                     \* allowed once Start joins the group)

Gens == 1..MaxGen

VARIABLES
    gen,      \* the generation c.Protocol is
    life,     \* client lifecycle: "running", "stopped", "starting"
    loops,    \* loops[g]: "run", "stopping" (signalled), "swcb" (shutdown
              \* watcher in RangeDoneFunc), "done" (every loop returned)
    dl,       \* dl[g]: the deadline watcher: "none", "armed", "cb" (in
              \* RangeDoneFunc), "done" (returned)
    queued,   \* queued[g]: generation g's range is still in the queue
    stopPc,   \* the Stop caller: "idle" or "join"
    stopGen,  \* the generation that Stop is joining
    startPc,  \* the Start caller: "idle" or "wait"
    startOld, \* the generation Start is waiting for
    cbStart   \* TRUE while the Start in progress was called from a callback

vars == <<gen, life, loops, dl, queued, stopPc, stopGen, startPc, startOld,
          cbStart>>

\* In English: "Generation 1 is running with one range queued and its
\* deadline armed; nobody is stopping or starting."
\* Literally: "Init is defined as: gen equals 1, and life equals "running",
\*   and loops is the function giving "run" to 1 and "done" to every other
\*   generation, and dl gives "armed" to 1 and "none" to every other, and
\*   queued gives TRUE to 1 and FALSE to every other, and stopPc and startPc
\*   equal "idle", and stopGen and startOld equal 0, and cbStart is FALSE."
Init ==
    /\ gen = 1
    /\ life = "running"
    /\ loops = [g \in Gens |-> IF g = 1 THEN "run" ELSE "done"]
    /\ dl = [g \in Gens |-> IF g = 1 THEN "armed" ELSE "none"]
    /\ queued = [g \in Gens |-> g = 1]
    /\ stopPc = "idle" /\ stopGen = 0
    /\ startPc = "idle" /\ startOld = 0
    /\ cbStart = FALSE

-----------------------------------------------------------------------------
(* The protocol instance and its shutdown watcher [G1 startShutdownWatcher].*)

\* In English: "A stopping instance's receive and send loops return
\* (DoneChan closes); its shutdown watcher wakes, and if the range is still
\* queued it takes it and runs RangeDoneFunc, otherwise every loop is done."
\* Literally: "LoopsWind(g) is defined as: loops[g] equals "stopping", and
\*   if queued[g] then loops' maps g to "swcb" and queued' maps g to FALSE,
\*   else loops' maps g to "done" and queued is unchanged; and the other
\*   variables are unchanged."
LoopsWind(g) ==
    /\ loops[g] = "stopping"
    /\ IF queued[g]
          THEN /\ loops' = [loops EXCEPT ![g] = "swcb"]
               /\ queued' = [queued EXCEPT ![g] = FALSE]
          ELSE /\ loops' = [loops EXCEPT ![g] = "done"]
               /\ UNCHANGED queued
    /\ UNCHANGED <<gen, life, dl, stopPc, stopGen, startPc, startOld, cbStart>>

\* In English: "The shutdown watcher's RangeDoneFunc returns; it is the last
\* loop, so the instance's loops are all done."
\* Literally: "SwCbEnd(g) is defined as: loops[g] equals "swcb", and loops'
\*   maps g to "done", and the other variables are unchanged."
SwCbEnd(g) ==
    /\ loops[g] = "swcb"
    /\ loops' = [loops EXCEPT ![g] = "done"]
    /\ UNCHANGED <<gen, life, dl, queued, stopPc, stopGen, startPc, startOld,
                   cbStart>>

-----------------------------------------------------------------------------
(* The range deadline watcher [G1 watchRangeDeadline], in the group.      *)

\* In English: "The range's timer fires while the range is still queued: the
\* watcher takes it out of the queue, stops the protocol (SendError) and
\* enters RangeDoneFunc."
\* Literally: "DeadlineFire(g) is defined as: dl[g] equals "armed", and
\*   queued[g] is true, and dl' maps g to "cb", and queued' maps g to FALSE,
\*   and loops' maps g to "stopping" if it was "run" and leaves it alone
\*   otherwise, and the other variables are unchanged."
DeadlineFire(g) ==
    /\ dl[g] = "armed" /\ queued[g]
    /\ dl' = [dl EXCEPT ![g] = "cb"]
    /\ queued' = [queued EXCEPT ![g] = FALSE]
    /\ loops' = [loops EXCEPT ![g] = IF @ = "run" THEN "stopping" ELSE @]
    /\ UNCHANGED <<gen, life, stopPc, stopGen, startPc, startOld, cbStart>>

\* In English: "The watcher returns without a callback: the range left the
\* queue some other way, or the instance is done."
\* Literally: "DeadlineQuiet(g) is defined as: dl[g] equals "armed", and
\*   (queued[g] is false or loops[g] is one of "swcb", "done"), and dl' maps
\*   g to "done", and the other variables are unchanged."
DeadlineQuiet(g) ==
    /\ dl[g] = "armed"
    /\ ~queued[g] \/ loops[g] \in {"swcb", "done"}
    /\ dl' = [dl EXCEPT ![g] = "done"]
    /\ UNCHANGED <<gen, life, loops, queued, stopPc, stopGen, startPc,
                   startOld, cbStart>>

\* In English: "The deadline's RangeDoneFunc returns, unless it is itself
\* waiting inside the Start it called."
\* Literally: "DeadlineCbEnd(g) is defined as: dl[g] equals "cb", and not
\*   (cbStart is true and startPc equals "wait"), and dl' maps g to "done",
\*   and the other variables are unchanged."
DeadlineCbEnd(g) ==
    /\ dl[g] = "cb"
    /\ ~(cbStart /\ startPc = "wait")
    /\ dl' = [dl EXCEPT ![g] = "done"]
    /\ UNCHANGED <<gen, life, loops, queued, stopPc, stopGen, startPc,
                   startOld, cbStart>>

\* In English: "With CbRestarts, the deadline's callback stops the running
\* client with its own context (Stop returns at once) and calls Start."
\* Literally: "CbRestart(g) is defined as: CbRestarts is true, and dl[g]
\*   equals "cb", and g equals gen, and life equals "running", and stopPc
\*   and startPc equal "idle", and gen is less than MaxGen, and life' equals
\*   "starting", and loops' maps g to "stopping" if it was "run", and
\*   startPc' equals "wait", and startOld' equals g, and cbStart' is TRUE,
\*   and the other variables are unchanged."
CbRestart(g) ==
    /\ CbRestarts
    /\ dl[g] = "cb" /\ g = gen /\ life = "running"
    /\ stopPc = "idle" /\ startPc = "idle" /\ gen < MaxGen
    /\ life' = "starting"
    /\ loops' = [loops EXCEPT ![g] = IF @ = "run" THEN "stopping" ELSE @]
    /\ startPc' = "wait" /\ startOld' = g /\ cbStart' = TRUE
    /\ UNCHANGED <<gen, dl, queued, stopPc, stopGen>>

-----------------------------------------------------------------------------
(* Stop and Start [G1].                                                    *)

\* In English: "Stop of the running client: under lifecycleMutex it marks
\* the client stopped and signals the protocol, then releases the lock and
\* joins."
\* Literally: "StopBegin is defined as: stopPc equals "idle", and life
\*   equals "running", and life' equals "stopped", and loops' maps gen to
\*   "stopping" if it was "run", and stopPc' equals "join", and stopGen'
\*   equals gen, and the other variables are unchanged."
StopBegin ==
    /\ stopPc = "idle" /\ life = "running"
    /\ life' = "stopped"
    /\ loops' = [loops EXCEPT ![gen] = IF @ = "run" THEN "stopping" ELSE @]
    /\ stopPc' = "join" /\ stopGen' = gen
    /\ UNCHANGED <<gen, dl, queued, startPc, startOld, cbStart>>

\* In English: "Stop's join finishes: the loops and every goroutine of the
\* group have returned."
\* Literally: "StopJoined is defined as: stopPc equals "join", and
\*   loops[stopGen] equals "done", and dl[stopGen] is "none" or "done", and
\*   stopPc' equals "idle", and the other variables are unchanged."
StopJoined ==
    /\ stopPc = "join"
    /\ loops[stopGen] = "done" /\ dl[stopGen] \in {"none", "done"}
    /\ stopPc' = "idle"
    /\ UNCHANGED <<gen, life, loops, dl, queued, stopGen, startPc, startOld,
                   cbStart>>

\* In English: "Stop's context ends before the join: it returns ctx.Err()."
\* Literally: "StopExpires is defined as: StopCtxMayExpire is true, and
\*   stopPc equals "join", and stopPc' equals "idle", and the other variables
\*   are unchanged."
StopExpires ==
    /\ StopCtxMayExpire /\ stopPc = "join"
    /\ stopPc' = "idle"
    /\ UNCHANGED <<gen, life, loops, dl, queued, stopGen, startPc, startOld,
                   cbStart>>

\* In English: "Start finds the client stopped and starts waiting for the
\* old instance. Unless ConcurrentStart, nobody is still in Stop."
\* Literally: "StartBegin is defined as: startPc equals "idle", and life
\*   equals "stopped", and gen is less than MaxGen, and (ConcurrentStart is
\*   true or stopPc equals "idle"), and life' equals "starting", and
\*   startPc' equals "wait", and startOld' equals gen, and the other
\*   variables are unchanged."
StartBegin ==
    /\ startPc = "idle" /\ life = "stopped" /\ gen < MaxGen
    /\ ConcurrentStart \/ stopPc = "idle"
    /\ life' = "starting"
    /\ startPc' = "wait" /\ startOld' = gen
    /\ UNCHANGED <<gen, loops, dl, queued, stopPc, stopGen, cbStart>>

\* In English: "Start's wait ends - the old loops are done and, with the
\* fix, so is the old group - and it installs and starts the next
\* generation, whose range is queued and armed."
\* Literally: "StartFinish is defined as: startPc equals "wait", and
\*   loops[startOld] equals "done", and (StartJoinsGroup implies dl[startOld]
\*   is "none" or "done"), and gen' equals gen plus 1, and life' equals
\*   "running", and loops', dl' and queued' map the new generation to "run",
\*   "armed" and TRUE, and startPc' equals "idle", and cbStart' is FALSE,
\*   and the other variables are unchanged."
StartFinish ==
    /\ startPc = "wait"
    /\ loops[startOld] = "done"
    /\ StartJoinsGroup => dl[startOld] \in {"none", "done"}
    /\ gen' = gen + 1
    /\ life' = "running"
    /\ loops' = [loops EXCEPT ![gen + 1] = "run"]
    /\ dl' = [dl EXCEPT ![gen + 1] = "armed"]
    /\ queued' = [queued EXCEPT ![gen + 1] = TRUE]
    /\ startPc' = "idle" /\ cbStart' = FALSE
    /\ UNCHANGED <<stopPc, stopGen, startOld>>

-----------------------------------------------------------------------------

\* In English: "Nothing is left to do: no goroutine is in a callback or
\* waiting, and the last generation is stopped and wound down, or running
\* untouched."
\* Literally: "Finished is defined as: stopPc and startPc equal "idle", and
\*   for every generation g, loops[g] is "run" or "done" and dl[g] is not
\*   "cb"; and the other variables are unchanged."
Finished ==
    /\ stopPc = "idle" /\ startPc = "idle"
    /\ \A g \in Gens : loops[g] \in {"run", "done"} /\ dl[g] /= "cb"
    /\ UNCHANGED vars

\* In English: "A step is one step of any goroutine, or nothing left to do."
\* Literally: "Next is defined as: there is a generation g for which
\*   LoopsWind(g), SwCbEnd(g), DeadlineFire(g), DeadlineQuiet(g),
\*   DeadlineCbEnd(g) or CbRestart(g) is a step; or StopBegin, StopJoined,
\*   StopExpires, StartBegin or StartFinish is a step; or Finished."
Next ==
    \/ \E g \in Gens :
          \/ LoopsWind(g) \/ SwCbEnd(g)
          \/ DeadlineFire(g) \/ DeadlineQuiet(g) \/ DeadlineCbEnd(g)
          \/ CbRestart(g)
    \/ StopBegin \/ StopJoined \/ StopExpires
    \/ StartBegin \/ StartFinish
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Every variable holds a value of the right kind."
\* Literally: "TypeOK is defined as: gen is in Gens, and life is one of the
\*   three lifecycle states, and loops, dl and queued are functions from
\*   Gens to their states, and the program counters are in their sets."
TypeOK ==
    /\ gen \in Gens
    /\ life \in {"running", "stopped", "starting"}
    /\ loops \in [Gens -> {"run", "stopping", "swcb", "done"}]
    /\ dl \in [Gens -> {"none", "armed", "cb", "done"}]
    /\ queued \in [Gens -> BOOLEAN]
    /\ stopPc \in {"idle", "join"} /\ stopGen \in 0..MaxGen
    /\ startPc \in {"idle", "wait"} /\ startOld \in 0..MaxGen
    /\ cbStart \in BOOLEAN

\* In English: "No callback of an older generation is running once a newer
\* generation has been started."
\* Literally: "NoOldGenCallbackAfterStart is defined as: for every g in 1
\*   through gen minus 1, dl[g] is not "cb" and loops[g] is not "swcb"."
NoOldGenCallbackAfterStart ==
    \A g \in 1..(gen - 1) : dl[g] /= "cb" /\ loops[g] /= "swcb"

\* Probes, each EXPECTED to be violated (reachability).
\* In English: "The client is never restarted." Violated = it is.
\* Literally: "ProbeNeverRestarts is defined as: gen equals 1."
ProbeNeverRestarts == gen = 1
\* In English: "Start never waits while the old deadline callback runs."
\* Violated = it does: the window the fix closes is reached.
\* Literally: "ProbeNoStartDuringOldCallback is defined as: not (startPc
\*   equals "wait" and dl[startOld] equals "cb")."
ProbeNoStartDuringOldCallback == ~(startPc = "wait" /\ dl[startOld] = "cb")
=============================================================================
