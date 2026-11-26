-------------------------- MODULE PooledEvalContext --------------------------
(***************************************************************************)
(* gOuroboros' Plutus evaluation pools (ledger/common/plutus_machine_pool.go *)
(* at gOuroboros 7cd17437), with evaluations running on several goroutines *)
(* under two cost models.                                                  *)
(*                                                                         *)
(*   [G1] PooledEvalContext 138-157: look the tuple (language, protocol    *)
(*        major, cost model list) up in a bounded LRU cache under its      *)
(*        mutex; on a miss build an EvalContext with the lock released,    *)
(*        then loadOrStoreEvalContext 99-124 stores it unless another      *)
(*        caller stored one first (and then returns that one), evicting   *)
(*        the least recently used entry past the limit.                    *)
(*   [G2] machinePoolFor 246-266: the Machine pool is a sync.Map keyed by *)
(*        (language, weak pointer to the EvalContext); the goroutine that  *)
(*        creates an entry registers runtime.AddCleanup to delete it once  *)
(*        the EvalContext is collected.                                    *)
(*   [G3] checkoutMachineReused 274-287 takes an idle Machine of the entry *)
(*        under the entry's mutex, or builds one from the caller's         *)
(*        EvalContext; runPooledPreparedContext 328-346 runs it (Run is    *)
(*        synchronous) and only then releaseMachine puts it back.          *)
(*                                                                         *)
(* An EvalContext is read-only once built (plutigo cek/eval_context.go),   *)
(* so sharing one between concurrent evaluations is intended; what must   *)
(* never be shared is a Machine. The questions: is a Machine ever run by  *)
(* two evaluations at once; is a Machine ever run for a tuple other than  *)
(* the one it was built for; does an evaluation ever get an EvalContext   *)
(* for a tuple other than the one it asked for.                            *)
(*                                                                         *)
(* The garbage collector is a step that may collect any EvalContext no    *)
(* cache entry and no evaluation holds, freeing its address for a later   *)
(* EvalContext; the cleanup runs as a later, separate step.               *)
(*                                                                         *)
(* Mutations (each a Bug cfg; the code at 7cd17437 passes):                *)
(*   "KeyNoCostModel"  the cache key leaves out the cost model list.       *)
(*   "PoolByAddress"   the pool key is the EvalContext's address, not a    *)
(*                     weak pointer, so a new EvalContext at a freed       *)
(*                     address finds the old one's Machines.               *)
(*   "ReleaseBeforeRun" the Machine goes back before Run returns.          *)
(*                                                                         *)
(* Not modelled: the idle bound (GOMAXPROCS), which only drops Machines;  *)
(* panics, after which the Machine is dropped, never released.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Evaluators, \* goroutines evaluating scripts
    Tuples,     \* (language, protocol major, cost model list) tuples
    Rounds,     \* evaluations per goroutine
    Limit,      \* evalContextCacheLimit
    MaxCtx,     \* EvalContexts that may be built, in all
    MaxM,       \* Machines that may be built, in all
    Mutation    \* "None", "KeyNoCostModel", "PoolByAddress", "ReleaseBeforeRun"

ASSUME Mutation \in {"None", "KeyNoCostModel", "PoolByAddress",
                     "ReleaseBeforeRun"}

Ctxs == 1 .. MaxCtx
Machines == 1 .. MaxM
None == 0

\* In English: "the cache key of a tuple; with KeyNoCostModel every tuple
\* (same language and major, different cost models) has the same key."
CacheKey(t) == IF Mutation = "KeyNoCostModel" THEN "one" ELSE t
CacheKeys == {CacheKey(t) : t \in Tuples}

VARIABLES
    nCtx,      \* EvalContexts built so far
    ctxTuple,  \* ctxTuple[c]: the tuple EvalContext c was built for
    ctxAddr,   \* ctxAddr[c]: its address
    alive,     \* alive[c]: not yet collected
    cache,     \* cache[k]: the EvalContext cached under key k, or None
    pool,      \* pool[k]: the idle Machines of pool key k
    hasPool,   \* the pool keys with an entry
    cleanup,   \* cleanup[c]: the pool key c's cleanup deletes, or None
    dead,      \* collected EvalContexts whose cleanup has not run
    nM,        \* Machines built so far
    mCtx,      \* mCtx[m]: the EvalContext Machine m was built from
    users,     \* users[m]: the evaluations running Machine m
    pc,        \* pc[e]: "idle", "built", "have", "run"
    want,      \* want[e]: the tuple evaluation e asked for
    ctx,       \* ctx[e]: the EvalContext evaluation e holds, or None
    built,     \* built[e]: the EvalContext e built on a miss, or None
    mach,      \* mach[e]: the Machine e checked out, or None
    done       \* done[e]: evaluations e finished

vars == <<nCtx, ctxTuple, ctxAddr, alive, cache, pool, hasPool, cleanup, dead,
          nM, mCtx, users, pc, want, ctx, built, mach, done>>

\* In English: "the pool key of EvalContext c: c itself (a weak pointer
\* identifies one object for its whole life), or its address under the
\* PoolByAddress mutation."
PoolKey(c) == IF Mutation = "PoolByAddress" THEN ctxAddr[c] ELSE c

Held == {ctx[e] : e \in Evaluators} \cup {built[e] : e \in Evaluators}
Cached == {cache[k] : k \in CacheKeys}

Init ==
    /\ nCtx = 0
    /\ ctxTuple = [c \in Ctxs |-> "none"]
    /\ ctxAddr = [c \in Ctxs |-> 0]
    /\ alive = [c \in Ctxs |-> FALSE]
    /\ cache = [k \in CacheKeys |-> None]
    /\ pool = [k \in Ctxs |-> {}]
    /\ hasPool = {}
    /\ cleanup = [c \in Ctxs |-> None]
    /\ dead = {}
    /\ nM = 0
    /\ mCtx = [m \in Machines |-> None]
    /\ users = [m \in Machines |-> {}]
    /\ pc = [e \in Evaluators |-> "idle"]
    /\ want = [e \in Evaluators |-> CHOOSE t \in Tuples : TRUE]
    /\ ctx = [e \in Evaluators |-> None]
    /\ built = [e \in Evaluators |-> None]
    /\ mach = [e \in Evaluators |-> None]
    /\ done = [e \in Evaluators |-> 0]

\* In English: "Evaluation e asks for tuple t and finds it cached [G1]."
Hit(e, t) ==
    /\ pc[e] = "idle" /\ done[e] < Rounds
    /\ cache[CacheKey(t)] # None
    /\ pc' = [pc EXCEPT ![e] = "have"]
    /\ want' = [want EXCEPT ![e] = t]
    /\ ctx' = [ctx EXCEPT ![e] = cache[CacheKey(t)]]
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, alive, cache, pool, hasPool,
                   cleanup, dead, nM, mCtx, users, built, mach, done>>

\* In English: "Evaluation e misses and builds an EvalContext for t with
\* the lock released, at any address no live EvalContext uses."
Miss(e, t) ==
    /\ pc[e] = "idle" /\ done[e] < Rounds
    /\ cache[CacheKey(t)] = None
    /\ nCtx < MaxCtx
    /\ \E a \in 1 .. MaxCtx :
         /\ \A c \in Ctxs : alive[c] => ctxAddr[c] # a
         /\ ctxAddr' = [ctxAddr EXCEPT ![nCtx + 1] = a]
    /\ nCtx' = nCtx + 1
    /\ ctxTuple' = [ctxTuple EXCEPT ![nCtx + 1] = t]
    /\ alive' = [alive EXCEPT ![nCtx + 1] = TRUE]
    /\ built' = [built EXCEPT ![e] = nCtx + 1]
    /\ want' = [want EXCEPT ![e] = t]
    /\ pc' = [pc EXCEPT ![e] = "built"]
    /\ UNCHANGED <<cache, pool, hasPool, cleanup, dead, nM, mCtx, users, ctx,
                   mach, done>>

\* In English: "loadOrStoreEvalContext: under the cache lock, use the one
\* another caller stored first, or store the built one, evicting another
\* entry past the limit."
Store(e) ==
    /\ pc[e] = "built"
    /\ LET k == CacheKey(want[e])
       IN IF cache[k] # None
            THEN /\ ctx' = [ctx EXCEPT ![e] = cache[k]]
                 /\ UNCHANGED cache
            ELSE /\ ctx' = [ctx EXCEPT ![e] = built[e]]
                 /\ \E evict \in SUBSET (CacheKeys \ {k}) :
                      LET next == [j \in CacheKeys |->
                                     IF j = k THEN built[e]
                                     ELSE IF j \in evict THEN None
                                     ELSE cache[j]]
                      IN /\ Cardinality({j \in CacheKeys : next[j] # None})
                              <= Limit
                         /\ cache' = next
    /\ built' = [built EXCEPT ![e] = None]
    /\ pc' = [pc EXCEPT ![e] = "have"]
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, alive, pool, hasPool, cleanup,
                   dead, nM, mCtx, users, want, mach, done>>

\* In English: "Evaluation e checks out a Machine [G2, G3]: the pool entry
\* for its EvalContext is created if missing (the creator registers the
\* cleanup); an idle Machine is taken, or a new one built from e's
\* EvalContext."
Checkout(e) ==
    /\ pc[e] = "have"
    /\ LET c == ctx[e]
           k == PoolKey(c)
           fresh == k \notin hasPool
       IN /\ hasPool' = hasPool \cup {k}
          /\ cleanup' = IF fresh THEN [cleanup EXCEPT ![c] = k] ELSE cleanup
          /\ IF ~fresh /\ pool[k] # {}
               THEN \E m \in pool[k] :
                      /\ pool' = [pool EXCEPT ![k] = @ \ {m}]
                      /\ mach' = [mach EXCEPT ![e] = m]
                      /\ users' = [users EXCEPT ![m] = @ \cup {e}]
                      /\ UNCHANGED <<nM, mCtx>>
               ELSE /\ nM < MaxM
                    /\ nM' = nM + 1
                    /\ mCtx' = [mCtx EXCEPT ![nM + 1] = c]
                    /\ mach' = [mach EXCEPT ![e] = nM + 1]
                    /\ users' = [users EXCEPT ![nM + 1] = {e}]
                    /\ pool' = IF fresh THEN [pool EXCEPT ![k] = {}] ELSE pool
    /\ pc' = [pc EXCEPT ![e] = "run"]
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, alive, cache, dead, want, ctx,
                   built, done>>

\* In English: "Under ReleaseBeforeRun the Machine goes back to the pool
\* while e is still running it."
EarlyRelease(e) ==
    /\ Mutation = "ReleaseBeforeRun"
    /\ pc[e] = "run" /\ mach[e] # None
    /\ hasPool' = hasPool \cup {PoolKey(ctx[e])}
    /\ pool' = [pool EXCEPT ![PoolKey(ctx[e])] = @ \cup {mach[e]}]
    /\ mach' = [mach EXCEPT ![e] = None]
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, alive, cache, cleanup, dead, nM,
                   mCtx, users, pc, want, ctx, built, done>>

\* In English: "Run returns and the Machine is released to the pool entry
\* for e's EvalContext (created if the cleanup deleted it meanwhile); e
\* drops its EvalContext."
Finish(e) ==
    /\ pc[e] = "run"
    /\ LET k == PoolKey(ctx[e])
           m == mach[e]
       IN /\ hasPool' = hasPool \cup {k}
          /\ pool' = IF m = None THEN pool
                     ELSE [pool EXCEPT ![k] = @ \cup {m}]
          /\ users' = [n \in Machines |->
                         IF e \in users[n] THEN users[n] \ {e} ELSE users[n]]
          /\ cleanup' = IF k \notin hasPool
                          THEN [cleanup EXCEPT ![ctx[e]] = k] ELSE cleanup
    /\ mach' = [mach EXCEPT ![e] = None]
    /\ ctx' = [ctx EXCEPT ![e] = None]
    /\ pc' = [pc EXCEPT ![e] = "idle"]
    /\ done' = [done EXCEPT ![e] = @ + 1]
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, alive, cache, dead, nM, mCtx,
                   want, built>>

\* In English: "The collector frees an EvalContext nothing holds strongly;
\* its address becomes free."
Collect(c) ==
    /\ alive[c] /\ c \notin Held /\ c \notin Cached
    /\ alive' = [alive EXCEPT ![c] = FALSE]
    /\ dead' = dead \cup {c}
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, cache, pool, hasPool, cleanup, nM,
                   mCtx, users, pc, want, ctx, built, mach, done>>

\* In English: "A collected EvalContext's cleanup deletes the pool entry it
\* registered."
Cleanup(c) ==
    /\ c \in dead
    /\ dead' = dead \ {c}
    /\ IF cleanup[c] # None
         THEN /\ hasPool' = hasPool \ {cleanup[c]}
              /\ pool' = [pool EXCEPT ![cleanup[c]] = {}]
         ELSE UNCHANGED <<hasPool, pool>>
    /\ UNCHANGED <<nCtx, ctxTuple, ctxAddr, alive, cache, cleanup, nM, mCtx,
                   users, pc, want, ctx, built, mach, done>>

Next ==
    \/ \E e \in Evaluators, t \in Tuples : Hit(e, t) \/ Miss(e, t)
    \/ \E e \in Evaluators :
         Store(e) \/ Checkout(e) \/ EarlyRelease(e) \/ Finish(e)
    \/ \E c \in Ctxs : Collect(c) \/ Cleanup(c)

Spec == Init /\ [][Next]_vars

\* In English: "No Machine is run by two evaluations at once."
MachineExclusive == \A m \in Machines : Cardinality(users[m]) <= 1

\* In English: "An evaluation runs a Machine built for the tuple it asked
\* for."
NoCrossTupleMachine ==
    \A e \in Evaluators :
        \A m \in Machines :
            e \in users[m] => ctxTuple[mCtx[m]] = want[e]

\* In English: "An evaluation holds an EvalContext for the tuple it asked
\* for."
ContextMatchesTuple ==
    \A e \in Evaluators :
        pc[e] \in {"have", "run"} => ctxTuple[ctx[e]] = want[e]

\* In English: "The cache holds at most Limit EvalContexts."
CacheBounded == Cardinality({k \in CacheKeys : cache[k] # None}) <= Limit
=============================================================================
