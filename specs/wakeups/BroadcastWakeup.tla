--------------------------- MODULE BroadcastWakeup ---------------------------
(***************************************************************************)
(* The close-and-replace broadcast channel, as gOuroboros uses it to wake  *)
(* goroutines waiting for a shared condition (v0.222.0 0c00b799):          *)
(*                                                                         *)
(*   site                          notifier                 waiter         *)
(*   pipeline completionChan       markProcessed            Fence,         *)
(*     (pipeline/pipeline.go)        :1032-1037               :1001-1012,  *)
(*                                                          waitForPending *)
(*                                                            Capacity     *)
(*                                                            :537-556     *)
(*   pipeline rawBytesFreed        releaseRawCborBytes      reserveRaw-    *)
(*                                   :448-462                 CborBytes    *)
(*                                                            :409-445     *)
(*   localmessagenotification      AddMessage :153-181      WaitForMessage *)
(*     messageAdded (server.go)                               :216-224,    *)
(*                                                          handleBlocking *)
(*                                                            Request      *)
(*                                                            :303-322     *)
(*   leiosfetch drainedCh          freeLocked :495-507,     acquireWith-   *)
(*     (client.go)                   abandon :361-379         RangeLimits  *)
(*                                                            :178-243     *)
(*                                                                         *)
(* In each, the waiter, under the lock, checks the condition and, if it    *)
(* must wait, takes the current channel; it then unlocks and selects on    *)
(* that channel (plus a context, a done channel and sometimes a timer).    *)
(* The notifier changes the state and, under the same lock, closes the     *)
(* channel and installs a new one. A channel is a generation number: the   *)
(* waiter remembers the generation it took; closing generation g wakes     *)
(* every waiter holding g.                                                 *)
(*                                                                         *)
(* pipeline's markProcessed differs: it stores completedSequence (an       *)
(* atomic) before taking completionMu, so the state change is a separate   *)
(* step outside the lock (StoreOutsideLock). It is still safe because the  *)
(* close follows the store and the waiter's load and take are both under   *)
(* the lock: a waiter that loaded the old value took a channel that the    *)
(* following close closes.                                                 *)
(*                                                                         *)
(* Mutations, each a Bug cfg:                                              *)
(*   TakeAfterUnlock  the waiter takes the channel after unlocking (the    *)
(*                    shape of the localmessagenotification lost wakeup    *)
(*                    before its fix);                                     *)
(*   CloseBeforeStore markProcessed closes and replaces before storing     *)
(*                    completedSequence.                                   *)
(*                                                                         *)
(* The reference (ouroboros-network, io-classes STM) waits with `retry`:   *)
(* a transaction that read a TVar and retried is re-run when that TVar     *)
(* changes, so a change between the read and the block cannot be missed.  *)
(* gOuroboros rebuilds that guarantee from a mutex and the channel's       *)
(* generation; this module checks the rebuild.                             *)
(*                                                                         *)
(* Primitives are written in place, named as a shared GoConcurrency module *)
(* would (`gen` for a broadcast channel's generation, `closed` for the     *)
(* set of closed generations); see the README.                             *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the top-level README's "Reading a formula      *)
(*   literally" table. Each goroutine is a program counter.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Waiters,           \* goroutines that wait (model values)
    MaxChanges,        \* state changes the notifier makes
    StoreOutsideLock,  \* TRUE for completionChan: the change is an atomic store before the lock
    TakeAfterUnlock,   \* mutation: the waiter takes the channel after unlocking
    CloseBeforeStore,  \* mutation (with StoreOutsideLock): close and replace, then store
    Timer              \* TRUE: a waiter's select also has a timer or context that may fire

VARIABLES
    version,   \* the shared state: how many changes it has seen
    gen,       \* the current channel's generation
    lock,      \* holder of the mutex: a waiter, "notifier", or "none"
    npc,       \* notifier: "idle", "stored", "closed", "unstored"
    changes,   \* changes the notifier has made
    wpc,       \* wpc[w]: "start", "checked", "unlocked", "parked", "done"
    seen,      \* seen[w]: the version w observed under the lock
    took       \* took[w]: the generation w took, 0 if none yet

vars == <<version, gen, lock, npc, changes, wpc, seen, took>>

\* In English: "Nothing has changed; every waiter is about to look."
Init ==
    /\ version = 0 /\ gen = 1 /\ lock = "none"
    /\ npc = "idle" /\ changes = 0
    /\ wpc = [w \in Waiters |-> "start"]
    /\ seen = [w \in Waiters |-> 0]
    /\ took = [w \in Waiters |-> 0]

\* In English: "Generation g is closed: every generation before the current."
IsClosed(g) == g < gen

-----------------------------------------------------------------------------
\* The waiter. It waits for any change after the version it saw.

\* In English: "w locks and reads the state. If it has changed since w last
\* looked, w is done. Otherwise it takes the current channel (or, with the
\* mutation, will take it only after unlocking)."
WaiterCheck(w) ==
    /\ wpc[w] = "start" /\ lock = "none"
    /\ IF version > seen[w]
       THEN /\ wpc' = [wpc EXCEPT ![w] = "done"]
            /\ UNCHANGED <<lock, seen, took>>
       ELSE /\ lock' = w
            /\ seen' = [seen EXCEPT ![w] = version]
            /\ took' = IF TakeAfterUnlock THEN took
                       ELSE [took EXCEPT ![w] = gen]
            /\ wpc' = [wpc EXCEPT ![w] = "checked"]
    /\ UNCHANGED <<version, gen, npc, changes>>

\* In English: "w unlocks."
WaiterUnlock(w) ==
    /\ wpc[w] = "checked" /\ lock = w
    /\ lock' = "none"
    /\ wpc' = [wpc EXCEPT ![w] = IF TakeAfterUnlock THEN "unlocked" ELSE "parked"]
    /\ UNCHANGED <<version, gen, npc, changes, seen, took>>

\* In English: "(mutation) w reads the channel field after unlocking."
WaiterLateTake(w) ==
    /\ wpc[w] = "unlocked"
    /\ took' = [took EXCEPT ![w] = gen]
    /\ wpc' = [wpc EXCEPT ![w] = "parked"]
    /\ UNCHANGED <<version, gen, lock, npc, changes, seen>>

\* In English: "w's select returns: its channel is closed, so it loops and
\* looks again; or its timer or context fires and it returns."
WaiterWake(w) ==
    /\ wpc[w] = "parked" /\ IsClosed(took[w])
    /\ wpc' = [wpc EXCEPT ![w] = "start"]
    /\ UNCHANGED <<version, gen, lock, npc, changes, seen, took>>

WaiterTimeout(w) ==
    /\ Timer /\ wpc[w] = "parked"
    /\ wpc' = [wpc EXCEPT ![w] = "done"]
    /\ UNCHANGED <<version, gen, lock, npc, changes, seen, took>>

-----------------------------------------------------------------------------
\* The notifier.

\* In English: "Under the lock: change the state, close the channel and
\* install a new one; or, for completionChan, store the change first
\* (outside the lock) and then do the close under the lock. With the
\* mutation, the close comes first and the store last."
NotifierStart ==
    /\ npc = "idle" /\ changes < MaxChanges
    /\ changes' = changes + 1
    /\ IF StoreOutsideLock /\ ~CloseBeforeStore
       THEN version' = version + 1 /\ npc' = "stored" /\ UNCHANGED <<lock, gen>>
       ELSE /\ lock = "none"
            /\ IF StoreOutsideLock          \* CloseBeforeStore
               THEN UNCHANGED version
               ELSE version' = version + 1
            /\ gen' = gen + 1
            /\ lock' = "notifier"
            /\ npc' = "closed"
    /\ UNCHANGED <<wpc, seen, took>>

NotifierLockClose ==
    /\ npc = "stored" /\ lock = "none"
    /\ gen' = gen + 1 /\ lock' = "notifier" /\ npc' = "closed"
    /\ UNCHANGED <<version, changes, wpc, seen, took>>

\* In English: "Unlock. With the mutation the change is stored only after
\* this, as a separate step."
NotifierUnlock ==
    /\ npc = "closed" /\ lock = "notifier"
    /\ lock' = "none"
    /\ npc' = IF StoreOutsideLock /\ CloseBeforeStore THEN "unstored" ELSE "idle"
    /\ UNCHANGED <<version, gen, changes, wpc, seen, took>>

\* In English: "(mutation) The atomic store of the change, after the close."
NotifierLateStore ==
    /\ npc = "unstored"
    /\ version' = version + 1 /\ npc' = "idle"
    /\ UNCHANGED <<gen, lock, changes, wpc, seen, took>>

-----------------------------------------------------------------------------

\* In English: "The notifier is done and every waiter has returned or is
\* waiting for a change that will never come; the honest end."
Finished ==
    /\ npc = "idle" /\ changes = MaxChanges
    /\ \A w \in Waiters :
         wpc[w] = "done" \/ (wpc[w] = "parked" /\ ~IsClosed(took[w]) /\ version = seen[w])

Next ==
    \/ \E w \in Waiters :
         WaiterCheck(w) \/ WaiterUnlock(w) \/ WaiterLateTake(w)
         \/ WaiterWake(w) \/ WaiterTimeout(w)
    \/ NotifierStart \/ NotifierLockClose \/ NotifierUnlock \/ NotifierLateStore
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ \A w \in Waiters :
         WF_vars(WaiterCheck(w)) /\ WF_vars(WaiterUnlock(w))
         /\ WF_vars(WaiterLateTake(w)) /\ WF_vars(WaiterWake(w))
    /\ WF_vars(NotifierStart) /\ WF_vars(NotifierLockClose)
    /\ WF_vars(NotifierUnlock) /\ WF_vars(NotifierLateStore)

-----------------------------------------------------------------------------

TypeOK ==
    /\ version \in 0..MaxChanges /\ gen \in 1..(MaxChanges + 1)
    /\ npc \in {"idle", "stored", "closed", "unstored"}
    /\ \A w \in Waiters : wpc[w] \in {"start", "checked", "unlocked", "parked", "done"}

\* In English: "No waiter is parked on an open channel while the state has
\* changed since it looked and the notifier has finished its step: such a
\* waiter would sleep until the next, unrelated, change."
NoLostWakeup ==
    \A w \in Waiters :
        (wpc[w] = "parked" /\ npc = "idle" /\ version > seen[w])
            => IsClosed(took[w])

\* In English: "A waiter that is parked after the state changed since it
\* looked eventually wakes."
WakeupDelivered ==
    \A w \in Waiters :
        [](wpc[w] = "parked" /\ version > seen[w] => <>(wpc[w] /= "parked"))
\* Waiters are interchangeable model values: no CHOOSE, no ordering, none named
\* in Init or Next. Safety configs only.
Sym == Permutations(Waiters)
=============================================================================
