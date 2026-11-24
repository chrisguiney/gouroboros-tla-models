----------------------------- MODULE TxScopedMemo -----------------------------
(***************************************************************************)
(* gOuroboros' transaction-scoped memo, cachedLedgerState.                 *)
(* TransactionScopedMemo (ledger/common/rules.go at gOuroboros 5c4f31c1).  *)
(* Several validation rules derive the same value from one transaction     *)
(* (today the TxScriptView, script/needed.go 143); the memo builds it once *)
(* and shares it, including with rules running on other goroutines.        *)
(*                                                                         *)
(*   [G1] :237-244  under memoMu, look for an entry for (tx, key); if one  *)
(*                  exists, unlock, wait for its done channel, and return  *)
(*                  its value and error;                                   *)
(*   [G2] :245-249  otherwise append a new entry and unlock;               *)
(*   [G3] :250-252  build() with the lock released; a deferred             *)
(*                  close(entry.done) publishes value and error.           *)
(* If build panics, the deferred close still runs with value and error     *)
(* both nil, and the entry stays in the memo. A waiter, or any later       *)
(* caller on the same scoped state, then gets (nil, nil): a success with   *)
(* no value, which NewTxScriptView turns into an empty script view.        *)
(*                                                                         *)
(* Fix (switch Fix): the builder that panics removes its entry under       *)
(* memoMu and marks it abandoned before closing done; a waiter that sees   *)
(* an abandoned entry goes round again and builds itself. This is what     *)
(* the hash cache does (HashCacheSpin.tla, PanicReset).                    *)
(*                                                                         *)
(* Reference: the reference has no such memo. A shared lazily evaluated    *)
(* value whose evaluation throws re-throws to everyone who forces it, so   *)
(* no reader ever sees a success without a value. Retrying the build gives *)
(* the same outcome: on the same input it fails again for every caller.   *)
(*                                                                         *)
(* One step is one lock acquire, one critical section with its release,   *)
(* one channel close or receive, or one call or return of build.           *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header, and   *)
(* the literal readings use README.md's "Reading a formula literally".    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Callers,    \* goroutines calling TransactionScopedMemo for one (tx, key)
    MaxCalls,   \* how many calls each caller makes
    MaxPanics,  \* how many build calls may panic, in all
    Fix,        \* TRUE: a panicking build abandons its entry. FALSE: gOuroboros 5c4f31c1
    Mutation    \* "None", or a deliberate defect:
                \*   "NoShare": the scan never finds an existing entry
                \*   "BuildUnderLock": memoMu stays held while build runs

ASSUME Mutation \in {"None", "NoShare", "BuildUnderLock"}

\* In English: entry ids; each call creates at most one entry.
\* Literally: "Entries is defined as 1 through MaxCalls times the number of
\*   members of Callers."
Entries == 1 .. (MaxCalls * Cardinality(Callers))

VARIABLES
    memo,      \* the set of entries in c.memo (all for the one (tx, key))
    made,      \* how many entries have been created
    done,      \* done[e]: entry e's done channel is closed
    value,     \* value[e]: "nil" or "built": what entry e holds
    abandoned, \* abandoned[e]: the fix marked entry e abandoned
    lock,      \* memoMu's holder, or "none"
    pc,        \* pc[g]: where caller g is
    cur,       \* cur[g]: the entry caller g waits for or builds
    calls,     \* calls[g]: how many calls caller g has started
    result,    \* result[g]: what caller g's last call ended with:
               \*   "none", "built", "nilnil" (success with no value), "panic"
    builds,    \* how many build calls returned a value
    panics     \* how many build calls panicked

\* Literally: "vars is defined as the tuple of all twelve variables."
vars == <<memo, made, done, value, abandoned, lock, pc, cur, calls, result,
          builds, panics>>

\* In English: nothing in the memo, no lock held, every caller idle.
\* Literally: "Init is defined as: memo equals the empty set, and made
\*   equals 0, and done maps every e in Entries to FALSE, and value maps
\*   every e in Entries to "nil", and abandoned maps every e in Entries to
\*   FALSE, and lock equals "none", and pc maps every g in Callers to
\*   "idle", and cur maps every g in Callers to 0, and calls maps every g
\*   in Callers to 0, and result maps every g in Callers to "none", and
\*   builds equals 0, and panics equals 0."
Init ==
    /\ memo = {}
    /\ made = 0
    /\ done = [e \in Entries |-> FALSE]
    /\ value = [e \in Entries |-> "nil"]
    /\ abandoned = [e \in Entries |-> FALSE]
    /\ lock = "none"
    /\ pc = [g \in Callers |-> "idle"]
    /\ cur = [g \in Callers |-> 0]
    /\ calls = [g \in Callers |-> 0]
    /\ result = [g \in Callers |-> "none"]
    /\ builds = 0
    /\ panics = 0

\* In English: caller g calls TransactionScopedMemo, if it has calls left.
\* Literally: "Call of g is defined as: pc of g equals "idle", and calls of
\*   g is less than MaxCalls, and calls in the next state equals calls
\*   except that its g entry is the old entry plus 1, and pc in the next
\*   state equals pc except that its g entry is "lock", and every other
\*   variable is unchanged."
Call(g) ==
    /\ pc[g] = "idle"
    /\ calls[g] < MaxCalls
    /\ calls' = [calls EXCEPT ![g] = @ + 1]
    /\ pc' = [pc EXCEPT ![g] = "lock"]
    /\ UNCHANGED <<memo, made, done, value, abandoned, lock, cur, result,
                   builds, panics>>

\* In English: [G1] c.memoMu.Lock().
\* Literally: "Lock of g is defined as: pc of g equals "lock", and lock
\*   equals "none", and lock in the next state equals g, and pc in the next
\*   state equals pc except that its g entry is "scan", and every other
\*   variable is unchanged."
Lock(g) ==
    /\ pc[g] = "lock"
    /\ lock = "none"
    /\ lock' = g
    /\ pc' = [pc EXCEPT ![g] = "scan"]
    /\ UNCHANGED <<memo, made, done, value, abandoned, cur, calls, result,
                   builds, panics>>

\* In English: [G1] [G2] holding memoMu, find the entry and go wait for it,
\* or append a new one and go build it; then unlock.
\* Literally: "Scan of g is defined as: pc of g equals "scan", and if memo
\*   does not equal the empty set and Mutation does not equal "NoShare", then (cur in the next state equals cur
\*   except that its g entry is the e chosen from memo, and pc in the next
\*   state equals pc except that its g entry is "wait", and memo and made
\*   are unchanged), else (made in the next state equals made plus 1, and
\*   memo in the next state equals the set containing made plus 1, and cur
\*   in the next state equals cur except that its g entry is made plus 1,
\*   and pc in the next state equals pc except that its g entry is
\*   "build"); and lock in the next state equals (if Mutation equals
\*   "BuildUnderLock" and memo equals the empty set then g else "none"),
\*   and every other variable is unchanged."
Scan(g) ==
    /\ pc[g] = "scan"
    /\ IF memo /= {} /\ Mutation /= "NoShare"
         THEN /\ cur' = [cur EXCEPT ![g] = CHOOSE e \in memo : TRUE]  \* found
              /\ pc' = [pc EXCEPT ![g] = "wait"]
              /\ UNCHANGED <<memo, made>>
         ELSE /\ made' = made + 1                                     \* append
              /\ memo' = {made + 1}
              /\ cur' = [cur EXCEPT ![g] = made + 1]
              /\ pc' = [pc EXCEPT ![g] = "build"]
    /\ lock' = IF Mutation = "BuildUnderLock" /\ memo = {} THEN g ELSE "none"  \* Unlock
    /\ UNCHANGED <<done, value, abandoned, calls, result, builds, panics>>

\* In English: [G1] the receive from done returns once it is closed. With
\* the fix, an abandoned entry sends the caller round again; otherwise it
\* returns the entry's value, which is nil if its build panicked.
\* Literally: "Wait of g is defined as: pc of g equals "wait", and done of
\*   cur of g is true, and if Fix and abandoned of cur of g, then (pc in
\*   the next state equals pc except that its g entry is "lock", and result
\*   is unchanged), else (result in the next state equals result except
\*   that its g entry is (if value of cur of g equals "built" then "built"
\*   else "nilnil"), and pc in the next state equals pc except that its g
\*   entry is "idle"); and every other variable is unchanged."
Wait(g) ==
    /\ pc[g] = "wait"
    /\ done[cur[g]]                                  \* <-entry.done
    /\ IF Fix /\ abandoned[cur[g]]
         THEN /\ pc' = [pc EXCEPT ![g] = "lock"]     \* retry
              /\ UNCHANGED result
         ELSE /\ result' = [result EXCEPT ![g] =
                              IF value[cur[g]] = "built" THEN "built" ELSE "nilnil"]
              /\ pc' = [pc EXCEPT ![g] = "idle"]
    /\ UNCHANGED <<memo, made, done, value, abandoned, lock, cur, calls,
                   builds, panics>>

\* In English: [G3] build returns a value; the deferred close follows.
\* Literally: "BuildReturns of g is defined as: pc of g equals "build", and
\*   value in the next state equals value except that its cur of g entry is
\*   "built", and builds in the next state equals builds plus 1, and pc in
\*   the next state equals pc except that its g entry is "close", and every
\*   other variable is unchanged."
BuildReturns(g) ==
    /\ pc[g] = "build"
    /\ value' = [value EXCEPT ![cur[g]] = "built"]
    /\ builds' = builds + 1
    /\ pc' = [pc EXCEPT ![g] = "close"]
    /\ UNCHANGED <<memo, made, done, abandoned, lock, cur, calls, result, panics>>

\* In English: [G3] build panics, while the panic budget lasts. Without the
\* fix the deferred close runs next; with it, the builder first takes
\* memoMu to abandon the entry.
\* Literally: "BuildPanics of g is defined as: pc of g equals "build", and
\*   panics is less than MaxPanics, and panics in the next state equals
\*   panics plus 1, and pc in the next state equals pc except that its g
\*   entry is (if Fix then "abandonLock" else "closePanic"), and every other
\*   variable is unchanged."
BuildPanics(g) ==
    /\ pc[g] = "build"
    /\ panics < MaxPanics
    /\ panics' = panics + 1
    /\ pc' = [pc EXCEPT ![g] = IF Fix THEN "abandonLock" ELSE "closePanic"]
    /\ UNCHANGED <<memo, made, done, value, abandoned, lock, cur, calls,
                   result, builds>>

\* In English: [G3] the deferred close(entry.done) after a successful
\* build; the caller returns the value.
\* Literally: "Close of g is defined as: pc of g equals "close", and done in
\*   the next state equals done except that its cur of g entry is TRUE, and
\*   result in the next state equals result except that its g entry is
\*   "built", and pc in the next state equals pc except that its g entry is
\*   "idle", and lock in the next state equals (if lock equals g then
\*   "none" else lock), and every other variable is unchanged."
Close(g) ==
    /\ pc[g] = "close"
    /\ done' = [done EXCEPT ![cur[g]] = TRUE]
    /\ result' = [result EXCEPT ![g] = "built"]
    /\ pc' = [pc EXCEPT ![g] = "idle"]
    /\ lock' = IF lock = g THEN "none" ELSE lock    \* BuildUnderLock only
    /\ UNCHANGED <<memo, made, value, abandoned, cur, calls, builds, panics>>

\* In English: [G3] gOuroboros: the deferred close runs during the panic,
\* with value still nil and the entry still in the memo; the panic reaches
\* the caller, which recovers it.
\* Literally: "ClosePanic of g is defined as: pc of g equals "closePanic",
\*   and done in the next state equals done except that its cur of g entry
\*   is TRUE, and result in the next state equals result except that its g
\*   entry is "panic", and pc in the next state equals pc except that its g
\*   entry is "idle", and lock in the next state equals (if lock equals g
\*   then "none" else lock), and every other variable is unchanged."
ClosePanic(g) ==
    /\ pc[g] = "closePanic"
    /\ done' = [done EXCEPT ![cur[g]] = TRUE]
    /\ result' = [result EXCEPT ![g] = "panic"]
    /\ pc' = [pc EXCEPT ![g] = "idle"]
    /\ lock' = IF lock = g THEN "none" ELSE lock    \* BuildUnderLock only
    /\ UNCHANGED <<memo, made, value, abandoned, cur, calls, builds, panics>>

\* In English: the fix: the panicking builder takes memoMu...
\* Literally: "AbandonLock of g is defined as: pc of g equals
\*   "abandonLock", and lock is a member of the set containing "none" and
\*   g, and lock in the next state
\*   equals g, and pc in the next state equals pc except that its g entry is
\*   "abandon", and every other variable is unchanged."
AbandonLock(g) ==
    /\ pc[g] = "abandonLock"
    /\ lock \in {"none", g}
    /\ lock' = g
    /\ pc' = [pc EXCEPT ![g] = "abandon"]
    /\ UNCHANGED <<memo, made, done, value, abandoned, cur, calls, result,
                   builds, panics>>

\* In English: ...removes its entry, marks it abandoned and unlocks; then
\* the deferred close wakes the waiters and the panic goes on.
\* Literally: "Abandon of g is defined as: pc of g equals "abandon", and
\*   memo in the next state equals memo without the members of the set
\*   containing cur of g, and abandoned in the next state equals abandoned
\*   except that its cur of g entry is TRUE, and lock in the next state
\*   equals "none", and pc in the next state equals pc except that its g
\*   entry is "closePanic", and every other variable is unchanged."
Abandon(g) ==
    /\ pc[g] = "abandon"
    /\ memo' = memo \ {cur[g]}
    /\ abandoned' = [abandoned EXCEPT ![cur[g]] = TRUE]
    /\ lock' = "none"
    /\ pc' = [pc EXCEPT ![g] = "closePanic"]
    /\ UNCHANGED <<made, done, value, cur, calls, result, builds, panics>>

\* Literally: "Step of g is defined as: Call of g, or Lock of g, or Scan of
\*   g, or Wait of g, or BuildReturns of g, or BuildPanics of g, or Close
\*   of g, or ClosePanic of g, or AbandonLock of g, or Abandon of g."
Step(g) ==
    \/ Call(g) \/ Lock(g) \/ Scan(g) \/ Wait(g) \/ BuildReturns(g)
    \/ BuildPanics(g) \/ Close(g) \/ ClosePanic(g) \/ AbandonLock(g) \/ Abandon(g)

\* In English: every caller made all its calls and is idle.
\* Literally: "Done is defined as: for all g in Callers, pc of g equals
\*   "idle" and calls of g equals MaxCalls; and vars is unchanged."
Done ==
    /\ \A g \in Callers : pc[g] = "idle" /\ calls[g] = MaxCalls
    /\ UNCHANGED vars

\* Literally: "Next is defined as: there exists a g in Callers such that
\*   Step of g, or Done."
Next == (\E g \in Callers : Step(g)) \/ Done

\* Literally: "Spec is defined as: Init, and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

\* In English: no call ever returns success with no value.
\* Literally: "NoSilentEmptySuccess is defined as: for all g in Callers,
\*   result of g does not equal "nilnil"."
NoSilentEmptySuccess == \A g \in Callers : result[g] /= "nilnil"

\* In English: build returns a value at most once for the key.
\* Literally: "BuildOnce is defined as: builds is less than or equal to 1."
BuildOnce == builds <= 1

\* In English: memoMu is never held while a caller waits on done or runs
\* build.
\* Literally: "NoLockAcrossWaitOrBuild is defined as: for all g in
\*   Callers, if pc of g is a member of the set containing "wait" and
\*   "build", then lock does not equal g."
NoLockAcrossWaitOrBuild ==
    \A g \in Callers : pc[g] \in {"wait", "build"} => lock /= g

\* Probe, expected to be violated: "no caller ever waits for another's
\* build that then panics".
\* Literally: "ProbeNoWaitOnPanic is defined as: there does not exist a g
\*   in Callers such that pc of g equals "wait" and there exists an h in
\*   Callers such that h does not equal g and cur of h equals cur of g and
\*   pc of h is a member of the set containing "closePanic", "abandonLock"
\*   and "abandon"."
ProbeNoWaitOnPanic ==
    ~\E g \in Callers :
        /\ pc[g] = "wait"
        /\ \E h \in Callers :
             h /= g /\ cur[h] = cur[g] /\ pc[h] \in {"closePanic", "abandonLock", "abandon"}
=============================================================================
