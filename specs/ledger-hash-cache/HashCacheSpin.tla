---------------------------- MODULE HashCacheSpin ----------------------------
(***************************************************************************)
(* gOuroboros' lock-free hash memo, Blake2b256Cache                        *)
(* (ledger/common/hash_cache.go at gOuroboros 5c4f31c1, line numbers       *)
(* below). Block headers and transaction bodies use it to compute their    *)
(* hash or id once and share it between goroutines.                        *)
(*                                                                         *)
(* The cache holds one pointer to a state object {value, state}. The state *)
(* word moves Empty -> Computing -> Ready. Get, as a loop:                 *)
(*   [G1] :43     load the pointer;                                        *)
(*   [G2] :44-54  if it is nil, allocate a fresh object and CAS it in; a   *)
(*                lost CAS goes round the loop again;                      *)
(*   [G3] :57-59  load the state word; Ready returns value;                *)
(*   [G4] :60-65  Empty: CAS Empty -> Computing; the winner computes, the  *)
(*                loser goes round the loop again;                         *)
(*   [G5] :66-77  the winner calls compute(); if it panics, the deferred   *)
(*                function stores Empty and re-panics;                     *)
(*   [G6] :76-79  otherwise the winner writes value (a plain write),       *)
(*                stores Ready (atomic) and returns value;                 *)
(*   [G7] :81-82  Computing: runtime.Gosched() and go round again.         *)
(*   [G8] :37-39  Reset stores nil in the pointer. SetCbor stores the new  *)
(*                bytes first, then calls Reset (ledger/shelley/shelley.go *)
(*                237-240, ledger/common/tx.go 440-445), and its comment   *)
(*                requires callers to synchronize it with Hash and Id.     *)
(*                                                                         *)
(* One step here is one atomic operation, one plain memory access to       *)
(* value, or one call or return of compute. Go's sync/atomic operations    *)
(* are sequentially consistent (the Go memory model, "Atomic Values"), so  *)
(* an interleaving of them is exactly what TLC explores. The plain write   *)
(* of value is ordered for readers only because it comes before the       *)
(* atomic Ready store that they observe; the ReadyBeforeValue mutation     *)
(* shows what goes wrong without that order.                               *)
(*                                                                         *)
(* No specification source: the reference has no such cache. Its header  *)
(* hash and transaction id are pure functions (memoized bytes hashed on    *)
(* demand, cardano-ledger 1210d37f, libs/cardano-ledger-core/src/Cardano/  *)
(* Ledger/Hashes.hs and eras/*/impl/src/.../TxBody.hs `txIdTxBody`), so    *)
(* the only property to keep is "every caller gets the hash of the         *)
(* current bytes", which is what a pure function gives.                    *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header, and   *)
(* the literal readings use README.md's "Reading a formula literally".    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Callers,      \* the goroutines that call Get, for example {"g1", "g2"}
    MaxCalls,     \* how many times each caller calls Get (keeps the model finite)
    MaxPanics,    \* how many compute calls may panic, in all
    ComputeMode,  \* "returns": compute returns unless it panics.
                  \* "blocks": compute never returns (it can still panic).
    MaxSetCbor,   \* how many times SetCbor may replace the bytes
    SetCborMode,  \* "contract": SetCbor runs only while no Get is in flight,
                  \*   as the setters' comments require [G8].
                  \* "racing": SetCbor may run at any time.
    Mutation      \* "None" (gOuroboros), or a deliberate defect:
                  \*   "NoCas": claim Computing with a load then a plain store
                  \*   "ReadyBeforeValue": store Ready, then write value
                  \*   "PanicKeepsComputing": the panic path does not store Empty
                  \*   "ResetBeforeBytes": SetCbor resets, then stores the bytes
                  \*   "NoSpin": a caller that sees Computing returns value

ASSUME ComputeMode \in {"returns", "blocks"}
ASSUME SetCborMode \in {"contract", "racing"}
ASSUME Mutation \in {"None", "NoCas", "ReadyBeforeValue",
                     "PanicKeepsComputing", "ResetBeforeBytes", "NoSpin"}

\* In English: each pointer epoch (between two Resets) allocates at most one
\* object per caller, so this many object ids are always enough.
\* Literally: "MaxObjects is defined as MaxSetCbor plus 1, times the number
\*   of members of Callers."
MaxObjects == (MaxSetCbor + 1) * Cardinality(Callers)

\* Literally: "Objects is defined as 1 through MaxObjects."
Objects == 1 .. MaxObjects

\* In English: 0 stands for a nil pointer, and for the zero hash (the value
\* of a fresh object). The hash of bytes version d is written d.
\* Literally: "Nil is defined as 0."
Nil == 0

VARIABLES
    ptr,       \* c.state: Nil, or the object it points to
    allocated, \* how many objects have been allocated
    st,        \* st[o]: object o's state word: "Empty", "Computing" or "Ready"
    val,       \* val[o]: object o's value field
    data,      \* the bytes the hash is computed from, as a version number
    pc,        \* pc[g]: where caller g is in Get
    obj,       \* obj[g]: the object caller g is working on (cacheState)
    fresh,     \* fresh[g]: the object caller g allocated before its CAS (newState)
    readData,  \* readData[g]: the bytes version compute read
    calls,     \* calls[g]: how many Gets caller g has started
    lastRet,   \* lastRet[g]: <<value returned, bytes version when it returned>>
    computes,  \* computes[o]: how many compute calls returned a value for o
    panics,    \* how many compute calls panicked
    panickedOn,\* the objects on which a compute call panicked
    spun,      \* TRUE once some caller has spun on Computing
    setPc,     \* the SetCbor goroutine: "idle", "bytes" or "reset"
    setCount   \* how many SetCbor calls have started

\* Literally: "vars is defined as the tuple of all seventeen variables."
vars == <<ptr, allocated, st, val, data, pc, obj, fresh, readData, calls,
          lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: the places a caller can be in Get.
\* Literally: "Pcs is defined as the set containing "idle", "load",
\*   "casPtr", "loadState", "casState", "storeComputing", "compute",
\*   "computing", "writeValue", "storeReady", "returnOwn", "readValue",
\*   "panicReset" and "spin"."
Pcs == {"idle", "load", "casPtr", "loadState", "casState", "storeComputing",
        "compute", "computing", "writeValue", "storeReady", "returnOwn",
        "readValue", "panicReset", "spin"}

\* In English: the places where a caller owns the computation of its object.
\* Literally: "OwnerPcs is defined as the set containing "compute",
\*   "computing", "writeValue", "storeReady" and "panicReset"."
OwnerPcs == {"compute", "computing", "writeValue", "storeReady", "panicReset"}

\* In English: the variables have the shapes the comments say.
\* Literally: "TypeOK is defined as: ptr is a member of 0 through MaxObjects,
\*   and allocated is a member of 0 through MaxObjects, and st is a member
\*   of the set of functions from Objects to the set containing "Empty",
\*   "Computing" and "Ready", and val is a function from Objects to the
\*   naturals, and pc is a function from Callers to Pcs, and obj and fresh
\*   are functions from Callers to 0 through MaxObjects, and setPc is a
\*   member of the set containing "idle", "bytes" and "reset"."
TypeOK ==
    /\ ptr \in 0 .. MaxObjects
    /\ allocated \in 0 .. MaxObjects
    /\ st \in [Objects -> {"Empty", "Computing", "Ready"}]
    /\ val \in [Objects -> Nat]
    /\ pc \in [Callers -> Pcs]
    /\ obj \in [Callers -> 0 .. MaxObjects]
    /\ fresh \in [Callers -> 0 .. MaxObjects]
    /\ setPc \in {"idle", "bytes", "reset"}

\* In English: no object exists yet, the bytes are version 1, every caller
\* is idle, and nothing has been returned.
\* Literally: "Init is defined as: ptr equals Nil, and allocated equals 0,
\*   and st is the function that maps every o in Objects to "Empty", and
\*   val is the function that maps every o in Objects to Nil, and data
\*   equals 1, and pc maps every g in Callers to "idle", and obj, fresh and
\*   readData map every g in Callers to 0, and calls maps every g in
\*   Callers to 0, and lastRet maps every g in Callers to the tuple of 1
\*   and 1, and computes maps every o in Objects to 0, and panics equals 0,
\*   and panickedOn equals the empty set, and spun equals FALSE, and setPc
\*   equals "idle", and setCount equals 0."
Init ==
    /\ ptr = Nil                              \* the zero Blake2b256Cache
    /\ allocated = 0
    /\ st = [o \in Objects |-> "Empty"]       \* a fresh object is Empty
    /\ val = [o \in Objects |-> Nil]          \* with a zero value
    /\ data = 1
    /\ pc = [g \in Callers |-> "idle"]
    /\ obj = [g \in Callers |-> 0]
    /\ fresh = [g \in Callers |-> 0]
    /\ readData = [g \in Callers |-> 0]
    /\ calls = [g \in Callers |-> 0]
    /\ lastRet = [g \in Callers |-> <<1, 1>>] \* a placeholder that satisfies the check
    /\ computes = [o \in Objects |-> 0]
    /\ panics = 0
    /\ panickedOn = {}
    /\ spun = FALSE
    /\ setPc = "idle"
    /\ setCount = 0

---------------------------------------------------------------------------
(* One caller's steps. Each changes pc[g] and the variables it names; the  *)
(* helper Keep(...) lists the rest as unchanged.                           *)

\* In English: caller g starts a Get, if it has calls left, and no SetCbor
\* is running when the contract applies.
\* Literally: "Call of g is defined as: pc of g equals "idle", and calls of
\*   g is less than MaxCalls, and (SetCborMode equals "racing" or setPc
\*   equals "idle"), and pc in the next state equals pc except that its g
\*   entry is "load", and calls in the next state equals calls except that
\*   its g entry is the old entry plus 1, and every other variable is
\*   unchanged."
Call(g) ==
    /\ pc[g] = "idle"
    /\ calls[g] < MaxCalls
    /\ SetCborMode = "racing" \/ setPc = "idle"   \* the setters' contract [G8]
    /\ pc' = [pc EXCEPT ![g] = "load"]
    /\ calls' = [calls EXCEPT ![g] = @ + 1]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, readData,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G1] load the pointer. If it is nil, allocate a fresh object
\* (not yet visible to anyone) and go to the CAS; otherwise work on the
\* object it points to.
\* Literally: "Load of g is defined as: pc of g equals "load", and if ptr
\*   equals Nil, then (fresh in the next state equals fresh except that its
\*   g entry is allocated plus 1, and allocated in the next state equals
\*   allocated plus 1, and pc in the next state equals pc except that its
\*   g entry is "casPtr", and obj is unchanged), else (obj in the next
\*   state equals obj except that its g entry is ptr, and pc in the next
\*   state equals pc except that its g entry is "loadState", and fresh and
\*   allocated are unchanged); and every other variable is unchanged."
Load(g) ==
    /\ pc[g] = "load"
    /\ IF ptr = Nil
         THEN /\ fresh' = [fresh EXCEPT ![g] = allocated + 1]  \* newState := &...{}
              /\ allocated' = allocated + 1
              /\ pc' = [pc EXCEPT ![g] = "casPtr"]
              /\ UNCHANGED obj
         ELSE /\ obj' = [obj EXCEPT ![g] = ptr]
              /\ pc' = [pc EXCEPT ![g] = "loadState"]
              /\ UNCHANGED <<fresh, allocated>>
    /\ UNCHANGED <<ptr, st, val, data, readData, calls, lastRet, computes,
                   panics, panickedOn, spun, setPc, setCount>>

\* In English: [G2] CAS the pointer from nil to the fresh object. The winner
\* works on its fresh object; a loser goes round the loop.
\* Literally: "CasPtr of g is defined as: pc of g equals "casPtr", and if
\*   ptr equals Nil, then (ptr in the next state equals fresh of g, and obj
\*   in the next state equals obj except that its g entry is fresh of g,
\*   and pc in the next state equals pc except that its g entry is
\*   "loadState"), else (pc in the next state equals pc except that its g
\*   entry is "load", and ptr and obj are unchanged); and every other
\*   variable is unchanged."
CasPtr(g) ==
    /\ pc[g] = "casPtr"
    /\ IF ptr = Nil
         THEN /\ ptr' = fresh[g]                          \* the CAS wins
              /\ obj' = [obj EXCEPT ![g] = fresh[g]]
              /\ pc' = [pc EXCEPT ![g] = "loadState"]
         ELSE /\ pc' = [pc EXCEPT ![g] = "load"]          \* lost: continue
              /\ UNCHANGED <<ptr, obj>>
    /\ UNCHANGED <<allocated, st, val, data, fresh, readData, calls, lastRet,
                   computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G3] [G4] [G7] load the object's state word. Ready: go read
\* value. Empty: try to claim it (with NoCas, by a plain store after this
\* load). Computing: spin (with NoSpin, read value anyway).
\* Literally: "LoadState of g is defined as: pc of g equals "loadState",
\*   and pc in the next state equals pc except that its g entry is, in the
\*   case st of obj of g equals "Ready", "readValue"; in the case it equals
\*   "Empty" and Mutation equals "NoCas", "storeComputing"; in the case it
\*   equals "Empty", "casState"; in the case Mutation equals "NoSpin",
\*   "readValue"; in every other case, "spin"; and every
\*   other variable is unchanged."
LoadState(g) ==
    /\ pc[g] = "loadState"
    /\ pc' = [pc EXCEPT ![g] =
                CASE st[obj[g]] = "Ready" -> "readValue"
                  [] st[obj[g]] = "Empty" /\ Mutation = "NoCas" -> "storeComputing"
                  [] st[obj[g]] = "Empty" -> "casState"
                  [] Mutation = "NoSpin" -> "readValue"
                  [] OTHER -> "spin"]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G4] CAS the state word from Empty to Computing. The winner
\* computes; a loser falls out of the switch and goes round the loop.
\* Literally: "CasState of g is defined as: pc of g equals "casState", and
\*   if st of obj of g equals "Empty", then (st in the next state equals st
\*   except that its obj of g entry is "Computing", and pc in the next state
\*   equals pc except that its g entry is "compute"), else (pc in the next
\*   state equals pc except that its g entry is "load", and st is
\*   unchanged); and every other variable is unchanged."
CasState(g) ==
    /\ pc[g] = "casState"
    /\ IF st[obj[g]] = "Empty"
         THEN /\ st' = [st EXCEPT ![obj[g]] = "Computing"]   \* the CAS wins
              /\ pc' = [pc EXCEPT ![g] = "compute"]
         ELSE /\ pc' = [pc EXCEPT ![g] = "load"]             \* lost: loop
              /\ UNCHANGED st
    /\ UNCHANGED <<ptr, allocated, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: the NoCas mutation: after a load saw Empty, store Computing
\* without checking that it is still Empty.
\* Literally: "StoreComputing of g is defined as: pc of g equals
\*   "storeComputing", and st in the next state equals st except that its
\*   obj of g entry is "Computing", and pc in the next state equals pc
\*   except that its g entry is "compute", and every other variable is
\*   unchanged."
StoreComputing(g) ==
    /\ pc[g] = "storeComputing"
    /\ st' = [st EXCEPT ![obj[g]] = "Computing"]
    /\ pc' = [pc EXCEPT ![g] = "compute"]
    /\ UNCHANGED <<ptr, allocated, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G5] compute() starts and reads the bytes.
\* Literally: "Compute of g is defined as: pc of g equals "compute", and
\*   readData in the next state equals readData except that its g entry is
\*   data, and pc in the next state equals pc except that its g entry is
\*   "computing", and every other variable is unchanged."
Compute(g) ==
    /\ pc[g] = "compute"
    /\ readData' = [readData EXCEPT ![g] = data]   \* h.Cbor()
    /\ pc' = [pc EXCEPT ![g] = "computing"]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, calls, lastRet,
                   computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G5] [G6] compute() returns (unless it blocks forever); the
\* winner goes on to write value, or, with ReadyBeforeValue, to store Ready
\* first.
\* Literally: "ComputeReturns of g is defined as: pc of g equals
\*   "computing", and ComputeMode equals "returns", and pc in the next state
\*   equals pc except that its g entry is (if Mutation equals
\*   "ReadyBeforeValue" then "storeReady" else "writeValue"), and every
\*   other variable is unchanged."
ComputeReturns(g) ==
    /\ pc[g] = "computing"
    /\ ComputeMode = "returns"
    /\ pc' = [pc EXCEPT ![g] =
                IF Mutation = "ReadyBeforeValue" THEN "storeReady" ELSE "writeValue"]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G5] compute() panics, while the panic budget lasts. The
\* deferred function runs next.
\* Literally: "ComputePanics of g is defined as: pc of g equals
\*   "computing", and panics is less than MaxPanics, and panics in the next
\*   state equals panics plus 1, and panickedOn in the next state equals the
\*   union of panickedOn and the set containing obj of g, and pc in the
\*   next state equals pc except that its g entry is "panicReset", and
\*   every other variable is unchanged."
ComputePanics(g) ==
    /\ pc[g] = "computing"
    /\ panics < MaxPanics
    /\ panics' = panics + 1
    /\ panickedOn' = panickedOn \cup {obj[g]}
    /\ pc' = [pc EXCEPT ![g] = "panicReset"]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, readData, calls,
                   lastRet, computes, spun, setPc, setCount>>

\* In English: [G5] the deferred function stores Empty and re-panics; the
\* panic leaves Get, and the caller (which recovered it) is idle again and
\* may call Get once more. PanicKeepsComputing skips the store.
\* Literally: "PanicReset of g is defined as: pc of g equals "panicReset",
\*   and st in the next state equals (if Mutation equals
\*   "PanicKeepsComputing" then st, else st except that its obj of g entry
\*   is "Empty"), and pc in the next state equals pc except that its g
\*   entry is "idle", and every other variable is unchanged."
PanicReset(g) ==
    /\ pc[g] = "panicReset"
    /\ st' = IF Mutation = "PanicKeepsComputing"
               THEN st
               ELSE [st EXCEPT ![obj[g]] = "Empty"]
    /\ pc' = [pc EXCEPT ![g] = "idle"]
    /\ UNCHANGED <<ptr, allocated, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G6] the plain write of value. With ReadyBeforeValue it
\* comes after the Ready store, and the caller then returns.
\* Literally: "WriteValue of g is defined as: pc of g equals "writeValue",
\*   and val in the next state equals val except that its obj of g entry is
\*   readData of g, and computes in the next state equals computes except
\*   that its obj of g entry is the old entry plus 1, and pc in the next
\*   state equals pc except that its g entry is (if Mutation equals
\*   "ReadyBeforeValue" then "returnOwn" else "storeReady"), and every other
\*   variable is unchanged."
WriteValue(g) ==
    /\ pc[g] = "writeValue"
    /\ val' = [val EXCEPT ![obj[g]] = readData[g]]   \* cacheState.value = compute()
    /\ computes' = [computes EXCEPT ![obj[g]] = @ + 1]
    /\ pc' = [pc EXCEPT ![g] =
                IF Mutation = "ReadyBeforeValue" THEN "returnOwn" ELSE "storeReady"]
    /\ UNCHANGED <<ptr, allocated, st, data, obj, fresh, readData, calls,
                   lastRet, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G6] the atomic Ready store.
\* Literally: "StoreReady of g is defined as: pc of g equals "storeReady",
\*   and st in the next state equals st except that its obj of g entry is
\*   "Ready", and pc in the next state equals pc except that its g entry is
\*   (if Mutation equals "ReadyBeforeValue" then "writeValue" else
\*   "returnOwn"), and every other variable is unchanged."
StoreReady(g) ==
    /\ pc[g] = "storeReady"
    /\ st' = [st EXCEPT ![obj[g]] = "Ready"]
    /\ pc' = [pc EXCEPT ![g] =
                IF Mutation = "ReadyBeforeValue" THEN "writeValue" ELSE "returnOwn"]
    /\ UNCHANGED <<ptr, allocated, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G3] [G6] read value and return it: a waiter that saw Ready,
\* or the winner after its own store.
\* Literally: "Return of g is defined as: pc of g is a member of the set
\*   containing "readValue" and "returnOwn", and lastRet in the next state
\*   equals lastRet except that its g entry is the tuple of val of obj of g
\*   and data, and pc in the next state equals pc except that its g entry
\*   is "idle", and every other variable is unchanged."
Return(g) ==
    /\ pc[g] \in {"readValue", "returnOwn"}
    /\ lastRet' = [lastRet EXCEPT ![g] = <<val[obj[g]], data>>]  \* return cacheState.value
    /\ pc' = [pc EXCEPT ![g] = "idle"]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, readData, calls,
                   computes, panics, panickedOn, spun, setPc, setCount>>

\* In English: [G7] the object is Computing: runtime.Gosched(), then go
\* round the loop. Nothing bounds how often this happens.
\* Literally: "Spin of g is defined as: pc of g equals "spin", and spun in
\*   the next state equals TRUE, and pc in the next state equals pc except
\*   that its g entry is "load", and every other variable is unchanged."
Spin(g) ==
    /\ pc[g] = "spin"
    /\ spun' = TRUE
    /\ pc' = [pc EXCEPT ![g] = "load"]
    /\ UNCHANGED <<ptr, allocated, st, val, data, obj, fresh, readData, calls,
                   lastRet, computes, panics, panickedOn, setPc, setCount>>

\* In English: one step of caller g.
\* Literally: "Step of g is defined as: Call of g, or Load of g, or CasPtr
\*   of g, or LoadState of g, or CasState of g, or StoreComputing of g, or
\*   Compute of g, or ComputeReturns of g, or ComputePanics of g, or
\*   PanicReset of g, or WriteValue of g, or StoreReady of g, or Return of
\*   g, or Spin of g."
Step(g) ==
    \/ Call(g) \/ Load(g) \/ CasPtr(g) \/ LoadState(g) \/ CasState(g)
    \/ StoreComputing(g) \/ Compute(g) \/ ComputeReturns(g) \/ ComputePanics(g)
    \/ PanicReset(g) \/ WriteValue(g) \/ StoreReady(g) \/ Return(g) \/ Spin(g)

---------------------------------------------------------------------------
(* SetCbor: store new bytes, then Reset (or, mutated, the other way).      *)

\* In English: SetCbor begins, while its budget lasts, and, under the
\* contract, only while every caller is idle. Its first step stores the
\* bytes (or, with ResetBeforeBytes, resets the pointer).
\* Literally: "SetBegin is defined as: setPc equals "idle", and setCount is
\*   less than MaxSetCbor, and (SetCborMode equals "racing" or for all g in
\*   Callers, pc of g equals "idle"), and setCount in the next state equals
\*   setCount plus 1, and if Mutation equals "ResetBeforeBytes", then (ptr
\*   in the next state equals Nil, and setPc in the next state equals
\*   "bytes", and data is unchanged), else (data in the next state equals
\*   data plus 1, and setPc in the next state equals "reset", and ptr is
\*   unchanged); and every other variable is unchanged."
SetBegin ==
    /\ setPc = "idle"
    /\ setCount < MaxSetCbor
    /\ SetCborMode = "racing" \/ \A g \in Callers : pc[g] = "idle"
    /\ setCount' = setCount + 1
    /\ IF Mutation = "ResetBeforeBytes"
         THEN /\ ptr' = Nil /\ setPc' = "bytes" /\ UNCHANGED data
         ELSE /\ data' = data + 1 /\ setPc' = "reset" /\ UNCHANGED ptr
    /\ UNCHANGED <<allocated, st, val, pc, obj, fresh, readData, calls, lastRet,
                   computes, panics, panickedOn, spun>>

\* In English: SetCbor's second step: Reset (or, mutated, store the bytes).
\* Literally: "SetEnd is defined as: setPc is a member of the set
\*   containing "bytes" and "reset", and if setPc equals "reset", then (ptr
\*   in the next state equals Nil, and data is unchanged), else (data in
\*   the next state equals data plus 1, and ptr is unchanged); and setPc in
\*   the next state equals "idle", and every other variable is unchanged."
SetEnd ==
    /\ setPc \in {"bytes", "reset"}
    /\ IF setPc = "reset"
         THEN /\ ptr' = Nil /\ UNCHANGED data           \* h.hash.Reset()
         ELSE /\ data' = data + 1 /\ UNCHANGED ptr      \* the bytes, after the reset
    /\ setPc' = "idle"
    /\ UNCHANGED <<allocated, st, val, pc, obj, fresh, readData, calls, lastRet,
                   computes, panics, panickedOn, spun, setCount>>

\* In English: every caller has made all its calls and SetCbor is idle:
\* nothing is left to do, so the model may stay here.
\* Literally: "Done is defined as: for all g in Callers, pc of g equals
\*   "idle" and calls of g equals MaxCalls; and setPc equals "idle"; and
\*   vars is unchanged."
Done ==
    /\ \A g \in Callers : pc[g] = "idle" /\ calls[g] = MaxCalls
    /\ setPc = "idle"
    /\ UNCHANGED vars

\* In English: a step is a step of some caller, a SetCbor step, or staying
\* done.
\* Literally: "Next is defined as: there exists a g in Callers such that
\*   Step of g, or SetBegin, or SetEnd, or Done."
Next == (\E g \in Callers : Step(g)) \/ SetBegin \/ SetEnd \/ Done

\* Literally: "Spec is defined as: Init, and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

\* In English: the Go scheduler eventually runs every runnable goroutine:
\* each caller that can take a step eventually does.
\* Literally: "FairSpec is defined as: Spec, and for all g in Callers, weak
\*   fairness of Step of g."
FairSpec == Spec /\ \A g \in Callers : WF_vars(Step(g))

---------------------------------------------------------------------------
(* Properties. *)

\* In English: at most one caller owns the computation of an object at a
\* time.
\* Literally: "AtMostOneComputer is defined as: for all o in Objects, the
\*   number of members of the set of every g in Callers such that pc of g
\*   is a member of OwnerPcs and obj of g equals o is less than or equal to
\*   1."
AtMostOneComputer ==
    \A o \in Objects :
        Cardinality({g \in Callers : pc[g] \in OwnerPcs /\ obj[g] = o}) <= 1

\* In English: compute returns a value at most once per object, that is,
\* once per transition to Ready.
\* Literally: "ComputeOncePerObject is defined as: for all o in Objects,
\*   computes of o is less than or equal to 1."
ComputeOncePerObject == \A o \in Objects : computes[o] <= 1

\* In English: value is never read while it is being written, which in Go
\* would be a data race.
\* Literally: "NoRacyRead is defined as: there does not exist a g in
\*   Callers and an h in Callers such that pc of g equals "writeValue" and
\*   pc of h equals "readValue" and obj of g equals obj of h."
NoRacyRead ==
    ~\E g, h \in Callers :
        pc[g] = "writeValue" /\ pc[h] = "readValue" /\ obj[g] = obj[h]

\* In English: a caller about to return holds an object that is Ready.
\* Literally: "NoReturnBeforeReady is defined as: for all g in Callers, if
\*   pc of g is a member of the set containing "readValue" and
\*   "returnOwn", then st of obj of g equals "Ready"."
NoReturnBeforeReady ==
    \A g \in Callers :
        pc[g] \in {"readValue", "returnOwn"} => st[obj[g]] = "Ready"

\* In English: every Get returned the hash of the bytes as they were when it
\* returned, so all callers between two SetCbor calls get the same value.
\* Only meaningful under the setters' contract.
\* Literally: "ReturnsCurrentHash is defined as: for all g in Callers,
\*   element 1 of lastRet of g equals element 2 of lastRet of g."
ReturnsCurrentHash == \A g \in Callers : lastRet[g][1] = lastRet[g][2]

\* In English: an object is Computing only while some caller owns it: a
\* panic never leaves it stuck, so the next caller can retry.
\* Literally: "NoOrphanComputing is defined as: for all o in Objects, if st
\*   of o equals "Computing", then there exists a g in Callers such that
\*   obj of g equals o and pc of g is a member of OwnerPcs."
NoOrphanComputing ==
    \A o \in Objects :
        st[o] = "Computing" => \E g \in Callers : obj[g] = o /\ pc[g] \in OwnerPcs

\* In English: whenever SetCbor is not half done, a Ready object that the
\* pointer holds has the hash of the current bytes.
\* Literally: "CachedMatchesBytes is defined as: if setPc equals "idle" and
\*   ptr does not equal Nil and st of ptr equals "Ready", then val of ptr
\*   equals data."
CachedMatchesBytes ==
    (setPc = "idle" /\ ptr /= Nil /\ st[ptr] = "Ready") => val[ptr] = data

\* In English: a caller spinning on Computing eventually returns.
\* Literally: "WaitersReturn is defined as: for all g in Callers, pc of g
\*   equals "spin" leads to pc of g equals "idle"."
WaitersReturn == \A g \in Callers : (pc[g] = "spin") ~> (pc[g] = "idle")

\* Probes, expected to be violated: they show a situation is reachable.

\* In English: "no caller ever spins": violated, so spinning happens.
\* Literally: "ProbeNoSpin is defined as: spun is not true."
ProbeNoSpin == ~spun

\* In English: "no object is ever computed after a panic on it": violated,
\* so the next caller does retry after a panic.
\* Literally: "ProbeNoRetryAfterPanic is defined as: for all o in
\*   panickedOn, computes of o equals 0."
ProbeNoRetryAfterPanic == \A o \in panickedOn : computes[o] = 0
=============================================================================
