----------------------- MODULE LocalTxMonitorTxIdCache -----------------------
(***************************************************************************)
(* The local-tx-monitor server's transaction-ID cache: the IDs that        *)
(* MsgHasTx needs, computed by parsing each mempool transaction once and   *)
(* kept across re-acquires while the transaction stays in the mempool.     *)
(*                                                                         *)
(* The protocol says nothing about a cache; it says what MsgHasTx answers: *)
(* whether the transaction is in the acquired snapshot. So the questions   *)
(* are whether the cache can ever change that answer, and whether it stays *)
(* bounded by the current snapshot.                                        *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex*)
(*        2105-2166: MsgHasTx asks whether a transaction is in the         *)
(*        acquired snapshot; MsgRelease releases it; queries need one.     *)
(*   [R1] ouroboros-consensus ec239d57f618 .../MiniProtocol/LocalTxMonitor/*)
(*        Server.hs 85-104: each acquire takes a new snapshot; the answer  *)
(*        is membership in that snapshot.                                  *)
(*   UNSOURCED (library design, not a protocol rule): the cache itself.    *)
(*                                                                         *)
(* gOuroboros protocol/localtxmonitor/server.go at 7cd17437:               *)
(*   [G1] txHashes is keyed by era and the maphash of the transaction's    *)
(*        bytes; a hit is confirmed with bytes.Equal (txHash). A key owned *)
(*        by other bytes (a hash collision) is answered by parsing and not *)
(*        cached.                                                          *)
(*   [G2] acquireMempool re-points each entry whose bytes are still in the *)
(*        new snapshot and deletes every other entry.                      *)
(*   [G3] handleRelease and handleDone call releaseMempool, which drops    *)
(*        the snapshot and the cache; MsgDone is legal only from StIdle,   *)
(*        so a restarted server begins with an empty cache.                *)
(*   [G4] hasTx walks the snapshot, computing each ID through the cache,   *)
(*        and stops at the first match, so a query may cache any subset.  *)
(*                                                                         *)
(* One era is enough: the era is part of the key and of the snapshot, so   *)
(* eras only multiply the cases.                                           *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend at the top of                   *)
(* specs/keepalive/KeepAlive.tla and the "Reading a formula literally"     *)
(* table in the top-level README. New here: SUBSET S, the set of all       *)
(* subsets of S (https://lamport.azurewebsites.net/tla/summary.pdf).       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    MaxSteps,        \* how many server steps to explore (keeps the model finite)
    ConfirmBytes,    \* TRUE: a cache hit must have the same bytes [G1]; FALSE: a mutation, the key alone
    SweepOnAcquire,  \* TRUE: an acquire drops entries for transactions that left [G2]; FALSE: a mutation
    ClearOnRelease   \* TRUE: release and restart drop the cache [G3]; FALSE: a mutation

\* In English: "Three mempool transactions. "a" and "b" share a maphash key,
\* the collision the bytes check exists for; "c" has a key of its own."
\* Literally: "Txs is defined as the set containing "a", "b" and "c"."
Txs == {"a", "b", "c"}

\* Literally: "Key of t is defined as: 1 if t is "a" or "b", otherwise 2."
Key(t) == IF t \in {"a", "b"} THEN 1 ELSE 2

\* In English: "Each transaction's ID, the answer to parsing it."
\* Literally: "Id of t is defined as: the case t equals "a" gives "A", t
\*   equals "b" gives "B", and t equals "c" gives "C"."
Id(t) == CASE t = "a" -> "A" [] t = "b" -> "B" [] t = "c" -> "C"

\* Literally: "Ids is defined as the set of Id of t for every t in Txs."
Ids == {Id(t) : t \in Txs}

VARIABLES
    held,   \* TRUE while the client holds a snapshot (the server is acquired)
    snap,   \* the transactions in the held snapshot
    cache,  \* the cache: a set of records [key, tx, id]
    steps   \* server steps taken so far

\* Literally: "vars is defined as the tuple of held, snap, cache and steps."
vars == <<held, snap, cache, steps>>

\* In English: "The cache entries that answer for transaction t: the entry
\* under t's key, and with ConfirmBytes only if it holds t's own bytes."
\* Literally: "Hits of t is defined as the set of every e in cache such that
\*   the key of e equals Key of t, and if ConfirmBytes then the tx of e
\*   equals t."
Hits(t) == {e \in cache : e.key = Key(t) /\ (ConfirmBytes => e.tx = t)}

\* In English: "The ID hasTx computes for t: from the cache on a hit,
\* otherwise by parsing [G1]."
\* Literally: "IdVia of t is defined as: if Hits of t is not empty, the id of
\*   some member of Hits of t, otherwise Id of t."
IdVia(t) == IF Hits(t) /= {} THEN (CHOOSE e \in Hits(t) : TRUE).id ELSE Id(t)

\* In English: "What MsgHasTx for ID q answers now [G4]."
\* Literally: "Answer of q is defined as: there exists a t in snap such that
\*   IdVia of t equals q."
Answer(q) == \E t \in snap : IdVia(t) = q

\* Literally: "Init is defined as: held is false, snap is empty, cache is
\*   empty and steps is 0."
Init ==
    /\ held = FALSE
    /\ snap = {}
    /\ cache = {}
    /\ steps = 0

\* In English: "MsgAcquire (or MsgAwaitAcquire) takes a new snapshot S, any
\* subset of the transactions. Entries whose transaction is still in S are
\* carried and re-pointed at S's bytes; with ConfirmBytes the carry needs
\* the same bytes, without it a key match re-points the entry at whatever
\* transaction now has that key, keeping its old ID. The rest are dropped
\* (unless SweepOnAcquire is off) [G2]."
\* Literally: "Acquire of S is defined as: steps is less than MaxSteps, and
\*   with matches the pairs <<e, t>> of an entry e in cache and a t in S
\*   whose key is e's key and (if ConfirmBytes) whose bytes are e's, cache
\*   becomes the records [key e.key, tx t, id e.id] for every pair in
\*   matches, together with, if SweepOnAcquire is off, every entry in no
\*   pair; and held becomes TRUE, snap becomes S, steps goes up by one."
\* New here: cache \X S is the set of all pairs <<e, t>>; x[1] and x[2]
\* are a pair's first and second parts.
Acquire(S) ==
    /\ steps < MaxSteps
    /\ LET matches == {x \in cache \X S : x[1].key = Key(x[2])
                                         /\ (ConfirmBytes => x[1].tx = x[2])}
           kept    == {[key |-> x[1].key, tx |-> x[2], id |-> x[1].id] : x \in matches}
           stale   == {e \in cache : ~\E x \in matches : x[1] = e}
       IN cache' = kept \cup (IF SweepOnAcquire THEN {} ELSE stale)
    /\ held' = TRUE
    /\ snap' = S
    /\ steps' = steps + 1

\* In English: "While answering a MsgHasTx, hasTx computes the ID of a
\* snapshot transaction t through the cache: a hit leaves the cache alone,
\* a key owned by other bytes is parsed and not cached, a free key is
\* filled [G1][G4]."
\* Literally: "Parse of t is defined as: held, and t is in snap, and steps
\*   is less than MaxSteps, and steps goes up by one, and cache becomes:
\*   cache if Hits of t is not empty or some entry has t's key; otherwise
\*   cache with the record [key Key of t, tx t, id Id of t] added; held and
\*   snap are unchanged."
Parse(t) ==
    /\ held /\ t \in snap
    /\ steps < MaxSteps
    /\ cache' = IF Hits(t) /= {} \/ \E e \in cache : e.key = Key(t)
                   THEN cache
                   ELSE cache \cup {[key |-> Key(t), tx |-> t, id |-> Id(t)]}
    /\ steps' = steps + 1
    /\ UNCHANGED <<held, snap>>

\* In English: "MsgRelease drops the snapshot and, with ClearOnRelease, the
\* cache [G3]."
\* Literally: "Release is defined as: held, and steps is less than
\*   MaxSteps, and held becomes FALSE, snap becomes empty, cache becomes
\*   empty if ClearOnRelease and stays otherwise, and steps goes up by one."
Release ==
    /\ held
    /\ steps < MaxSteps
    /\ held' = FALSE
    /\ snap' = {}
    /\ cache' = IF ClearOnRelease THEN {} ELSE cache
    /\ steps' = steps + 1

\* In English: "MsgDone, legal only in StIdle, restarts the server: the
\* same release, then a new run [G3]."
\* Literally: "Restart is defined as: held is false, and steps is less than
\*   MaxSteps, and cache becomes empty if ClearOnRelease and stays
\*   otherwise, and steps goes up by one, and held and snap are unchanged."
Restart ==
    /\ ~held
    /\ steps < MaxSteps
    /\ cache' = IF ClearOnRelease THEN {} ELSE cache
    /\ steps' = steps + 1
    /\ UNCHANGED <<held, snap>>

\* Literally: "Done is defined as: steps equals MaxSteps and vars is
\*   unchanged."
Done == steps = MaxSteps /\ UNCHANGED vars

\* Literally: "Next is defined as: there exists an S among the subsets of
\*   Txs such that Acquire of S, or there exists a t in Txs such that Parse
\*   of t, or Release, or Restart, or Done."
Next ==
    \/ \E S \in SUBSET Txs : Acquire(S)
    \/ \E t \in Txs : Parse(t)
    \/ Release
    \/ Restart
    \/ Done

\* Literally: "Spec is defined as: Init, and always either Next or vars
\*   stays the same."
Spec == Init /\ [][Next]_vars

\* ---- Invariants ---------------------------------------------------------

\* In English: "MsgHasTx answers, for every ID, exactly whether the held
\* snapshot contains a transaction with that ID: the cache never changes an
\* answer [S1][R1]."
\* Literally: "AnswersMatchSnapshot is defined as: for every q in Ids,
\*   Answer of q holds if and only if there exists a t in snap such that Id
\*   of t equals q."
AnswersMatchSnapshot == \A q \in Ids : Answer(q) <=> \E t \in snap : Id(t) = q

\* In English: "Every entry belongs to a transaction in the held snapshot,
\* so the cache is never larger than the snapshot."
\* Literally: "CacheWithinSnapshot is defined as: for every e in cache, the
\*   tx of e is in snap."
CacheWithinSnapshot == \A e \in cache : e.tx \in snap

\* In English: "At most one entry per key."
\* Literally: "OneEntryPerKey is defined as: for every e and f in cache, if
\*   their keys are equal, e equals f."
OneEntryPerKey == \A e, f \in cache : e.key = f.key => e = f

\* In English: "Nothing is cached while no snapshot is held, so a released
\* or restarted server serves nothing from an earlier run."
\* Literally: "NothingCachedWhenIdle is defined as: if held is false then
\*   cache is empty."
NothingCachedWhenIdle == ~held => cache = {}

\* In English: "Every entry's ID is the ID of the bytes it points at."
\* Literally: "EntriesCorrect is defined as: for every e in cache, the id of
\*   e equals Id of the tx of e."
EntriesCorrect == \A e \in cache : e.id = Id(e.tx)

\* ---- Reachability probe (must fail on the passing config) ---------------

\* In English: "The cache never carries an entry into a new snapshot that
\* also holds the colliding transaction."
ProbeNoCollisionHeld == ~(\E e \in cache : e.tx = "a" /\ "b" \in snap)
=============================================================================
