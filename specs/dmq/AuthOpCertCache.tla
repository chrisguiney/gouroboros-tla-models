--------------------------- MODULE AuthOpCertCache ---------------------------
(***************************************************************************)
(* The opcert counter cache of gOuroboros' DMQ MessageAuthenticator        *)
(* (protocol/common/authentication.go at gOuroboros 7cd17437), with        *)
(* several connections verifying messages of one pool at once.             *)
(*                                                                         *)
(* The authenticator keeps, under one mutex mu, the pool's last recorded   *)
(* opcert counter (kesOpCertCache), the ids of accepted messages           *)
(* (acceptedIDs) and the time of the pool's last accepted message          *)
(* (lastSig). It caches no verdict: every verification re-checks the       *)
(* signatures, so the only thing a later message inherits from an earlier  *)
(* one is the counter, the held set and the rate-limit time.              *)
(*                                                                         *)
(*   [G1] prepare 356-425: snapshot the counter under mu, verify with the  *)
(*        lock released; a message already held is a duplicate: it is      *)
(*        exempt from the rate limit and the counter, and commit skips it. *)
(*   [G2] commit 427-494, under mu: for each prepared message, refuse it   *)
(*        if its counter is below the recorded one (441); then, if it was  *)
(*        accepted meanwhile by another commit, treat it as a duplicate    *)
(*        (452-459); otherwise re-check the rate limit and record it.      *)
(*   [G3] verifyMessageInternal 526-621 on the authenticator itself (the   *)
(*        deprecated VerifyMessageWithSlot, 510-515): rate lookup and      *)
(*        counter check (each under mu), then verifyKESPeriodRotation      *)
(*        writes the counter (940-956), then recordRate re-checks the rate *)
(*        limit (669-688) and may refuse the message the counter of which *)
(*        is already written.                                              *)
(*                                                                         *)
(* Reference: dmq-node a267003c14e9 validates a message in one STM         *)
(* transaction against the mempool (Validate.hs 115-212), and drops a      *)
(* message it already holds before validating it (ouroboros-network       *)
(* Mempool/Simple.hs 183-245), so a duplicate is never refused for its     *)
(* counter and a refused message records nothing.                          *)
(*                                                                         *)
(* Defects (each is a Bug cfg):                                            *)
(*   counter first [G2]: a message another connection accepted between    *)
(*        this connection's prepare and commit is refused "opcert number   *)
(*        went backwards" once the pool's counter has moved past it,       *)
(*        although it is a duplicate; node-to-node this disconnects an     *)
(*        honest relaying peer.                                            *)
(*   direct [G3]: the counter is written before the rate re-check, so a    *)
(*        message refused as too frequent still raises the pool's counter. *)
(* Fixes: commit tests "held now" before the counter (HeldFirst); the      *)
(* deprecated entry point goes through prepare and commit (Direct off).    *)
(*                                                                         *)
(* Not modelled: RemoveKESOpCertCacheEntry (documented to forget a pool),  *)
(* the once-a-minute pruning of expired ids (callers check expiry before   *)
(* authentication), and signatures (a message here is valid apart from    *)
(* its counter and rate).                                                  *)
(*                                                                         *)
(* One step is one critical section under mu, or one verification with   *)
(* the lock released.                                                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    Workers,    \* connections running prepare/commit
    Delay,      \* minSigDelay in ticks
    MaxT,       \* last clock value
    HeldFirst,  \* TRUE: the fix; FALSE: gOuroboros 7cd17437 (counter first)
    Direct,     \* TRUE: a deprecated VerifyMessageWithSlot caller runs too
    Mutation    \* "None" or "NoRecheck": commit skips the counter re-check

ASSUME Mutation \in {"None", "NoRecheck"}

\* In English: two messages of one pool, under opcert counters 1 and 2.
\* Literally: "Msgs is the set m1, m2; Ctr maps m1 to 1 and m2 to 2."
Msgs == {"m1", "m2"}
Ctr == [m \in Msgs |-> IF m = "m1" THEN 1 ELSE 2]

Idle == [kind |-> "idle"]

VARIABLES
    now,       \* the clock
    cache,     \* kesOpCertCache[pool]; 0 when the pool was never seen
    accepted,  \* acceptedIDs: messages accepted
    lastT,     \* lastSig[pool]; -1 when none
    pending,   \* pending[w]: Idle or a prepared message
    dpc,       \* the direct caller: "idle", "looked", "rotated"
    dq,        \* the direct caller's message and time
    out        \* the last verdict, for the invariants

vars == <<now, cache, accepted, lastT, pending, dpc, dq, out>>

\* In English: "the counter check: the pool was never seen, or the
\* message's counter is not below the recorded one."
CtrOK(id) == cache = 0 \/ Ctr[id] >= cache

\* In English: "the rate limit at time at."
RateOK(at) == lastT < 0 \/ at - lastT >= Delay

Max(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ now = 0
    /\ cache = 0
    /\ accepted = {}
    /\ lastT = -1
    /\ pending = [w \in Workers |-> Idle]
    /\ dpc = "idle"
    /\ dq = [id |-> "m1", at |-> 0]
    /\ out = [kind |-> "none"]

\* In English: "Time passes."
Tick ==
    /\ now < MaxT
    /\ now' = now + 1
    /\ UNCHANGED <<cache, accepted, lastT, pending, dpc, dq, out>>

\* In English: "Worker w prepares message id [G1]: a held message passes as
\* a duplicate; any other passes the rate limit and the counter check
\* against the snapshot. A prepare that fails changes nothing, so only
\* the ones that pass are steps."
Prepare(w, id) ==
    /\ pending[w] = Idle
    /\ LET held == id \in accepted
       IN /\ held \/ (RateOK(now) /\ CtrOK(id))
          /\ pending' = [pending EXCEPT ![w] =
                [kind |-> "prepared", id |-> id, at |-> now, held |-> held]]
    /\ UNCHANGED <<now, cache, accepted, lastT, dpc, dq, out>>

\* In English: "Worker w commits under mu [G2]. A message held at prepare
\* is skipped. Otherwise, on 7cd17437, the counter is re-checked first,
\* then a message accepted meanwhile is a duplicate, then the rate limit is
\* re-checked. With the fix a message accepted meanwhile is a duplicate
\* before any re-check."
Commit(w) ==
    /\ pending[w] # Idle
    /\ LET q == pending[w]
           heldNow == q.id \in accepted
           ctrOK == CtrOK(q.id) \/ Mutation = "NoRecheck"
           dup == q.held \/ heldNow
           ok == IF q.held THEN TRUE
                 ELSE IF HeldFirst /\ heldNow THEN TRUE
                 ELSE ctrOK /\ (heldNow \/ RateOK(q.at))
           fresh == ok /\ ~dup
       IN /\ IF fresh
                THEN /\ accepted' = accepted \cup {q.id}
                     /\ lastT' = q.at
                     /\ cache' = Max(cache, Ctr[q.id])
                ELSE UNCHANGED <<accepted, lastT, cache>>
          /\ out' = [kind |-> "commit", id |-> q.id, dup |-> dup, ok |-> ok,
                     below |-> fresh /\ cache > 0 /\ Ctr[q.id] < cache]
    /\ pending' = [pending EXCEPT ![w] = Idle]
    /\ UNCHANGED <<now, dpc, dq>>

\* In English: "The direct caller looks up the rate limit and checks the
\* counter [G3]. A held message is exempt from both and records nothing,
\* so it ends here."
DirectLook(id) ==
    /\ Direct /\ dpc = "idle"
    /\ id \notin accepted
    /\ RateOK(now) /\ CtrOK(id)
    /\ dpc' = "looked"
    /\ dq' = [id |-> id, at |-> now]
    /\ UNCHANGED <<now, cache, accepted, lastT, pending, out>>

\* In English: "verifyKESPeriodRotation: under mu, refuse a counter below
\* the recorded one, otherwise write it."
DirectRotate ==
    /\ dpc = "looked"
    /\ IF CtrOK(dq.id)
         THEN /\ cache' = Ctr[dq.id]
              /\ dpc' = "rotated"
              /\ out' = out
         ELSE /\ cache' = cache
              /\ dpc' = "idle"
              /\ out' = [kind |-> "direct", id |-> dq.id, dup |-> FALSE,
                         ok |-> FALSE, below |-> FALSE]
    /\ UNCHANGED <<now, accepted, lastT, pending, dq>>

\* In English: "recordRate: under mu, a message accepted meanwhile is a
\* duplicate; otherwise re-check the rate limit and record, or refuse."
DirectRecord ==
    /\ dpc = "rotated"
    /\ LET heldNow == dq.id \in accepted
           ok == heldNow \/ RateOK(dq.at)
       IN /\ IF ok /\ ~heldNow
                THEN /\ accepted' = accepted \cup {dq.id}
                     /\ lastT' = dq.at
                ELSE UNCHANGED <<accepted, lastT>>
          /\ out' = [kind |-> "direct", id |-> dq.id, dup |-> heldNow,
                     ok |-> ok, below |-> FALSE]
    /\ dpc' = "idle"
    /\ UNCHANGED <<now, cache, pending, dq>>

Next ==
    \/ Tick
    \/ \E w \in Workers, id \in Msgs : Prepare(w, id)
    \/ \E w \in Workers : Commit(w)
    \/ \E id \in Msgs : DirectLook(id)
    \/ DirectRotate
    \/ DirectRecord

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ now \in 0 .. MaxT
    /\ cache \in 0 .. 2
    /\ accepted \subseteq Msgs
    /\ lastT \in -1 .. MaxT
    /\ dpc \in {"idle", "looked", "rotated"}

\* In English: "A message another connection accepted first is never
\* refused: it is a duplicate."
\* Literally: "DuplicateNeverRefused is defined as: if out.kind is not
\*   "none" and out.dup, then out.ok."
DuplicateNeverRefused == (out.kind # "none" /\ out.dup) => out.ok

\* In English: "The recorded counter is the highest counter of an accepted
\* message: a refused message records none."
\* Literally: "CacheIsMaxAccepted is defined as: cache equals the largest
\*   Ctr of a member of accepted, or 0 when accepted is empty."
CacheIsMaxAccepted ==
    cache = IF accepted = {} THEN 0
            ELSE CHOOSE c \in {Ctr[m] : m \in accepted} :
                     \A m \in accepted : Ctr[m] <= c

\* In English: "No new acceptance carries a counter below the recorded
\* one."
\* Literally: "CounterNeverBackwards is defined as: if out.kind is not
\*   "none", then out.below is false."
CounterNeverBackwards == out.kind # "none" => ~out.below

\* In English: "The recorded counter never decreases."
CacheMonotonic == [][cache' >= cache]_cache
=============================================================================
