--------------------------- MODULE MessageValidity ---------------------------
(***************************************************************************)
(* Model `dmq`, part 5: when a DMQ message is valid.                       *)
(*                                                                         *)
(* A node accepts a DMQ message only if it has not expired, does not       *)
(* expire too far in the future, has a body of the allowed size, is signed *)
(* with the KES key evolved to the period the message claims, comes from a *)
(* registered pool, and its operational-certificate counter has not gone   *)
(* backwards. Three of these depend on state that changes over time: the   *)
(* clock, the current KES period, and the highest counter seen per pool.   *)
(*                                                                         *)
(* gOuroboros checks a batch in two steps: PrepareMessages verifies every  *)
(* message against a snapshot of the counters and returns a commit         *)
(* function; the commit re-checks the counters and records them. Two       *)
(* batches may be prepared at once and committed in either order.          *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoAcceptBeyondReference  gOuroboros never accepts a message the       *)
(*                    reference would reject at the same moment.           *)
(*   AcceptAsReference        gOuroboros accepts every message the         *)
(*                    reference accepts.                                   *)
(*   SeenMonotone     a pool's recorded counter never goes down.           *)
(*   RejectKeepsSeen  a rejected batch records nothing.                    *)
(*                                                                         *)
(* Sources:                                                                *)
(*   CIP-0137 (cardano-foundation/CIPs db48da14bff1), CIP-0137/README.md:  *)
(*   [C1] 155: messageBody = bstr .size (90..2000).                        *)
(*   [C2] 336-337: expired messages are invalid; an expiry too far in the *)
(*        future is a protocol violation.                                  *)
(*   [C3] 395-411: opcert, KES signature, pool in the stake distribution,  *)
(*        opcert counter never lower than one seen before.                 *)
(*   Reference, IntersectMBO/dmq-node a267003c14e9, dmq-node/:             *)
(*   [R1] src/DMQ/Protocol/SigSubmission/Validate.hs 115-122: expired if   *)
(*        now > expiresAt; too far if expiresAt >= now + 1800 s; now is a  *)
(*        POSIXTime with sub-second precision.                             *)
(*   [R2] Validate.hs 156-161: claimed KES period in                       *)
(*        [ocertKESPeriod, ocertKESPeriod + maxKESEvo).                     *)
(*   [R3] Validate.hs 167-177: pool in the stake map with non-zero set     *)
(*        snapshot stake.                                                  *)
(*   [R4] Validate.hs 183-197: counter >= the last one seen for the pool;  *)
(*        the map is updated only if every check passes (lines 96-100).    *)
(*   [R5] Validate.hs 207-212: KES signature verified at evolution         *)
(*        sigKESPeriod - ocertKESPeriod. The current slot is not used.     *)
(*   [R6] src/DMQ/Protocol/SigSubmission/Codec.hs 193-202 and             *)
(*        src/DMQ/Policy.hs 42-49: body of 90 to 2000 bytes, checked when  *)
(*        the message is decoded.                                          *)
(*   [R7] src/DMQ/Policy.hs 60-61: maxSigExpiresAtDelay = 1800 s.          *)
(*   gOuroboros, blinklabs-io/gouroboros 62fa36d1, protocol/common/:       *)
(*   [G1] authentication.go verifyMessageInternal: stake, opcert, chain    *)
(*        counter, KES signature, counter rotation.                        *)
(*   [G2] authentication.go verifyKESSignature: window checks on the       *)
(*        claimed and the current period; signature verified at           *)
(*        currentPeriod - ocertKESPeriod.                                  *)
(*   [G3] authentication.go PrepareMessages: snapshot, verify, commit with *)
(*        a re-check of the batch's last counter per pool.                 *)
(*   [G4] authentication.go TTLValidator.ValidateMessageTTLAt: now        *)
(*        truncated to whole seconds; expiresAt <= now + maxTTL accepted. *)
(*                                                                         *)
(* Time is counted in half-second ticks so that "now" can fall between    *)
(* two whole seconds, as the reference's clock can. Expiry times are whole *)
(* seconds, as on the wire.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences     \* numbers (with -1), and lists

CONSTANTS
    Pools,        \* the pools that may sign messages
    Staked,       \* the pools with stake in the current distribution
    ChainFloor,   \* the lowest counter gOuroboros's chain lookup allows [G1]
    Counters,     \* opcert counters a message may carry
    CertPeriods,  \* KES periods an opcert may start at
    MsgPeriods,   \* KES periods a message may claim
    SigEvos,      \* KES evolutions a signature may really be made at
    Exps,         \* expiry times, in whole seconds
    Bodies,       \* body sizes: "short" (< 90), "ok", "long" (> 2000)
    MaxEvo,       \* maxKESEvolutions
    TTL,          \* the longest allowed time to live, in seconds [R7]
    MaxTicks,     \* the clock stops here (keeps the model finite)
    MaxPeriod,    \* the current KES period stops here
    Workers,      \* goroutines that may hold a prepared batch at once
    BatchLen,     \* messages per batch: 1 or 2
    Mutation      \* "none", or which gOuroboros behaviour to model (cfgs)

\* In English: "Never is the counter value of a pool not seen yet."
\* Literally: "Never is defined as minus one."
Never == -1

\* In English: "Idle marks a worker with no prepared batch." It is a record,
\* like a prepared batch, so that the two can be compared.
\* Literally: "Idle is defined as the record whose field kind is "idle"."
Idle == [kind |-> "idle"]

\* In English: "Msgs is every message the model may see: every pool,
\* counter, opcert start, claimed period, real signing evolution, expiry
\* and body size from the cfg."
\* Literally: "Msgs is defined as the set of all records whose field pool
\*   is a member of Pools, field ctr is a member of Counters, field cert is a
\*   member of CertPeriods, field kp is a member of MsgPeriods, field sig is
\*   a member of SigEvos, field exp is a member of Exps, and field body is a
\*   member of Bodies."
Msgs == [pool : Pools, ctr : Counters, cert : CertPeriods, kp : MsgPeriods,
         sig : SigEvos, exp : Exps, body : Bodies]

\* In English: "Batches is every list of exactly BatchLen messages."
\* Literally: "Batches is defined as the set of all functions from the
\*   numbers 1 to BatchLen to Msgs."
Batches == [1..BatchLen -> Msgs]

VARIABLES
    now,      \* the clock, in half-second ticks
    period,   \* the current KES period, from the node's own slot [G2]
    seen,     \* pool -> highest counter recorded, or Never [R4][G3]
    pending,  \* worker -> a prepared batch, or Idle [G3]
    last      \* the most recent decision, for the invariants

\* Literally: "vars is defined as the tuple of all five variables."
vars == <<now, period, seen, pending, last>>

\* In English: "After message m is accepted, the pool's recorded counter
\* is m's counter." (Accepting m already required it to be no lower.)
\* Literally: "Record of s and m is defined as the function s, except that
\*   its value at m.pool is m.ctr."
Record(s, m) == [s EXCEPT ![m.pool] = m.ctr]

(***************************************************************************)
(* The reference rule [R1]-[R6], for one message, at clock nowT, with     *)
(* counters s. It does not use the current KES period at all [R5].         *)
(***************************************************************************)
\* In English: "The reference accepts m when it has not expired, does not
\* expire 1800 s or more after now, has an allowed body, claims a KES
\* period inside its opcert's window, comes from a staked pool, has a
\* counter no lower than the last one seen, and its signature was made at
\* the evolution its claimed period implies."
\* Literally: "RefOK of m, nowT and s is defined as: nowT is at most 2 times
\*   m.exp, and 2 times m.exp is less than nowT plus 2 times TTL, and m.body
\*   equals "ok", and m.kp is at least m.cert, and m.kp is less than m.cert
\*   plus MaxEvo, and m.pool is a member of Staked, and s of m.pool is at
\*   most m.ctr, and m.sig equals m.kp minus m.cert."
RefOK(m, nowT, s) ==
    /\ nowT <= 2 * m.exp                    \* not expired [R1]
    /\ 2 * m.exp < nowT + 2 * TTL           \* not too far ahead, strictly [R1]
    /\ m.body = "ok"                        \* 90..2000 bytes [R6][C1]
    /\ m.kp >= m.cert                       \* not before the opcert [R2]
    /\ m.kp < m.cert + MaxEvo               \* not after the opcert ends [R2]
    /\ m.pool \in Staked                    \* registered pool [R3]
    /\ s[m.pool] <= m.ctr                   \* counter not backwards [R4]
    /\ m.sig = m.kp - m.cert                \* signed at the claimed period [R5]

\* In English: "The reference accepts a whole batch, message by message,
\* each one checked against the counters the earlier ones recorded."
\* Literally: "RefBatchOK of b, nowT and s is defined as: if the length of
\*   b equals 1, then RefOK of b of 1, nowT and s; otherwise RefOK of b of
\*   1, nowT and s, and RefOK of b of 2, nowT and Record of s and b of 1."
RefBatchOK(b, nowT, s) ==
    IF Len(b) = 1 THEN RefOK(b[1], nowT, s)
    ELSE RefOK(b[1], nowT, s) /\ RefOK(b[2], nowT, Record(s, b[1]))

(***************************************************************************)
(* gOuroboros [G1]-[G4], with the cfg's Mutation selecting which of its   *)
(* current behaviours to use. "none" is the behaviour after the fixes.     *)
(***************************************************************************)
\* In English: "gOuroboros reads the clock in whole seconds when Mutation
\* is "TruncateNow" (main today), and in full precision otherwise."
\* Literally: "GoNow of nowT is defined as: if Mutation equals
\*   "TruncateNow", then 2 times (nowT divided by 2, rounded down); otherwise
\*   nowT."
GoNow(nowT) == IF Mutation = "TruncateNow" THEN 2 * (nowT \div 2) ELSE nowT

\* In English: "The evolution gOuroboros verifies the signature at: from
\* the current period when Mutation is "KesAtCurrent" (main today), from
\* the claimed period otherwise."
\* Literally: "GoEvo of m and per is defined as: if Mutation equals
\*   "KesAtCurrent", then per minus m.cert; otherwise m.kp minus m.cert."
GoEvo(m, per) == IF Mutation = "KesAtCurrent" THEN per - m.cert
                 ELSE m.kp - m.cert

\* In English: "Checks gOuroboros main makes that the reference does not
\* ("Extras"): the counter is not below the one in its chain state, and the
\* opcert has started and not ended at the node's own current period. The
\* fixes drop both, so otherwise there are none."
\* Literally: "GoExtras of m and per is defined as: if Mutation is a member
\*   of the set of "Extras" and "KesAtCurrent", then m.ctr is at least
\*   ChainFloor, and per is at least m.cert, and per minus m.cert is less
\*   than MaxEvo; otherwise TRUE."
GoExtras(m, per) ==
    IF Mutation \in {"Extras", "KesAtCurrent"}
    THEN /\ m.ctr >= ChainFloor             \* chain-state counter [G1]
         /\ per >= m.cert                   \* opcert started by now [G2]
         /\ per - m.cert < MaxEvo           \* opcert not ended by now [G2]
    ELSE TRUE

\* In English: "gOuroboros accepts m at clock nowT, current period per,
\* counters s, when every check it makes passes."
\* Literally: "GoOK of m, nowT, per and s is defined as: GoNow of nowT is at
\*   most 2 times m.exp; and, if Mutation equals "LaxUpper", 2 times m.exp is
\*   at most GoNow of nowT plus 2 times TTL, otherwise it is less than that;
\*   and Mutation equals "NoBodySize" or m.body equals "ok"; and m.pool is a
\*   member of Staked; and GoExtras of m and per; and m.kp is at least m.cert
\*   and less than m.cert plus MaxEvo; and m.sig equals GoEvo of m and per;
\*   and Mutation equals "NoCounterCheck" or s of m.pool is at most m.ctr."
GoOK(m, nowT, per, s) ==
    /\ GoNow(nowT) <= 2 * m.exp                         \* [G4]
    /\ IF Mutation = "LaxUpper"
         THEN 2 * m.exp <= GoNow(nowT) + 2 * TTL        \* main: equal passes [G4]
         ELSE 2 * m.exp < GoNow(nowT) + 2 * TTL
    /\ Mutation = "NoBodySize" \/ m.body = "ok"         \* main has no size check
    /\ m.pool \in Staked                                \* [G1]
    /\ GoExtras(m, per)                                 \* [G1][G2]
    /\ m.kp >= m.cert /\ m.kp < m.cert + MaxEvo         \* [G2]
    /\ m.sig = GoEvo(m, per)                            \* [G2]
    /\ Mutation = "NoCounterCheck" \/ s[m.pool] <= m.ctr \* [G1]

\* In English: "gOuroboros prepares a batch: it checks each message in
\* turn against a private copy of the counters that the earlier messages
\* updated."
\* Literally: "GoBatchOK of b, nowT, per and s is defined as: if the length
\*   of b equals 1, then GoOK of b of 1, nowT, per and s; otherwise GoOK of b
\*   of 1, nowT, per and s, and GoOK of b of 2, nowT, per and Record of s
\*   and b of 1."
GoBatchOK(b, nowT, per, s) ==
    IF Len(b) = 1 THEN GoOK(b[1], nowT, per, s)
    ELSE GoOK(b[1], nowT, per, s) /\ GoOK(b[2], nowT, per, Record(s, b[1]))

\* In English: "The counters after the batch, in the private copy."
\* Literally: "After of s and b is defined as: if the length of b equals 1,
\*   then Record of s and b of 1; otherwise Record of (Record of s and b of
\*   1) and b of 2."
After(s, b) == IF Len(b) = 1 THEN Record(s, b[1])
               ELSE Record(Record(s, b[1]), b[2])

\* In English: "The pools a batch touches."
\* Literally: "Touched of b is defined as the set of b of i's pool, for
\*   every i that is a member of the domain of b."
Touched(b) == {b[i].pool : i \in DOMAIN b}

\* In English: "At commit, gOuroboros re-checks every message's counter
\* against the counters recorded since the batch was prepared, as the
\* reference would check them now. "FinalOnlyRecheck" (main today)
\* re-checks only the last counter per pool, so an earlier, lower one in
\* the same batch escapes; "NoCommitRecheck" and "CommitOverwrites" skip
\* the re-check."
\* Literally: "CommitOK of fin, b and s is defined as: in the case Mutation
\*   is a member of the set of "NoCommitRecheck" and "CommitOverwrites",
\*   TRUE; in the case Mutation equals
\*   "FinalOnlyRecheck", for every p that is a member of Touched of b, fin of
\*   p is at least s of p; in any other case, for every i that is a member of
\*   the domain of b, b of i's ctr is at least s of b of i's pool."
CommitOK(fin, b, s) ==
    CASE Mutation \in {"NoCommitRecheck", "CommitOverwrites"} -> TRUE
      [] Mutation = "FinalOnlyRecheck" -> \A p \in Touched(b) : fin[p] >= s[p]
      [] OTHER -> \A i \in DOMAIN b : b[i].ctr >= s[b[i].pool]

\* In English: "What commit writes: for each touched pool the higher of
\* the batch's counter and the recorded one ("CommitOverwrites": the
\* batch's, even if lower)."
\* Literally: "Merged of fin, b and s is defined as the function that maps
\*   every p in Pools to: if p is a member of Touched of b, then (if
\*   Mutation equals "CommitOverwrites" or fin of p is greater than s of p,
\*   then fin of p, otherwise s of p); otherwise s of p."
Merged(fin, b, s) ==
    [p \in Pools |->
        IF p \in Touched(b)
        THEN IF Mutation = "CommitOverwrites" \/ fin[p] > s[p]
             THEN fin[p] ELSE s[p]
        ELSE s[p]]

\* In English: "Start: clock 0, period 0, no counters, no batches, no
\* decision yet."
\* Literally: "Init is defined as: now equals 0, and period equals 0, and
\*   seen equals the function mapping every p in Pools to Never, and pending
\*   equals the function mapping every w in Workers to Idle, and last equals
\*   the record whose field kind is "none"."
Init ==
    /\ now = 0
    /\ period = 0
    /\ seen = [p \in Pools |-> Never]
    /\ pending = [w \in Workers |-> Idle]
    /\ last = [kind |-> "none"]

\* In English: "Half a second passes."
\* Literally: "Tick is defined as: now is less than MaxTicks, and now in
\*   the next state equals now plus 1, and period, seen, pending and last
\*   are unchanged."
Tick ==
    /\ now < MaxTicks
    /\ now' = now + 1
    /\ UNCHANGED <<period, seen, pending, last>>

\* In English: "The node's slot moves into the next KES period."
\* Literally: "NextPeriod is defined as: period is less than MaxPeriod, and
\*   period in the next state equals period plus 1, and now, seen, pending
\*   and last are unchanged."
NextPeriod ==
    /\ period < MaxPeriod
    /\ period' = period + 1
    /\ UNCHANGED <<now, seen, pending, last>>

\* In English: "Worker w prepares batch b against a snapshot of the
\* counters. If it passes, w holds it until commit; if not, it is rejected
\* and nothing is recorded ("RecordOnReject": the counters the batch got
\* through before failing are recorded anyway)."
\* Literally: "Prepare of w and b is defined as: pending of w equals Idle,
\*   and, letting ok be GoBatchOK of b, now, period and seen: if ok, then
\*   pending in the next state equals pending except that w maps to the
\*   record of kind "prepared", b, now, period and After of seen and b, and seen is
\*   unchanged; otherwise pending is unchanged and seen in the next state
\*   equals (if Mutation equals "RecordOnReject" then Record of seen and b of
\*   1, otherwise seen); and last in the next state equals the record of
\*   kind "prepare", b, now, period, seen and ok; and now and period are
\*   unchanged."
Prepare(w, b) ==
    /\ pending[w] = Idle
    /\ LET ok == GoBatchOK(b, now, period, seen) IN
         /\ IF ok
              THEN /\ pending' = [pending EXCEPT ![w] =
                          [kind |-> "prepared", batch |-> b, now |-> now,
                           period |-> period, fin |-> After(seen, b)]]
                   /\ UNCHANGED seen
              ELSE /\ UNCHANGED pending
                   /\ seen' = IF Mutation = "RecordOnReject"
                              THEN Record(seen, b[1]) ELSE seen
         /\ last' = [kind |-> "prepare", batch |-> b, now |-> now,
                     period |-> period, seen |-> seen, accepted |-> ok]
    /\ UNCHANGED <<now, period>>

\* In English: "Worker w commits its prepared batch: if the re-check
\* passes, the counters are merged in and the batch is accepted; if not,
\* it is rejected and nothing changes. Either way w is idle again."
\* Literally: "Commit of w is defined as: pending of w is not Idle, and,
\*   letting q be pending of w and ok be CommitOK of q.fin, q.batch and
\*   seen: seen in the next state equals (if ok then Merged of q.fin, q.batch
\*   and seen, otherwise seen), and pending in the next state equals pending
\*   except that w maps to Idle, and last in the next state equals the
\*   record of kind "commit", q's batch, now and period, seen and ok; and now
\*   and period are unchanged."
Commit(w) ==
    /\ pending[w] # Idle
    /\ LET q == pending[w]
           ok == CommitOK(q.fin, q.batch, seen)
       IN /\ seen' = IF ok THEN Merged(q.fin, q.batch, seen) ELSE seen
          /\ pending' = [pending EXCEPT ![w] = Idle]
          /\ last' = [kind |-> "commit", batch |-> q.batch, now |-> q.now,
                      period |-> q.period, seen |-> seen, accepted |-> ok]
    /\ UNCHANGED <<now, period>>

\* In English: "Some step happens: time passes, the period advances, a
\* worker prepares a batch, or a worker commits one."
\* Literally: "Next is defined as: Tick, or NextPeriod, or there exist w in
\*   Workers and b in Batches such that Prepare of w and b, or there exists
\*   w in Workers such that Commit of w."
Next ==
    \/ Tick
    \/ NextPeriod
    \/ \E w \in Workers, b \in Batches : Prepare(w, b)
    \/ \E w \in Workers : Commit(w)

\* Literally: "Spec is defined as: Init, and always (Next or vars unchanged)."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
\* In English: "Whatever gOuroboros accepted, the reference would accept
\* at the same moment with the same counters." For a commit, "the same
\* counters" are the ones recorded when it commits.
\* Literally: "NoAcceptBeyondReference is defined as: if last.kind is not
\*   "none" and last.accepted, then RefBatchOK of last.batch, last.now and
\*   last.seen."
NoAcceptBeyondReference ==
    (last.kind # "none" /\ last.accepted)
        => RefBatchOK(last.batch, last.now, last.seen)

\* In English: "Whatever the reference would accept, gOuroboros accepted
\* too."
\* Literally: "AcceptAsReference is defined as: if last.kind is not "none"
\*   and RefBatchOK of last.batch, last.now and last.seen, then
\*   last.accepted."
AcceptAsReference ==
    (/\ last.kind # "none"
     /\ RefBatchOK(last.batch, last.now, last.seen))
        => last.accepted

\* In English: "A pool's recorded counter never goes down."
\* Literally: "SeenMonotone is defined as: always, for every step, for
\*   every p in Pools, seen of p in the next state is at least seen of p."
SeenMonotone == [][\A p \in Pools : seen'[p] >= seen[p]]_vars

\* In English: "A rejected decision records nothing."
\* Literally: "RejectKeepsSeen is defined as: always, for every step, if
\*   last in the next state is not of kind "none" and is not accepted, and
\*   last changed, then seen in the next state equals seen."
RejectKeepsSeen ==
    [][(last'.kind # "none" /\ ~last'.accepted /\ last' # last)
          => seen' = seen]_vars

(***************************************************************************)
(* Probes: each is expected to be violated, showing the state is reachable *)
(***************************************************************************)
\* In English: "No message signed in an earlier KES period is accepted
\* after the period has moved on." Violated once the fix lets a message
\* cross a period boundary, as the reference allows.
\* Literally: "ProbeNoCrossPeriodAccept is defined as: it is not the case
\*   that last.kind is not "none" and last.accepted and last.period is
\*   greater than last.batch of 1's kp."
ProbeNoCrossPeriodAccept ==
    ~(last.kind # "none" /\ last.accepted /\ last.period > last.batch[1].kp)

\* In English: "No batch is ever accepted." Violated: acceptance happens.
\* Literally: "ProbeNoAccept is defined as: it is not the case that
\*   last.kind equals "commit" and last.accepted."
ProbeNoAccept == ~(last.kind = "commit" /\ last.accepted)
=============================================================================
