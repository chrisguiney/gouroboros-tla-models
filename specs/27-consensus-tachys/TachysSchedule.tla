--------------------------- MODULE TachysSchedule ---------------------------
(***************************************************************************)
(* The Ouroboros Tachys public slot leader schedule (CIP-0177): the        *)
(* cumulative stake distribution, the per-slot sample, the leader lookup,  *)
(* and what changes in header validation and block production.            *)
(*                                                                         *)
(* Tachys keeps Praos (headers, VRF, KES, opcerts, the epoch nonce) and    *)
(* replaces one thing: who may make a block in a slot. Instead of a        *)
(* private VRF lottery, every slot has exactly one leader, drawn from the  *)
(* stake distribution with a hash of the epoch nonce and the slot.         *)
(*                                                                         *)
(* Sources. specs/27-consensus-tachys/README.md has links and quotes.      *)
(*   Specification: cardano-foundation/CIPs 86b89208d3b2,                  *)
(*   CIP-0177/README.md (the revision gOuroboros pins):                    *)
(*   [S1] 96, 112: headers, VRF and KES stay as in Praos; only            *)
(*        authorisation changes.                                           *)
(*   [S2] 114-116, 390: one SPO per slot, drawn with probability equal to  *)
(*        its stake fraction, independently per slot, seeded by the epoch  *)
(*        nonce.                                                           *)
(*   [S3] 151-155: the new leader check: the SPO identifier computed for   *)
(*        the slot must equal the hash of the header's cold key.           *)
(*   [S4] 163-165: sample = hash(nonce representation ++ slot              *)
(*        representation), read as a fraction with denominator 2^256.      *)
(*   [S5] 167-171: each SPO owns an interval [lo, hi), inclusive below,    *)
(*        exclusive above, of width exactly its stake fraction; the        *)
(*        intervals are contiguous and cover [0, 1); exact integer         *)
(*        arithmetic is allowed.                                           *)
(*   [S6] 175-183: the cumulative distribution is built by a running sum   *)
(*        over SPOs in order of the representation of their identifiers.   *)
(*   [S7] 191-195: block production reuses the validity predicate.         *)
(*   Reference: no implementation of CIP-0177 exists in                    *)
(*   IntersectMBO/ouroboros-consensus ec239d57f618 or cardano-ledger       *)
(*   1210d37f. The model uses the reference only for the distribution     *)
(*   that a Tachys node would read:                                        *)
(*   [R1] cardano-ledger 1210d37f, libs/cardano-ledger-core/src/Cardano/   *)
(*        Ledger/State/SnapShots.hs 679-696: PoolDistr keeps every pool    *)
(*        with at least one delegator (`spssNumDelegators > 0`), so a pool *)
(*        whose delegators hold no stake is in it with stake 0.            *)
(*   [R2] same file 317-321: total active stake is a NonZero Coin that     *)
(*        defaults to 1 when no stake is delegated.                        *)
(*                                                                         *)
(* gOuroboros (main 756a9a898573): consensus/tachys.go                     *)
(* (NewTachysLeaderSelector 56-102, LeaderForSample 142-167, IsLeader,     *)
(* AuthorizeIssuer 184-197, IsTachysSlotLeader 202-260), consensus/        *)
(* validate.go (NewTachysHeaderValidator 39-53, validateLeadership         *)
(* 480-500), consensus/block.go (CheckSlotLeadership, BuildHeader).        *)
(* The caller modelled is Dingo's ledger/tachys.go                         *)
(* tachysPoolsFromStakeDistribution, which drops zero-stake pools.         *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla and the   *)
(* repository README section "Reading a formula literally".                *)
(* New here: RECURSIVE (an operator that calls itself, like a recursive Go *)
(* function), and SUBSET S (every subset of S).                            *)
(*                                                                         *)
(* ABSTRACTIONS                                                            *)
(*   - A pool ID is a natural number; numeric order stands for the byte    *)
(*     order of 28-byte IDs [S6].                                          *)
(*   - A sample is a number in 0..D-1; D stands for 2^256 [S4]. The hash   *)
(*     is any function from (nonce, slot) to a sample: TLC tries them all, *)
(*     so no particular hash output is assumed.                            *)
(*   - WordMax stands for the largest uint64.                              *)
(*   - Header cryptography is a record of booleans: each check passed or   *)
(*     failed. Model 13 checks opcerts and KES themselves.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Pools,      \* every pool ID that can appear (natural numbers)
    MaxStake,   \* a pool's stake is one of 0..MaxStake
    D,          \* the number of samples; stands for 2^256 [S4]
    Nonces,     \* the epoch nonces the model tries
    Slots,      \* the slots the model tries
    WordMax,    \* the largest value a uint64 holds, scaled down
    ZeroStake,  \* "Filter": the caller drops zero-stake pools (Dingo);
                \* "Pass": the caller passes the reference PoolDistr as is
    Declared,   \* "Exact": the caller passes the exact sum as totalStake;
                \* "Any": the caller may pass any total (0..sum+1)
    GoZero,     \* "Reject": gOuroboros main rejects a zero-stake pool;
                \* "Accept": a zero-stake pool gets an empty interval
    Mutation    \* "none", or a deliberate bug to prove an invariant can fail

\* In English: "D is a positive number and pool IDs are numbers."
\* Literally: "it is assumed that D is a member of the set of naturals
\*   without 0, and Pools is a subset of the naturals."
ASSUME D \in Nat \ {0} /\ Pools \subseteq Nat

\* In English: "The possible samples: 0 up to D-1, standing for 0 up to
\* 2^256 - 1 [S4]."
\* Literally: "Samples is defined as 0 through D minus 1."
Samples == 0..(D - 1)
\* In English: "The stakes a pool can hold in the model."
\* Literally: "Stakes is defined as 0 through MaxStake."
Stakes == 0..MaxStake

\* In English: "Sum calls itself."
\* Literally: "Sum is defined recursively" (the reading sits above the next
\*   definition).
RECURSIVE Sum(_, _)
\* In English: "Sum(f, S) adds up f[x] for every x in S."
\* Literally: "Sum of f and S is defined as: if S equals the empty set then
\*   0, else, letting x be the x chosen from S such that TRUE, f of x plus
\*   Sum of f and S without the members of the set containing x."
Sum(f, S) == IF S = {} THEN 0                          \* nothing to add
             ELSE LET x == CHOOSE x \in S : TRUE       \* take any member
                  IN f[x] + Sum(f, S \ {x})            \* add it to the rest

\* In English: "Every way to list the members of S once each, in any
\* order." The caller's slice can be in any order.
\* Literally: "Orderings of S is defined as the set of every o in the set of
\*   functions from 1 through the number of members of S to S such that for
\*   all i in the domain of o and for all j in the domain of o, if i does not
\*   equal j then o of i does not equal o of j."
Orderings(S) ==
    {o \in [1..Cardinality(S) -> S] :
        \A i \in DOMAIN o : \A j \in DOMAIN o : i /= j => o[i] /= o[j]}  \* no repeats

\* In English: "The members of S listed in increasing order" [S6].
\* Literally: "Sorted of S is defined as the function that maps every i in
\*   1 through the number of members of S to the x, chosen from S, such that
\*   the number of members of the set of every y in S such that y is less
\*   than x equals i minus 1."
Sorted(S) ==
    [i \in 1..Cardinality(S) |->
        CHOOSE x \in S : Cardinality({y \in S : y < x}) = i - 1]  \* the i-th smallest

\* In English: "The distributions the reference can produce: any set of
\* pools, each with any stake, including 0 [R1]."
\* Literally: "Distributions is defined as the union of all the sets in the
\*   set of the set of functions from S to Stakes, for every S that is a
\*   member of the set of subsets of Pools."
Distributions == UNION {[S -> Stakes] : S \in SUBSET Pools}

\* In English: "Every combination of header checks: VRF proof, KES
\* signature, opcert signature, registered VRF key, and whether the VRF
\* output would also pass the Praos threshold."
\* Literally: "Crypto is defined as the set of records whose field vrf is a
\*   member of BOOLEAN, field kes is a member of BOOLEAN, field ocert is a
\*   member of BOOLEAN, field vrfKey is a member of BOOLEAN, and field praos
\*   is a member of BOOLEAN."
Crypto == [vrf : BOOLEAN, kes : BOOLEAN, ocert : BOOLEAN,
           vrfKey : BOOLEAN, praos : BOOLEAN]

VARIABLES
    dist,       \* the reference stake distribution for the epoch [R1]
    order,      \* the order of the caller's slice (any order)
    hash,       \* the sample for each (nonce, slot): any function [S4]
    declared,   \* the totalStake the caller passes
    sel,        \* the selector gOuroboros built, or [ok |-> FALSE]
    callerStake,\* the caller's slice contents now; it may change them later
    log,        \* every <<nonce, slot, leader>> answer given so far
    phase       \* "build", "query", or "failed"

\* In English: "All the variables, for saying "nothing changes"."
\* Literally: "vars is defined as the tuple of dist, order, hash, declared,
\*   sel, callerStake, log and phase."
vars == <<dist, order, hash, declared, sel, callerStake, log, phase>>

(***************************************************************************)
(* THE SPECIFICATION'S SCHEDULE [S5][S6]                                   *)
(***************************************************************************)

\* In English: "The total active stake: the sum of every pool's stake."
\* Literally: "Total is defined as Sum of dist and the domain of dist."
Total == Sum(dist, DOMAIN dist)

\* In English: "A schedule exists when some stake is delegated. With no
\* stake there is no interval to land in; the reference's NonZero total
\* of 1 [R2] would make every fraction 0, so no pool covers [0, 1)."
\* Literally: "SpecDefined is defined as Total is greater than 0."
SpecDefined == Total > 0

\* In English: "Pool p's interval starts at the stake of every pool with a
\* smaller ID [S6]."
\* Literally: "Lo of p is defined as Sum of dist and the set of every q in
\*   the domain of dist such that q is less than p."
Lo(p) == Sum(dist, {q \in DOMAIN dist : q < p})

\* In English: "and ends its own stake later (exclusive) [S5]."
\* Literally: "Hi of p is defined as Lo of p plus dist of p."
Hi(p) == Lo(p) + dist[p]

\* In English: "Sample x lands in p's interval: lo/T <= x/D < hi/T, with
\* both sides multiplied out so that only integers are compared [S5]."
\* Literally: "InSpec of x and p is defined as Lo of p times D is at most x
\*   times Total, and x times Total is less than Hi of p times D."
InSpec(x, p) == /\ Lo(p) * D <= x * Total   \* at or above the lower bound
                /\ x * Total < Hi(p) * D    \* strictly below the upper bound

\* In English: "Every pool whose interval holds x."
\* Literally: "SpecLeaders of x is defined as the set of every p in the
\*   domain of dist such that InSpec of x and p."
SpecLeaders(x) == {p \in DOMAIN dist : InSpec(x, p)}

\* In English: "The leader for x: the pool whose interval holds it, or 0 when
\* none does."
\* Literally: "SpecLeader of x is defined as: if SpecLeaders of x equals the
\*   empty set then 0, else the p, chosen from SpecLeaders of x, such that
\*   TRUE."
SpecLeader(x) == IF SpecLeaders(x) = {} THEN 0
                 ELSE CHOOSE p \in SpecLeaders(x) : TRUE

(***************************************************************************)
(* THE CALLER [Dingo ledger/tachys.go]                                     *)
(***************************************************************************)

\* In English: "The pools the caller hands to gOuroboros: all of them, or
\* only those with stake."
\* Literally: "InputPools is defined as: if ZeroStake equals "Filter" then
\*   the set of every p in the domain of dist such that dist of p is greater
\*   than 0, else the domain of dist."
InputPools == IF ZeroStake = "Filter"
              THEN {p \in DOMAIN dist : dist[p] > 0}   \* Dingo drops zero stake
              ELSE DOMAIN dist                         \* the PoolDistr as is

(***************************************************************************)
(* gOuroboros: NewTachysLeaderSelector (tachys.go 56-102)                  *)
(***************************************************************************)

\* In English: "The order gOuroboros lays the intervals out in: sorted by
\* ID; the "unsorted" mutation keeps the caller's order."
\* Literally: "GoOrder of o and S is defined as: if Mutation equals
\*   "unsorted" then o, else Sorted of S."
GoOrder(o, S) == IF Mutation = "unsorted" THEN o ELSE Sorted(S)

\* In English: "Interval i's upper bound: the running sum of stakes up to
\* and including pool i (tachys.go 83-91). The "upperIsStake" mutation
\* forgets the running sum."
\* Literally: "Uppers of ids and st is defined as the function that maps
\*   every i in the domain of ids to: if Mutation equals "upperIsStake" then
\*   st of ids of i, else Sum of the function that maps every j in 1 through
\*   i to st of ids of j, and 1 through i."
Uppers(ids, st) ==
    [i \in DOMAIN ids |->
        IF Mutation = "upperIsStake" THEN st[ids[i]]           \* bug: own stake only
        ELSE Sum([j \in 1..i |-> st[ids[j]]], 1..i)]          \* running sum

\* In English: "Build the selector, failing as gOuroboros does: no pools,
\* a zero total, a zero-stake pool (unless accepted), a running sum past
\* uint64, or a sum that is not the declared total (unless the mutation
\* drops that check)."
\* Literally: "GoBuild of S, st, o and t is defined as: letting ids be
\*   GoOrder of o and S, and up be Uppers of ids and st: if S equals the
\*   empty set, or t equals 0, or (GoZero equals "Reject" and there exists
\*   a p in S such that st of p equals 0), or there exists an i in the domain
\*   of up such that up of i is greater than WordMax, or (Mutation does not
\*   equal "noTotalCheck" and Sum of st and S does not equal t), then the
\*   record whose field ok is FALSE, else the record whose field ok is TRUE,
\*   field ids is ids, field up is up, and field total is t."
GoBuild(S, st, o, t) ==
    LET ids == GoOrder(o, S)
        up  == Uppers(ids, st)
    IN IF \/ S = {}                                          \* empty (line 60)
          \/ t = 0                                           \* zero total (63)
          \/ GoZero = "Reject" /\ \E p \in S : st[p] = 0     \* zero stake (73)
          \/ \E i \in DOMAIN up : up[i] > WordMax            \* overflow (84)
          \/ Mutation /= "noTotalCheck" /\ Sum(st, S) /= t   \* mismatch (93)
       THEN [ok |-> FALSE]
       ELSE [ok |-> TRUE, ids |-> ids, up |-> up, total |-> t]

(***************************************************************************)
(* gOuroboros: LeaderForSample (tachys.go 142-167)                          *)
(***************************************************************************)

\* In English: "The search predicate: x*total < upper*D. The "inclusive"
\* mutation uses <=, putting each upper bound inside its interval."
\* Literally: "Below of a and b is defined as: if Mutation equals
\*   "inclusive" then a is at most b, else a is less than b."
Below(a, b) == IF Mutation = "inclusive" THEN a <= b ELSE a < b

\* In English: "The uppers the lookup reads: the selector's own copy, or,
\* with the "alias" mutation, ones recomputed from the caller's slice as it
\* is now."
\* Literally: "LiveUp is defined as: if Mutation equals "alias" then Uppers
\*   of sel's ids and callerStake, else sel's up."
LiveUp == IF Mutation = "alias" THEN Uppers(sel.ids, callerStake) ELSE sel.up

\* In English: "sort.Search: the first interval whose upper bound is above
\* the sample, or 0 when none is (Go would index past the end and panic)."
\* Literally: "GoIndex of x is defined as: letting hits be the set of every
\*   i in the domain of LiveUp such that Below of x times sel's total and
\*   LiveUp of i times D: if hits equals the empty set then 0, else the i,
\*   chosen from hits, such that for all j in hits, i is at most j."
GoIndex(x) ==
    LET hits == {i \in DOMAIN LiveUp : Below(x * sel.total, LiveUp[i] * D)}
    IN IF hits = {} THEN 0
       ELSE CHOOSE i \in hits : \A j \in hits : i <= j      \* the smallest

\* In English: "The pool gOuroboros names for sample x (0 if none)."
\* Literally: "GoLeader of x is defined as: if GoIndex of x equals 0 then 0,
\*   else sel's ids of GoIndex of x."
GoLeader(x) == IF GoIndex(x) = 0 THEN 0 ELSE sel.ids[GoIndex(x)]

\* In English: "Leader(nonce, slot): hash the pair to a sample, look it up."
\* Literally: "GoLeaderAt of n and s is defined as GoLeader of hash of the
\*   tuple of n and s."
GoLeaderAt(n, s) == GoLeader(hash[<<n, s>>])

\* In English: "The intervals gOuroboros holds for sample x, read with its
\* own comparison: lower bound (the previous upper) at or below, and Below
\* the upper."
\* Literally: "GoCovering of x is defined as the set of every i in the
\*   domain of sel's up such that, letting lo be (if i equals 1 then 0 else
\*   sel's up of i minus 1), lo times D is at most x times sel's total and
\*   Below of x times sel's total and sel's up of i times D."
GoCovering(x) ==
    {i \in DOMAIN sel.up :
        LET lo == IF i = 1 THEN 0 ELSE sel.up[i - 1]
        IN /\ lo * D <= x * sel.total                       \* at or above lo
           /\ Below(x * sel.total, sel.up[i] * D)}          \* below hi

(***************************************************************************)
(* gOuroboros: header validation and block production                      *)
(***************************************************************************)

\* In English: "AuthorizeIssuer: the issuer is the scheduled pool. The
\* "anyPool" mutation accepts any pool in the distribution."
\* Literally: "GoAuthorized of n, s and p is defined as: if Mutation equals
\*   "anyPool" then there exists an i in the domain of sel's ids such that sel's
\*   ids of i equals p, else GoLeaderAt of n and s equals p."
GoAuthorized(n, s, p) ==
    IF Mutation = "anyPool" THEN \E i \in DOMAIN sel.ids : sel.ids[i] = p
    ELSE GoLeaderAt(n, s) = p

\* In English: "ValidateHeader with a Tachys selector: the VRF proof is
\* still verified and the leader check runs only after it (validate.go
\* 185-198); authorisation is the schedule instead of the Praos threshold;
\* KES, opcert and VRF-key checks are unchanged. Mutations: "praosThreshold"
\* keeps the Praos threshold as well, "skipVrf" drops VRF verification."
\* Literally: "GoValidate of n, s, p and c is defined as: (Mutation equals
\*   "skipVrf" or c's vrf) and GoAuthorized of n, s and p and (if Mutation
\*   equals "praosThreshold" then c's praos, else TRUE) and c's kes and c's
\*   ocert and c's vrfKey."
GoValidate(n, s, p, c) ==
    /\ Mutation = "skipVrf" \/ c.vrf                        \* VRF proof (step 4)
    /\ GoAuthorized(n, s, p)                                \* the schedule (step 5)
    /\ IF Mutation = "praosThreshold" THEN c.praos ELSE TRUE \* no Praos lottery
    /\ c.kes                                                \* KES (steps 7-8)
    /\ c.ocert                                              \* opcert (9-10)
    /\ c.vrfKey                                             \* registered VRF key

\* In English: "IsTachysSlotLeader: the producer forges exactly when the
\* schedule names it. The "forgePraos" mutation also asks the Praos
\* lottery."
\* Literally: "GoForge of n, s, p and praos is defined as GoAuthorized of n,
\*   s and p, and (if Mutation equals "forgePraos" then praos, else TRUE)."
GoForge(n, s, p, praos) ==
    /\ GoAuthorized(n, s, p)                                \* scheduled
    /\ IF Mutation = "forgePraos" THEN praos ELSE TRUE      \* no lottery

(***************************************************************************)
(* THE STATE MACHINE                                                       *)
(***************************************************************************)

\* In English: "Start from any distribution, any slice order, any hash,
\* and a declared total that is exact or, with Declared = "Any", anything
\* from 0 to one past the sum."
\* Literally: "Init is defined as: dist is a member of Distributions, and
\*   order is a member of Orderings of InputPools, and hash is a member of the
\*   set of functions from the Cartesian product of Nonces and Slots to
\*   Samples, and declared is a member of (if Declared equals "Exact" then the
\*   set containing Sum of dist and InputPools, else 0 through Sum of dist and
\*   InputPools plus 1), and callerStake equals the function that maps every
\*   p in InputPools to dist of p, and log equals the empty set, and phase
\*   equals "build", and sel equals the record whose field ok is FALSE."
Init ==
    /\ dist \in Distributions                               \* any epoch snapshot
    /\ order \in Orderings(InputPools)                      \* any slice order
    /\ hash \in [Nonces \X Slots -> Samples]                \* any hash
    /\ declared \in IF Declared = "Exact"
                    THEN {Sum(dist, InputPools)}            \* the exact sum
                    ELSE 0..(Sum(dist, InputPools) + 1)     \* any total
    /\ callerStake = [p \in InputPools |-> dist[p]]         \* the slice
    /\ log = {}                                             \* nothing asked yet
    /\ phase = "build"                                      \* not built yet
    /\ sel = [ok |-> FALSE]                                 \* no selector yet

\* In English: "The caller calls NewTachysLeaderSelector."
\* Literally: "Build is defined as: phase equals "build", and sel in the next
\*   state equals GoBuild of InputPools, callerStake, order and declared, and
\*   phase in the next state equals (if sel in the next state's ok then
\*   "query", else "failed"), and dist, order, hash, declared, callerStake
\*   and log are unchanged."
Build ==
    /\ phase = "build"                                      \* only once
    /\ sel' = GoBuild(InputPools, callerStake, order, declared)
    /\ phase' = IF sel'.ok THEN "query" ELSE "failed"       \* built or refused
    /\ UNCHANGED <<dist, order, hash, declared, callerStake, log>>

\* In English: "Someone asks for the leader of (n, s); the answer is
\* logged."
\* Literally: "Query of n and s is defined as: phase equals "query", and log
\*   in the next state equals the union of log and the set containing the
\*   tuple of n, s and GoLeaderAt of n and s, and dist, order, hash,
\*   declared, sel, callerStake and phase are unchanged."
Query(n, s) ==
    /\ phase = "query"                                      \* selector built
    /\ log' = log \cup {<<n, s, GoLeaderAt(n, s)>>}         \* record the answer
    /\ UNCHANGED <<dist, order, hash, declared, sel, callerStake, phase>>

\* In English: "After building, the caller reuses its slice and overwrites
\* the stakes (TestTachysSelectorCopiesDistribution does this)."
\* Literally: "CallerReuses is defined as: phase equals "query", and
\*   callerStake in the next state is a member of the set of functions from
\*   the domain of callerStake to Stakes, and dist, order, hash, declared,
\*   sel, log and phase are unchanged."
CallerReuses ==
    /\ phase = "query"                                      \* after building
    /\ callerStake' \in [DOMAIN callerStake -> Stakes]      \* any new contents
    /\ UNCHANGED <<dist, order, hash, declared, sel, log, phase>>

\* In English: "A refused distribution leaves nothing to do; the model
\* idles rather than reporting a deadlock (BuildAgrees checks refusals)."
\* Literally: "Idle is defined as: phase equals "failed", and vars is
\*   unchanged."
Idle == phase = "failed" /\ UNCHANGED vars

\* In English: "A step builds the selector, answers a query, lets the
\* caller reuse its slice, or idles after a refusal."
\* Literally: "Next is defined as: Build, or there exists an n in Nonces and
\*   an s in Slots such that Query of n and s, or CallerReuses, or Idle."
Next == Build \/ (\E n \in Nonces, s \in Slots : Query(n, s)) \/ CallerReuses \/ Idle

\* In English: "Start in Init and take Next steps."
\* Literally: "Spec is defined as Init and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

\* In English: "Once built, gOuroboros has a schedule exactly when the
\* specification has one."
\* Literally: "BuildAgrees is defined as: if phase does not equal "build"
\*   then sel's ok if and only if SpecDefined."
BuildAgrees == phase /= "build" => (sel.ok <=> SpecDefined)

\* In English: "Every sample has exactly one leader: one interval of the
\* specification [S5] and one of gOuroboros hold it."
\* Literally: "ExactlyOneLeader is defined as: (if SpecDefined then for all
\*   x in Samples, the number of members of SpecLeaders of x equals 1), and
\*   (if sel's ok then for all x in Samples, the number of members of
\*   GoCovering of x equals 1)."
ExactlyOneLeader ==
    /\ SpecDefined => \A x \in Samples : Cardinality(SpecLeaders(x)) = 1
    /\ sel.ok => \A x \in Samples : Cardinality(GoCovering(x)) = 1

\* In English: "The lookup always finds a pool: no sample falls past the
\* last interval (Go would panic)."
\* Literally: "LeaderDefined is defined as: if sel's ok then for all x in
\*   Samples, GoIndex of x does not equal 0."
LeaderDefined == sel.ok => \A x \in Samples : GoIndex(x) /= 0

\* In English: "gOuroboros names the specification's leader for every
\* sample."
\* Literally: "LeaderAgrees is defined as: if sel's ok then for all x in
\*   Samples, GoLeader of x equals SpecLeader of x."
LeaderAgrees == sel.ok => \A x \in Samples : GoLeader(x) = SpecLeader(x)

\* In English: "Each interval is exactly as wide as its pool's stake [S5]."
\* Literally: "WidthEqualsStake is defined as: if sel's ok then for all i in
\*   the domain of sel's up, sel's up of i minus (if i equals 1 then 0 else
\*   sel's up of i minus 1) equals dist of sel's ids of i."
WidthEqualsStake ==
    sel.ok => \A i \in DOMAIN sel.up :
        sel.up[i] - (IF i = 1 THEN 0 ELSE sel.up[i - 1]) = dist[sel.ids[i]]

\* In English: "A pool's chance is its stake share: of the D samples, the
\* number it leads is within one of stake*D/T [S2]."
\* Literally: "Proportional is defined as: if sel's ok then for all p in the
\*   domain of dist, letting c be the number of members of the set of every x
\*   in Samples such that GoLeader of x equals p: c times Total plus Total is
\*   greater than dist of p times D, and c times Total is less than dist of p
\*   times D plus Total."
Proportional ==
    sel.ok => \A p \in DOMAIN dist :
        LET c == Cardinality({x \in Samples : GoLeader(x) = p})
        IN /\ c * Total + Total > dist[p] * D               \* not one short
           /\ c * Total < dist[p] * D + Total               \* not one over

\* In English: "A pool with no stake never leads."
\* Literally: "ZeroStakeNeverLeads is defined as: if sel's ok then for all x
\*   in Samples, (GoLeader of x is a member of the domain of dist) and dist of
\*   GoLeader of x is greater than 0."
ZeroStakeNeverLeads ==
    sel.ok => \A x \in Samples :
        GoLeader(x) \in DOMAIN dist /\ dist[GoLeader(x)] > 0

\* In English: "The same nonce and slot always give the same leader, even
\* after the caller reuses its slice."
\* Literally: "SameInputsSameLeader is defined as: for all e in log,
\*   GoLeaderAt of e's element 1 and e's element 2 equals e's element 3."
SameInputsSameLeader == \A e \in log : GoLeaderAt(e[1], e[2]) = e[3]

\* In English: "The validator accepts exactly the scheduled issuer, when
\* every cryptographic check passes, whether or not the VRF output would
\* have won a Praos lottery [S1][S3]."
\* Literally: "ValidatorExact is defined as: if sel's ok then for all n in
\*   Nonces, s in Slots, p in Pools and c in Crypto, GoValidate of n, s, p
\*   and c if and only if (c's vrf and c's kes and c's ocert and c's vrfKey
\*   and p equals SpecLeader of hash of the tuple of n and s)."
ValidatorExact ==
    sel.ok => \A n \in Nonces, s \in Slots, p \in Pools, c \in Crypto :
        GoValidate(n, s, p, c) <=>
            /\ c.vrf /\ c.kes /\ c.ocert /\ c.vrfKey        \* Praos authentication
            /\ p = SpecLeader(hash[<<n, s>>])               \* the scheduled pool

\* In English: "A producer forges exactly when its header would be
\* authorised [S7]."
\* Literally: "ForgeMatchesValidate is defined as: if sel's ok then for all n
\*   in Nonces, s in Slots, p in Pools and b in BOOLEAN, GoForge of n, s, p
\*   and b if and only if p equals SpecLeader of hash of the tuple of n and s."
ForgeMatchesValidate ==
    sel.ok => \A n \in Nonces, s \in Slots, p \in Pools, b \in BOOLEAN :
        GoForge(n, s, p, b) <=> p = SpecLeader(hash[<<n, s>>])

(***************************************************************************)
(* PROBES: expected to be violated, to show a state is reachable.          *)
(***************************************************************************)

\* In English: "Some sample sits exactly on an interval's upper bound, so
\* the exclusive edge is exercised."
\* Literally: "ProbeBoundary is defined as: it is not true that (sel's ok and
\*   there exists an x in Samples and an i in the domain of sel's up such
\*   that i is less than the length of sel's up and x times sel's total
\*   equals sel's up of i times D)."
ProbeBoundary ==
    ~(sel.ok /\ \E x \in Samples, i \in DOMAIN sel.up :
                    i < Len(sel.up) /\ x * sel.total = sel.up[i] * D)

\* In English: "A reference distribution with a zero-stake pool still gets
\* a schedule."
\* Literally: "ProbeZeroStake is defined as: it is not true that (sel's ok
\*   and there exists a p in the domain of dist such that dist of p equals
\*   0)."
ProbeZeroStake == ~(sel.ok /\ \E p \in DOMAIN dist : dist[p] = 0)

\* In English: "A single-pool schedule is built."
\* Literally: "ProbeSinglePool is defined as: it is not true that (sel's ok
\*   and the length of sel's ids equals 1)."
ProbeSinglePool == ~(sel.ok /\ Len(sel.ids) = 1)

\* In English: "The largest sample is asked for."
\* Literally: "ProbeLargestSample is defined as: it is not true that there
\*   exists an e in log such that hash of the tuple of e's element 1 and e's
\*   element 2 equals D minus 1."
ProbeLargestSample == ~(\E e \in log : hash[<<e[1], e[2]>>] = D - 1)

\* In English: "The caller overwrote its slice after building and a later
\* query still ran."
\* Literally: "ProbeReused is defined as: it is not true that (log does not
\*   equal the empty set and there exists a p in the domain of callerStake
\*   such that callerStake of p does not equal dist of p)."
ProbeReused ==
    ~(log /= {} /\ \E p \in DOMAIN callerStake : callerStake[p] /= dist[p])
=============================================================================
