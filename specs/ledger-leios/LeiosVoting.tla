---------------------------- MODULE LeiosVoting ----------------------------
(***************************************************************************)
(* Seating the Leios voting committee, collecting its votes in one         *)
(* election, and turning them into a certificate.                          *)
(*                                                                         *)
(* At the epoch boundary the committee is fixed: the Nc pools with the     *)
(* most stake, ties broken by ascending pool id, every pool if fewer are   *)
(* registered. A seat holds a key only if its pool registered one, its     *)
(* proof of possession verifies, and it has not aged out. Each seat's      *)
(* vote weighs its pool's share of the total active stake.                 *)
(*                                                                         *)
(* In one election slot up to two announcements ("a" and "b", an           *)
(* equivocating pair) may be voted on. Votes arrive in any order, any      *)
(* number of times, from any seat number, with good or bad signatures.     *)
(* The node keeps the first valid vote of each seat in the election,       *)
(* whichever announcement it is for, tallies each announcement, and        *)
(* aggregates the votes for an announcement into its certificate the       *)
(* moment its tally reaches the quorum share tau of the total stake.       *)
(*                                                                         *)
(* gOuroboros neither seats the committee nor collects votes: the caller   *)
(* hands it the seated committee, and it verifies certificates. So the     *)
(* model asks whether every certificate the reference forms is one         *)
(* gOuroboros accepts, and whether, over every signer set, gOuroboros      *)
(* accepts exactly what the reference accepts.                            *)
(*                                                                         *)
(* Sources (quotes and links in README.md).                                *)
(*   CIP-0164 at cardano-foundation/CIPs db48da14bff1, CIP-0164/README.md: *)
(*   [C1] 851-887 "Committee Structure": the top Nc pools by active stake, *)
(*        ties by ascending pool id, all of them if fewer; every vote      *)
(*        carries its pool's active stake.                                 *)
(*   [C2] 1146-1158 "Committee Selection": the order is the seat index.    *)
(*   [C3] 800-849 "Key Registration and Rotation": only a key with a       *)
(*        valid proof of possession may sit; a seat without one is         *)
(*        keyless and cannot sign; keys rotate with a time-to-live.        *)
(*   [C4] 374-391 "Step 4": certified when the voters' stake reaches tau   *)
(*        of the total active stake (formula >=; the prose says exceeds).  *)
(*   [C5] 1083-1103 "Voting & Certification": at most one vote per         *)
(*        committee member per slot is forwarded; a running tally per EB.  *)
(*   [C6] 911-930 "Certificate Validation": signature, eligibility, stake. *)
(*   [C7] 2797-2869 "Design Decisions": stake-based truncation replaced    *)
(*        wFA^LS (persistent plus per-EB non-persistent voters).           *)
(*   Reference:                                                            *)
(*   [R1] cardano-ledger 1210d37f (same at b21c518e, the ledger            *)
(*        ouroboros-consensus ec239d57f618 pins), libs/cardano-ledger-     *)
(*        core/src/Cardano/Ledger/State/Leios.hs 93-121                    *)
(*        selectLeiosCommittee: partial sort by (Down stake, pool id),     *)
(*        take min(committeeSize, candidates), key only while honoured.    *)
(*   [R2] cardano-ledger 1210d37f, eras/dijkstra/impl/src/Cardano/Ledger/  *)
(*        Dijkstra/Rules/Snap.hs 157-180: a key is honoured for            *)
(*        ceil(maxKESEvo * slotsPerKESPeriod / epochLength) + 2 epochs.    *)
(*   [R3] cardano-base 242f1ebde40b (cardano-crypto-leios 0.3.0.0, the     *)
(*        version ec239d57f618's CHaP index resolves), cardano-crypto-     *)
(*        leios/src/Cardano/Crypto/Leios.hs 156-170 mkLeiosCommittee (bad  *)
(*        proof: keyless), 229-265 aggregateLeiosCert, 291-342             *)
(*        verifyLeiosCert (keyless, weight >= threshold, signature).       *)
(*   [R4] ouroboros-consensus ec239d57f618, ouroboros-consensus/src/       *)
(*        ouroboros-consensus/Ouroboros/Consensus/Leios/VoteState.hs       *)
(*        224-316 addVote (seen before validation; aggregate once, while   *)
(*        no certificate), 318-345 validateVote (SeatNotResolvable,        *)
(*        SeatHasNoKey, BadSignature), 348-399 recordVote (one vote per    *)
(*        seat per election slot; quorum <= tally).                        *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 62fa36d1):              *)
(*   [G1] ledger/leios/certificate.go 102-235                              *)
(*        VerifyDijkstraCertificateForMessage: len(Committee) must equal   *)
(*        committeeSize (121), keyless signer (169), no signers (197),     *)
(*        quorum signerStake/total >= tau (208), aggregate signature.      *)
(*   [G2] ledger/common/state.go 193-217: the caller supplies the seated   *)
(*        committee; keys "must be from the snapshot's registered pool     *)
(*        parameters". Nothing says aged-out keys must be withheld.        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Scenario,   \* the stake distribution: "ties", "few", "aged" or "wide"
    Nc,         \* the committee-size protocol parameter
    TauNum,     \* the quorum threshold is TauNum / TauDen of active stake
    TauDen,
    GoExactNc,  \* TRUE: gOuroboros checks the committee against Nc (main)
    CallerDropsAgedKeys, \* TRUE: the caller withholds aged-out keys
    Mutation    \* "none", or one deliberate break (see README)

VARIABLES
    committee,    \* seat number -> pool, fixed at the epoch boundary
    recorded,     \* the votes the node keeps: tuples <<seat, ann, sigOK>>
    tally,        \* per announcement, the stake the node counted for it
    certified,    \* per announcement, whether its certificate was formed
    certSigners,  \* per announcement, the seats its certificate names
    certSigs,     \* per announcement, the votes whose signatures it holds
    outcomes      \* what the node did with each vote so far (for probes)

\* In English: "All the variables, for stuttering steps."
\* Literally: "vars is defined as the tuple of committee, recorded, tally,
\*   certified, certSigners, certSigs and outcomes."
vars == <<committee, recorded, tally, certified, certSigners, certSigs, outcomes>>

(***************************************************************************)
(* Arithmetic helpers.                                                     *)
(***************************************************************************)

\* In English: "The smaller of two numbers."
\* Literally: "Min of a and b is defined as: if a is less than b then a, else
\*   b."
Min(a, b) == IF a < b THEN a ELSE b

\* In English: "The larger of two numbers."
\* Literally: "Max of a and b is defined as: if a is greater than b then a,
\*   else b."
Max(a, b) == IF a > b THEN a ELSE b

(***************************************************************************)
(* The scenarios: each pool's stake and the state of its voting key.       *)
(* Pool ids are 1, 2, ... ; "valid" is a registered, honoured key with a   *)
(* good proof; "badpop" a key whose proof fails; "aged" a key past its     *)
(* time-to-live [R2]; "none" no key at all.                                *)
(***************************************************************************)

\* In English: "Each scenario's stakes, by pool id. "ties" has three pools
\* of equal stake around the seat boundary; "few" has fewer pools than Nc."
\* Literally: "StakeTable is defined as: in the case Scenario equals "ties",
\*   the tuple of 4, 2, 2, 2 and 1; in the case Scenario equals "few", the
\*   tuple of 3 and 2; in the case Scenario equals "aged", the tuple of 3, 2
\*   and 1; in every other case, the tuple of 2, 2, 2 and 1."
StakeTable ==
    CASE Scenario = "ties" -> <<4, 2, 2, 2, 1>>
      [] Scenario = "few"  -> <<3, 2>>
      [] Scenario = "aged" -> <<3, 2, 1>>
      [] OTHER             -> <<2, 2, 2, 1>>

\* In English: "Each scenario's key states, by pool id."
\* Literally: "KeyTable is defined as: in the case Scenario equals "ties", the
\*   tuple of "valid", "valid", "badpop", "valid" and "valid"; in the case
\*   Scenario equals "few", the tuple of "valid" and "none"; in the case
\*   Scenario equals "aged", the tuple of "valid", "valid" and "aged"; in
\*   every other case, the tuple of "valid", "valid", "valid" and "valid"."
KeyTable ==
    CASE Scenario = "ties" -> <<"valid", "valid", "badpop", "valid", "valid">>
      [] Scenario = "few"  -> <<"valid", "none">>
      [] Scenario = "aged" -> <<"valid", "valid", "aged">>
      [] OTHER             -> <<"valid", "valid", "valid", "valid">>

\* In English: "The registered pools, by id."
\* Literally: "Pools is defined as 1 through the length of StakeTable."
Pools == 1..Len(StakeTable)

\* In English: "Pool p's active stake."
\* Literally: "StakeOf of p is defined as element p of StakeTable."
StakeOf(p) == StakeTable[p]

\* In English: "Pool p's voting-key state."
\* Literally: "KeyOf of p is defined as element p of KeyTable."
KeyOf(p) == KeyTable[p]

\* In English: "The stake of a set of pools."
RECURSIVE PoolStake(_)
\* Literally: "PoolStake of S is defined as: if S equals the empty set then
\*   0, else, letting p be the x, chosen from S, such that TRUE: StakeOf of p
\*   plus PoolStake of (S without the members of the set containing p)."
PoolStake(S) ==
    IF S = {} THEN 0
    ELSE LET p == CHOOSE x \in S : TRUE IN StakeOf(p) + PoolStake(S \ {p})

\* In English: "The total active stake: every pool, seated or not. The
\* weight of a seat is its pool's stake over this [R1: lcWeight is the
\* pool's stake ratio]."
\* Literally: "Total is defined as PoolStake of Pools."
Total == PoolStake(Pools)

(***************************************************************************)
(* Committee selection [C1][C2][R1].                                       *)
(***************************************************************************)

\* In English: "Pool q is seated before pool p: more stake, or equal stake
\* and a smaller id. The TieBreakDesc mutation breaks ties the wrong way."
\* Literally: "Beats of q and p is defined as: StakeOf of q is greater than
\*   StakeOf of p, or (StakeOf of q equals StakeOf of p, and if Mutation
\*   equals "TieBreakDesc" then q is greater than p, else q is less than p)."
Beats(q, p) ==
    \/ StakeOf(q) > StakeOf(p)
    \/ /\ StakeOf(q) = StakeOf(p)
       /\ IF Mutation = "TieBreakDesc" THEN q > p ELSE q < p

\* In English: "Pool p's place in the order: how many pools come before it."
\* Literally: "Rank of p is defined as the number of members of the set of
\*   every q in Pools such that q does not equal p and Beats of q and p."
Rank(p) == Cardinality({q \in Pools : q # p /\ Beats(q, p)})

\* In English: "The number of seats: Nc, or every pool if fewer. The
\* NoTruncation mutation seats every pool."
\* Literally: "N is defined as: if Mutation equals "NoTruncation" then the
\*   number of members of Pools, else Min of Nc and the number of members of
\*   Pools."
N == IF Mutation = "NoTruncation"
     THEN Cardinality(Pools)
     ELSE Min(Nc, Cardinality(Pools))

\* In English: "The seat numbers, which votes carry as voter_id."
\* Literally: "Seats is defined as 0 through (N minus 1)."
Seats == 0..(N - 1)

\* In English: "The selection: the pool whose rank is i goes in seat i. The
\* reference partial-sorts by (descending stake, pool id) and takes the
\* first N [R1]; ranking each pool by how many beat it gives the same
\* order."
\* Literally: "Selected is defined as the function that maps every i in
\*   Seats to the p, chosen from Pools, such that Rank of p equals i."
Selected == [i \in Seats |-> CHOOSE p \in Pools : Rank(p) = i]

\* In English: "The pool sitting in seat i of the committee the epoch
\* boundary fixed."
\* Literally: "SeatPool of i is defined as committee of i."
SeatPool(i) == committee[i]

\* In English: "The pools that got a seat."
\* Literally: "SeatedPools is defined as the set of SeatPool of i, for every
\*   i that is a member of Seats."
SeatedPools == {SeatPool(i) : i \in Seats}

\* In English: "Seat i's weight: its pool's stake."
\* Literally: "W of i is defined as StakeOf of SeatPool of i."
W(i) == StakeOf(SeatPool(i))

\* In English: "The stake of a set of seats."
RECURSIVE SumW(_)
\* Literally: "SumW of S is defined as: if S equals the empty set then 0,
\*   else, letting i be the x, chosen from S, such that TRUE: W of i plus
\*   SumW of (S without the members of the set containing i)."
SumW(S) ==
    IF S = {} THEN 0
    ELSE LET i == CHOOSE x \in S : TRUE IN W(i) + SumW(S \ {i})

\* In English: "The reference seats a key only if it is valid: a missing,
\* badly proven or aged-out key leaves the seat keyless [R1][R3]. The
\* HonourAgedKey mutation keeps aged-out keys."
\* Literally: "Honoured of p is defined as: KeyOf of p equals "valid", or
\*   (Mutation equals "HonourAgedKey" and KeyOf of p equals "aged")."
Honoured(p) ==
    \/ KeyOf(p) = "valid"
    \/ Mutation = "HonourAgedKey" /\ KeyOf(p) = "aged"

\* In English: "The seats the node votes and aggregates with: those with a
\* key."
\* Literally: "Keyed is defined as the set of every i in Seats such that
\*   Honoured of SeatPool of i."
Keyed == {i \in Seats : Honoured(SeatPool(i))}

\* In English: "The seats a verifying node treats as keyed: only valid keys,
\* whatever the aggregator thought."
\* Literally: "RefKeyed is defined as the set of every i in Seats such that
\*   KeyOf of SeatPool of i equals "valid"."
RefKeyed == {i \in Seats : KeyOf(SeatPool(i)) = "valid"}

\* In English: "The seats whose key gOuroboros is handed: valid keys, and
\* aged-out ones unless the caller withholds them [G2]. A badly proven key
\* is handed over too, but gOuroboros checks the proof and rejects a signer
\* that holds one, so it counts as keyless here."
\* Literally: "GoKeyed is defined as the set of every i in Seats such that
\*   KeyOf of SeatPool of i equals "valid", or (CallerDropsAgedKeys is not
\*   true and KeyOf of SeatPool of i equals "aged")."
GoKeyed ==
    {i \in Seats :
        \/ KeyOf(SeatPool(i)) = "valid"
        \/ ~CallerDropsAgedKeys /\ KeyOf(SeatPool(i)) = "aged"}

(***************************************************************************)
(* The quorum [C4][R3][G1]: the weight reaches tau of the total stake.    *)
(***************************************************************************)

\* In English: "Stake s reaches the quorum: s / Total >= TauNum / TauDen,
\* compared without division."
\* Literally: "Quorum of s is defined as s times TauDen is greater than or
\*   equal to TauNum times Total."
Quorum(s) == s * TauDen >= TauNum * Total

\* In English: "The aggregator's own quorum test. The StrictTally mutation
\* waits for strictly more than the quorum."
\* Literally: "TallyQuorum of s is defined as: if Mutation equals
\*   "StrictTally" then s times TauDen is greater than TauNum times Total,
\*   else Quorum of s."
TallyQuorum(s) ==
    IF Mutation = "StrictTally" THEN s * TauDen > TauNum * Total
    ELSE Quorum(s)

(***************************************************************************)
(* Votes [C5][R4].                                                         *)
(***************************************************************************)

\* In English: "The announcements of the election: an equivocating pair."
\* Literally: "Anns is defined as the set containing "a" and "b"."
Anns == {"a", "b"}

\* In English: "The voter ids a vote may carry, including ids past the
\* committee, which name no seat."
\* Literally: "VoteSeats is defined as 0 through (Max of Nc and the number of
\*   members of Pools, minus 1)."
VoteSeats == 0..(Max(Nc, Cardinality(Pools)) - 1)

\* In English: "Every vote message: a voter id, an announcement, and whether
\* its signature verifies under that seat's key over that announcement."
\* Literally: "Votes is defined as the Cartesian product of VoteSeats, Anns
\*   and BOOLEAN."
Votes == VoteSeats \X Anns \X BOOLEAN

\* In English: "The seats with a kept vote for announcement a."
\* Literally: "VotersFor of R and a is defined as the set of r[1], for every
\*   r that is a member of the set of every x in R such that x[2] equals a."
VotersFor(R, a) == {r[1] : r \in {x \in R : x[2] = a}}

\* In English: "What the node does with an arriving vote, before it keeps
\* it [R4]: a vote of a seat it already has a vote of, in this election, is
\* dropped unverified, whichever announcement it is for; then the seat must
\* exist and have a key, and the signature must verify. "Duplicate" and
\* "Equivocation" are both the reference's AlreadyKnown. The mutations
\* drop one of these checks."
\* Literally: "Verdict of s, a and ok is defined as: letting same be (there
\*   exists an r in recorded such that r[1] equals s and r[2] equals a), and
\*   seen be (if Mutation equals "CountDuplicate" then FALSE, else if
\*   Mutation equals "CountEquivocation" then same, else there exists an r
\*   in recorded such that r[1] equals s): in the case seen and same,
\*   "Duplicate"; in the case seen, "Equivocation"; in the case s is not a
\*   member of Seats, "SeatNotResolvable"; in the case s is not a member of
\*   Keyed and Mutation does not equal "AcceptKeyless", "SeatHasNoKey"; in
\*   the case ok is not true and Mutation does not equal "AcceptBadSig",
\*   "BadSignature"; in every other case, "Added"."
Verdict(s, a, ok) ==
    LET same == \E r \in recorded : r[1] = s /\ r[2] = a
        seen == IF Mutation = "CountDuplicate" THEN FALSE
                ELSE IF Mutation = "CountEquivocation" THEN same
                ELSE \E r \in recorded : r[1] = s
    IN CASE seen /\ same -> "Duplicate"
         [] seen -> "Equivocation"
         [] s \notin Seats -> "SeatNotResolvable"
         [] s \notin Keyed /\ Mutation # "AcceptKeyless" -> "SeatHasNoKey"
         [] ~ok /\ Mutation # "AcceptBadSig" -> "BadSignature"
         [] OTHER -> "Added"

\* In English: "The votes a certificate for a aggregates: the kept votes for
\* a [R4 recordVote]. The AggregateAllSeats mutation takes every kept vote."
\* Literally: "CertVotes of R and a is defined as: if Mutation equals
\*   "AggregateAllSeats" then R, else the set of every x in R such that x[2]
\*   equals a."
CertVotes(R, a) ==
    IF Mutation = "AggregateAllSeats" THEN R ELSE {x \in R : x[2] = a}

(***************************************************************************)
(* The steps.                                                              *)
(***************************************************************************)

\* In English: "The committee is seated; nothing has arrived; no tally, no
\* certificate."
\* Literally: "Init is defined as: committee equals Selected, and recorded
\*   equals the empty set, and tally
\*   equals the function that maps every a in Anns to 0, and certified
\*   equals the function that maps every a in Anns to FALSE, and certSigners
\*   equals the function that maps every a in Anns to the empty set, and
\*   certSigs equals the function that maps every a in Anns to the empty set,
\*   and outcomes equals the empty set."
Init ==
    /\ committee = Selected
    /\ recorded = {}
    /\ tally = [a \in Anns |-> 0]
    /\ certified = [a \in Anns |-> FALSE]
    /\ certSigners = [a \in Anns |-> {}]
    /\ certSigs = [a \in Anns |-> {}]
    /\ outcomes = {}

\* In English: "Vote <<s, a, ok>> arrives. If the node keeps it, it adds the
\* seat's weight to a's tally and, if that tally now reaches the quorum and
\* a has no certificate yet, aggregates a's votes into one. Otherwise only
\* the outcome is noted. The tally bound only keeps mutated runs finite: the
\* reference never counts more than Total."
\* Literally: "Receive of s, a and ok is defined as: tally of a is less than
\*   or equal to 2 times Total, and letting v be the tuple of s, a and ok,
\*   and why be Verdict of s, a and ok: outcomes in the next state equals the
\*   union of outcomes and the set containing why, and if why equals "Added"
\*   then (recorded in the next state equals the union of recorded and the
\*   set containing v, and tally in the next state equals tally except that
\*   its a entry is the old entry plus W of s, and if certified of a is not
\*   true and TallyQuorum of (tally of a plus W of s) then (certified in the
\*   next state equals certified except that its a entry is TRUE, and
\*   certSigs in the next state equals certSigs except that its a entry is
\*   CertVotes of (the union of recorded and the set containing v) and a, and
\*   certSigners in the next state equals certSigners except that its a
\*   entry is the set of x[1], for every x that is a member of that same
\*   CertVotes), else certified, certSigners and certSigs are unchanged),
\*   else recorded, tally, certified, certSigners and certSigs are
\*   unchanged."
Receive(s, a, ok) ==
    /\ tally[a] <= 2 * Total
    /\ LET v == <<s, a, ok>>
           why == Verdict(s, a, ok)
       IN /\ outcomes' = outcomes \cup {why}
          /\ UNCHANGED committee
          /\ IF why = "Added"
             THEN LET kept == recorded \cup {v}
                      agg == CertVotes(kept, a)
                  IN /\ recorded' = kept
                     /\ tally' = [tally EXCEPT ![a] = @ + W(s)]
                     /\ IF ~certified[a] /\ TallyQuorum(tally[a] + W(s))
                        THEN /\ certified' = [certified EXCEPT ![a] = TRUE]
                             /\ certSigs' = [certSigs EXCEPT ![a] = agg]
                             /\ certSigners' =
                                    [certSigners EXCEPT ![a] = {x[1] : x \in agg}]
                        ELSE UNCHANGED <<certified, certSigners, certSigs>>
             ELSE UNCHANGED <<recorded, tally, certified, certSigners, certSigs>>

\* In English: "Some vote arrives."
\* Literally: "Next is defined as: there exists a v in Votes such that
\*   Receive of v[1], v[2] and v[3]."
Next == \E v \in Votes : Receive(v[1], v[2], v[3])

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verifying a certificate.                                                *)
(***************************************************************************)

\* In English: "The aggregate signature verifies under the signers' keys over
\* announcement a: it holds exactly one valid signature of a from each
\* signer and nothing else."
\* Literally: "SigOK of S, V and a is defined as: V equals the set of the
\*   tuple of i, a and TRUE, for every i that is a member of S."
SigOK(S, V, a) == V = {<<i, a, TRUE>> : i \in S}

\* In English: "The reference accepts a certificate for a naming seats S
\* with signatures V [R3 verifyLeiosCert]: no keyless signer, quorum, and
\* the aggregate signature."
\* Literally: "RefAccepts of S, V and a is defined as: S is a subset of
\*   RefKeyed, and Quorum of SumW of S, and SigOK of S, V and a."
RefAccepts(S, V, a) ==
    /\ S \subseteq RefKeyed
    /\ Quorum(SumW(S))
    /\ SigOK(S, V, a)

\* In English: "gOuroboros accepts it [G1]: the committee has the size it is
\* told (Nc on main, which fails with fewer pools: DRIFT L9), no signer
\* without a key it was handed, at least one signer, quorum, signature. The
\* StrictQuorum mutation demands strictly more than tau."
\* Literally: "GoAccepts of S, V and a is defined as: (GoExactNc is not true
\*   or N equals Nc), and S is a subset of GoKeyed, and S does not equal the
\*   empty set, and Quorum of SumW of S, and (if Mutation equals
\*   "StrictQuorum" then SumW of S times TauDen is greater than TauNum times
\*   Total, else TRUE), and SigOK of S, V and a."
GoAccepts(S, V, a) ==
    /\ ~GoExactNc \/ N = Nc
    /\ S \subseteq GoKeyed
    /\ S # {}
    /\ Quorum(SumW(S))
    /\ IF Mutation = "StrictQuorum" THEN SumW(S) * TauDen > TauNum * Total
       ELSE TRUE
    /\ SigOK(S, V, a)

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

\* In English: "Every variable has the expected shape."
\* Literally: "TypeOK is defined as: committee is a member of the set of
\*   functions from Seats to Pools, and recorded is a subset of Votes, and tally
\*   is a member of the set of functions from Anns to Nat, and certified is a
\*   member of the set of functions from Anns to BOOLEAN, and certSigners is
\*   a member of the set of functions from Anns to the set of subsets of
\*   VoteSeats, and certSigs is a member of the set of functions from Anns
\*   to the set of subsets of Votes."
TypeOK ==
    /\ committee \in [Seats -> Pools]
    /\ recorded \subseteq Votes
    /\ tally \in [Anns -> Nat]
    /\ certified \in [Anns -> BOOLEAN]
    /\ certSigners \in [Anns -> SUBSET VoteSeats]
    /\ certSigs \in [Anns -> SUBSET Votes]

\* In English: "The committee has min(Nc, pools) seats [C1]."
\* Literally: "CommitteeSize is defined as: the number of members of the
\*   domain of committee equals Min of Nc and the number of members of
\*   Pools."
CommitteeSize == Cardinality(DOMAIN committee) = Min(Nc, Cardinality(Pools))

\* In English: "Seats are in descending stake, ties by ascending pool id
\* [C1][C2]."
\* Literally: "SeatOrder is defined as: for all i in Seats and j in Seats, if
\*   i is less than j, then StakeOf of SeatPool of i is greater than StakeOf
\*   of SeatPool of j, or (StakeOf of SeatPool of i equals StakeOf of
\*   SeatPool of j and SeatPool of i is less than SeatPool of j)."
SeatOrder ==
    \A i, j \in Seats :
        i < j =>
            \/ StakeOf(SeatPool(i)) > StakeOf(SeatPool(j))
            \/ /\ StakeOf(SeatPool(i)) = StakeOf(SeatPool(j))
               /\ SeatPool(i) < SeatPool(j)

\* In English: "No unseated pool should have been seated instead [C1]."
\* Literally: "TopStake is defined as: for all i in Seats and p in (Pools
\*   without the members of SeatedPools), StakeOf of SeatPool of i is greater
\*   than StakeOf of p, or (StakeOf of SeatPool of i equals StakeOf of p and
\*   SeatPool of i is less than p)."
TopStake ==
    \A i \in Seats, p \in Pools \ SeatedPools :
        \/ StakeOf(SeatPool(i)) > StakeOf(p)
        \/ StakeOf(SeatPool(i)) = StakeOf(p) /\ SeatPool(i) < p

\* In English: "Only a valid, honoured key sits on the committee [C3][R1]."
\* Literally: "OnlyHonouredKeys is defined as: for all i in Keyed, KeyOf of
\*   SeatPool of i equals "valid"."
OnlyHonouredKeys == \A i \in Keyed : KeyOf(SeatPool(i)) = "valid"

\* In English: "The node keeps at most one vote per seat per election, so an
\* equivocating seat is never counted twice [C5][R4]."
\* Literally: "OneVotePerSeat is defined as: for all r1 in recorded and r2 in
\*   recorded, if r1[1] equals r2[1], then r1 equals r2."
OneVotePerSeat == \A r1, r2 \in recorded : r1[1] = r2[1] => r1 = r2

\* In English: "Every kept vote is from a keyed seat with a good signature
\* [R4 validateVote]."
\* Literally: "OnlyValidVotes is defined as: for all r in recorded, r[1] is
\*   a member of RefKeyed and r[3]."
OnlyValidVotes == \A r \in recorded : r[1] \in RefKeyed /\ r[3]

\* In English: "Each tally is the weight of the seats whose kept vote is for
\* that announcement [R4: slotTallies' INVARIANT]."
\* Literally: "TallyMatches is defined as: for all a in Anns, tally of a
\*   equals SumW of VotersFor of recorded and a."
TallyMatches == \A a \in Anns : tally[a] = SumW(VotersFor(recorded, a))

\* In English: "Once the votes for an announcement reach quorum, it has its
\* certificate [R4: aggregated as soon as quorum is reached]."
\* Literally: "CertAtQuorum is defined as: for all a in Anns, if Quorum of
\*   tally of a, then certified of a."
CertAtQuorum == \A a \in Anns : Quorum(tally[a]) => certified[a]

\* In English: "Every certificate the node forms is one the reference
\* accepts [C6][R3]."
\* Literally: "CertsVerify is defined as: for all a in Anns, if certified of
\*   a, then RefAccepts of certSigners of a, certSigs of a, and a."
CertsVerify ==
    \A a \in Anns : certified[a] => RefAccepts(certSigners[a], certSigs[a], a)

\* In English: "Every certificate the node forms is one gOuroboros accepts."
\* Literally: "GoAcceptsCerts is defined as: for all a in Anns, if certified
\*   of a, then GoAccepts of certSigners of a, certSigs of a, and a."
GoAcceptsCerts ==
    \A a \in Anns : certified[a] => GoAccepts(certSigners[a], certSigs[a], a)

\* In English: "With tau above one half, at most one announcement of an
\* election is certified: a seat votes once, so two disjoint quorums would
\* need more than all the stake."
\* Literally: "AtMostOneCert is defined as: the number of members of the set
\*   of every a in Anns such that certified of a is less than or equal to 1."
AtMostOneCert == Cardinality({a \in Anns : certified[a]}) <= 1

\* In English: "Over every signer set, each signing with a good signature,
\* gOuroboros accepts exactly what the reference accepts. A state-free
\* check: it holds or fails for the constants alone."
\* Literally: "GoAgrees is defined as: for all S in the set of subsets of
\*   Seats and a in Anns, letting V be the set of the tuple of i, a and TRUE,
\*   for every i that is a member of S: GoAccepts of S, V and a equals
\*   RefAccepts of S, V and a."
GoAgrees ==
    \A S \in SUBSET Seats, a \in Anns :
        LET V == {<<i, a, TRUE>> : i \in S}
        IN GoAccepts(S, V, a) = RefAccepts(S, V, a)

(***************************************************************************)
(* Probes, each EXPECTED to be violated: the behaviour is reachable.       *)
(***************************************************************************)

\* In English: "Probe: no certificate is ever formed."
\* Literally: "ProbeNoCert is defined as: for all a in Anns, certified of a is
\*   not true."
ProbeNoCert == \A a \in Anns : ~certified[a]

\* In English: "Probe: no equivocating vote is ever dropped."
\* Literally: "ProbeNoEquivocation is defined as: "Equivocation" is not a
\*   member of outcomes."
ProbeNoEquivocation == "Equivocation" \notin outcomes

\* In English: "Probe: no repeated vote is ever dropped."
\* Literally: "ProbeNoDuplicate is defined as: "Duplicate" is not a member
\*   of outcomes."
ProbeNoDuplicate == "Duplicate" \notin outcomes

\* In English: "Probe: no vote of a keyless seat is ever refused."
\* Literally: "ProbeNoKeyless is defined as: "SeatHasNoKey" is not a member
\*   of outcomes."
ProbeNoKeyless == "SeatHasNoKey" \notin outcomes

\* In English: "Probe: no vote naming no seat is ever refused."
\* Literally: "ProbeNoUnresolvable is defined as: "SeatNotResolvable" is not
\*   a member of outcomes."
ProbeNoUnresolvable == "SeatNotResolvable" \notin outcomes

\* In English: "Probe: no badly signed vote is ever refused."
\* Literally: "ProbeNoBadSignature is defined as: "BadSignature" is not a
\*   member of outcomes."
ProbeNoBadSignature == "BadSignature" \notin outcomes

\* In English: "Probe: the two announcements never both hold kept votes."
\* Literally: "ProbeNoSplit is defined as: there does not exist an r1 in
\*   recorded and r2 in recorded such that r1[2] does not equal r2[2]."
ProbeNoSplit == ~\E r1, r2 \in recorded : r1[2] # r2[2]
=============================================================================
