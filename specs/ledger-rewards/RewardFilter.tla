---------------------------- MODULE RewardFilter ----------------------------
(***************************************************************************)
(* How much of one stake credential's computed rewards is paid, and how   *)
(* much returns to the reserves, as a table over the rewards a credential *)
(* can be owed in one reward update.                                       *)
(*                                                                         *)
(* A credential can be owed a leader reward from each pool whose reward   *)
(* account it is (two pools here, P1 before P2 in key-hash order) and a   *)
(* member reward from the one pool it delegates to. A leader reward is    *)
(* computed for every pool that made blocks, even when it is zero; a      *)
(* member reward of zero is not computed.                                  *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd:              *)
(*   [R1] eras/shelley/impl/src/Cardano/Ledger/Shelley/Rewards.hs 150-171 *)
(*        filterRewards, aggregateRewards: while                           *)
(*        hardforkAllegraAggregatedRewards is false a credential is paid  *)
(*        only Set.findMin of its rewards; from then on all of them.      *)
(*   [R2] eras/shelley/impl/src/Cardano/Ledger/Shelley/Era.hs 231-232     *)
(*        hardforkAllegraAggregatedRewards pv = pvMajor pv > 2.           *)
(*   [R3] libs/cardano-ledger-core/src/Cardano/Ledger/Rewards.hs 80-83:   *)
(*        Ord Reward puts every leader reward before every member reward, *)
(*        and orders rewards of one kind by pool key hash, not amount.    *)
(*   [R4] Shelley/LedgerState/PulsingReward.hs 176-183 collectLRs: a       *)
(*        leader reward is recorded for each block-producing pool, zero   *)
(*        included; 262-276 completeRupd: deltaR2 = R - sumRewards, so     *)
(*        whatever is not paid returns to the reserves.                    *)
(*   [R5] Shelley/Rewards.hs 294-296 rewardOnePoolMember: a zero member   *)
(*        reward is Nothing.                                               *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ledger/common/rewards.go    *)
(* CalculateRewards:                                                       *)
(*   [G1] fix/ledger-rewards-reference b667cca8 (PR #3275): every non-zero *)
(*        reward is paid in every protocol version.                        *)
(*   [G2] the fix on that branch: before version 3 each credential keeps   *)
(*        only its least reward in the reference order, a zero leader      *)
(*        reward included, and the rest returns to the reserves.          *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    PVs,     \* protocol major versions to try, a subset of {2, 3}
    GoRule   \* "payAll" [G1] or "filter" [G2]

VARIABLE owed   \* the rewards one credential is owed in this update

\* In English: "A leader reward from a pool can be absent, zero, or
\*   positive."
\* Literally: "LeaderKinds is defined as the set containing "none", "zero"
\*   and "pos"."
LeaderKinds == {"none", "zero", "pos"}

\* In English: "The amounts used for positive rewards: P1's leader reward
\*   is larger than P2's, so ordering by amount and by pool disagree."
\* Literally: "LeaderAmount of p and k is defined as: 0 unless k is "pos";
\*   5 for P1 and 3 for P2."
LeaderAmount(p, k) ==
    IF k /= "pos" THEN 0 ELSE IF p = "P1" THEN 5 ELSE 3

\* In English: "A member reward, when owed, is 2."
\* Literally: "MemberAmount of m is defined as: 0 if m is "none", else 2."
MemberAmount(m) == IF m = "none" THEN 0 ELSE 2

\* In English: "Every protocol version, pair of leader rewards and member
\*   reward (from neither pool, P1 or P2)."
\* Literally: "Inputs is defined as the set of records whose pv is in PVs,
\*   whose l1 and l2 are in LeaderKinds, and whose member is "none", "P1"
\*   or "P2"."
Inputs == [pv : PVs, l1 : LeaderKinds, l2 : LeaderKinds,
           member : {"none", "P1", "P2"}]

\* In English: "Everything computed for the credential." [R4] [R5]
\* Literally: "Computed of i is defined as the sum of the two leader
\*   amounts and the member amount."
Computed(i) ==
    LeaderAmount("P1", i.l1) + LeaderAmount("P2", i.l2) +
    MemberAmount(i.member)

\* In English: "The reference pays all of it from version 3; before, only
\*   the least reward: P1's leader reward if computed, else P2's, else the
\*   member reward." [R1] [R2] [R3]
\* Literally: "RefPaid of i is defined as: if the pv of i is greater than 2
\*   then Computed of i; else if l1 is not "none" then P1's leader amount;
\*   else if l2 is not "none" then P2's leader amount; else the member
\*   amount."
RefPaid(i) ==
    IF i.pv > 2 THEN Computed(i)
    ELSE IF i.l1 /= "none" THEN LeaderAmount("P1", i.l1)
    ELSE IF i.l2 /= "none" THEN LeaderAmount("P2", i.l2)
    ELSE MemberAmount(i.member)

\* In English: "gOuroboros pays everything [G1], or as the reference [G2]."
\* Literally: "GoPaid of i is defined as: if GoRule is "payAll" then
\*   Computed of i, else RefPaid of i."
GoPaid(i) == IF GoRule = "payAll" THEN Computed(i) ELSE RefPaid(i)

\* In English: "Pick any one input."
\* Literally: "Init is defined as: owed is a member of Inputs."
Init == owed \in Inputs

\* In English: "A table has no steps: the input stays as it is."
\* Literally: "Next is defined as: owed is unchanged."
Next == UNCHANGED owed

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or owed
\*   stays the same."
Spec == Init /\ [][Next]_owed

\* In English: "gOuroboros pays the credential what the reference pays, so
\*   the same amount returns to the reserves (Computed minus paid)."
\* Literally: "PaidAsReference is defined as: GoPaid of owed equals RefPaid
\*   of owed."
PaidAsReference == GoPaid(owed) = RefPaid(owed)
=============================================================================
