---------------------------- MODULE RewardPots ----------------------------
(***************************************************************************)
(* The ada pots across epoch boundaries: how a reward update moves value   *)
(* between the reserves, the treasury, the fee pot and the reward          *)
(* accounts, and how one pool's reward is split between its leader and a   *)
(* member.                                                                 *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37f.                   *)
(*   [R1] eras/shelley/impl/src/Cardano/Ledger/Shelley/LedgerState/        *)
(*        PulsingReward.hs 89-196 (startStep): deltaR1, eta, the reward    *)
(*        pot, deltaT1 and R; 244-282 (completeRupd): deltaR2 = R less     *)
(*        the rewards, deltaR = deltaR2 - deltaR1, deltaF = -fees.         *)
(*   [R2] libs/cardano-ledger-core/src/Cardano/Ledger/State/SnapShots.hs   *)
(*        141-165: maxPool'.                                               *)
(*   [R3] eras/shelley/impl/src/Cardano/Ledger/Shelley/Rewards.hs 61-99:   *)
(*        apparent performance, leader and member rewards; 206-292:        *)
(*        mkPoolRewardInfo (no blocks, no reward; pledge check) and the    *)
(*        registration prefilter before protocol version 7.               *)
(*   [R4] eras/shelley/impl/src/Cardano/Ledger/Shelley/LedgerState/        *)
(*        IncrementalStake.hs 95-128 (applyRUpdFiltered): rewards to       *)
(*        unregistered credentials go to the treasury.                     *)
(*   [R5] eras/shelley/impl/src/Cardano/Ledger/Shelley/Era.hs 256-257:     *)
(*        the prefilter is dropped from protocol version 7.               *)
(* The Shelley formal specification states the same in its rewards        *)
(* chapter (rewards.tex: createRUpd, applyRUpd, maxPool, r_operator,       *)
(* r_member).                                                              *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ledger/common/rewards.go:    *)
(* CalculateAdaPots (the start of the update) and CalculateRewards (the    *)
(* split and the pots after it).                                           *)
(*                                                                         *)
(* One pool, one owner who is also the leader, one member. Stake is a     *)
(* fixed snapshot; value moves through transactions (fees, registering     *)
(* and deregistering the member) and through reward updates. Numbers are  *)
(* small so TLC can check every path. Symbols are read as in              *)
(* specs/keepalive/KeepAlive.tla.                                          *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    PV,         \* the protocol major version of the update (6 or 8)
    MaxEpoch,   \* how many epoch boundaries a run may cross
    Mutation    \* "none" for the reference; otherwise a gOuroboros or
                \* invented deviation (see Mutations)

\* Literally: "Mutations is defined as the set containing "none",
\*   "PayWholePot", "NoBlocksPaid", "UnregToLeader", "NoReserveReturn",
\*   "IgnorePledge" and "UnregDropped"."
\* In English: the behaviours a configuration may switch on. "none" is the
\* reference. The first four are what CalculateRewards did before it
\* followed the reference; the last three are invented to prove each
\* invariant can fail.
Mutations == {"none", "PayWholePot", "NoBlocksPaid", "UnregToLeader",
              "NoReserveReturn", "IgnorePledge", "UnregDropped"}

ASSUME Mutation \in Mutations   \* a typo in a cfg is an error, not "none"
ASSUME PV \in {6, 8}            \* one version on each side of [R5]

\* ---------------------------------------------------------------------
\* Exact rationals, as <<numerator, denominator>> with a positive
\* denominator. TLC has integers only.
\* ---------------------------------------------------------------------

RECURSIVE GCD(_, _)
\* Literally: "GCD of x and y is defined as: if y equals 0 then x else GCD of
\*   y and x modulo y."
\* In English: the greatest common divisor, by Euclid's algorithm.
GCD(x, y) == IF y = 0 THEN x ELSE GCD(y, x % y)

\* Literally: "Abs of x is defined as: if x is less than 0 then 0 minus x
\*   else x."
\* In English: the absolute value of x.
Abs(x) == IF x < 0 THEN 0 - x ELSE x

\* Literally: "Norm of n and d is defined as the pair n integer-divided by g
\*   and d integer-divided by g, where g is GCD of Abs of n and d, or the
\*   pair 0, 1 when g is 0."
\* In English: n/d in lowest terms, so numbers stay small enough for TLC.
Norm(n, d) == LET g == GCD(Abs(n), d)
              IN IF g = 0 THEN <<0, 1>> ELSE <<n \div g, d \div g>>

\* Literally: "Q of n and d is defined as the pair n, d."
\* In English: the fraction n/d.
Q(n, d) == <<n, d>>
\* Literally: "QAdd of a and b is defined as Norm of a1 times b2 plus b1
\*   times a2, and a2 times b2."
\* In English: a + b.
QAdd(a, b) == Norm(a[1] * b[2] + b[1] * a[2], a[2] * b[2])
\* Literally: "QSub of a and b is defined as Norm of a1 times b2 minus b1
\*   times a2, and a2 times b2."
\* In English: a - b.
QSub(a, b) == Norm(a[1] * b[2] - b[1] * a[2], a[2] * b[2])
\* Literally: "QMul of a and b is defined as Norm of a1 times b1, and a2
\*   times b2."
\* In English: a * b.
QMul(a, b) == Norm(a[1] * b[1], a[2] * b[2])
\* Literally: "QDiv of a and b is defined as: if b1 is greater than 0 then
\*   Norm of a1 times b2 and a2 times b1, else Norm of 0 minus a1 times
\*   b2 and a2 times (0 minus b1)."
\* In English: a / b, keeping the denominator positive (b is never 0 here).
QDiv(a, b) == IF b[1] > 0 THEN Norm(a[1] * b[2], a[2] * b[1])
                          ELSE Norm(0 - (a[1] * b[2]), a[2] * (0 - b[1]))
\* Literally: "QLeq of a and b is defined as a1 times b2 is at most b1 times
\*   a2."
\* In English: a <= b.
QLeq(a, b) == a[1] * b[2] <= b[1] * a[2]
\* Literally: "QMin of a and b is defined as: if QLeq of a and b then a else
\*   b."
\* In English: the smaller of a and b.
QMin(a, b) == IF QLeq(a, b) THEN a ELSE b
\* Literally: "Floor of a is defined as: if a1 is at least 0 then a1
\*   integer-divided by a2, else 0."
\* In English: floor(a) for a >= 0, and 0 for a negative value (the
\* reference never floors a negative amount here).
Floor(a) == IF a[1] >= 0 THEN a[1] \div a[2] ELSE 0

\* ---------------------------------------------------------------------
\* The fixed numbers: supply, protocol parameters, the stake snapshot.
\* ---------------------------------------------------------------------

\* Literally: "MaxSupply is defined as 100."
\* In English: all the lovelace there is; every pot is a part of it.
MaxSupply == 100
\* Literally: "Deposit is defined as 1."
\* In English: the stake-credential deposit.
Deposit == 1
\* Literally: "Rho is defined as Q of 1 and 2."
\* In English: rho, the share of the reserves an epoch may expand by.
Rho == Q(1, 2)
\* Literally: "Tau is defined as Q of 1 and 5."
\* In English: tau, the treasury's cut of the reward pot.
Tau == Q(1, 5)
\* Literally: "A0 is defined as Q of 1 and 2."
\* In English: a0, how much pledge raises a pool's reward.
A0 == Q(1, 2)
\* Literally: "NOpt is defined as 2."
\* In English: nOpt, the desired number of pools; the saturation point z0
\* is 1/2.
NOpt == 2
\* Literally: "ExpectedBlocks is defined as 2."
\* In English: floor((1 - d) * f * slotsPerEpoch) with d = 0 [R1].
ExpectedBlocks == 2
\* Literally: "Cost is defined as 1."
\* In English: the pool's fixed cost, taken by the leader first.
Cost == 1
\* Literally: "Margin is defined as Q of 1 and 10."
\* In English: the pool's margin, the leader's cut of the rest.
Margin == Q(1, 10)
\* Literally: "OwnerStake is defined as 6."
\* In English: the stake the owner delegates to the pool.
OwnerStake == 6
\* Literally: "MemberStake is defined as 4."
\* In English: the stake the member delegates to the pool.
MemberStake == 4
\* Literally: "PoolStake is defined as OwnerStake plus MemberStake."
\* In English: the pool's stake in the snapshot.
PoolStake == OwnerStake + MemberStake
\* Literally: "ActiveStake is defined as PoolStake."
\* In English: the only pool holds all the active stake.
ActiveStake == PoolStake
\* Literally: "Pledges is defined as the set containing 6 and 7."
\* In English: a pledge the owner's stake meets, and one it does not.
Pledges == {6, 7}

VARIABLES
    reserves,   \* the reserves pot
    treasury,   \* the treasury pot
    fees,       \* the fee pot
    deposits,   \* deposits held for registered credentials
    utxo,       \* everything held in outputs
    ownerAcct,  \* the owner's (leader's) reward account balance
    memberAcct, \* the member's reward account balance
    memberReg,  \* TRUE while the member's credential is registered
    ru,         \* the pending reward update; ru.active is FALSE when none is
    epoch       \* how many boundaries have passed

\* Literally: "NoUpdate is defined as the record whose field active is FALSE
\*   and whose other fields are 0, 1, TRUE or 6."
\* In English: the value of ru when no reward update is pending. The other
\* fields only keep every value of ru the same shape.
NoUpdate == [active |-> FALSE, blocks |-> 0, pledge |-> 6, circ |-> 1,
             feesSS |-> 0, dR1 |-> 0, dT1 |-> 0, R |-> 0, poolR |-> 0,
             leader |-> 0, member |-> 0, dR2 |-> 0, memberRegAtStart |-> TRUE]

\* Literally: "vars is defined as the tuple of every variable."
\* In English: everything a step may change.
vars == <<reserves, treasury, fees, deposits, utxo, ownerAcct, memberAcct,
          memberReg, ru, epoch>>

\* ---------------------------------------------------------------------
\* The reference arithmetic [R1]-[R3].
\* ---------------------------------------------------------------------

\* Literally: "DeltaR1 of res and b is defined as Floor of QMul of QMul of
\*   QMin of Q of 1 and 1 and Q of b and ExpectedBlocks, and Rho, and Q of
\*   res and 1."
\* In English: floor(min(1, eta) * rho * reserves), eta = b / expected [R1].
DeltaR1(res, b) ==
    Floor(QMul(QMul(QMin(Q(1, 1), Q(b, ExpectedBlocks)), Rho), Q(res, 1)))

\* Literally: "MaxPool of r, circ and pledge is defined as Floor of QMul of
\*   f1 and f2, where z0 is Q of 1 and NOpt, s is QMin of sigma and z0, p is
\*   QMin of the relative pledge and z0, f1 is r divided by 1 plus A0, f4 is
\*   (z0 minus s) divided by z0, f3 is (s minus p times f4) divided by z0,
\*   and f2 is s plus p times A0 times f3."
\* In English: maxPool' [R2]: what the pool can earn from R at best.
MaxPool(r, circ, pledge) ==
    LET z0 == Q(1, NOpt)
        s  == QMin(Q(PoolStake, circ), z0)
        p  == QMin(Q(pledge, circ), z0)
        f1 == QDiv(Q(r, 1), QAdd(Q(1, 1), A0))
        f4 == QDiv(QSub(z0, s), z0)
        f3 == QDiv(QSub(s, QMul(p, f4)), z0)
        f2 == QAdd(s, QMul(QMul(p, A0), f3))
    IN Floor(QMul(f1, f2))

\* Literally: "PoolReward of b and maxP is defined as: if b equals 0 then 0
\*   else Floor of QMul of QDiv of Q of b and b, and Q of PoolStake and
\*   ActiveStake, and Q of maxP and 1."
\* In English: a pool that made no blocks earns nothing; otherwise
\* floor(apparentPerformance * maxP), where apparent performance is the
\* pool's share of the blocks over its share of the active stake [R3]. The
\* pool made every block here, so beta = b / b.
PoolReward(b, maxP) ==
    IF b = 0 THEN 0
    ELSE Floor(QMul(QDiv(Q(b, b), Q(PoolStake, ActiveStake)), Q(maxP, 1)))

\* Literally: "Leader of f and circ is defined as: if f is at most Cost then
\*   f else Cost plus Floor of (f minus Cost) times (Margin plus (1 minus
\*   Margin) times the owner share over sigma)."
\* In English: the leader's reward [R3].
Leader(f, circ) ==
    IF f <= Cost THEN f
    ELSE Cost + Floor(QMul(Q(f - Cost, 1),
                           QAdd(Margin,
                                QDiv(QMul(QSub(Q(1, 1), Margin),
                                          Q(OwnerStake, circ)),
                                     Q(PoolStake, circ)))))

\* Literally: "Member of f and circ is defined as: if f is at most Cost then
\*   0 else Floor of (f minus Cost) times (1 minus Margin) times the member
\*   share over sigma."
\* In English: the member's reward [R3].
Member(f, circ) ==
    IF f <= Cost THEN 0
    ELSE Floor(QDiv(QMul(QMul(Q(f - Cost, 1), QSub(Q(1, 1), Margin)),
                         Q(MemberStake, circ)),
                    Q(PoolStake, circ)))

\* ---------------------------------------------------------------------
\* Initial state and steps.
\* ---------------------------------------------------------------------

\* Literally: "Init is defined as: reserves equals 60 and treasury equals 0
\*   and fees equals 0 and deposits equals 2 times Deposit and utxo equals
\*   MaxSupply minus 60 minus 2 times Deposit and both accounts equal 0 and
\*   memberReg equals TRUE and ru is not active and epoch equals 0."
\* In English: both credentials registered, nothing paid yet.
Init ==
    /\ reserves = 60
    /\ treasury = 0
    /\ fees = 0
    /\ deposits = 2 * Deposit
    /\ utxo = MaxSupply - 60 - 2 * Deposit
    /\ ownerAcct = 0
    /\ memberAcct = 0
    /\ memberReg = TRUE
    /\ ru = NoUpdate
    /\ epoch = 0

\* Literally: "PayFee of f is defined as: utxo is at least f and fees plus f
\*   is at most 3, and in the next state utxo is utxo minus f and fees is
\*   fees plus f, and the rest is unchanged."
\* In English: a transaction pays fee f into the fee pot. The cap of 3
\* keeps the model finite.
PayFee(f) ==
    /\ utxo >= f
    /\ fees + f <= 3
    /\ utxo' = utxo - f
    /\ fees' = fees + f
    /\ UNCHANGED <<reserves, treasury, deposits, ownerAcct, memberAcct,
                   memberReg, ru, epoch>>

\* Literally: "Deregister is defined as: memberReg is TRUE, and in the next
\*   state memberReg is FALSE, memberAcct is 0, deposits is deposits minus
\*   Deposit, and utxo is utxo plus memberAcct plus Deposit."
\* In English: the member withdraws its balance and deregisters, getting
\* its deposit back.
Deregister ==
    /\ memberReg
    /\ memberReg' = FALSE
    /\ memberAcct' = 0
    /\ deposits' = deposits - Deposit
    /\ utxo' = utxo + memberAcct + Deposit
    /\ UNCHANGED <<reserves, treasury, fees, ownerAcct, ru, epoch>>

\* Literally: "Register is defined as: memberReg is FALSE and utxo is at
\*   least Deposit, and in the next state memberReg is TRUE, deposits is
\*   deposits plus Deposit and utxo is utxo minus Deposit."
\* In English: the member registers again.
Register ==
    /\ ~memberReg
    /\ utxo >= Deposit
    /\ memberReg' = TRUE
    /\ deposits' = deposits + Deposit
    /\ utxo' = utxo - Deposit
    /\ UNCHANGED <<reserves, treasury, fees, ownerAcct, memberAcct, ru, epoch>>

\* Literally: "StartUpdate of b and pledge is defined as: ru is not active
\*   and epoch is less than MaxEpoch, and in the next state ru is the record
\*   built below, and the rest is unchanged."
\* In English: the reward update starts [R1]: the pool made b blocks and
\* declared the given pledge. The record holds every amount the update
\* will move when it is applied, and the inputs the invariants recompute
\* the reference from.
StartUpdate(b, pledge) ==
    LET circ   == MaxSupply - reserves                \* circulation [R1]
        dR1    == DeltaR1(reserves, b)
        rPot   == fees + dR1
        dT1    == Floor(QMul(Tau, Q(rPot, 1)))
        R      == rPot - dT1
        met    == pledge <= OwnerStake                 \* pledge check [R3]
        maxP   == IF met \/ Mutation = "IgnorePledge"
                  THEN MaxPool(R, circ, pledge) ELSE 0
        \* NoBlocksPaid hands a blockless pool the whole pot, as the old
        \* equal-share fallback did when no pool had a positive share
        poolR0 == IF b = 0 /\ Mutation = "NoBlocksPaid"
                  THEN R ELSE PoolReward(b, maxP)
        \* PayWholePot hands the pool all of R, as a pro-rata split did
        poolR  == IF Mutation = "PayWholePot" THEN R ELSE poolR0
        lead0  == Leader(poolR, circ)
        mem0   == Member(poolR, circ)
        \* before version 7 an unregistered member is not computed [R3, R5]
        memComputed == memberReg \/ PV >= 7
        \* UnregToLeader gives an unregistered member's share to the leader
        toLeader == Mutation = "UnregToLeader" /\ ~memberReg
        lead   == IF toLeader THEN lead0 + mem0 ELSE lead0
        mem    == IF memComputed /\ ~toLeader THEN mem0 ELSE 0
        dR2    == IF Mutation = "NoReserveReturn" THEN 0
                  ELSE R - lead - mem
    IN /\ ~ru.active
       /\ epoch < MaxEpoch
       /\ ru' = [active |-> TRUE, blocks |-> b, pledge |-> pledge, circ |-> circ,
                 feesSS |-> fees, dR1 |-> dR1, dT1 |-> dT1, R |-> R,
                 poolR |-> poolR, leader |-> lead, member |-> mem,
                 dR2 |-> dR2, memberRegAtStart |-> memberReg]
       /\ UNCHANGED <<reserves, treasury, fees, deposits, utxo, ownerAcct,
                      memberAcct, memberReg, epoch>>

\* Literally: "ApplyUpdate is defined as: ru is active, and in the next
\*   state treasury is treasury plus dT1 plus the unregistered reward,
\*   reserves is reserves minus dR1 plus dR2, fees is fees minus the
\*   snapshot fees, the accounts gain their rewards if registered, ru is
\*   NoUpdate and epoch is epoch plus 1."
\* In English: the epoch boundary applies the update [R1, R4]. The leader
\* is always registered here; a member reward for a credential no longer
\* registered goes to the treasury.
ApplyUpdate ==
    LET unreg == IF memberReg THEN 0 ELSE ru.member
    IN /\ ru.active
       /\ treasury' = treasury + ru.dT1
                      + (IF Mutation = "UnregDropped" THEN 0 ELSE unreg)
       /\ reserves' = reserves - ru.dR1 + ru.dR2
       /\ fees' = fees - ru.feesSS
       /\ ownerAcct' = ownerAcct + ru.leader
       /\ memberAcct' = memberAcct + (IF memberReg THEN ru.member ELSE 0)
       /\ ru' = NoUpdate
       /\ epoch' = epoch + 1
       /\ UNCHANGED <<deposits, utxo, memberReg>>

\* Literally: "Finished is defined as: epoch equals MaxEpoch and ru is not
\*   active, and the variables are unchanged."
\* In English: the run has crossed every boundary it may; it idles rather
\* than counting as a deadlock.
Finished == epoch = MaxEpoch /\ ~ru.active /\ UNCHANGED vars

\* Literally: "Next is defined as: there exists f in 1..2 such that PayFee
\*   of f, or Deregister, or Register, or there exist b in 0..2 and a pledge
\*   in Pledges such that StartUpdate of b and the pledge, or ApplyUpdate,
\*   or Finished."
\* In English: any of the steps above, in any order.
Next ==
    \/ \E f \in 1..2 : PayFee(f)
    \/ Deregister
    \/ Register
    \/ \E b \in 0..2, pledge \in Pledges : StartUpdate(b, pledge)
    \/ ApplyUpdate
    \/ Finished

\* Literally: "Spec is defined as Init and always Next or the variables
\*   unchanged."
\* In English: start in Init; every step is a Next step or changes nothing.
Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------
\* Invariants.
\* ---------------------------------------------------------------------

\* Literally: "ValuePreserved is defined as reserves plus treasury plus fees
\*   plus deposits plus utxo plus both accounts equals MaxSupply."
\* In English: no step creates or destroys lovelace.
ValuePreserved ==
    reserves + treasury + fees + deposits + utxo + ownerAcct + memberAcct
        = MaxSupply

\* Literally: "UpdateBalanced is defined as: ru is not active or dT1 plus
\*   (dR2 minus dR1) plus leader plus member minus the snapshot fees equals
\*   0."
\* In English: deltaT + deltaR + rewards + deltaF = 0 [R1]: the update only
\* moves value. (A member reward the boundary sends to the treasury is
\* still one of the rewards.)
UpdateBalanced ==
    ~ru.active \/
    ru.dT1 + (ru.dR2 - ru.dR1) + ru.leader + ru.member - ru.feesSS = 0

\* Literally: "SplitMatchesReference is defined as: ru is not active or the
\*   update's dT1, R, pool reward, leader and member equal those the
\*   reference computes from the same inputs."
\* In English: the treasury cut and the pool split are the reference's
\* [R1]-[R3], including no reward for a pool without blocks, maxPool' of 0
\* for an unmet pledge, and no member reward computed for an unregistered
\* member before version 7.
SplitMatchesReference ==
    ~ru.active \/
    LET circ == ru.circ
        rPot == ru.feesSS + ru.dR1
        R    == rPot - Floor(QMul(Tau, Q(rPot, 1)))
        maxP == IF ru.pledge <= OwnerStake THEN MaxPool(R, circ, ru.pledge)
                ELSE 0
        f    == PoolReward(ru.blocks, maxP)
        lead == IF ru.blocks = 0 THEN 0 ELSE Leader(f, circ)
        mem  == IF ru.blocks = 0 \/ ~(ru.memberRegAtStart \/ PV >= 7) THEN 0
                ELSE Member(f, circ)
    IN /\ ru.dT1 = Floor(QMul(Tau, Q(rPot, 1)))
       /\ ru.R = R
       /\ ru.poolR = f
       /\ ru.leader = lead
       /\ ru.member = mem

\* Literally: "NoBlocksNoReward is defined as: ru is not active or ru's
\*   blocks is not 0 or the pool reward is 0."
\* In English: a pool that made no blocks earns nothing [R3].
NoBlocksNoReward == ~ru.active \/ ru.blocks # 0 \/ ru.poolR = 0

\* Literally: "PledgeUnmetNoReward is defined as: ru is not active or the
\*   pledge is at most OwnerStake or the pool reward is 0."
\* In English: an unmet pledge zeroes the pool's reward [R3].
PledgeUnmetNoReward == ~ru.active \/ ru.pledge <= OwnerStake \/ ru.poolR = 0

\* Literally: "PoolRewardWithinMax is defined as: ru is not active or the
\*   pool reward is at most MaxPool of R, circ and the pledge."
\* In English: with a performance of 1, the pool never earns more than
\* maxPool' [R2]; the rest of R stays for the reserves.
PoolRewardWithinMax ==
    ~ru.active \/ ru.poolR <= MaxPool(ru.R, ru.circ, ru.pledge)

\* Literally: "TypeOK is defined as every pot is a natural number."
\* In English: no pot ever goes negative.
TypeOK ==
    /\ reserves \in Nat /\ treasury \in Nat /\ fees \in Nat
    /\ deposits \in Nat /\ utxo \in Nat
    /\ ownerAcct \in Nat /\ memberAcct \in Nat

\* Probes: each is expected to be violated, showing the state is reached.
\* Literally: "ProbeNoUnregisteredToTreasury is defined as: ru is not
\*   active or memberReg or ru's member is 0."
\* In English: violated when an update about to be applied owes a reward to
\* a member that is no longer registered (which goes to the treasury).
ProbeNoUnregisteredToTreasury == ~ru.active \/ memberReg \/ ru.member = 0
\* Literally: "ProbeNoReserveReturn is defined as: ru is not active or ru's
\*   dR2 is 0."
\* In English: violated when part of R returns to the reserves.
ProbeNoReserveReturn == ~ru.active \/ ru.dR2 = 0
\* Literally: "ProbePrefilterSkipsMember is defined as: ru is not active or
\*   ru's memberRegAtStart or ru's member is not 0 or ru's blocks is 0 or ru's
\*   pool reward is at most Cost."
\* In English: violated when, before version 7, a paying pool's member
\* reward is not computed because the member was unregistered at the start.
ProbePrefilterSkipsMember ==
    ~ru.active \/ ru.memberRegAtStart \/ ru.member # 0 \/ ru.blocks = 0
        \/ ru.poolR <= Cost
=============================================================================
