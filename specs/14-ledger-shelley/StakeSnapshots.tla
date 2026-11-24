-------------------------- MODULE StakeSnapshots --------------------------
(***************************************************************************)
(* The mark/set/go stake snapshots (SNAP) at the epoch boundary, and which *)
(* snapshot leader election and the reward calculation read.              *)
(*                                                                         *)
(* One pool. Its delegated stake changes during an epoch, and it may       *)
(* re-register with a new VRF key. At every boundary SNAP rotates the      *)
(* snapshots and then POOLREAP adopts re-registered parameters. The model  *)
(* records, for every epoch, which snapshot elected its leaders, which     *)
(* snapshot paid its rewards, and which VRF key its block headers must     *)
(* carry.                                                                  *)
(*                                                                         *)
(* gOuroboros does not implement SNAP or the reward update: the caller     *)
(* keeps the snapshots. What gOuroboros does fix is the contract of        *)
(* VerifyBlock: the issuer's VRF key hash comes from                       *)
(* VerifyConfig.LeaderPoolVrfKeyHash, which "must use the active snapshot, *)
(* not current registration". The constant LeaderSource says what the      *)
(* caller answers it from, and the model checks the header VRF key that    *)
(* gOuroboros would then accept.                                           *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd; links and     *)
(* quotes are in specs/14-ledger-shelley/README.md.                        *)
(*   [S6] eras/shelley/formal-spec/epoch.tex 87-94, 205-225: "mark" is the *)
(*        newest snapshot, "set" elects leaders, "go" is used for rewards. *)
(*   [S7] epoch.tex 470-500: SNAP: mark := stake, set := mark, go := set.  *)
(*   [R6] eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Epoch.hs      *)
(*        157-164: SNAP runs before POOLREAP.                              *)
(*   [R7] .../Shelley/Rules/Snap.hs 75-102: the rotation.                  *)
(*   [R8] .../Shelley/Rules/PoolReap.hs 137-155: POOLREAP makes the future *)
(*        pool parameters current.                                         *)
(*   [R9] libs/cardano-ledger-core/src/Cardano/Ledger/State/SnapShots.hs   *)
(*        469-473, 543-555: the set snapshot's pool distribution drives   *)
(*        leader election; mark rotates into set, set into go.            *)
(*   [R10] .../Shelley/LedgerState/PulsingReward.hs 99-100 and             *)
(*        .../Shelley/Rules/Tick.hs 272-276: the reward update in epoch e  *)
(*        reads the go snapshot and the blocks made in epoch e-1 (bprev). *)
(*   gOuroboros [G6]: ledger/common/verify_config.go 159-171 and           *)
(*        ledger/verify_block.go 1765-1830 (the issuer VRF check).         *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla.          *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    MaxEpoch,      \* the last epoch the model runs to
    MaxStake,      \* the pool's stake takes values 0..MaxStake
    MaxKeys,       \* how many VRF keys the pool may use (first key is 1)
    LeaderSource,  \* where the caller answers LeaderPoolVrfKeyHash from:
                   \*  "Set": the set snapshot, as the contract demands
                   \*  "Current": the pool's current registration
    Mutation       \* "none", "ReapFirst" (POOLREAP before SNAP), or
                   \* "RewardFromSet" (the reward update reads set, not go)

Epochs == 0..MaxEpoch
None == -1        \* "not recorded yet"

\* A snapshot records the stake and VRF key it saw, and the epoch whose
\* starting boundary took it (0 for the genesis snapshot).
Snap(s, k, t) == [stake |-> s, vrf |-> k, taken |-> t]

VARIABLES
    epoch,        \* the current epoch
    stake,        \* the pool's delegated stake now
    vrf,          \* the VRF key in the pool's current registration
    futureVrf,    \* a re-registered VRF key waiting for the boundary, or 0
    nextKey,      \* the next fresh VRF key
    regEpoch,     \* regEpoch[k]: the epoch key k was registered in
    stakeAt,      \* stakeAt[e]: the live stake when the boundary into e ran
    mark, set, go,
    leaderSnap,   \* leaderSnap[e]: the snapshot (by .taken) electing epoch e
    leaderStake,  \* leaderStake[e]: the stake that snapshot gave the pool
    leaderVrf,    \* leaderVrf[e]: the VRF key headers in epoch e must carry
    acceptedVrf,  \* acceptedVrf[e]: the key gOuroboros accepts, per LeaderSource
    rewardSnap    \* rewardSnap[x]: the snapshot paying for epoch x's blocks

vars == <<epoch, stake, vrf, futureVrf, nextKey, regEpoch, stakeAt, mark,
          set, go, leaderSnap, leaderStake, leaderVrf, acceptedVrf, rewardSnap>>

\* In English: at the start all three snapshots are the genesis one, taken
\* "at epoch 0", with the pool's first key. Epoch 0's leaders come from it.
Init ==
    /\ epoch = 0
    /\ stake = 1
    /\ vrf = 1
    /\ futureVrf = 0
    /\ nextKey = 2
    /\ regEpoch = [k \in 1..MaxKeys |-> IF k = 1 THEN 0 ELSE None]
    /\ stakeAt = [e \in Epochs |-> IF e = 0 THEN 1 ELSE None]
    /\ mark = Snap(1, 1, 0)
    /\ set  = Snap(1, 1, 0)
    /\ go   = Snap(1, 1, 0)
    /\ leaderSnap  = [e \in Epochs |-> IF e = 0 THEN 0 ELSE None]
    /\ leaderStake = [e \in Epochs |-> IF e = 0 THEN 1 ELSE None]
    /\ leaderVrf   = [e \in Epochs |-> IF e = 0 THEN 1 ELSE None]
    /\ acceptedVrf = [e \in Epochs |-> IF e = 0 THEN 1 ELSE None]
    /\ rewardSnap  = [e \in Epochs |-> None]

\* In English: during the epoch, delegations move the pool's stake.
ChangeStake ==
    /\ epoch < MaxEpoch
    /\ \E s \in 0..MaxStake :
        /\ s # stake
        /\ stake' = s
    /\ UNCHANGED <<epoch, vrf, futureVrf, nextKey, regEpoch, stakeAt, mark,
                   set, go, leaderSnap, leaderStake, leaderVrf, acceptedVrf,
                   rewardSnap>>

\* In English: the pool re-registers with a fresh VRF key. The key waits in
\* the future parameters until the next boundary (Pool-reReg, [R8]).
ReRegister ==
    /\ epoch < MaxEpoch
    /\ nextKey <= MaxKeys
    /\ futureVrf' = nextKey
    /\ nextKey' = nextKey + 1
    /\ regEpoch' = [regEpoch EXCEPT ![nextKey] = epoch]
    /\ UNCHANGED <<epoch, stake, vrf, stakeAt, mark, set, go, leaderSnap,
                   leaderStake, leaderVrf, acceptedVrf, rewardSnap>>

\* In English: the boundary into epoch e. Under the reference order SNAP
\* rotates first, taking the new mark from the current registration, and
\* then POOLREAP makes a re-registered key current [R6]. The set snapshot
\* now elects epoch e's leaders [R9]. The reward update that runs during e
\* reads go and pays for the blocks of epoch e-1 [R10].
Boundary ==
    LET e        == epoch + 1
        adopted  == IF futureVrf # 0 THEN futureVrf ELSE vrf
        markVrf  == IF Mutation = "ReapFirst" THEN adopted ELSE vrf
        newMark  == Snap(stake, markVrf, e)
        newSet   == mark
        newGo    == set
        payFrom  == IF Mutation = "RewardFromSet" THEN newSet ELSE newGo
    IN
    /\ epoch < MaxEpoch
    /\ epoch' = e
    /\ mark' = newMark                        \* mark := current stake  [S7][R7]
    /\ set'  = newSet                         \* set  := old mark
    /\ go'   = newGo                          \* go   := old set
    /\ vrf' = adopted                         \* POOLREAP adopts future params [R8]
    /\ futureVrf' = 0
    /\ stakeAt' = [stakeAt EXCEPT ![e] = stake]
    /\ leaderSnap'  = [leaderSnap EXCEPT ![e] = newSet.taken]
    /\ leaderStake' = [leaderStake EXCEPT ![e] = newSet.stake]
    /\ leaderVrf'   = [leaderVrf EXCEPT ![e] = newSet.vrf]
    /\ acceptedVrf' = [acceptedVrf EXCEPT ![e] =
                         IF LeaderSource = "Set" THEN newSet.vrf ELSE adopted]
    /\ rewardSnap'  = [rewardSnap EXCEPT ![e - 1] = payFrom.taken]
    /\ UNCHANGED <<stake, nextKey, regEpoch>>

\* In English: at the last epoch the model stops without deadlock.
Done ==
    /\ epoch = MaxEpoch
    /\ UNCHANGED vars

Next == ChangeStake \/ ReRegister \/ Boundary \/ Done

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must always be true.                                               *)

\* In English: the blocks of every epoch are paid from the same snapshot
\* that elected that epoch's leaders.
SameSnapshotElectsAndPays ==
    \A x \in Epochs :
        rewardSnap[x] # None => rewardSnap[x] = leaderSnap[x]

\* In English: leaders of epoch e (e >= 2) are elected with the stake the
\* pool had at the boundary into e-1, that is, at the end of epoch e-2. A
\* change of delegation in epoch d counts for leader election from d+2.
LeaderStakeAge ==
    \A e \in Epochs :
        (e >= 2 /\ leaderStake[e] # None) => leaderStake[e] = stakeAt[e - 1]

\* In English: a VRF key registered in epoch r is required in block headers
\* no earlier than epoch r+3. Until then the previous key stays the leader
\* key.
VrfKeyDelay ==
    \A e \in Epochs, k \in 1..MaxKeys :
        (leaderVrf[e] = k /\ k > 1) => e >= regEpoch[k] + 3

\* In English: the key gOuroboros accepts in a header is the key the ledger
\* requires: the caller answers LeaderPoolVrfKeyHash from the set snapshot.
GoLeaderVrfMatches ==
    \A e \in Epochs : acceptedVrf[e] = leaderVrf[e]

\* Reachability probe: claims a fresh key is never required in a header.
\* Expected to fail, so VrfKeyDelay is not vacuous.
ProbeNewKeyNeverUsed ==
    \A e \in Epochs : leaderVrf[e] # None => leaderVrf[e] = 1

\* Reachability probe: claims the leader stake never differs from the live
\* stake, which fails as soon as a delegation moves between snapshots.
ProbeLeaderStakeAlwaysLive ==
    \A e \in Epochs : (e = epoch /\ leaderStake[e] # None) => leaderStake[e] = stake
=============================================================================
