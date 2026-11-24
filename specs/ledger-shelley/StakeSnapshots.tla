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
(* quotes are in specs/ledger-shelley/README.md.                        *)
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
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.          *)
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

\* In English: the epochs the model runs through.
\* Literally: "Epochs is defined as 0 through MaxEpoch."
Epochs == 0..MaxEpoch
\* Literally: "None is defined as negative 1."
None == -1        \* "not recorded yet"

\* A snapshot records the stake and VRF key it saw, and the epoch whose
\* starting boundary took it (0 for the genesis snapshot).
\* Literally: "Snap of s, k and t is defined as the record whose field stake is
\*   s, whose field vrf is k, and whose field taken is t."
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

\* Literally: "vars is defined as the tuple of epoch, stake, vrf, futureVrf,
\*   nextKey, regEpoch, stakeAt, mark, set, go, leaderSnap, leaderStake,
\*   leaderVrf, acceptedVrf and rewardSnap."
vars == <<epoch, stake, vrf, futureVrf, nextKey, regEpoch, stakeAt, mark,
          set, go, leaderSnap, leaderStake, leaderVrf, acceptedVrf, rewardSnap>>

\* In English: at the start all three snapshots are the genesis one, taken
\* "at epoch 0", with the pool's first key. Epoch 0's leaders come from it.
\* Literally: "Init is defined as: epoch equals 0, and stake equals 1, and vrf
\*   equals 1, and futureVrf equals 0, and nextKey equals 2, and regEpoch equals
\*   the function that maps every k in 1 through MaxKeys to (if k equals 1 then
\*   0, else None), and stakeAt equals the function that maps every e in Epochs
\*   to (if e equals 0 then 1, else None), and mark equals Snap of 1, 1 and 0,
\*   and set equals Snap of 1, 1 and 0, and go equals Snap of 1, 1 and 0, and
\*   leaderSnap equals the function that maps every e in Epochs to (if e equals
\*   0 then 0, else None), and leaderStake equals the function that maps every e
\*   in Epochs to (if e equals 0 then 1, else None), and leaderVrf equals the
\*   function that maps every e in Epochs to (if e equals 0 then 1, else None),
\*   and acceptedVrf equals the function that maps every e in Epochs to (if e
\*   equals 0 then 1, else None), and rewardSnap equals the function that maps
\*   every e in Epochs to None."
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
\* Literally: "ChangeStake is defined as: epoch is less than MaxEpoch, and there
\*   exists an s in 0 through MaxStake such that s does not equal stake and
\*   stake in the next state equals s, and epoch, vrf, futureVrf, nextKey,
\*   regEpoch, stakeAt, mark, set, go, leaderSnap, leaderStake, leaderVrf,
\*   acceptedVrf and rewardSnap are unchanged."
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
\* Literally: "ReRegister is defined as: epoch is less than MaxEpoch, and
\*   nextKey is less than or equal to MaxKeys, and futureVrf in the next state
\*   equals nextKey, and nextKey in the next state equals nextKey plus 1, and
\*   regEpoch in the next state equals regEpoch except that its nextKey entry is
\*   epoch, and epoch, stake, vrf, stakeAt, mark, set, go, leaderSnap,
\*   leaderStake, leaderVrf, acceptedVrf and rewardSnap are unchanged."
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
\* Literally: "Boundary is defined as: letting e be epoch plus 1; adopted be: if
\*   futureVrf does not equal 0 then futureVrf, else vrf; markVrf be: if
\*   Mutation equals "ReapFirst" then adopted, else vrf; newMark be Snap of
\*   stake, markVrf and e; newSet be mark; newGo be set; payFrom be: if Mutation
\*   equals "RewardFromSet" then newSet, else newGo: epoch is less than
\*   MaxEpoch, and epoch in the next state equals e, and mark in the next state
\*   equals newMark, and set in the next state equals newSet, and go in the next
\*   state equals newGo, and vrf in the next state equals adopted, and futureVrf
\*   in the next state equals 0, and stakeAt in the next state equals stakeAt
\*   except that its e entry is stake, and leaderSnap in the next state equals
\*   leaderSnap except that its e entry is newSet's taken, and leaderStake in
\*   the next state equals leaderStake except that its e entry is newSet's
\*   stake, and leaderVrf in the next state equals leaderVrf except that its e
\*   entry is newSet's vrf, and acceptedVrf in the next state equals acceptedVrf
\*   except that its e entry is: if LeaderSource equals "Set" then newSet's vrf,
\*   else adopted; and rewardSnap in the next state equals rewardSnap except
\*   that its e minus 1 entry is payFrom's taken, and stake, nextKey and
\*   regEpoch are unchanged."
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
\* Literally: "Done is defined as: epoch equals MaxEpoch, and vars is
\*   unchanged."
Done ==
    /\ epoch = MaxEpoch
    /\ UNCHANGED vars

\* In English: "Each step changes the stake, re-registers, crosses a boundary,
\* or stops."
\* Literally: "Next is defined as: ChangeStake or ReRegister or Boundary or
\*   Done."
Next == ChangeStake \/ ReRegister \/ Boundary \/ Done

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must always be true.                                               *)

\* In English: the blocks of every epoch are paid from the same snapshot
\* that elected that epoch's leaders.
\* Literally: "SameSnapshotElectsAndPays is defined as: for all x in Epochs, if
\*   rewardSnap of x does not equal None, then rewardSnap of x equals leaderSnap
\*   of x."
SameSnapshotElectsAndPays ==
    \A x \in Epochs :
        rewardSnap[x] # None => rewardSnap[x] = leaderSnap[x]

\* In English: leaders of epoch e (e >= 2) are elected with the stake the
\* pool had at the boundary into e-1, that is, at the end of epoch e-2. A
\* change of delegation in epoch d counts for leader election from d+2.
\* Literally: "LeaderStakeAge is defined as: for all e in Epochs, if e is
\*   greater than or equal to 2 and leaderStake of e does not equal None, then
\*   leaderStake of e equals stakeAt of e minus 1."
LeaderStakeAge ==
    \A e \in Epochs :
        (e >= 2 /\ leaderStake[e] # None) => leaderStake[e] = stakeAt[e - 1]

\* In English: a VRF key registered in epoch r is required in block headers
\* no earlier than epoch r+3. Until then the previous key stays the leader
\* key.
\* Literally: "VrfKeyDelay is defined as: for all e in Epochs and all k in 1
\*   through MaxKeys, if leaderVrf of e equals k and k is greater than 1, then e
\*   is greater than or equal to regEpoch of k plus 3."
VrfKeyDelay ==
    \A e \in Epochs, k \in 1..MaxKeys :
        (leaderVrf[e] = k /\ k > 1) => e >= regEpoch[k] + 3

\* In English: the key gOuroboros accepts in a header is the key the ledger
\* requires: the caller answers LeaderPoolVrfKeyHash from the set snapshot.
\* Literally: "GoLeaderVrfMatches is defined as: for all e in Epochs,
\*   acceptedVrf of e equals leaderVrf of e."
GoLeaderVrfMatches ==
    \A e \in Epochs : acceptedVrf[e] = leaderVrf[e]

\* Reachability probe: claims a fresh key is never required in a header.
\* Expected to fail, so VrfKeyDelay is not vacuous.
\* Literally: "ProbeNewKeyNeverUsed is defined as: for all e in Epochs, if
\*   leaderVrf of e does not equal None, then leaderVrf of e equals 1."
ProbeNewKeyNeverUsed ==
    \A e \in Epochs : leaderVrf[e] # None => leaderVrf[e] = 1

\* Reachability probe: claims the leader stake never differs from the live
\* stake, which fails as soon as a delegation moves between snapshots.
\* Literally: "ProbeLeaderStakeAlwaysLive is defined as: for all e in Epochs, if
\*   e equals epoch and leaderStake of e does not equal None, then leaderStake
\*   of e equals stake."
ProbeLeaderStakeAlwaysLive ==
    \A e \in Epochs : (e = epoch /\ leaderStake[e] # None) => leaderStake[e] = stake
=============================================================================
