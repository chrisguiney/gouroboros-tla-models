# Shelley certificate lifecycles, the epoch boundary, and preservation of value

The Shelley ledger tracks who has registered a stake credential, which pool
each credential delegates to, which pools are registered or retiring, and
the deposits all of that locks up. The formal specification defines these
as transition systems: DELEG and POOL for each certificate, POOLREAP and
SNAP at the epoch boundary. Every era up to Babbage uses the same rules.

This model has two parts. `CertLifecycle.tla` models the certificate
lifecycles, their deposits, and the ada pots. `StakeSnapshots.tla` models the
mark/set/go snapshots and which of them leader election and rewards read.

## What gOuroboros does, and does not, implement

gOuroboros does **not** hold ledger state. It has no epoch-boundary code:
no POOLREAP, no SNAP, no reward update applied to accounts. A caller (Dingo)
keeps the state and hands gOuroboros a `LedgerState` to read
(`ledger/common/state.go`). gOuroboros then implements:

- **Transaction validation against that state.** The DELEG predicates
  (`UtxoValidateDelegation`, `ledger/shelley/rules.go` 757-864), the POOL
  predicates (`UtxoValidatePoolCertificates` 1349-1692), and value
  conservation with deposits and refunds
  (`UtxoValidateValueNotConservedUtxo` 341-450, and
  `PoolRegistrationDepositDue` in `ledger/common/pool_deposit.go`). Allegra,
  Mary, Alonzo and Babbage call the same Shelley functions (Alonzo and
  Babbage only for phase-2-valid transactions).
- **A block-scoped state fold.** `BlockLedgerState`
  (`ledger/common/block_state.go`) applies each transaction's
  registrations, deregistrations, pool registrations and retirements, so the
  next transaction in the same block is validated against the state its
  predecessors left. This is the only place gOuroboros changes certificate
  state, and it lasts one block.
- **Reward arithmetic** (`ledger/common/rewards.go`) as a pure function over
  a caller-supplied `RewardSnapshot`. Which snapshot is supplied is the
  caller's choice. Not modelled here.
- **The issuer VRF check** in `VerifyBlock`, which takes the pool's VRF key
  hash from a caller callback, `LeaderPoolVrfKeyHash`, that "must use the
  active snapshot, not current registration" (`ledger/common/verify_config.go`
  159-171).

So POOLREAP, SNAP and preservation of value are modelled from the
specification and reference only; for them the model checks the rules and
the contract gOuroboros places on its caller, not gOuroboros code.

## Part 1: certificate lifecycles and the ada they move (`CertLifecycle.tla`)

### What the model contains

Two stake credentials (`c1` holds the pool's reward account), one pool, a
key deposit of 1, a pool deposit of 2, `eMax` of 2, a fee of 1 per
transaction. Steps: a transaction carrying one certificate
(RegKey, DeregKey, Deleg, RegPool, RetirePool with any epoch) or a Conway
vote by the pool (PoolVote; the voter must be in `psStakePools`, [R11]), a full
withdrawal, a reward of one lovelace from the reserves (a stand-in for the
reward update), a new block within the epoch, and the epoch boundary
(fees to reserves, then POOLREAP).

Alongside the ledger it models what gOuroboros sees: the caller's view at
the start of each block, and `BlockLedgerState`'s own record of the pool
for the block. The constant `View` says how the caller reports a pool whose
retirement has taken effect:

- `Reaped`: the pool is gone, as in the ledger.
- `StaleHonest`: `PoolCurrentState` still returns the old registration with
  its reached retirement epoch, while `IsPoolRegistered` says false. The
  comment on `PoolRegistrationDepositDue` says a provider may do this (it
  was written after a Preview block was rejected for that reason), and it is
  why that function treats a reached retirement as "not registered".
- `StaleMock`: the same, but `IsPoolRegistered` is "`PoolCurrentState`
  returned a registration", which is how ouroboros-mock's `MockLedgerState`
  and Dingo's `LedgerView.IsPoolRegistered` derive it.

### The questions

1. **`ValuePreserved`**: is UTxO + deposits + fees + treasury + reserves +
   reward balances constant across every step? ([R5])
2. **`DepositsMatchObligation`**: does the deposit pot always hold exactly
   one key deposit per registered credential and one pool deposit for a
   registered pool? (the obligation; the reference asserts it after POOLREAP)
3. **`DelegationsWellFormed`**: does a delegation only ever exist from a
   registered credential to a registered pool?
4. **`RetirementPending`**: is a scheduled retirement always for a registered
   pool, in the future, and within `eMax`?
5. **`GoAgrees`**: in every reachable state and block, does gOuroboros accept
   exactly the certificates the ledger accepts, and charge the same deposit
   or refund for each?
6. Deadlock: the epoch boundary is always possible until the last epoch,
   where an explicit `Done` step stutters.

### The answers

| Config | View | Result | Distinct states |
|---|---|---|---|
| `CertLifecycle.cfg` | Reaped | all six hold | 1,811 (depth 20) |
| `CertLifecycleDeep.cfg` | Reaped, 8 ada in UTxO, 4 epochs | all hold | 323,461 (depth 40) |
| `CertLifecycleStaleHonestBug.cfg` | StaleHonest, gOuroboros today | **`GoAgrees` fails** | 1,725 |
| `CertLifecycleStaleHonestFixed.cfg` | StaleHonest, with the fix | all hold | 323,461 |
| `CertLifecycleStaleMockBug.cfg` | StaleMock, with the fix | **`GoAgrees` fails** | 343 |
| `CertLifecycleEpochAware.cfg` | StaleMock, PR #3129 (`EpochAware`) | all hold | 614,652 (depth 40) |
| `CertLifecycleEpochAwareHonest.cfg` | StaleHonest, PR #3129 | all hold | 614,652 |
| `CertLifecycleVoterHidesEpochBug.cfg` | Reaped, PR #3129 at `24916e07` (`VoterSeesEpoch = FALSE`) | **`GoAgrees` fails** | 3 steps |

Questions 1-4 hold: the ledger rules as modelled preserve value and keep
the deposit pot equal to the obligation, through registration,
deregistration, re-registration, retirement and reaping, including a
reaped pool whose reward account is unregistered (its deposit goes to the
treasury).

With a faithful caller (`Reaped`), gOuroboros agrees with the ledger on
every certificate in every state, inside a block as well as across blocks.

**The defect (`StaleHonestBug`).** The counterexample: the pool retires and
is reaped at the boundary into epoch 2. In epoch 2 a transaction registers
it again. The ledger treats that as a new registration (it is no longer in
`psStakePools`), charges the deposit, and the pool is registered. gOuroboros
charges the deposit correctly (`PoolRegistrationDepositDue` sees the reached
retirement), but `BlockLedgerState.applyPoolRegistration` decides "new or
re-registration" from `PoolCurrentState` alone, sees the stale
registration, and records only deferred parameters. `IsPoolRegistered`
then still answers from the caller's view (false), so a later transaction
in the **same block** that delegates to the pool, or retires it, is
rejected. A node would refuse a valid block. The reference decides on
membership of `psStakePools` ([R2], `Pool.hs` 251-269), which is what
`IsPoolRegistered` reports; the fix uses it (`GoFixed = TRUE`), and the
`StaleHonestFixed` config passes.

**The contract gap (`StaleMockBug`), not fixed.** If the caller's
`IsPoolRegistered` is true for a pool whose `PoolCurrentState` is stale, as
ouroboros-mock and Dingo's `LedgerView` derive it, gOuroboros accepts a
delegation to, or a retirement of, a pool that is already gone. Whether
Dingo's `PoolCurrentState` ever returns a stale registration today was not
established here (its effective-registration query appears to account for
retirements). The point is that gOuroboros has two notions of "registered":
`PoolRegistrationDepositDue` is epoch-aware, and the DELEG and POOL checks
trust `IsPoolRegistered`. `PoolState`'s doc comment should say which is
authoritative, or one epoch-aware predicate should serve all three checks.

**One epoch-aware predicate (PR #3129, `EpochAware`).** The PR makes
`PoolRegistered` (a registration from `PoolCurrentState`, and no retirement
or one whose epoch is still ahead) decide DELEG, POOL, the Conway voter
check and `BlockLedgerState`'s new-or-re-registration choice. With it the
stalest view (`StaleMock`) agrees with the ledger in every state
(`CertLifecycleEpochAware`), so the PR closes the contract gap as well as
the defect.

**Review finding: the voter check could not see the epoch
(`VoterHidesEpochBug`).** Deciding a pool with a pending retirement needs
the epoch. The Dijkstra voter check reads a committee view that did not
pass the wrapped state's `EpochState` through, so `PoolRegistered` failed
and a vote by a registered pool with a pending retirement was refused,
which the reference accepts ([R11]: membership of `psStakePools`, which a
pending retirement does not change). Counterexample: register the pool,
schedule its retirement for epoch 1, vote in epoch 0. The model had shared
the gap: it had no voter check and no switch for the epoch-aware predicate,
so it could not have caught it. `PoolVote`, `EpochAware` and
`VoterSeesEpoch` now cover it, and `RetiringPoolNeverVotesBug` shows the
passing configs reach a vote by a retiring pool. Fixed at `97dc89b2`: a
view that answers committee lookups itself (and so must not be unwrapped)
names its parent through `LedgerStateCapabilityParent`, which first-provider
lookups such as `EpochStateFor` follow. The same audit found the Dijkstra
reward-account view hiding DRep delegations from a pre-PV12 withdrawal; it
now unwraps. That view is outside this model (withdrawals carry no pool).

### Checking the checks

Each invariant is shown able to fail by a deliberate mistake (all configs
named `*Bug.cfg` must fail):

| Config | Mutation | Fails |
|---|---|---|
| `CertLifecycleDropUnclaimedBug` | POOLREAP drops an unclaimed pool deposit | `ValuePreserved` (495 states) |
| `CertLifecycleRefundTwiceBug` | a deregistration takes one extra lovelace from the deposit pot | `ValuePreserved` (132) |
| `CertLifecycleReRegDepositBug` | a re-registration takes a second pool deposit | `DepositsMatchObligation` (140) |
| `CertLifecycleKeepDelegationsBug` | POOLREAP keeps delegations to the retired pool | `DelegationsWellFormed` (1,643) |
| `CertLifecycleRetireLateBug` | retirement at `eMax + 1` accepted | `RetirementPending` (534) |

Reachability probes, each claiming an event never happens, all fail, so the
passing runs do reach them: a reaped pool's deposit going to the treasury
(`UnclaimedNeverHappensBug`, 855 states), POOLREAP clearing a delegation
(`DelegationNeverClearedBug`, 1,405), a re-registration cancelling a
retirement (`ReRegNeverCancelsBug`, 792), and a reaped pool being
registered again (`ReapedPoolNeverRegisteredBug`, 1,682), and a vote by a
pool with a pending retirement (`RetiringPoolNeverVotesBug`).

## Part 2: stake snapshots (`StakeSnapshots.tla`)

### What the model contains

One pool whose delegated stake changes during each epoch and which may
re-register with a fresh VRF key. At each boundary SNAP rotates
(go := set, set := mark, mark := current) and then POOLREAP makes
re-registered parameters current ([R6] `Epoch.hs` 157-164). The model
records, for every epoch, which snapshot elected its leaders (set, [R9]),
which paid its blocks' rewards (go, read during the next epoch together
with the previous epoch's block counts, [R10]), and which VRF key its
headers must carry. `LeaderSource` says where the caller answers
`LeaderPoolVrfKeyHash` from.

### The questions and answers

| Invariant | Question | Answer |
|---|---|---|
| `SameSnapshotElectsAndPays` | Are an epoch's blocks paid from the snapshot that elected its leaders? | Holds. |
| `LeaderStakeAge` | Are epoch e's leaders elected with the stake at the boundary into e-1 (the end of e-2)? | Holds: a delegation change in epoch d counts for leader election from d+2. |
| `VrfKeyDelay` | Is a VRF key registered in epoch r required in headers no earlier than r+3? | Holds: adopted at r+1 after SNAP, marked at r+2, leader key in r+3. |
| `GoLeaderVrfMatches` | Does gOuroboros accept the key the ledger requires, when the caller follows the `LeaderPoolVrfKeyHash` contract? | Holds with `LeaderSource = "Set"`. |

`StakeSnapshots.cfg` (6 epochs): 4,606 distinct states, depth 15.
`StakeSnapshotsDeep.cfg` (8 epochs): 30,462 states, depth 19.

Checking the checks: `StakeSnapshotsCurrentSourceBug` (a caller answering
from current registration, which the contract forbids) fails
`GoLeaderVrfMatches`; `ReapFirstBug` (POOLREAP before SNAP) fails
`VrfKeyDelay`; `RewardFromSetBug` (rewards read set) fails
`SameSnapshotElectsAndPays`. Probes: a fresh key does become the leader key
(`NewKeyNeverUsedBug`), and leader stake lags live stake
(`LeaderStakeAlwaysLiveBug`).

This part has no gOuroboros code to check beyond the caller contract; the
existing `TestVerifyBlockStateUsesLeaderSnapshot`
(`ledger/verify_block_leader_snapshot_test.go`) already pins that
`VerifyBlock` uses the callback and not the registration.

## Modelling mistakes

- The first version used `"unknown"` and `TRUE` in one variable; TLC
  cannot compare a string with a boolean. The block record became two
  booleans and a number.
- The first `ReRegDepositBug` config passed: with 5 ada in the UTxO a
  second pool registration could never be afforded, so the mutation was
  unreachable. Its config now starts with 8.

## Go tests and mutations (gOuroboros)

Existing tests already pin each DELEG and POOL predicate one certificate at
a time, and in-transaction sequences (`ledger/deleg_stake_rules_test.go`,
`ledger/pool_rules_test.go`, `ledger/delegation_certificate_order_test.go`,
`ledger/shelley/pool_deposit_rules_test.go`,
`ledger/common/value_conservation_deposit_test.go`,
`ledger/common/block_state_test.go`).

New, on branch `test/ledger-shelley-state-model`:
`ledger/cert_lifecycle_model_test.go`, `TestCertLifecycleModel`. It
restates this model's rules in Go, plays the caller (answers
`LedgerState` from the model state, performs POOLREAP at the boundary),
and walks every state reachable within three epochs: 336 states. In each it
checks all 12 certificates against a fresh block and after each accepted
certificate of an earlier transaction in the same block (1,824 two-
transaction blocks), 23,760 cells: accepted or refused as the model says,
and the deposit or refund value conservation charges. Mutations, each
killed:

| Mutation | Failing cell |
|---|---|
| `applyPoolRegistration` does not record a new pool | `after RegPool: RegPool` deposit |
| `validatePoolRetirement` upper bound `>=` instead of `>` | `RetirePool(+2)` refused |
| value conservation omits the deregistration refund | `DeregKey` deposit |
| `deregisterAccount` does not record the deregistration | `after DeregKey: RegKey` refused |
| DELEG skips the zero-balance check | `DeregKey` with a balance accepted |
| `PoolRegistrationDepositDue` never charges a new pool | `RegPool` deposit |

Fix, on branch `fix/ledger-shelley-reregister-reaped-pool`:
`TestBlockLedgerStateRegistersReapedPoolAsNew` fails before the fix and
passes after it.

## Specification, reference and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
|---|---|---|---|---|
| Delegation to an unregistered pool | rejected in DELEGS [S2] | rejected in DELEG [R1] | rejected [G1] | agree |
| Deregistration refund | `keyDeposit` per certificate [S5] | the deposit recorded at registration; `keyDeposit` if registered earlier in the tx [R4] | recorded deposit, else `keyDeposit` | agree with reference |
| Re-registration of a registered pool | no deposit, future params, cancels retirement [S3] | same [R2] | same | agree |
| Registration of a pool whose retirement took effect | new pool, deposit due | new pool (not in `psStakePools`) | deposit due; but `BlockLedgerState` kept it as a re-registration when the caller's view is stale | **defect, fixed on branch** |
| Delegation to / retirement of a reaped pool | rejected | rejected | main: trusts the caller's `IsPoolRegistered`; PR #3129: epoch-aware `PoolRegistered` | **contract gap**, closed by the PR |
| Vote by a pool with a pending retirement | accepted (in `psStakePools`) | accepted [R11] | PR #3129 `24916e07`: refused in Dijkstra (view hid the epoch); `97dc89b2`: accepted | **defect in PR, fixed** |
| Order of SNAP and POOLREAP | SNAP then POOLREAP | SNAP then POOLREAP [R6] | not implemented (caller) | n/a |
| Leader snapshot | set | set [R9] | caller callback, contract says active snapshot | agree on contract |
| Reward snapshot | go | go, with previous epoch's blocks [R10] | caller supplies `RewardSnapshot` | n/a |

## Sources

All IntersectMBO/cardano-ledger commit
`1210d37fe6bdef32e85179ae08b7e1e8cfd75273`.

| Tag | File | Lines | What |
|---|---|---|---|
| S1 | `eras/shelley/formal-spec/delegation.tex` | 403-510 | Deleg-Reg, Deleg-Dereg (`hk -> 0 in rewards`), Deleg-Deleg |
| S2 | same | 1137 | `c in DCertDeleg => dpool c in dom poolParams` |
| S3 | same | 737-830 | Pool-Reg, Pool-reReg, Pool-Retire (`cepoch < e <= cepoch + emax`) |
| S4 | `eras/shelley/formal-spec/epoch.tex` | 559-640, 244-250 | POOLREAP; obligation |
| S5 | `eras/shelley/formal-spec/utxo.tex` | 100-111, 267-305 | consumed, produced, UTXO rule |
| S6 | `epoch.tex` | 87-94, 205-225 | mark, set, go; set elects leaders |
| S7 | `epoch.tex` | 470-500 | SNAP rule |
| R1 | `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Deleg.hs` | 305-342 | delegationTransition |
| R2 | `.../Shelley/Rules/Pool.hs` | 251-315 | poolTransition |
| R3 | `.../Shelley/Rules/PoolReap.hs` | 120-217 | poolReapTransition |
| R4 | `.../Shelley/TxCert.hs` | 670-719 | shelleyTotalDepositsTxCerts, shelleyTotalRefundsTxCerts |
| R5 | `.../Shelley/AdaPots.hs` | 51-93 | totalAdaPotsES |
| R6 | `.../Shelley/Rules/Epoch.hs` | 157-164 | SNAP, then POOLREAP |
| R7 | `.../Shelley/Rules/Snap.hs` | 75-102 | snapTransition |
| R8 | `.../Shelley/Rules/PoolReap.hs` | 137-155 | future pool parameters become current |
| R9 | `libs/cardano-ledger-core/src/Cardano/Ledger/State/SnapShots.hs` | 469-473, 543-555 | set drives leader election; rotation |
| R10 | `.../Shelley/LedgerState/PulsingReward.hs` 99-100; `.../Shelley/Rules/Tick.hs` 272-276 | | reward update reads go and bprev |
| R11 | `eras/conway/impl/src/Cardano/Ledger/Conway/Rules/Gov.hs` | 473, 596-604 | a stake-pool voter must be in `psStakePools`, else `VotersDoNotExist` |

gOuroboros commit `61046085`: G1 `ledger/shelley/rules.go` 757-864; G2
same 1644-1692; G3 same 341-450 and `ledger/common/pool_deposit.go` 40-66;
G4 `ledger/common/block_state.go` 520-592, 702-753; G5
`ledger/common/state.go` 103-125; G6 `ledger/common/verify_config.go`
159-171, `ledger/verify_block.go` 1765-1830. G7 (PR #3129, `97dc89b2`):
`ledger/common/pool_deposit.go` `PoolRegistered`, `ledger/common/rules.go`
`LedgerStateCapabilityParent`, `ledger/conway/rules.go`
`UtxoValidateUnknownVoters`, `ledger/dijkstra/rules.go`
`dijkstraCommitteeCredentialView`.

## What the conformance vectors already cover

`internal/test/conformance` runs the Cardano Blueprint corpus pinned by
ouroboros-mock. Every vector in it is dumped from the Conway-era test suite
(`eras/conway/impl/dump/...`), including the four "Shelley" families, which
are Shelley ImpSpec tests run in Conway. So:

- **Conway DELEG (95) and CERTS (13)** cover the Conway versions of
  registration (with and without the explicit deposit), deregistration with
  a balance, delegation to an unregistered pool, register-and-delegate in
  one transaction, and one "delegate, retire and re-register pool" case.
- **Not covered by any vector:** the Shelley-to-Babbage DELEG rule
  (pre-Conway registration certificates and `keyDeposit` refunds), the POOL
  rule (no POOL family at all), POOLREAP, SNAP, and the cross-transaction
  fold of `BlockLedgerState`. Those are what this model and its Go test
  address.

## Not modelled

Multi-asset values, MIR certificates and genesis delegation, pointer
addresses, the reward formula and the reward update's amounts, protocol
parameter updates (a changed `keyDeposit` between registration and
refund), VRF-key uniqueness from protocol version 11, more than one pool,
and transactions with several certificates (covered by existing Go tests).

## Running it

```sh
bin/tlc -workers auto -config specs/ledger-shelley/CertLifecycle.cfg specs/ledger-shelley/CertLifecycle.tla
bin/tlc -workers auto -config specs/ledger-shelley/CertLifecycleDeep.cfg specs/ledger-shelley/CertLifecycle.tla
bin/tlc -workers auto -config specs/ledger-shelley/CertLifecycleStaleHonestFixed.cfg specs/ledger-shelley/CertLifecycle.tla
bin/tlc -workers auto -config specs/ledger-shelley/StakeSnapshots.cfg specs/ledger-shelley/StakeSnapshots.tla
bin/tlc -workers auto -config specs/ledger-shelley/StakeSnapshotsDeep.cfg specs/ledger-shelley/StakeSnapshots.tla
# every config, Bug configs expected to fail:
scripts/run-model.sh specs/ledger-shelley
```
