# Reward pots

`RewardPots.tla` follows the ada pots across epoch boundaries: a reward
update starts, takes deltaR1 from the reserves, gives the treasury its cut,
splits one pool's reward between its leader and a member, and is applied at
the boundary, returning what was not paid to the reserves. Transactions pay
fees and register or deregister the member in between, so a member can be
registered when the update starts and not when it is applied.

Sources are cardano-ledger `1210d37f`: `Shelley/LedgerState/PulsingReward.hs`
(`startStep`, `completeRupd`), `State/SnapShots.hs` (`maxPool'`),
`Shelley/Rewards.hs` (`mkApparentPerformance`, `calcStakePoolOperatorReward`,
`calcStakePoolMemberReward`, `mkPoolRewardInfo`, `rewardOnePoolMember`),
`Shelley/LedgerState/IncrementalStake.hs` (`applyRUpdFiltered`) and
`Shelley/Era.hs` (`hardforkBabbageForgoRewardPrefilter`). The Shelley formal
specification's rewards chapter (`rewards.tex`) defines the same quantities;
the `formal-spec` directory is not present at the pinned revision, so the
model cites the implementation.

## What it checks

| Invariant | Meaning |
| --- | --- |
| `ValuePreserved` | reserves + treasury + fees + deposits + outputs + reward accounts is the supply in every state |
| `UpdateBalanced` | deltaT + deltaR + rewards + deltaF = 0 for every pending update |
| `SplitMatchesReference` | deltaT1, R, the pool reward, the leader and the member reward are the reference's |
| `NoBlocksNoReward` | a pool that made no blocks earns nothing |
| `PledgeUnmetNoReward` | a pool whose owners' stake is below its pledge earns nothing |
| `PoolRewardWithinMax` | with a performance of 1 the pool earns at most `maxPool'` |
| `TypeOK` | no pot goes negative |

## Configurations

| Config | Expected | What it shows |
| --- | --- | --- |
| `RewardPots.cfg` | pass (8,188 states) | protocol version 6: the registration prefilter |
| `RewardPotsPV8.cfg` | pass (7,868 states) | version 8: no prefilter, unregistered rewards to the treasury |
| `RewardPotsWholePotBug.cfg` | `PoolRewardWithinMax` violated | the pool paid all of R, as gOuroboros's old pro-rata split did |
| `RewardPotsNoBlocksPaidBug.cfg` | `NoBlocksNoReward` violated | a blockless pool paid, as gOuroboros's old equal-share fallback did |
| `RewardPotsUnregToLeaderBug.cfg` | `SplitMatchesReference` violated | an unregistered member's share given to the leader, as gOuroboros did |
| `RewardPotsNoReserveReturnBug.cfg` | `ValuePreserved` violated | deltaR2 not returned |
| `RewardPotsBalanceBug.cfg` | `UpdateBalanced` violated | the same, seen in the update itself |
| `RewardPotsIgnorePledgeBug.cfg` | `PledgeUnmetNoReward` violated | the pledge check skipped |
| `RewardPotsUnregDroppedBug.cfg` | `ValuePreserved` violated | an unregistered reward neither credited nor sent to the treasury |
| `RewardPotsProbeUnregisteredBug.cfg` | probe violated | a reward is owed to a deregistered member at the boundary |
| `RewardPotsProbeReserveReturnBug.cfg` | probe violated | part of R returns to the reserves |
| `RewardPotsProbePrefilterBug.cfg` | probe violated | before version 7 an unregistered member's reward is not computed |

## Spec, reference, and gOuroboros

| Question | Spec (`rewards.tex`) | Reference (`cardano-ledger`) | gOuroboros before | gOuroboros after (`fix/ledger-rewards-reference`) |
| --- | --- | --- | --- | --- |
| deltaR1 | floor(min(1, eta) * rho * reserves) | same; eta = 1 when d >= 0.8, else blocks / floor((1-d) f slots) | rho in millionths floored, then eta floored again; d ignored; exact `ExpansionRate` ignored | reference |
| Treasury cut | floor(tau * (fees + deltaR1)) | same | tau in ten-thousandths; exact `TreasuryRate` ignored | reference |
| Existing rewards pot | not applicable | not applicable | dropped (value lost) | kept |
| Pool reward | floor(appPerf * maxPool) | same, `maxPool'` with a0, nOpt and the pledge check | a share formula of its own, the whole pot split pro rata; no nOpt, no pledge check | reference |
| Pool without blocks | no reward | no reward | perfect performance when no block counts; equal shares when no pool had a share | no reward |
| Relative stake | against total stake (circulation) | against circulation; apparent performance against active stake | active stake only | `RewardSnapshot.TotalStake` (falls back to active stake) |
| Unregistered member | filtered before Babbage; to the treasury at application | prefilter before version 7; to the treasury at application | share added to the operator | prefilter before 7; to the treasury from 7 |
| Undistributed rewards | back to the reserves (deltaR2) | same | none (whole pot paid) | back to the reserves |
| Owners as members | no member reward | `notPoolOwner` | owners paid as members too | reference |

gOuroboros reads registration once (`RewardSnapshot.StakeRegistrations`), so
it uses the same view for the prefilter and for application. The model also
covers a member deregistering between the two; that case belongs to the
caller, which applies the update.

## Go tests (on `fix/ledger-rewards-reference`)

- `TestCalculateAdaPotsReferenceTable`, `TestCalculateRewardsReferenceTable`:
  exact values computed from a Python `fractions` transcription of the
  reference.
- `TestRewardUpdateCells`: the model's cells (version 6 or 8, blocks, pledge
  met or not, member registered or not) on one pool, checking the
  invariants above against a transcription of the reference formulas.
- `TestRewardUpdateConservesAda`: value preservation across
  `CalculateAdaPots` and `CalculateRewards`.

Mutations of the pledge check, the no-block rule, the prefilter version, the
deltaR2 return, the unregistered-to-treasury move, the d >= 0.8 rule, the
(1-d) expected blocks, owner exclusion, the z0 cap, the kept pot and the
apparent performance each fail at least one of these tests.

## Not modelled

- Several pools; the pro-rata interaction between pools is gone in the
  reference, so one pool shows every rule.
- Shelley's (protocol version 2) one-reward-per-credential filter and
  aggregation across pools: the caller applies the result.
- The non-myopic likelihoods and the pulser's chunking.
- Dijkstra's pledge leverage and minimum margin: covered by Go tables, not
  here.
