# Conway governance

## What the code does

A Conway governance action is proposed with a deposit, voted on by
the constitutional committee (CC), DReps and stake pools (SPOs), ratified at
an epoch boundary, and then enacted or left to expire. Enacting an action
removes its rivals. Every action that leaves the proposals set gets its
deposit back.

gOuroboros implements **only the transaction checks** (the GOV rule):
`ledger/conway/rules.go` has 17 governance rules, among them
`UtxoValidateProposalAncestry`, `UtxoValidateProposalDeposit`,
`UtxoValidateHardForkCanFollow`, `UtxoValidateUnknownVoters`,
`UtxoValidateVotingOnExpiredGovAction`, `UtxoValidateBootstrapVotingRestrictions`,
`UtxoValidateStakePoolVotingRestrictions` and `UtxoValidateCCVotingRestrictions`.
It does **not** implement ratification, enactment, the delay rule, expiry
at the boundary, pruning of rivals, deposit refunds, DRep expiry and
activity (dormant epochs), or committee-member expiry. Those belong to the
code that keeps ledger state (Dingo, or `ouroboros-mock`'s
`conformance/ratification.go` in the conformance tests). gOuroboros reads
the state they produce through `LedgerState` (`GovActionById`,
`GovPurposeRoots`, `GovActionState.ExpirySlot`, committee and DRep
lookups).

So the model has two jobs: check the lifecycle the reference defines, and
check the place where gOuroboros' checks and that lifecycle depend on each
other (ancestry at submission, and what `GovActionById` may return).

The parts that are pure functions over data (who may vote on what, what a
proposal's predecessor may be) are not modelled in TLA+. They are tested
in Go as full tables.

## The questions

1. If GOV checks ancestry, does every live proposal always hang off its
   purpose's tree, and does every enacted action name the last enacted
   action of its purpose?
2. Is at most one delaying action enacted per boundary, with nothing after it?
3. Is every deposit returned exactly once, when and only when its action
   leaves the proposals?
4. Do the spec's orphan removal (`Epoch.lagda.md`) and the reference's tree
   pruning (`proposalsApplyEnactment`) leave the same proposals?
5. What does gOuroboros rely on from the ledger state for 1 to hold?

## The answers

`GovLifecycle.tla`. Three action kinds stand for all seven: HF
(HardForkInitiation, delaying, has a purpose), PP (ParameterChange,
non-delaying, has a purpose), TW (TreasuryWithdrawals, no purpose). Votes
are abstracted to "accepted". Ratification runs over the snapshot taken at
the previous boundary, as the reference's pulser does.

| Config | Result | Distinct states | Depth |
|---|---|---:|---:|
| `GovLifecycle.cfg` (3 actions, 3 epochs, lifetime 1) | pass | 23,210 | 10 |
| `GovLifecycleDeep.cfg` (4 actions, 4 epochs, lifetime 2) | pass | 2,019,018 | 13 |

1. Yes. `TreeWellFormed` and `EnactedPrevMatchesRoot` hold. The ratifier
   compares an action's predecessor with its own copy of the roots, updated
   by earlier enactments in the same pass, so a ParameterChange and its
   child can be enacted at the same boundary (probe `NeverChained`).
2. Yes (`DelayingIsLast`). A ParameterChange still enacts at the same
   boundary as a HardForkInitiation that comes after it in priority order,
   but never after one.
3. Yes (`DepositsReturnedOnce`), because the reference removes expired
   actions first and then looks for rivals in the tree that is left.
4. Yes (`SpecAgrees`), as long as the tree is well formed. Without the
   ancestry check they disagree (`GovLifecycleNoAncestrySpecBug.cfg`).
5. `UtxoValidateProposalAncestry` accepts any predecessor that
   `GovActionById` returns with the right purpose. If the state answers for
   an action enacted long ago that is no longer the root, the tree breaks
   (`GovLifecycleStaleLookupBug.cfg`, `TreeWellFormed`). Dingo filters these
   out (`ledger/view.go` `GovActionById`, at 2fc7975d), but gOuroboros'
   interface did not say it must.

   The current root must not be answered for either.
   `UtxoValidateUnknownGovActionIds` accepts a vote on any action
   `GovActionExists` finds, and the reference looks a voted-on id up in the
   live proposals only (`proposalsActionsMap`, `GovActionsDoNotExist`). If
   the state answers for the current root, a vote on an enacted action gets
   through (`GovLifecycleRootVoteBug.cfg`, `VotesOnlyLive`). Dingo returns the
   current root at 2fc7975d (`ledger/view.go` 2680-2692), so this was live.
   The model before this check let the root vote through unnoticed: its
   `Vote` drew only from live actions, so no invariant looked at what the
   lookup let a vote name. With `VotesOnlyLive` removed, the root-vote
   mutation passes (43,529 states).

## Checking the checks

Every invariant fails under some mutation, and every probe is violated.

| Config (expected to fail) | Mutation | Violated | States |
|---|---|---|---:|
| `GovLifecycleNoAncestryBug.cfg` | GOV accepts any predecessor | `TreeWellFormed` | 153 |
| `GovLifecycleNoAncestrySpecBug.cfg` | same, only `SpecAgrees` checked | `SpecAgrees` | 451 |
| `GovLifecycleStaleLookupBug.cfg` | lookup answers for an old enacted action | `TreeWellFormed` | 7,415 |
| `GovLifecycleRootVoteBug.cfg` | lookup answers for a purpose's current root (lifetime 2) | `VotesOnlyLive` | 2,739 |
| `GovLifecycleNoThreadRootBug.cfg` | ratifier keeps the roots from the start of the pass | `EnactedPrevMatchesRoot` | 4,135 |
| `GovLifecycleNoDelayBug.cfg` | a delaying enactment does not stop the pass | `DelayingIsLast` | 1,312 |
| `GovLifecyclePruneBeforeExpiryBug.cfg` | rivals found in the tree before expiry pruning | `DepositsReturnedOnce` (refunded twice) | 3,499 |
| `GovLifecycleNever{Enacted,Expired,Pruned,Delayed,Chained}ProbeBug.cfg` | probes | each its own | 850 to 5,020 |

## Go tests and mutations

Branch `test/governance-rule-model` in gOuroboros, file
`ledger/conway/gov_rule_model_test.go`. The expected values are written
from the reference, not from the code.

- `TestGovVoterActionTableModel`: 5 voter types x 8 action kinds
  (ParameterChange split into security-group and other) x PV9, PV10, PV11 =
  120 cells, through the three rules that together are the reference's
  `DisallowedVoters` and `DisallowedVotesDuringBootstrap`.
- `TestGovProposalAncestryTableModel`: 5 action kinds with a predecessor x
  8 kinds of predecessor (none, root, unknown, a live action of each kind)
  x roots set or not = 80 cells.

Each mutation of `ledger/conway/rules.go` makes cells fail:

| Mutation | Failing cells |
|---|---:|
| bootstrap: DReps may vote on anything | 14 |
| bootstrap: TreasuryWithdrawals counted as a bootstrap action | 2 |
| SPOs may vote on TreasuryWithdrawals | 2 |
| SPOs may vote on any ParameterChange | 3 |
| CC may vote on UpdateCommittee | 4 |
| UpdateCommittee given its own purpose | 6 |
| ancestry ignores purpose | 36 |
| no predecessor accepted even with a root | 5 |
| the root not accepted as a predecessor | 5 |

What existing tests already pinned: `rules_gov_transition_test.go` covers
each rule with hand-picked cells (deposit, return accounts, hard-fork
follow, HF-purpose ancestry, same-transaction proposals, expiry at and
after `ExpirySlot`, bootstrap and SPO samples); `rules_test.go` has the
bootstrap proposal table. The new tables add the full cross products,
including the committee purpose shared by two action kinds.

## What the conformance vectors cover

`internal/test/conformance/` runs 2,574 Blueprint vectors; 2,207 are Conway,
1,787 of them GOV, RATIFY, ENACT and EPOCH. They do **not** test gOuroboros'
ratification or enactment, because gOuroboros has none: the harness's
`MockStateManager` (`ouroboros-mock` v0.21.3, `conformance/ratification.go`)
does that work. For transactions the harness first runs its own validator
(`conformance/validation.go`, `ValidateTransaction`), which rejects many
governance failures before gOuroboros' rules see them.

To see what the vectors pin in gOuroboros, each of the 17 governance rules
was made to `return nil` in turn and the vectors re-run. **15 of the 17 can
be removed with all 2,574 vectors still passing.** Only
`UtxoValidateProposalProcedures` (4 vectors fail) and
`UtxoValidateEmptyTreasuryWithdrawals` (3 fail) are pinned. Ancestry,
deposit, hard-fork follow, network ids, return accounts, guardrails,
well-formedness, bootstrap proposals, unknown voters, unknown actions,
expired actions, bootstrap votes, SPO and CC restrictions, and unelected
committee voters are covered only by unit tests.

**Rules-only replay (local branch `test/conway-gov-reference`, `7c2f2013`).**
`TestRulesOnlyConformanceVectors` replays every vector without the
harness's validator, running the full Conway rule list less fee and size,
with purpose roots, the guardrails script, stake-credential deposits and
proposal contents read from the mock's state. All vectors reach their
expected outcome except three it cannot judge (a vote at slot 0 on an
expired action; two vectors whose parsed current epoch is stale). The same
mutation study then fails at least one vector for ProposalProcedures,
EmptyTreasuryWithdrawals, GovActionWellFormedness (and
`UpdateCommitteeGovAction.Validate`'s ConflictingCommitteeUpdate through
it), GuardrailsScriptHash, HardForkCanFollow, ProposalAncestry,
ProposalReturnAccounts, UnknownVoters and CCVotingRestrictions; and for
UnknownGovActionIds and VotingOnExpiredGovAction disabled together. Still
not pinned by any vector: ProposalDeposit, ProposalNetworkIds (now a 12-cell
table from Gov.hs 532-546), the return-address shape (5-cell table),
BootstrapAllowedGovActions and BootstrapVotingRestrictions (no PV9 vectors),
StakePoolVotingRestrictions, UnelectedCommitteeVoters (PV11 only), and
ValidateCommitteeTerm, which is a ratification predicate outside the
transaction rules. These keep their unit tests and the voter table.

Also seen: the mock's `buildLedgerState` sets `ExpirySlot` to
`ExpiresAfter * 432000`, the first slot of the expiry epoch rather than its
last, which would refuse votes one epoch early if the vectors reached it.

## Spec, reference, and gOuroboros

| Question | Spec (`formal-ledger-specifications`) | Reference (`cardano-ledger`) | gOuroboros | Verdict |
|---|---|---|---|---|
| Removing rivals at the boundary | remove enacted and expired, then orphans until none | remove expired with descendants, then siblings of each enacted with descendants | not implemented | agree on well-formed trees (model) |
| Return account must be registered | always | skipped in bootstrap (PV9) | skipped in PV9 | follows reference |
| CC voter must be in the enacted committee | always (`isRegistered`) | only from PV11; before, any authorized hot key | same as reference | follows reference |
| Vote expiry | epoch `<= expiresAfter` | same | `slot <= ExpirySlot`; correct only if `ExpirySlot` is the last slot of that epoch | contract now documented |
| Predecessor lookup | proposals in the gov state | the proposals tree | the purpose root from `GovPurposeRoots`, then whatever `GovActionById` returns | contract now documented |
| Vote on an enacted action | `GovActionsDoNotExist` | `proposalsActionsMap` holds live proposals only | main: accepted when `GovActionById` returns the root, which the old contract allowed and Dingo does; PR 3155 head `b5294771`: the contract excludes roots, and the hard-fork check takes the root from `GovPurposeRoots` | does not conform → conforms (model: `VotesOnlyLive`); Dingo must stop returning the root |
| Voter x action table | `canVote` (threshold defined) | `isVotingAllowed` + bootstrap | three rules | agree on all 120 cells |
| Ratification, delay, enactment, deposits, DRep and CC expiry | defined | defined | absent | out of gOuroboros' scope |

## Fix: PR 3155

Head `b5294771` (`fix/conway-governance-checks`). Review follow-up: the
`GovActionById` contract no longer lets a state return a purpose's current
root, and `UtxoValidateHardForkCanFollow` requires `GovPurposeRootsState`
for a predecessor the transaction did not propose, since a lookup miss no
longer tells an unknown predecessor from the root. Go tests:
`TestUtxoValidateHardForkCanFollowNeedsRootsForLedgerPredecessor` (fails
before the fix with "predecessor does not exist") and
`TestUtxoValidateUnknownGovActionIdsRefusesEnactedRoot`. The ancestry table
(`TestGovProposalAncestryTableModel`) already kept the root out of the
lookup. ouroboros-mock's conformance `buildLedgerState` removes an enacted
proposal (`enactProposal` calls `removeProposal`), so it meets the contract
as is.

## Earlier fix branch

`fix/governance-state-lookup-contract` (from 61046085): doc comments on
`LedgerState.GovActionById`, `GovActionExists` and
`GovActionState.ExpirySlot` that state what the GOV rules rely on. No
behaviour change, so no test.

Not fixed, noted: `UtxoValidateCCVotingRestrictions` dereferences a nil
voter key where its sibling rules skip it (only reachable from a hand-built
transaction, not from decoded CBOR); the doc comment on
`UtxoValidateHardForkCanFollow` says a predecessor without recorded
contents "leaves the numeric check deferred", but the code returns
`GovernanceStateUnavailableError`.

## Sources

| Tag | Source |
|---|---|
| Spec | `IntersectMBO/formal-ledger-specifications` 77acd80ad33015f0274a8852f906cc0280236b86, `src/Ledger/Conway/Specification/`: `Gov.lagda.md` 206-228, 250-270, 317-330, 424-433, 503-528; `Ratify.lagda.md` 575-629, 735-756; `Epoch.lagda.md` 609-660 |
| Reference | `IntersectMBO/cardano-ledger` 1210d37fe6bdef32e85179ae08b7e1e8cfd75273, `eras/conway/impl/src/Cardano/Ledger/Conway/`: `Rules/Gov.hs` 177-218, 356-391, 401-418, 460-631; `Governance/Internal.hs` 335-550; `Governance/Proposals.hs` 297-334, 499-563; `Rules/Ratify.hs` 284-382; `Rules/Epoch.hs` 183-206, 300-376; `Governance/DRepPulser.hs` 377-430; `Governance.hs` 474-518 |
| gOuroboros | 61046085, `ledger/conway/rules.go`, `ledger/common/state.go` |
| Harness | `blinklabs-io/ouroboros-mock` v0.21.3, `conformance/harness.go` 681-721, `validation.go` 38-73, `mock_state_manager.go` 1538-1756 |
| Dingo | `blinklabs-io/dingo` 2fc7975d, `ledger/view.go` 2660-2715 |

## Not modelled

Vote counting and thresholds (abstracted to "accepted"); treasury
sufficiency for withdrawals; committee term limits and minimum size; DRep
registration, expiry, activity and dormant epochs; committee-member expiry;
the other four action kinds (each behaves like HF or PP here); the
hard-fork protocol-version rule.

## Running it

```sh
bin/tlc -workers auto -config specs/ledger-governance/GovLifecycle.cfg specs/ledger-governance/GovLifecycle.tla
bin/tlc -workers auto -config specs/ledger-governance/GovLifecycleDeep.cfg specs/ledger-governance/GovLifecycle.tla
scripts/run-model.sh specs/ledger-governance   # every config; *Bug ones must fail
```
