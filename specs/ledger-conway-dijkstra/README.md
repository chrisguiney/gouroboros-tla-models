# what Conway and Dijkstra add to transaction validation

Model `ledger-utxo` covers the UTXO rule from Shelley to Babbage: inputs exist, the
fee is paid, value is conserved, outputs are big enough, collateral. Conway
keeps that rule and adds checks around it. Dijkstra changes its shape: a
transaction may carry sub-transactions, and the whole batch is validated
and applied as one.

This model does not repeat model `ledger-utxo`. It assumes model `ledger-utxo`'s checks pass and
keeps only the fields Conway and Dijkstra look at. The witness rules
(UTXOW) and block bodies are another model's.

## What changed

Conway:

- **Reference-script fees.** Reading reference scripts costs extra. The
  price per byte starts at `minFeeRefScriptCostPerByte` and is multiplied
  by 1.2 after every 25,600 bytes. The exact total is floored once.
  An input that is both read and spent counts once.
- **Reference-script limit.** At most 200 KiB of reference scripts per
  transaction.
- **Treasury.** A transaction may state the current treasury value; it
  must equal the treasury. A donation to the treasury counts as produced
  value; a donation of zero does not decode.
- **Deposits in the balance.** Stake registration, DRep registration and
  proposals put deposits on the produced side, from the protocol
  parameters. A stake refund is the deposit the ledger recorded; a DRep
  refund is the amount the certificate states.
- **Withdrawals.** From protocol version 10, a withdrawal to a key-hash
  reward account needs a DRep delegation (any DRep, including
  always-abstain and no-confidence). Script-hash accounts are exempt.
  Version 9 (the bootstrap phase) has no such rule.
- **Disjoint inputs.** A reference input may not also be spent at
  versions 9 and 10 (Babbage's rule, `8 < pv < 11`). Version 11 allows it.
- **Removed.** The protocol-parameter update field, MIR and genesis
  delegation certificates do not decode in Conway.
- **Valid only.** Conway runs the treasury, reference-script size and
  delegation checks only for a phase-2-valid transaction. Value
  conservation and disjointness run for every transaction.

Dijkstra (protocol version 12):

- **Sub-transactions.** Each sub-transaction is checked in order against
  the UTxO as the earlier ones left it. The top level is checked against the
  UTxO after all of them. Every level's spent and reference inputs must also
  be in the original UTxO. A phase-2-invalid batch applies no
  sub-transaction, so overlaps are not refused.
- **Every level counts.** Value conservation, the reference-script size
  and fee, and the treasury value cover every level.
- **Treasury value and reference-script size are checked for every
  transaction.** Dijkstra moved them out of the phase-2-valid branch.
- **Withdrawals (CIP-159).** A withdrawal may be partial; the batch may not
  take more than the account's original balance. In legacy mode (the top
  level needs a Plutus V1-V3 script) the top level must take exactly what
  is left after the sub-transactions, including their direct deposits.
- **Direct deposits (CIP-159).** A level may pay into a registered reward
  account; it is produced value.
- **Removed.** The DRep-delegation rule for withdrawals, the disjointness
  rule, and the legacy stake registration certificates (tags 0 and 1).
  CIP-181's removal of the delegation rule at protocol version 12 is
  Dijkstra's removal: the reference's Conway rule still applies at every
  version except 9.

### Which Dijkstra draft

gOuroboros pins the Dijkstra CDDL in `ledger/dijkstra/doc.go` at
cardano-ledger `505fa72260632fca6df33e18e18719730bf9a460`, the commit the
ouroboros-leios rc-2026w41 release is built against. It is an ancestor of
the reference revision used here, `1210d37fe6bd`; 30 commits since then
touch `eras/dijkstra/.../Rules`. The rules are cited at `1210d37fe6bd`.
Sub-transactions are CIP-0118 (nested transactions); direct deposits and
partial withdrawals are CIP-0159.

## What the model contains

`ConwayLedger.tla` (one transaction; Era is a constant):

- `GateTxs`: IsValid, the treasury field (absent, equal, wrong), the
  reference-script size (0 to one over the limit), a fee at or one below
  the reference-script fee, a withdrawal (none, key, script), and an input
  both read and spent.
- `BalTxs`: IsValid, one certificate (stake or DRep registration or
  deregistration, or a proposal), a donation, and an output that balances
  or is one off.
- The starting states: every protocol version of the era, the credential
  registered or not, its DRep delegation none, a DRep, or always-abstain.

`SubTx.tla` (Dijkstra batches):

- `InputBatches`: each level spends any subset of places `a`, `b`, `c`
  (`c` never exists) and reads none, `a` or `c`; up to two
  sub-transactions; valid or not.
- `TreasBatches`, `RefBatches`: the treasury field and reference-script
  size at each level.
- `WdrlBatches`: legacy mode or not; what the top and one sub-transaction
  withdraw; the sub-transaction's direct deposit; for an account registered
  or not with a balance of 1 or 2.
- `Spec`: a ledger that applies two batches (valid or invalid, with
  sub-transactions, direct deposits and donations) and checks that value
  is preserved, no input is spent twice, and an invalid batch gives up only
  its collateral.

`SubCerts.tla` (Dijkstra batches' certificates; extends `SubTx.tla`'s
families):

- `EBatches`: each level withdraws nothing, zero or one coin, carries one
  certificate (register, deregister or delegate the one stake credential,
  or register the one pool), and pays a direct deposit or not; up to two
  sub-transactions; valid or not; for a credential registered (balance 0
  or 1) or not and a pool registered or not. The reference applies the
  sub-transactions, then the top; within a level the withdrawal, then the
  certificate, then the direct deposit.
- `DBatches`: each level registers the pool or not; normal or legacy mode;
  the pool deposits the top and the first sub-transaction leave room for.
  The batch owes one deposit per pool the original state lacks; in legacy
  mode the top must also balance alone against the pool state after the
  sub-transactions.
- `OBatches`: each level registers the pool with parameters A, A with
  another BLS key, or B, with or without the owner's witness; the pool
  absent, or current A or B with pending A, B or none. Owners must witness
  unless the pool exists before the level and its latest parameters equal
  the new ones apart from the BLS key; never in an invalid batch.
- `Spec`: a ledger that applies three valid batches of one sub-transaction
  and a top and checks that the deposit pot equals the deposits of what is
  registered and that value is preserved.
- `RBatches`: pool registration, retirement and delegation across levels; a
  retirement needs the pool registered and leaves it registered for the
  rest of the batch.
- `MBatches`: a withdrawal and up to two certificates in one level, run in
  order, with at most one sub-transaction.
- `LBatches`: legacy mode with certificates: only the sub-transactions'
  withdrawals count against the original balance; the top's withdrawal
  must exist in the current accounts and drain the balance the
  sub-transactions left, before the top's certificate; its account need
  not exist originally.
- `IBatches`: account balance intervals (CIP-159): each level's interval
  against the account as the earlier levels left it, at the level's start;
  the top's starting interval against the original account.

`SubGov.tla` (Dijkstra batches' governance):

- `GBatches`: each level registers the credential, a DRep, the committee
  hot key or the pool, proposes an Info action or not, and casts a DRep,
  committee or pool vote on an existing action or (from the top) on the
  sub-transaction's proposal. A vote names an action by a transaction id
  that covers the vote, so a level cannot name its own proposal or a later
  one. Certificates come before proposals, proposals before votes.
- `CBatches`: DRep register, deregister and update; committee authorize and
  resign for a seated member C1 and for C2, whom an earlier level's
  UpdateCommittee proposal would add; a resigned member can do neither.
- `PBatches`: a ParameterChange (maxTxSize, nOpt, eMax, coinsPerUTxOByte
  unset, zero or good; pledge leverage unset, below 1, at least 1, or
  removed) or an UpdateCommittee whose member's term ends before, at or
  after the current epoch, at the top or in a sub-transaction.

`SubGuards.tla` (Dijkstra guards):

- `WBatches`: for a key, native or Plutus guard credential g: whether the
  top lists g, carries g's signature, where g's script is provided (nowhere,
  top, first sub-transaction), and what each level requires of g (nothing,
  without a datum, with one). Required guards must be listed at the top;
  datums must match the script kind against the batch's scripts; a listed
  script guard needs its script, a listed key guard its signature; all
  whatever IsValid says.
- `CBatches`: what each level requires (g or another credential h, with or
  without a datum); the top-level guard script's context must carry the
  levels' datums for g, keyed by level, and each required credential once.

## The questions

1. **`GoAgrees`** (both modules): does gOuroboros accept exactly the
   transactions the reference accepts?
2. **`FeeTiersMatter`**: is the fee table fine enough that flooring each
   tier separately would be caught?
3. **`ValuePreserved`**, **`SpentOnce`**, **`InvalidKeeps`**: the
   reference's batch rules, applied, keep value, never spend an input
   twice, and leave an invalid batch's other inputs alone.
4. **`DepositsMatch`**, **`ValuePreserved`** (`SubCerts`): certificates
   threaded through the levels keep the deposit pot equal to what is
   registered.

## The answers

| Config | Result | Distinct states |
|---|---|---|
| `ConwayLedgerConway` | `TypeOK`, `GoAgrees`, `FeeTiersMatter` hold: 396 gate and 72 balance transactions in each state | 18 |
| `ConwayLedgerDijkstra` | all hold | 6 |
| `SubTxTable` | `GoAgrees` holds: 29,294 batches in each state | 4 |
| `SubTxLedger` | `ValuePreserved`, `SpentOnce`, `InvalidKeeps` hold over two batches | 72 |
| `SubCertsTable` | `GoAgrees` holds: 55,860 entity and 208 deposit batches in each of 6 plain states, 1,168 owner batches in each of 21 | 21 |
| `SubCertsLedger` | `DepositsMatch`, `ValuePreserved` hold over three batches | 48 |
| `SubGuardsTable` | `GoAgrees` holds: 312 key and 912 native or Plutus guard batches, 155 context batches | 3 |
| `SubGovTable` | `GoAgrees` holds: 5,740 governance batches in each of 16 states, 8,736 DRep/committee batches in each of 6 | 48 |

gOuroboros agrees with the reference on every modelled cell. No defect was
found in this area. It has been worked over before: treasury values,
reference-script fees, sub-transaction inputs and withdrawals each have
dedicated tests, and this model's job here is to show that the decisions
fit together across protocol versions, validity and levels.

Observations, none of which changes an accepted transaction:

- `conway.UtxoValidateWithdrawals` skips the delegation rule at
  `pv >= 12`. The reference's Conway rule would still apply there, but no
  Conway ledger runs at version 12; Dijkstra has no such rule.
- gOuroboros decides legacy mode for withdrawals from the needed scripts of
  every level; the reference uses the top level only. A sub-transaction
  needing a Plutus V1-V3 script fails script-context translation
  (`UnsupportedScriptInSubTx`), so the two only differ on a transaction
  that is refused anyway.
- In Dijkstra the reference counts a stake refund as the certificate's
  amount; gOuroboros counts the recorded deposit. A valid transaction must
  state the recorded deposit, and an invalid one skips value conservation,
  so they agree on every transaction.

## Checking the checks

| Config | What it changes | Fails |
|---|---|---|
| `ConwayLedgerFeeTiersTrivialBug` | a price of 1/2 per byte, where per-tier flooring is exact | `FeeTiersMatter` |
| `ConwayLedgerGoFeeFloorPerTierBug` | fee floored tier by tier | `GoAgrees` |
| `ConwayLedgerGoTreasuryAnyPhaseBug` | Conway checks an invalid transaction's treasury value | `GoAgrees` |
| `ConwayLedgerGoTreasuryValidOnlyBug` | Dijkstra skips it | `GoAgrees` |
| `ConwayLedgerGoRefSizeValidOnlyBug` | Dijkstra skips the reference-script limit when invalid | `GoAgrees` |
| `ConwayLedgerGoDelegAtBootstrapBug` | delegation rule at version 9 | `GoAgrees` |
| `ConwayLedgerGoDelegDRepOnlyBug` | always-abstain does not count | `GoAgrees` |
| `ConwayLedgerGoDelegScriptsBug` | script accounts need a delegation | `GoAgrees` |
| `ConwayLedgerGoDisjointThroughPV11Bug` | disjointness at version 11 | `GoAgrees` |
| `ConwayLedgerGoRefundFromCertBug` | Conway refunds the stated amount for an unregistered credential | `GoAgrees` |
| `ConwayLedgerGoDonationIgnoredBug` | donation left out of produced | `GoAgrees` |
| `ConwayLedgerGoValueAnyPhaseBug` | Dijkstra checks an invalid batch's value | `GoAgrees` |
| `SubTxGoBadInputsTopOnlyBug` | only the top's inputs must exist | `GoAgrees` |
| `SubTxGoRefsUncheckedBug` | reference inputs need not exist | `GoAgrees` |
| `SubTxGoNoDuplicatesAnyPhaseBug` | an invalid batch may not overlap | `GoAgrees` |
| `SubTxGoTreasTopOnlyBug`, `SubTxGoTreasValidOnlyBug` | treasury value of the top only; of a valid batch only | `GoAgrees` |
| `SubTxGoRefTopOnlyBug` | reference-script size of the top only | `GoAgrees` |
| `SubTxGoNoAggregateBug` | withdrawals per level only | `GoAgrees` |
| `SubTxGoDrainOriginalBug` | legacy top drains the original balance | `GoAgrees` |
| `SubTxSpecSubsAgainstOriginalBug` | sub-transactions checked against the original UTxO only | `SpentOnce` |
| `SubTxSpecInvalidAppliesSubsBug` | an invalid batch spends its sub-transactions' inputs | `InvalidKeeps` |
| `SubTxSpecDonationLostBug` | donation never reaches the treasury | `ValuePreserved` |
| `SubCertsGoEntTopFirstBug` | the top's certificates before the sub-transactions' | `GoAgrees` |
| `SubCertsGoEntUnthreadedBug` | every level against the original account and pool | `GoAgrees` |
| `SubCertsGoEntCertsFirstBug` | certificate before the level's withdrawal | `GoAgrees` |
| `SubCertsGoEntDepositFirstBug` | direct deposit before the level's certificate | `GoAgrees` |
| `SubCertsGoEntAnyPhaseBug` | an invalid batch's certificates checked | `GoAgrees` |
| `SubCertsGoEntCurrentOnlyBug` | withdrawal account checked in the current state only | `GoAgrees` |
| `SubCertsGoDepPerLevelBug` | a pool deposit per registering level | `GoAgrees` |
| `SubCertsGoDepLegacyOriginalBug` | legacy top against the original pool state | `GoAgrees` |
| `SubCertsGoDepAnyPhaseBug` | an invalid batch's deposits checked | `GoAgrees` |
| `SubCertsGoOwnUnthreadedBug` | owner rule against the original pool state | `GoAgrees` |
| `SubCertsGoOwnIgnorePendingBug` | owner rule ignores pending parameters | `GoAgrees` |
| `SubCertsGoOwnAnyPhaseBug` | owners needed in an invalid batch | `GoAgrees` |
| `SubCertsGoOwnBlsCountsBug` | a BLS-only change needs the owners | `GoAgrees` |
| `SubCertsSpecPoolDepositPerLevelBug` | the ledger charges a pool deposit per level | `DepositsMatch` |
| `SubCertsSpecDirectDepositFreeBug` | a direct deposit not taken from the UTxO | `ValuePreserved` |
| `SubCertsGoRetRemovesPoolBug`, `SubCertsGoRetUnthreadedBug` | retirement unregisters at once; pool state not threaded | `GoAgrees` |
| `SubCertsGoMultiLevelStartBug`, `SubCertsGoMultiFirstOnlyBug` | each certificate against the level's start; only the first certificate carries | `GoAgrees` |
| `SubCertsGoLegDrainOriginalBug`, `SubCertsGoLegTopOriginalBug` | legacy top drains original less sub withdrawals; top account must exist originally | `GoAgrees` |
| `SubCertsGoIvAfterWithdrawalBug`, `SubCertsGoIvOriginalBug` | interval after the level's withdrawal; against the original account | `GoAgrees` |
| `SubGovGoGovUnthreadedBug`, `SubGovGoGovBeforeCertsBug`, `SubGovGoGovAnyPhaseBug` | governance against the original state; before the level's certificates; when invalid | `GoAgrees` |
| `SubGuardsGoGuardTopOnlyBug`, `SubGuardsGoGuardDatumTopOnlyBug` | only the top's requirements listed; only the top's datums judged | `GoAgrees` |
| `SubGuardsGoGuardDatumLevelScriptsBug`, `SubGuardsGoGuardKeyDatumOkBug` | datum judged against the level's own scripts; key guard with a datum | `GoAgrees` |
| `SubGuardsGoCtxTopOnlyBug`, `SubGuardsGoCtxAnyDatumBug`, `SubGuardsGoCtxNoDedupBug` | context: top's datum only; another credential's datum; a credential per requiring level | `GoAgrees` |
| `SubGovGoPpuMainBug` | gOuroboros main: eMax zero and leverage below 1 accepted (DRIFT L24) | `GoAgrees` |
| `SubGovGoPropAnyPhaseBug`, `SubGovGoPropTopOnlyBug`, `SubGovGoUcNowOkBug` | proposals checked when invalid; a sub-transaction's not checked; a term ending now allowed | `GoAgrees` |
| `SubGovGoComMainBug` | gOuroboros main: an earlier level's UpdateCommittee proposal is not a membership (DRIFT L23) | `GoAgrees` |
| `SubGovGoComUnthreadedBug`, `SubGovGoComResignAgainBug`, `SubGovGoComSameLevelBug` | not threaded; a resigned member resigns again; a level's own proposal counts | `GoAgrees` |

Reachability probes, each failing as required: a key withdrawal refused by
the delegation rule alone, an invalid Dijkstra transaction refused for its
treasury value, a transaction reading and spending one input accepted at
version 11 (`ConwayLedger`); an invalid batch with overlapping
sub-transactions accepted, a partial withdrawal accepted, a legacy top
draining its sub-transaction's direct deposit, an invalid batch applied, a
batch moving value to the treasury or reward account (`SubTx`); one level
withdrawing the whole balance then deregistering, a top-level BLS-only
re-registration without owners after a sub-transaction registered the
pool, a credential registered in a sub-transaction and deregistered at the
top, the pool registered at two levels, a legacy top withdrawing from an
account its sub-transaction registered, one level deregistering then
re-registering (`SubCerts`); the top voting on the sub-transaction's
proposal, the top authorizing a member a sub-transaction proposed
(`SubGov`).

Further probes: a sub-transaction requiring a Plutus guard whose script
only the top provides, a guard's context with two levels' datums
(`SubGuards`).

`SubGov` found two defects: DRIFT L23 and L24 (the latter where the formal
spec and the reference also differ; gOuroboros follows the reference).
`SubGuards` found none. The spec and the reference agree in
this area too.

`SubCerts` found no difference between the formal specification
(formal-ledger-specifications `60b68036c8b4`, Dijkstra `Ledger`,
`Entities`, `Certs` `newCertDeposits`, `Utxo` `producedBatch` and
`producedLegacy`) and the reference in this area, and none between the
reference and gOuroboros: no `DRIFT.md` entry.

## Go tests and mutations (gOuroboros)

Branch `test/ledger-conway-dijkstra-model`,
`ledger/dijkstra/conway_dijkstra_model_test.go`. Each test restates the
model's `Spec*` predicate in Go and builds every cell as a real Conway or
Dijkstra transaction against a mock ledger state (ouroboros-mock). The
Dijkstra rules are taken from the production rule list, so the phase
table is under test too.

| Test | Cells |
|---|---|
| `TestConwayLedgerModelGates` | 22,680 Conway (pv 9-11), 7,560 Dijkstra |
| `TestConwayLedgerModelBalance` | 144 Conway, 144 Dijkstra |
| `TestSubTxModelInputs` | 28,848 |
| `TestSubTxModelTreasury` | 78 |
| `TestSubTxModelRefScriptSize` | 168 |
| `TestSubTxModelWithdrawals` | 800 |
| `TestSubTxModelEntities` (`SubCerts` `EBatches`) | 335,160 |
| `TestSubTxModelPoolDeposit` (`DBatches`) | 416 |
| `TestSubTxModelPoolOwnerWitnesses` (`OBatches`) | 8,176 |
| `TestSubTxModelPoolRetirement` (`RBatches`) | 336 |
| `TestSubTxModelMultiCertificateLevels` (`MBatches`) | 21,672 |
| `TestSubTxModelLegacyWithdrawalCertificates` (`LBatches`) | 1,872 |
| `TestSubTxModelBalanceIntervals` (`IBatches`) | 109,800 |
| `TestSubTxModelGovernance` (`SubGov` `GBatches`, a subtest per state) | 91,840 |
| `TestSubTxModelDRepCommitteeCertificates` (`CBatches` without proposals) | 7,008 |
| `TestSubTxModelGuards` (`SubGuards` `WBatches`) | 2,136 |
| `TestSubTxModelGuardContext` (`SubGuards` `CBatches`) | 155 |
| `TestSubTxModelProposalChecks` (`SubGov` `PBatches`, without eMax zero or leverage below 1) | 660 |

Commit `824672bf` adds the last three. With the fix on
`fix/dijkstra-ppu-well-formed` (`9f7e7d38`) applied, the proposal walk
including eMax zero and leverage below 1 (1,308 cells) agrees; on main 96
of those cells fail.

Commits `727e0cd0` and `f8b8a8a9` on the same branch add the last six.
The DRep/committee test leaves out the cells with an UpdateCommittee
proposal, which fail on main (DRIFT L23); with the fix on
`fix/dijkstra-committee-proposed-member` (`0a8bde9f`) applied, all 52,416
`CBatches` cells agree, and 7 fail without it.

The `SubCerts` tests are on branch `test/dijkstra-subtx-certs-model`
(`ledger/dijkstra/subtx_certs_model_test.go`, commit `b1d3d9db`). The
entity test runs the production BatchWithdrawals,
AccountBalanceIntervals (which refuses a direct deposit to a missing
account), Withdrawals, CertificateDeposits, Delegation and
PoolCertificates rules; the deposit test both value-conservation rules;
the owner test RequiredVKeyWitnesses with a ledger state that reports
pending pool parameters.

The Go gate test uses the eras' real tier: Conway's fixed 25,600 bytes and
6/5 multiplier, Dijkstra's parameters (25,600 bytes, 3/2), a price of 1/3
lovelace per byte, and sizes in steps of 12,800 bytes up to one step over
the 204,800-byte limit.

Mutations, each killed (first failing cell):

| Mutation | First failing cell |
|---|---|
| Conway multiplier 6/5 replaced by 1 | Conway pv 9, 38,400 bytes, fee one short, accepted |
| Conway treasury value checked when invalid | Conway, invalid, wrong treasury value, refused |
| delegation rule from version 9 | Conway pv 9, key withdrawal without delegation, refused |
| disjointness through version 11 | Conway pv 11, overlap, refused |
| donation left out of produced | Conway, donation 1, refused |
| Dijkstra reference-script limit valid only | Dijkstra, invalid, over the limit, accepted |
| Dijkstra value checked when invalid | Dijkstra, invalid, unbalanced, refused |
| NoDuplicateInputs when invalid | invalid batch, top and sub spend `a`, refused |
| reference inputs not resolved | sub reads `c`, accepted |
| BadInputs on the top only | sub reads `c`, accepted |
| treasury value of the top only | sub's treasury value wrong, accepted |
| reference-script size of the top only | subs 3 + 3 units, accepted |
| no aggregate withdrawal bound | withdrawals 1 + 1 against balance 1 with a deposit of 1, accepted |
| legacy top not exact | legacy, balance 1, top withdraws 0, accepted |
| delegation overlay not threaded (`validateDijkstraGovernanceLevels` validates every level against the base state) | subs register the credential and the pool, top delegates, refused |
| direct deposit before certificates (`dijkstraApplyAccountLevel`) | sub registers and deposits, refused |
| withdrawals dropped from the threaded block state (`ApplyCertificateDepositLevel`) | balance 1, sub withdraws 1, later sub deregisters, refused |
| legacy check against the original pool state | sub and top register the pool, top leaves no deposit, refused |
| owner rule unthreaded (`UtxoValidateRequiredVKeyWitnesses` skips `ApplyPoolCertificates`) | subs register A with and without owners, refused |
| owners required when invalid | invalid, sub registers A without owners, refused |

| governance view not threaded (`validate(level, ls)`) | sub registers a DRep, top votes as it, refused |
| committee changes not applied between levels | sub resigns C1, later sub authorizes C1, accepted |
| pool certificates not threaded in `UtxoValidatePoolCertificates` | subs register then retire the pool, refused |
| only a level's first certificate applied to the threaded block state | sub registers then deregisters, top registers, refused |
| direct deposits not applied by `dijkstraApplyAccountLevel` | sub deposits into an unregistered account, accepted |
| balance intervals against an unthreaded account | sub registers, top's interval refused |
| required guards of sub-transactions ignored | sub requires a key guard the top does not list, accepted |
| sub-transactions' guard datums not judged | sub requires a key guard with a datum, accepted |
| context keeps a level's entry without a datum | context walk fails |
| Conway non-zero field check removed from Dijkstra updates | coinsPerUTxOByte zero, accepted |

Moving `ApplyCertificateDepositLevel`'s withdrawals after the certificates
survives: the per-level Conway rule already sees a level's own withdrawal,
and the threaded state after the level is the same either way.

## Specification, reference and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
|---|---|---|---|---|
| Reference-script fee | tiered, floor once | `tierRefScriptFee` | `CalculateRefScriptFee` | agree |
| Scripts counted | refs ∪ spent | `txNonDistinctRefScriptsSize` | `ConsumedReferenceScriptSize`, keyed by input | agree |
| Dijkstra scripts counted | every level | `batchNonDistinctRefScriptsSize` | `consumedRefScriptSize` | agree |
| Treasury value | equals the treasury | Conway valid only; Dijkstra always, every level | same | agree |
| Reference-script limit | 200 KiB | Conway valid only; Dijkstra always | same | agree |
| Delegated withdrawals | pv >= 10, key hashes | Conway `pv /= 9`; removed in Dijkstra | `10 <= pv < 12` | agree on every reachable version |
| Disjoint inputs | — | `8 < pv < 11`; none in Dijkstra | pv < 11; not in the Dijkstra list | agree |
| Deposits | parameters | `conwayTotalDepositsTxCerts`, proposals × `ppGovActionDeposit` | same | agree |
| Stake refund | recorded deposit | Conway lookup; Dijkstra the stated amount | recorded deposit | agree on acceptance |
| Donation | produced | `conwayProducedValue`; zero does not decode | same | agree |
| Sub-transaction inputs | in order against the threaded UTxO | `SUBUTXO`, `allInputsTxBodyF` | per level against the original, no duplicates when valid | agree |
| Withdrawals | partial, aggregate bound; legacy drain | `ENTITIES`, `SUBENTITIES` | `BatchWithdrawals`, threaded `Withdrawals` | agree |
| Sub-transaction certificates | SUBLEDGERS then ENTITIES; withdraw, CERTS, deposit | `SUBENTITIES`, `SUBCERTS` (Conway DELEG, Dijkstra POOL) | levels in order through `BlockLedgerState` and overlays | agree |
| Batch pool deposit | `newCertDeposits` over `allDCerts` | `getTotalDepositsTxCerts` over the batch | one per operator over the flattened batch | agree |
| Legacy-mode deposit | `producedLegacy` with `pools'` | top alone, `postSubsPState` | top alone after applying sub levels | agree |
| Sub-transaction proposals and votes | SUBLEDGER-V: SUBENTITIES then SUBGOV; LEDGER-V top GOVS after SUBLEDGERS | `SUBGOV` = Conway GOV with the sub's id and post-SUBENTITIES state | `validateDijkstraGovernanceLevels` overlay | agree |
| Committee certificate for a proposed member | `allColdCreds govState₁` | committee proposals of the current state | wrapped state only | does not conform (L23) |
| Account balance intervals | SUBENTITIES/ENTITIES `dom ⊆ dom rewards` at level start; starting vs `rewards₀` | same | threaded overlay | agree |
| Required top-level guards and datums | marked TODO in the reference | `MissingRequiredGuards` (top, always), `validateGuardDatums` per level against the batch's scripts | `validateDijkstraRequiredTopLevelGuards`, `validateDijkstraGuardDatums` | agree |
| Guard script context | — | `transGuardingTopTxInfo` | `dijkstraTopTxInfoGuardDatumsV4`, `dijkstraBatchRequiredGuardsV4` | agree |
| Parameter-update well-formedness | leverage ≥ 1, quorum > 1/2; no eMax/nOpt/empty | `ppuWellFormed` adds eMax, nOpt, empty; no quorum | main: no eMax, leverage ≥ 0 | does not conform (L24) |
| Owner witnesses | — | `poolOwnersWitnessRequired`, pre-level `PState`, never when invalid | `PoolOwnersWitnessRequired`, threaded | agree |
| Removed fields | — | update field, MIR, genesis delegation; Dijkstra tags 0, 1 | decode errors | agree |

## Sources

IntersectMBO/cardano-ledger commit `1210d37fe6bdef32e85179ae08b7e1e8cfd75273`;
the full list with line numbers is in the header of each module
(`[C1]`-`[C8]`, `[D1]`-`[D9]`). gOuroboros commit `756a9a89`: `[G1]`-`[G6]`.

## Not modelled

Model `ledger-utxo`'s checks (assumed to pass), witnesses and script evaluation,
governance (model `ledger-governance`), certificate state transitions beyond registration
(model `ledger-shelley`), account balance intervals and guards, the
per-block reference-script limit (block bodies), protocol versions above
12, the evaluation of guard scripts (only their context is modelled), and
every other field of a parameter update (Conway's model and unit tests).
`SubGov`
uses Info proposals only, so ancestry, treasury withdrawals and
voter/action-type restrictions are Conway's and not re-checked per level.

## Running it

```sh
scripts/run-model.sh specs/ledger-conway-dijkstra
make ledger-conway-dijkstra
```
