# Model 24: what Conway and Dijkstra add to transaction validation

Model 17 covers the UTXO rule from Shelley to Babbage: inputs exist, the
fee is paid, value is conserved, outputs are big enough, collateral. Conway
keeps that rule and adds checks around it. Dijkstra changes its shape: a
transaction may carry sub-transactions, and the whole batch is validated
and applied as one.

This model does not repeat model 17. It assumes model 17's checks pass and
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

## The questions

1. **`GoAgrees`** (both modules): does gOuroboros accept exactly the
   transactions the reference accepts?
2. **`FeeTiersMatter`**: is the fee table fine enough that flooring each
   tier separately would be caught?
3. **`ValuePreserved`**, **`SpentOnce`**, **`InvalidKeeps`**: the
   reference's batch rules, applied, keep value, never spend an input
   twice, and leave an invalid batch's other inputs alone.

## The answers

| Config | Result | Distinct states |
|---|---|---|
| `ConwayLedgerConway` | `TypeOK`, `GoAgrees`, `FeeTiersMatter` hold: 396 gate and 72 balance transactions in each state | 18 |
| `ConwayLedgerDijkstra` | all hold | 6 |
| `SubTxTable` | `GoAgrees` holds: 29,294 batches in each state | 4 |
| `SubTxLedger` | `ValuePreserved`, `SpentOnce`, `InvalidKeeps` hold over two batches | 72 |

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

Reachability probes, each failing as required: a key withdrawal refused by
the delegation rule alone, an invalid Dijkstra transaction refused for its
treasury value, a transaction reading and spending one input accepted at
version 11 (`ConwayLedger`); an invalid batch with overlapping
sub-transactions accepted, a partial withdrawal accepted, a legacy top
draining its sub-transaction's direct deposit, an invalid batch applied, a
batch moving value to the treasury or reward account (`SubTx`).

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
| Removed fields | — | update field, MIR, genesis delegation; Dijkstra tags 0, 1 | decode errors | agree |

## Sources

IntersectMBO/cardano-ledger commit `1210d37fe6bdef32e85179ae08b7e1e8cfd75273`;
the full list with line numbers is in the header of each module
(`[C1]`-`[C8]`, `[D1]`-`[D9]`). gOuroboros commit `756a9a89`: `[G1]`-`[G6]`.

## Not modelled

Model 17's checks (assumed to pass), witnesses and script evaluation,
governance (model 15), certificate state transitions beyond registration
(model 14), pool deposits, account balance intervals and guards, the
per-block reference-script limit (block bodies), protocol versions above
12, and sub-transactions' certificates and governance procedures.

## Running it

```sh
scripts/run-model.sh specs/24-ledger-conway-dijkstra
make ledger-conway-dijkstra
```
