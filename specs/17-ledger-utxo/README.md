# Model 17: the UTXO rule from Shelley to Babbage

Every transaction passes the UTXO rule: its inputs exist, it pays at least
the minimum fee, it consumes exactly what it produces, its outputs are big
enough and not too big, and the current slot is inside its validity window.
From Alonzo a transaction may run Plutus scripts; then it puts up
collateral, and it declares in advance whether its scripts will pass
(IsValid). A transaction that declares they fail is still put on chain, but
it only gives up its collateral. Babbage adds reference inputs (read, not
spent), a collateral return output, and a stated total collateral.

`Utxo.tla` models all of that at a small scale for each era, and what
gOuroboros decides for the same transactions. A Plutus script is not
evaluated: whether a transaction's scripts pass is a field of the
transaction, so TLC tries both answers. Certificates are reduced to one
stake credential's registration, deregistration and reward withdrawal; their
own rules are model 14's.

## What gOuroboros does

gOuroboros validates a transaction against a caller-supplied `LedgerState`
with the era's ordered rule list (`UtxoValidationRuleDescriptors` in
`ledger/<era>/rules.go`), and reports what a transaction consumes and
produces (`Consumed`/`Produced`), which `BlockLedgerState.ApplyTransaction`
folds into the block's UTxO view. It does not keep the UTxO or the fee and
deposit pots; the caller (Dingo) does. So the model's ledger half (value
preservation across a run of transactions) checks the reference's rules and
the contract, and the table half checks gOuroboros' decisions.

Era delegation, read from each function body at `d0b95845`:

| Rule | Shelley | Allegra | Mary | Alonzo | Babbage |
|---|---|---|---|---|---|
| Validity | `TimeToLive` (ttl >= slot) | own interval | Allegra's | Allegra's | Allegra's |
| BadInputs | spent inputs | Shelley's | Shelley's | Shelley's (spent only); fixed: own, with collateral | Shelley's (spent only); fixed: own, with collateral and reference inputs |
| Value | own | Shelley's | own, with tokens | own | own |
| OutputTooSmall | coins | Shelley's | own (token exempts) | own, coins | own, with the return |
| OutputTooBig | - | - | own (4000) | own (`MaxValueSize`) | own, with the return |
| Collateral | - | - | - | own | own, with the return |

## What the model contains

Three places for outputs: `a` and `b` (each empty, or two or three
ada-units, a token or not, under a key or a script) and `c`, always empty,
so a transaction naming `c` names an input that does not exist. A minimum
fee of 1, a minimum output of 1, a key deposit of 1, a collateral
percentage of 150, at most two collateral inputs.

A transaction has spent inputs, collateral and reference inputs (any subset
of the three places), a fee, a mint or burn of the token, a registration or
deregistration and a withdrawal, an output that balances or is one coin or
token off, a too-big flag, validity bounds, redeemers, IsValid and the
scripts' result, and from Babbage a collateral return and a total
collateral.

Two specifications:

- `TableSpec` builds every small UTxO (place by place) and three slot and
  credential states, and checks `GoAgrees` in each: over five families of
  transactions around a base one (which inputs exist; the balance; the
  outputs; the validity interval; collateral and phase 2, about 5,000
  transactions per Babbage state), gOuroboros accepts exactly what the
  reference accepts.
- `Spec` applies accepted transactions to a ledger with three coins and a
  token at `a` and two coins at `b`, a registered credential with a reward
  of one, for three transactions (two in Babbage): valid ones, ones with
  redeemers whose scripts pass, and IsValid=false ones whose scripts fail.

## The questions

1. **`GoAgrees`**: in each era, does gOuroboros accept exactly the
   transactions the reference accepts?
2. **`ValuePreserved`**: is UTxO + fees + deposits + reward constant?
3. **`TokensPreserved`**: do tokens change only by minting and burning?
4. **`KeptUnspent`**: does a valid transaction leave its reference inputs
   alone, and an invalid one everything but its collateral?
5. Deadlock: none; the ledger stops after its last transaction, or earlier
   if no transaction can be accepted (an invalid transaction can give up the
   last outputs as collateral).

## The answers

| Config | Result | Distinct states |
|---|---|---|
| `UtxoShelleyTable` .. `UtxoBabbageTable` | `GoAgrees`, `GoBadInputsComplete` hold in every era | 253 per era with tokens (91 Shelley, Allegra) |
| `UtxoAlonzoNoCollLookup`, `UtxoBabbageNoCollLookup`, `UtxoBabbageNoRefLookup` | both hold with a witness lookup removed | 253 |
| `UtxoShelleyLedger` .. `UtxoMaryLedger` | all hold | see "Running it" |
| `UtxoAlonzoLedger` | all hold | 1,322 |
| `UtxoBabbageLedger` (2 transactions) | all hold | 2,328 |

gOuroboros agrees with the reference on every modelled cell in every era.
The cells conformance cannot reach are the pre-Conway ones: every vector in
the Blueprint corpus pinned by ouroboros-mock is dumped from the Conway
test suite (model 14's README), so none exercises the Shelley inclusive
TTL, the Allegra exclusive upper bound, Mary's pointwise minimum (a token
output below the coin minimum is accepted), Alonzo's collateral without a
return, or Babbage's collateral return, total collateral and permitted
overlap of reference and spent inputs (protocol versions 7 and 8).

**Finding, fixed on gOuroboros branch `fix/ledger-bad-inputs-reference-set`.**
The reference's BadInputs covers the spent inputs and the collateral in
Alonzo, and the reference inputs too from Babbage (`Alonzo/Rules/Utxo.hs`
538-540, `Babbage/Rules/Utxo.hs` 380-382 over `babbageAllInputsTxBodyF`,
`Babbage/TxBody.hs` 228-236). Conway runs `babbageUtxoValidation`
(`Conway/Rules/Utxo.hs` 254) with the same set at every protocol version;
the reference/spent disjointness for 8 < pv < 11 is a separate rule.
Dijkstra checks the same set plus each sub-transaction's spent and
reference inputs against the UTxO before the sub-transactions
(`Dijkstra/Rules/Utxo.hs` 346-354, `Dijkstra/TxBody.hs` 1555-1562).
gOuroboros' `UtxoValidateBadInputsUtxo` at `d0b95845` covered only the
spent inputs in every era; it agreed on acceptance only because
`ValidateCollateralVKeyWitnesses` resolves every collateral input and the
script-witness rules resolve every reference input, and the rejection
carried a witness-rule error, not `BadInputsUTxO`.

The model's `GoBadInputs` is now the reference's set ([G9]), and the
invariant `GoBadInputsComplete` says BadInputs alone rejects exactly when
the reference's does. `UtxoGoBadInputsSpentOnly{Alonzo,Babbage}Bug` put the
old predicate back and fail it. `UtxoAlonzoNoCollLookup`,
`UtxoBabbageNoCollLookup` and `UtxoBabbageNoRefLookup` remove a witness
rule's lookup and still pass `GoAgrees`: the rejection no longer depends
on it. `UtxoGoSpentOnlyCollUnresolvedBug` and
`UtxoGoSpentOnlyRefsUnresolvedBug` show the old code's dependence: with the
old predicate and the lookup removed, a transaction without redeemers
naming missing collateral (or any missing reference input) is accepted.
Conway and Dijkstra use Babbage's set, so the model stops at Babbage;
sub-transactions are covered by the Go tests only.

## Checking the checks

| Config | Mutation | Fails |
|---|---|---|
| `UtxoGoTtlExclusiveBug` | Shelley TTL exclusive | `GoAgrees` |
| `UtxoGoIntervalInclusiveBug` | Allegra accepts at invalidHereafter | `GoAgrees` |
| `UtxoGoMaryCoinMinBug` | Mary coin minimum applied to a token output | `GoAgrees` |
| `UtxoGoSpentOnlyCollUnresolvedBug` | old BadInputs, and collateral resolved only with redeemers | `GoAgrees` |
| `UtxoGoSpentOnlyRefsUnresolvedBug` | old BadInputs, and reference inputs never resolved | `GoAgrees` |
| `UtxoGoBadInputsSpentOnlyAlonzoBug` | old BadInputs (spent inputs only), Alonzo | `GoBadInputsComplete` |
| `UtxoGoBadInputsSpentOnlyBabbageBug` | old BadInputs (spent inputs only), Babbage | `GoBadInputsComplete` |
| `UtxoGoCollIgnoresReturnBug` | collateral percentage ignores the return | `GoAgrees` |
| `UtxoGoDisjointAlwaysBug` | Babbage pv 7-8 rejects overlapping reference inputs | `GoAgrees` |
| `UtxoSpecNoRefundBug` | consumed leaves out the refund | `ValuePreserved` |
| `UtxoSpecMintIgnoredBug` | token balance leaves out the mint | `TokensPreserved` |
| `UtxoSpecRefConsumedBug` | reference inputs spent | `KeptUnspent` |
| `UtxoSpecInvalidSpendsInputsBug` | invalid tx spends its inputs | `KeptUnspent` |
| `UtxoSpecFeeIgnoresReturnBug` | invalid tx moves all collateral to fees and returns some | `ValuePreserved` |

Reachability probes, each failing as required: an invalid transaction is
applied, a collateral return is created, a reference input is read, and
read while also spent, a token is burned, a refund is collected (ledger);
Mary accepts a token output below the coin minimum, a transaction with
redeemers is accepted, one with a return and total collateral is accepted,
and Babbage accepts overlapping reference and spent inputs (table).

## Go tests and mutations (gOuroboros)

Branch `test/ledger-utxo-model`, `ledger/utxo_rule_model_test.go`:

- `TestUtxoRuleModel` restates `SpecAccepts` in Go and builds every family
  as a real transaction of each era (its own body, output and witness-set
  types), against mock ledger states, runs the era's rule list, and checks
  acceptance: 367,720 cells across the five eras. Rules outside the model
  (signatures, witnesses, script data hash, network) run too, and count
  only when they fail to resolve an input, which is how gOuroboros rejects
  missing collateral and reference inputs. Plutus evaluation is replaced by
  `ValidatePlutusScriptResult` fed the model's result.
- `TestUtxoRuleModelApply` checks `Consumed`/`Produced` for valid and
  invalid Alonzo and Babbage transactions, with and without a return.

Mutations, each killed:

| Mutation | First failing cell |
|---|---|
| Shelley TTL `>` | Shelley, slot 1, ttl 1 refused |
| Allegra upper bound `>` | Allegra, slot 1, hi 1 accepted |
| Mary token output not exempt | Mary, coin-0 output holding a minted token refused |
| Mary withdrawals not consumed | Mary, withdrawal with an output one short accepted |
| Mary mint not counted | Mary, mint 1 refused |
| Alonzo collateral tokens allowed | Alonzo, token collateral accepted |
| Babbage return not subtracted | Babbage, collateral 2 less return 1 against fee 1 accepted |
| Babbage return tokens unchecked | Babbage, token collateral without return accepted |
| Babbage total collateral unchecked | Babbage, total 1 against balance 2 accepted |
| Babbage OutputTooSmall without the return | Babbage, zero-coin return accepted |
| `ValidatePlutusScriptResult` accepts passing scripts on IsValid=false | Alonzo |
| `ValidateCollateralVKeyWitnesses` skips unresolved collateral | Alonzo, missing collateral, no redeemers, accepted |
| Babbage invalid return at index 0 | `TestUtxoRuleModelApply` |
| Alonzo invalid tx also consumes inputs | `TestUtxoRuleModelApply` |

## Specification, reference and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
|---|---|---|---|---|
| Shelley TTL | `slot <= ttl` | `ttl >= slot` | `ttl >= slot` | agree |
| Allegra+ interval | `invalidBefore <= slot < invalidHereafter` | `inInterval` | same; a zero start is absent | agree |
| Mary output minimum | `getValue txout >= inject (scaledMinDeposit ...)` | `pointwise (<)`: a token exempts | positive token exempts | agree with reference |
| Alonzo+ output minimum | coins >= size-based minimum | `not pointwise (>=)` | coins compared | agree |
| Babbage outputs | all outputs incl. return | `allSizedOutputsTxBodyF` | `TransactionOutputsAndCollateralReturn` | agree |
| Inputs that must exist | Alonzo `txins ∪ collateral`; Babbage `∪ refInputs` | same; Conway same; Dijkstra adds sub-transaction inputs and reference inputs | was spent only (the rest by witness rules); fixed branch: same set as the reference | agree after the fix; see finding |
| Collateral rules gate | `txrdmrs ≠ ∅` | same | redeemers present | agree |
| Collateral balance | Babbage: coins less return | `collAdaBalance` | same, cross-multiplied | agree |
| Collateral tokens | Babbage: all returned | `isAdaOnly (coll - ret)` | `MultiAsset.Compare` | agree |
| Total collateral | equals balance when stated | same | same; return above coins rejected | agree |
| Reference/spent overlap | — | rejected only for 8 < pv < 11 | Babbage pv <= 8 skips | agree |
| IsValid | must match the scripts | `ValidationTagMismatch` | `ValidatePlutusScriptResult`, IsValid flag | agree |
| Invalid tx effect | collateral out, return in, balance to fees | `updateUTxOState` Phase2Invalid | `Consumed`/`Produced` | agree |
| Value conservation | consumed = produced incl. deposits, refunds, mint | same | same | agree |

## Sources

All IntersectMBO/cardano-ledger commit
`1210d37fe6bdef32e85179ae08b7e1e8cfd75273`.

| Tag | File | Lines | What |
|---|---|---|---|
| S1 | `eras/shelley/formal-spec/utxo.tex` | | consumed, produced, UTXO |
| S2 | `eras/shelley-ma/formal-spec/utxo.tex` | | interval, mint, value size |
| S3 | `eras/alonzo/formal-spec/utxo.tex` | | feesOK, collateral, UTXOS |
| S4 | `eras/babbage/formal-spec/utxo.tex` | | reference inputs, return |
| R1 | `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Utxo.hs` | 364-427, 511-519 | utxoInductive, TTL, value |
| R2 | `eras/allegra/impl/src/Cardano/Ledger/Allegra/Rules/Utxo.hs` | 175-293 | interval, OutputTooSmall (`pointwise (<)`), OutputTooBig |
| R3 | `eras/mary/impl/src/Cardano/Ledger/Mary/TxOut.hs` 33-60; `Mary/Value.hs` 234-235 | | scaledMinDeposit; pointwise |
| R4 | `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxo.hs` | 291-366, 392-411, 507-576 | collateral, minimum, rule order |
| R5 | `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxos.hs` | 147-166, 223-247 | IsValid must match |
| R6 | `eras/babbage/impl/src/Cardano/Ledger/Babbage/Rules/Utxo.hs` | 183-305, 329-419, 456-490 | collateral with return, disjointness, rule order, invalid tx |
| R7 | `eras/babbage/impl/src/Cardano/Ledger/Babbage/Collateral.hs` | 30-41 | collAdaBalance |

gOuroboros commit `d0b95845`: see `[G1]`-`[G8]` in `Utxo.tla`.

## Not modelled

Witnesses and signatures, script data hash, datums, network ids, bootstrap
address attributes, transaction size and execution-unit limits, the
outside-forecast rule, the exact size-based minimum formulas (the model's
minimum is "at least one unit"; the Go test's unit is far above the
Alonzo and Babbage formula values), protocol versions 9 and later
(Conway's disjointness), explicit zero encodings of optional fields
(covered by existing presence tests), and more than one token.

## Running it

```sh
scripts/run-model.sh specs/17-ledger-utxo   # every config, Bug configs expected to fail
make ledger-utxo
```
