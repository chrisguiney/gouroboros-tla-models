# the block-body rule

A block's header promises a body: its size and its hash. The block-body
rule (BBODY) checks that promise, runs the block's transactions in order
(the LEDGERS rule), and bounds what the whole block may cost: execution
units from Alonzo, reference-script bytes from Conway. Conway and Dijkstra
also check the header's protocol version here.

`BlockBody.tla` models that rule for every Shelley-family era at a small
scale, and what gOuroboros decides for the same blocks. A transaction's own
rules are model `ledger-utxo`'s; here a transaction is valid when every output it
names exists when it is applied. The header's cryptography is model `consensus`'s,
and the Leios parts of a Dijkstra body are model `ledger-leios`'s.

## What gOuroboros does

`VerifyBlock` (`ledger/verify_block.go`) checks the declared body size and
the body hash (`verifyBlock`, lines 1239-1323 at `756a9a89`), then
`VerifyBlockState` checks the maximum body size and the execution-unit
total (1411-1605), the transactions in order (`verifyBlockTransactions`,
798-817, over `common.BlockLedgerState`), and the Conway and Dijkstra
reference-script total (1735-1765,
`common.ConsumedReferenceScriptSizePerBlock`). The block decoders reject
unequal body and witness counts (`common.ExtractAndSetTransactionCbor`)
and out-of-range invalid indexes (`ledger/<era>/<era>.go`), and
`common.TransactionValidityFlags` turns the list into per-transaction
flags.

## What the model contains

A block is up to two or three transactions, an invalid_transactions list
(any order, repeats allowed, one index out of range), and the header's
declared size (exact, one less, one more), body hash (right or wrong),
witness-set count (equal, one fewer, one more) and protocol version.

A transaction names a spent input, a collateral input and an optional
reference input, relative to itself: `g` (a genesis output with a
reference script), `k` (a genesis output without), `prev` (the previous
transaction's output) and `prevret` (its collateral return); it has a
script on its output or not, and 0 or 1 execution units.

The model states the reference twice: declaratively (`SpecAccepts`: what
the earlier transactions left is the start plus their outputs minus their
spends), and step by step (`Envelope`, `ApplyTx`, `Totals`). It states
gOuroboros once (`GoAccepts`, `GoFlag`).

## The questions

1. **`Sound`** and **`Complete`**: does the step-by-step reference accept
   exactly the blocks the declarative rules accept?
2. **`UtxoMatches`**: while transactions apply, is the UTxO what the
   declarative rules say, so that an invalid transaction removed only its
   collateral and added only its return?
3. **`FlagsAgree`**: are gOuroboros' validity flags the reference's
   `alignedValidFlags` for every list the decoder accepts, including
   out-of-order and repeated indexes?
4. **`GoAgrees`**: does gOuroboros accept exactly the blocks the reference
   accepts?

## The answers

| Config | Era, scope | Result | Distinct states |
|---|---|---|---|
| `BlockBodyShelley` | Shelley/Allegra/Mary: envelope, three transactions | all hold | 1,465 |
| `BlockBodyAlonzo` | Alonzo/Babbage: ledger order, invalid lists, units | all hold | 45,019 |
| `BlockBodyAlonzoEnvelope` | decode, size, maximum, hash | all hold | 1,425 |
| `BlockBodyConwayPV10` | reference scripts against the start | all hold, and no block is rejected for a script made in it | 4,265 |
| `BlockBodyConwayPV11` | reference scripts with earlier outputs | all hold | 4,265 |
| `BlockBodyConwayHeader` | mainnet header version, gOuroboros fixed | all hold | 25 |
| `BlockBodyConwayTestnetHeader` | off mainnet, gOuroboros main | all hold | 28 |
| `BlockBodyDijkstraHeader` | HeaderProtVerTooLow | all hold | 25 |

**Finding, fixed on gOuroboros branch
`fix/ledger-bbody-header-protver-too-high`.** The Conway BBODY rule
rejects a mainnet block whose header major protocol version is more than
one above the version in force (`HeaderProtVerTooHigh`,
`Conway/Rules/Bbody.hs` 303-330). gOuroboros `main` had no such check
anywhere. `BlockBodyGoMainProtVerBug` (gOuroboros `main`) fails
`GoAgrees`; `BlockBodyConwayHeader` (the fix) passes. Off mainnet there is
no bound, and `main` already agrees (`BlockBodyConwayTestnetHeader`).

**Drift, needing a decision.** gOuroboros reads a maximum body size of 0
as "no limit" (`verify_block.go` 1568, pinned by
`TestVerifyBlock_BlockLimits_ZeroSizeLimitsAreUnlimited`); the reference's
`chainChecks` (`Chain.hs` 71-80) has no such case, so it rejects every
block. `BlockBodyGoZeroMaxBodyBug` shows the difference. No real
parameters set 0.

## Three-way comparison

| Rule | Specification | Reference (`1210d37f`) | gOuroboros (`756a9a89`) |
|---|---|---|---|
| Declared size = real size | Shelley formal spec, BBODY | `Shelley/Rules/Bbody.hs` 260-281 | `verify_block.go` 1272 |
| Real size <= maxBBSize | CHAIN rule | `Shelley/Chain.hs` 71-80 (0 means nothing fits) | 1568-1600 (0 means no limit) |
| Body hash | BBODY | `Bbody.hs` 283-300; Alonzo's four parts `BlockBody/Internal.hs` 209-224 | 1316 (`ValidateBlockBodyHash`, 3 or 4 parts) |
| Decoding: counts, index range | CDDL | `Alonzo/BlockBody/Internal.hs` 242-275 | `common.go` 1279; `alonzo.go` 111, `babbage.go` 97, `conway.go` 104 |
| Validity flags | (not stated) | `alignedValidFlags`, 304-311 | `TransactionValidityFlags`, `common.go` 1452-1479: same flags |
| Transactions in order | LEDGERS | `Shelley/Rules/Ledgers.hs` 214-231 | `verifyBlockTransactions` 798-817 with `BlockLedgerState` |
| Invalid tx: collateral only | Alonzo UTXOS | `Babbage/Rules/Utxo.hs` 456-490 | `ApplyTransaction` with `Consumed`/`Produced` |
| Units over every tx | Alonzo BBODY | `Alonzo/Rules/Bbody.hs` 157-175 | `sumBlockExUnits` 714-773 |
| Ref-script bytes per block | Conway BBODY | `Conway/Rules/Bbody.hs` 356-383; 1 MiB, `PParams.hs` 983 | `ConsumedReferenceScriptSizePerBlock`, `ref_scripts.go` 185-230 |
| Header version too high (mainnet) | Conway BBODY | `Conway/Rules/Bbody.hs` 303-330 | absent; fixed on branch |
| Header version too low | Dijkstra BBODY | `Dijkstra/Rules/Bbody.hs` 428-438 | `dijkstra/leios_header.go` 29-42 |

## Checking the checks

| Config | Mutation | Fails |
|---|---|---|
| `BlockBodyNoSizeCheckBug` | no size checks | `Sound` |
| `BlockBodyNoHashCheckBug` | no hash check | `Sound` |
| `BlockBodyNoIndexRangeBug` | an out-of-range index decodes | `Sound` |
| `BlockBodyNoProtVerCheckBug` | no header version rule | `Sound` |
| `BlockBodyLedgerAgainstStartBug` | every tx checked against the start | `Sound` |
| `BlockBodyLedgerAgainstStartCompleteBug` | the same | `Complete` |
| `BlockBodyInvalidSpendsInputsBug` | an invalid tx spends its input too | `UtxoMatches` |
| `BlockBodyExValidOnlyBug` | units summed over valid txs only | `Sound` |
| `BlockBodyRefStartAlwaysBug` | pv 11 measures against the start | `Sound` |
| `BlockBodyGoSkipRepeatsBug` | the Go flag loop ignores a repeated index | `FlagsAgree` |
| `BlockBodyGoMainProtVerBug` | gOuroboros `main` | `GoAgrees` |
| `BlockBodyGoZeroMaxBodyBug` | maximum body size 0 | `GoAgrees` |

Reachability probes, each failing as required: an accepted block spends an
output made earlier in it, holds a phase-2-invalid transaction, and has an
out-of-order or repeated invalid list; a block is rejected for its units,
for its header version, and (pv 11) for a script made earlier in it.

## The Go tests

Branch `test/ledger-bbody-model`, `ledger/block_body_model_test.go` and
`ledger/block_body_model_decode_test.go`, restate the model and run its
cells on gOuroboros: validity flags (60 lists), decoding of a real Conway
block (104), ledger order (2,323 Alonzo blocks), units (51), reference
scripts at pv 10 and 11 (2,018), the Conway limit's version switch, and the
envelope through `VerifyBlock` (36). Each group was checked to fail under a
deliberate code mutation (skip repeated indexes; an invalid transaction
keeping its collateral; checking against the start; units over valid
transactions only; no accumulation; no input/reference dedup; no index
range check; a strict units comparison; no declared size; an off-by-one
maximum; no hash). The fix branch adds
`TestVerifyBlockStateConwayHeaderProtVerTooHigh`.

The reference-script measure through protocol version 10 relies on the
caller's `UtxoState` wrapping `common.ErrUtxoNotFound` for a missing
input (`ledger/common/state.go` 31-37): a reference input to an output made
earlier in the same block is absent from the starting state, and an error
that does not wrap it rejects the block. ouroboros-mock's `WithUtxos`
returns its own `ErrNotFound`, so the test supplies a lookup that wraps it.

## Not covered

Byron (model `ledger-byron`); the Leios certificate and endorser-block parts of a
Dijkstra body (model `ledger-leios`); Peras certificates in a Dijkstra body; Dijkstra
sub-transactions' units and outputs; header size and cryptography (model
13); the transaction-index limit of 65,536 (no block can hold that many);
execution units as two dimensions (gOuroboros checks memory and steps
separately, as the reference's pointwise comparison does).

## Running it

```sh
make ledger-bbody     # every config; Bug configs must fail (about 20 s)
```
