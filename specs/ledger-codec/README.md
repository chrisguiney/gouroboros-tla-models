# Ledger encodings

Four small tables, one per encoding decision gOuroboros made differently
from cardano-ledger before a fix. Each module picks one cell of its table
in the initial state and never moves (`Next` leaves every variable
unchanged), so TLC checks every cell. A constant `Rule` selects gOuroboros
before the fix (`"main"`) or on the fix branch (`"fixed"`), and each
invariant names the reference rule it compares with.

Each `*MainBug.cfg` was written and run first, against `"main"` only, and
reproduces the input the fix's Go test fails on; the fixed configuration
was added after.

Sources are cardano-ledger `1210d37fe6bd`, cited per rule in each module
header (`[S1]`...).

## What it checks

| Module | Invariant | Reference rule |
| --- | --- | --- |
| `ProtVerWidth.tla` | `MinorWidthAsReference` | `ProtVer`'s minor is a `Word32` (`BaseTypes.hs` 212) |
| | `OutcomeAsReference` | decoding (`decodeProtVer`, `BaseTypes.hs` 254-264) and `pvCanFollow` (`Shelley/PParams.hs` 338-340) together |
| | `MajorWidthAsReference` | the major is refused at decoding above `ProtVerHigh era + 1` |
| `CostModelLanguages.tla` | `LegacyCostModelsAsReference` | before version 9, `decodeCostModelLegacy` accepts PlutusV1 and PlutusV2 with their exact parameter counts (`Plutus/CostModels.hs` 307-338) |
| `PreConwaySetTag.tla` | `SetTagAsReference` | `decodeSet` refuses a tag before version 9 and permits tag 258 from 9 (`Binary/Decoding/Decoder.hs` 930-953); witness sets use `decodeList` below 9 (`Shelley/TxWits.hs` 261-273, `Alonzo/TxWits.hs` 347-357, 569-580, 660-700, 721-730) |
| `TxOutValueData.tla` | `TransValueAsReference` | `transValue` always has the ada entry, zero included (`Plutus/TxInfo.hs` 186-187, `Alonzo/Plutus/TxInfo.hs` 417-418, `Babbage/TxInfo.hs` 158) |
| `MaryMinCoin.tla` | `MinCoinAsReference` | `MinCoinTxOut` is `scaledMinDeposit` of the output (`Mary/TxOut.hs` 47-76, `Mary/Value.hs` 238-258, 747-762) |
| | `VerdictAsReference` | the too-small verdict is `pointwise (<)` against that minimum (`Allegra/Rules/Utxo.hs` 270-284) |

`ProtVerWidth` scales the widths so TLC's integers suffice: `W16` = 12
stands for 65,535 and `W32` = 20 for 4,294,967,295; every era's major
bound (`Internal/Definition/Era.hs` 92-125: Shelley 2 to Babbage 8) stays
far below `W16`, as in the real numbers.

## Configurations

| Config | Fix | Rule | Result | Counterexample, and the Go test it matches |
| --- | --- | --- | --- | --- |
| `ProtVerWidthMainBug.cfg` | L14 | main | **fails** `MinorWidthAsReference` | Shelley, proposal minor 65,536: refused. `TestClassicProtocolParameterUpdateDomains` "protocol minor Word32 width accepted" (`[2, MaxUint32]`) fails on main |
| `ProtVerWidthMainOutcomeBug.cfg` | L14 | main | **fails** `OutcomeAsReference` | current `(2, 65535)`, proposal `(2, 65536)`: the reference lets it follow, main refuses it |
| `ProtVerWidth.cfg` | L14 | fixed | passes | |
| `ProtVerWidthMajorClassBug.cfg` | L14 | fixed | **fails** `MajorWidthAsReference` (known difference) | Shelley, proposal major 4: the reference refuses it at decoding, gOuroboros by the follow rule. The verdict agrees |
| `ProtVerWidthWrapBug.cfg` | L14 | fixed | **fails** `OutcomeAsReference` (found by the model) | current `(2, maxBound)`, proposal `(2, 0)`: `pvCanFollow` adds 1 to the minor in `Word32`, which wraps to 0, so the reference accepts; gOuroboros' `protocolVersionCanFollow` does not wrap and refuses |
| `CostModelLanguagesMainBug.cfg` | L29 | main | **fails** `LegacyCostModelsAsReference` | version 5, one exact PlutusV2 model: "unknown cost model language 1", as `TestAlonzoCostModelUpdateLanguagesAsReference` reports at pv 5 |
| `CostModelLanguages.cfg` | L29 | fixed | passes | versions 5-8, one or two models of four languages, exact or short |
| `PreConwaySetTagMainBug.cfg` | L30 | main | **fails** `SetTagAsReference` | Shelley pool owners with tag 258: decoded. The first cell of `TestPreConwaySetFieldsRefuseTag258` ("shelley pool owners") |
| `PreConwaySetTagMainOtherTagBug.cfg` | L30 | main | **fails** `SetTagAsReference` | any tag on pool owners and witness-set fields |
| `PreConwaySetTag.cfg` | L30 | fixed | passes | tags none and 258, every era Shelley to Conway, every set field |
| `PreConwaySetTagOtherTagBug.cfg` | L30 | fixed | **fails** `SetTagAsReference` (found by the model) | Shelley witness set, a field with a tag other than 258 and no tag 258 head elsewhere: decoded; the reference refuses every tag |
| `PreConwaySetTagBuiltOwnersBug.cfg` | L30 | anyTag | **fails** `BuiltOwnersRoundTrip` | a built Shelley pool registration: owners written under tag 258, then refused by the decoder |
| `TxOutValueDataMainBug.cfg` | L15 | main | **fails** `TransValueAsReference` | a Shelley output of coin 0 in a PlutusV3 TxInfo: no ada entry. `TestTxOutPlutusDataKeepsZeroAda` "shelley" |
| `TxOutValueData.cfg` | L15 | fixed | passes | four output eras, PlutusV1 to V3, coin 0 or 1, with and without assets |
| `MaryMinCoinMainBug.cfg` | L33 | main | **fails** `MinCoinAsReference` | mv 27, one policy, one asset with an empty name: minimum 38, main returns 27 |
| `MaryMinCoinMainVerdict.cfg` | L33 | main | passes `VerdictAsReference` | the verdict already agrees, so the fix must not change it |
| `MaryMinCoin.cfg` | L33 | fixed | passes | mv 27 and 1,000,000, seven value shapes, coin around the parameter, zero-quantity output |
| `MaryMinCoinZeroCountedBug.cfg` | L33 | zeroCounted | **fails** `VerdictAsReference` | a zero-quantity output with coin equal to mv: sizing the zero entry raises the minimum and rejects it; the reference holds no zero quantity |

## Found by the model

- **L30, another tag on a witness-set field.** The fix
  (`fix/ledger-pre-conway-set-tag`, `e9dd7145`) re-reads a witness set
  only when its bytes contain a tag 258 head, and the re-read refuses a
  field headed by any tag. So a witness-set field (Shelley 0-2, Alonzo
  0-4, Babbage 0-6) tagged with another number, for example 259, decodes
  unless a tag 258 head appears somewhere else in the same map, where the
  reference refuses every tag. Checked in Go on the fix branch: a Shelley
  vkey witness list under tag 259 decodes, and the same list with the
  bytes `d9 01 02` inside a signature is refused; on the fix's parent both
  decode. Pool owners (any tag) and the typed input and signer sets
  ("unexpected tag type") already refuse another tag.
- **L14, the minor's wraparound.** From a current minor of `Word32`
  `maxBound`, the reference's `pvCanFollow` lets `(major, 0)` follow,
  because `minor + 1` wraps; gOuroboros refuses it. Reachable only from a
  genesis or chain whose minor is already `maxBound`.

## Spec, reference, and gOuroboros

| Fix | Branch / PR | gOuroboros before | gOuroboros after |
| --- | --- | --- | --- |
| L14 | `fix/ledger-pparam-update-minor-width`, PR #3278 | major and minor at most 16 bits (`ledger/common/pparam_update_validation.go`) | minor at most 32 bits; major still 16 |
| L29 | `fix/ledger-alonzo-v2-cost-model-update` (`283f75cb`), PR #3280 | Alonzo update: PlutusV1 only (`ledger/alonzo/pparams.go`) | PlutusV1 and PlutusV2, as Babbage |
| L30 | `fix/ledger-pre-conway-set-tag` (`e9dd7145`), PR #3289 | tag 258 refused before Conway on spent inputs only | refused on every set field before Conway (`ledger/common/pre_conway_sets.go`, `certs.go`) |
| L15 | `fix/script-context-zero-ada-output` (`51c2b6f3`), PR #3281 | an output's `ToPlutusData` writes the ada entry only for a positive coin | always |

## Not modelled

- Duplicate members of a pre-Conway set (silently merged by the
  reference): unchanged by these fixes.
- The multi-asset entries' own encoding and order, and the mint value:
  pinned by the Conway `translations.cbor` golden test.
- Cost model values (each parameter's range): checked by `mkCostModel` in
  the reference and by Go unit tests.

## Running it

```sh
scripts/run-model.sh specs/ledger-codec
# or one config:
cd specs/ledger-codec && ../../bin/tlc -config ProtVerWidthMainBug.cfg ProtVerWidth.tla
```

All 13 configs run in a few seconds.
