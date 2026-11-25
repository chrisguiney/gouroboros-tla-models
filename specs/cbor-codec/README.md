# CBOR codec decisions

Five small table models, one per codec decision gOuroboros changed to
follow the reference. Each picks one abstract input (a protocol version, an
encoding shape, a Go value) and compares gOuroboros's verdict or bytes with
the reference's. There are no steps: a table model is a state machine whose
only state is its input, so TLC checks every row of the table.

Each model was written bug-first: the config with gOuroboros's old rule
(`*MainBug.cfg`) was run and its counterexample compared with the input the
Go test fails on, before the config with the fixed rule was added. Configs
ending `FixBug.cfg` are cases the fix leaves different from the reference
(see "What the models found").

Run every config with `scripts/run-model.sh specs/cbor-codec`.

## Sources

| Tag | Source |
| --- | --- |
| R-rat | cardano-ledger [`1210d37fe6bd`](https://github.com/IntersectMBO/cardano-ledger/tree/1210d37fe6bd) `libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/Decoder.hs` 465-484 (`decodeRational`), 1347-1354 (`allowTag`); `Plain.hs` 159-189 (`decodeRationalWithTag`, `assertTag`); `Decoding/DecCBOR.hs` 210-211, 271-280 (`decodeIntegralRational`); `libs/cardano-ledger-core/src/Cardano/Ledger/BaseTypes.hs` 386-428 (`BoundedRatio`), 469-480, 544-556 (`NonNegativeInterval`, `UnitInterval`) |
| R-constr | plutus [`bdc12f105a98`](https://github.com/IntersectMBO/plutus/tree/bdc12f105a98) `plutus-core/plutus-core/src/PlutusCore/Data.hs` 146-160 (`encodeData`), 185-198 (`encodeBs`), 271-275 (`decodeListOf`), 286-307 (`decodeConstr`); `plutus-core/plutus-core/test/CBOR/DataStability.hs` |
| R-set | RFC 8949 section 3.1; cardano-ledger `1210d37fe6bd` `eras/conway/impl/golden/tx.cbor` (field 20) and `Decoding/Decoder.hs` 1057-1080 |
| R-ma | cardano-ledger `1210d37fe6bd` `eras/mary/impl/src/Cardano/Ledger/Mary/Value.hs` 299-308 (`decodeMaryValue`), 331-352 (`decodeMultiAsset`), 369-393 (`decodeIntegerBounded64`); conway.cddl `multiasset`, `mint` |

## Models

| Model | Decision | Invariant | DRIFT | Fix |
| --- | --- | --- | --- | --- |
| `CborRational.tla` | protocol version x tags before a rational -> accept | `TagsAsReferenceRational` | L25 | `fix/cbor-rat-single-tag` `fe4f8206` (#3282) |
| `PlutusConstrFields.tla` | tag family x alternative number x fields item -> accept | `FieldsAsDecodeListOf` | L26 | `fix/cbor-constructor-fields-list` `a37a8a90` (#3283) |
| `ValueSetMembers.tla` | position x tag 258 content x member kinds x whole-tree overrun -> accept | `SetMembersAsRfc8949`, `TreeBudgetHolds` | L27 | `fix/cbor-value-set-members` `a69cd1ad` (#3284) |
| `MultiAssetQuantity.tla` | protocol version x field x value x head or bignum -> accept | `QuantityAsDecodeWord64` | L28 | `fix/ledger-multiasset-bignum-quantity` `4ae0d4f9` (#3279) |
| `ConstructorEncoding.tla` | tag family x Go fields value x item kinds -> byte shape (hence hash) | `BytesAsPlutusEncodeData` | L31 | `fix/cbor-constructor-indefinite-fields` `c03e5b5a` (#3290) |

## Configs

| Config | Rule | Result | Counterexample, and the Go input it matches |
| --- | --- | --- | --- |
| `CborRationalMainBug` | main vs `decodeRational`, pv 9, 12 | fails | tags `<<31>>`: `d81f820102` |
| `CborRationalMainNestedBug` | main, tag 30 only | fails | tags `<<30, 30>>`: `d81ed81e820102` |
| `CborRational` | fix vs `decodeRational`, pv 9, 10, 12 | passes (63 states) | |
| `CborRationalBoundedMainBug` | main vs `BoundedRatio` | fails | tags `<<>>` |
| `CborRationalBoundedFixBug` | fix vs `BoundedRatio` | fails (residual) | tags `<<>>`: `820102` accepted |
| `PlutusConstrFieldsMainBug` | main | fails | 121 with a uint: `d87901` |
| `PlutusConstrFields` | fix | passes (42 states) | |
| `ValueSetMembersMainBug` | main | fails | a set of one array-keyed map: `d9010281a1820102f5` |
| `ValueSetMembers` | fix sharing the tree budget | passes | |
| `ValueSetMembersMergedFreshBug` | fix merged with main, fresh budget per set | fails (`TreeBudgetHolds`) | two 10-member sets under a 16-element tree limit |
| `ValueSetMembersOtherTagFixBug` | fix, unknown-tag member | fails (residual) | `d9010281d903e8a1820102f5` |
| `MultiAssetQuantityMainBug` | main, value five | fails | output asset bignum 5 at pv 8: `c24105` |
| `MultiAssetQuantityMainAnyBug` | main, every value | fails | output asset bignum 0 at pv 8 |
| `MultiAssetQuantity` | fix, asset quantities and bare coin | passes (135 states) | |
| `MultiAssetQuantityCoinInPairFixBug` | fix, coin of a `[coin, multiasset]` pair | fails (residual) | `82c24105<multiasset>` |
| `ConstructorEncodingMainBug` | main | fails | nil fields: `d879f6`, plutus `d87980` |
| `ConstructorEncodingMainSliceBug` | main, `[]any{1}` | fails | `d8798101`, plutus `d8799f01ff` |
| `ConstructorEncoding` | fix [G6], every container and item kind | passes | |
| `ConstructorEncodingGoArrayFixBug` | fix, Go array | fails (residual) | `d879820102` |
| `ConstructorEncodingNestedSliceFixBug` | fix, nested `[]any` | fails (residual, known) | `d8799f8101ff` |
| `ConstructorEncodingLongBytesFixBug` | fix, 65-byte field | fails (residual) | definite `5841...` |
| `ConstructorEncodingEmptyIndefFixBug` | fix, empty `IndefLengthList` | fails (residual) | `d8799fff` |
| `ConstructorEncodingNamedBytesMapFixBug` | [G4], 65-byte `PlutusV1Script` | fails | definite `5841...` |
| `ConstructorEncodingBigIntValueMapFixBug` | [G4], `big.Int` value, 65-byte magnitude | fails | `c25841...` |
| `ConstructorEncodingScalarFieldsMergedBug` | [G4] merged with main, fields `5` | fails | `d87905`, which `ConstructorDecoder` refuses |

Every counterexample above was also checked in Go against the named
commit and its parent.

## What the models found

The five fixes each pass under the rule they cite. Siblings that still
differ from the reference:

1. **L25: an untagged rational.** Every gOuroboros `cbor.Rat` ledger field
   is a `BoundedRatio` in the reference (`UnitInterval`,
   `NonNegativeInterval`: a0, rho, tau, d, execution prices, pool margin,
   committee quorum, voting thresholds), and those decode with
   `assertTag 30` at every protocol version: the tag is required. The fix
   follows `decodeRational` (DecCBOR `Rational`), where the tag is optional
   from version 9 and refused before it, and still accepts `820102`
   (`CborRationalBoundedFixBug`; `TestRatAcceptsOnlyOneTag30` asserts the
   acceptance).
2. **L28: a bignum coin in a Mary value pair.** `MaryTransactionOutputValue`
   reads the pair's coin into a `uint64` through the library, which accepts
   `c24105` as 5; `decodeMaryValue` reads it with `decodeWord64` and refuses
   it (`MultiAssetQuantityCoinInPairFixBug`). Any other `uint64` field the
   library fills is in the same class (`cbor.Decode(c24105, &uint64)` gives
   5).
3. **L31: other field and item shapes.** A Go array of fields is written
   definite, an empty `IndefLengthList` as `9fff`, and a byte string longer
   than 64 bytes as one definite string; plutus writes an indefinite list,
   `80`, and 64-byte chunks. Nested `[]any` lists stay definite, as DRIFT
   L31 already records.
4. **L27: an unrecognised tag around a composite-key map** is still
   refused, inside a set or alone. No Cardano structure carries one.

`MultiAssetQuantity` now also varies the encoding over a non-minimal tag
head (`d8 02`, `d8 03`) and a bignum behind a duplicate asset name. At
15156a03 the quantity check ran only when a literal `c2` or `c3` byte
occurred and read quantities through a Go map, so both forms passed
(`MultiAssetQuantityFixPairTagFormsBug`). The fix reads every quantity pair
by pair from the wire (`MultiAssetQuantityWalk`, `GoRule = "fixWalk"`).
