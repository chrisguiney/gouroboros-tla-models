# Transaction body id

A table model of what gOuroboros hashes for a transaction body's id,
written bug-first for #3141 (DRIFT L2). The spec says the id is the
Blake2b-256 hash of the body's CBOR serialization; a reference body always
carries its bytes. A gOuroboros body built in code carries none, so the id
depends on what gOuroboros hashes in its place.

The model (`TxBodyId.tla`) picks one abstract body: a fee (5 or 6 stand
for two different bodies), whether it carries the bytes it was decoded
from, whether it is a Dijkstra body with an empty CIP-159 map (keys 24 to
27), and whether it can be encoded. The hash is collision-free: an id is a
record of what was hashed.

## Sources

| Tag | Source |
| --- | --- |
| S1 | cardano-ledger [`1210d37fe6bd`](https://github.com/IntersectMBO/cardano-ledger/tree/1210d37fe6bd) `eras/shelley/formal-spec/crypto-details.tex` 64-69 |
| R1 | same revision, `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/TxBody.hs` 518-552 (`encodeTxBodyRaw`, `Omit` on an empty map at 24-27), 449-452 (the decoder refuses one) |
| G1 | gOuroboros `d0b95845` `ledger/common/tx.go` 719-721 (`Id` hashes `Cbor()`) |
| G3 | gOuroboros `bcd8a77b` (#3141) `ledger/common/tx.go` 734-746 (`TransactionBodyId`), `ledger/dijkstra/dijkstra.go` |

## Invariants

| Invariant | Says |
| --- | --- |
| `IdAsBlake2bOfBodyEncoding` | for every body the reference can represent, the id is the hash of its serialization |
| `UnencodableGetsZeroId` | a body that cannot be encoded gets the zero id, never a hash that looks real |

## Configs

| Config | Rule | Result | Counterexample, and the Go test it matches |
| --- | --- | --- | --- |
| `TxBodyIdMainBug` | main before #3141 | fails `IdAsBlake2bOfBodyEncoding` | a built body with fee 5 gets the empty-input hash (`TestTransactionBodyIdHashesBodyEncoding`: fees 5 and 6 collide) |
| `TxBodyIdDraftBug` | #3141's first draft (review follow-up) | fails `IdAsBlake2bOfBodyEncoding` | a built Dijkstra body with an empty CIP-159 map fails to encode and falls back to the empty-input hash (`TestDijkstraBodyIdOmitsEmptyMaps`) |
| `TxBodyId` | #3141 (`bcd8a77b`) | passes both | |

## Running it

```sh
scripts/run-model.sh specs/ledger-txid
```
