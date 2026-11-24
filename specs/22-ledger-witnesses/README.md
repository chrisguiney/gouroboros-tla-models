# Model 22: the UTXOW witness rules

Before the UTXO rule looks at value and fees, the UTXOW rule checks that a
transaction is authorized: every key that must sign has a witness, every
script that must run is supplied and passes, every Plutus script has its
redeemer, every datum a script needs is there and no datum is there that
nothing needs, and the declared script integrity hash covers the right
redeemers, datums and cost models.

`Witnesses.tla` models which witness, script, redeemer and datum each
transaction needs, and whether it supplies it, in every era from Shelley to
Dijkstra. It does no cryptography: a key is a name, a signature is either
supplied or not, and a hash is the set of things it covers.

## What gOuroboros does

Each era's rule list (`UtxoValidationRuleDescriptors` in
`ledger/<era>/rules.go`) runs the witness checks as separate rules. Read
from each function body at `756a9a89`:

| Check | Shelley-Mary | Alonzo, Babbage | Conway | Dijkstra |
|---|---|---|---|---|
| Required key witnesses | `common.ValidateRequiredVKeyWitnesses` (via Shelley's wrapper) | same, direct | same | per transaction level, with the pool-owner exemption |
| Input witnesses, signatures | `common.UtxoValidateSignatures` | same | same | per level |
| Collateral witnesses | - | `common.ValidateCollateralVKeyWitnesses` | same | Conway's |
| MIR quorum | `common.ValidateMIRGenesisQuorum` | same | - | - |
| Update-proposal delegates | `common.ValidateClassicProtocolParameterUpdates` | same | - | - |
| Native scripts | witness-set scripts (`FirstInvalidNativeScript`) | Alonzo: Mary's; Babbage: needed scripts incl. reference (`script.NativeScriptsToEvaluate`) | Babbage's | own levels |
| Needed vs supplied scripts | `common.ValidateScriptWitnesses` | same | same | own, across levels |
| Redeemers | - | `ValidateScriptWitnesses`, `ValidateExactExtraneousRedeemers`, `ValidateRedeemerAndScriptWitnesses`; Babbage adds `script.ValidateRequiredRedeemers` | same | own |
| Datums | - | `ValidateRequiredSpendingDatums`, `ValidateSupplementalDatums`; Babbage adds the PlutusV1 restrictions | same | own |
| Integrity hash | - | own `UtxoValidateScriptDataHash`, needed languages only | own | own (preserved CBOR) |

## What the model contains

Three keys: `v1` and `v2` are vkeys; `b` is a bootstrap key, whose hash is
the address root a bootstrap witness supplies. The state is the environment
of a cell: which keys have a witness, and the validity interval's bounds
(absent, or 0 to 3). `TableSpec` reaches every environment (8 in Shelley,
which has no lower bound and whose TTL never reaches the multisig
evaluator, and 200 in the other eras), and in each one checks five families:

1. **Key witnesses.** A source needs one key (`v1` or `b`): a spent input
   (a Byron address for `b`), collateral, a withdrawal, a stake delegation,
   a pool registration's operator, a pool owner (operator `v2`), a pool
   retirement, a required signer, a DRep voter, a genesis key delegation,
   a MIR certificate whose one genesis delegate is the key (quorum 1), an
   update proposal from a genesis key delegated to the key; or a tag-0
   registration, which needs nothing. An extra `v2` witness may carry a
   bad signature. In Dijkstra the transaction may be phase-2 invalid,
   which excuses the pool owners.
2. **Native scripts.** "all", "any" and "at least m (0-3)" over zero, one
   or two leaves; a leaf is a signature by any key, or (from Allegra) a
   start or expiry slot 0-2.
3. **Scripts and redeemers.** A purpose (spend, withdraw, certify, mint
   from Mary, vote from Conway) needs a native or (from Alonzo) Plutus
   script, supplied in the witness set, by a reference input (from
   Babbage), both or neither; an unneeded script may be supplied in the
   witness set or by reference; the redeemer is absent, at the purpose, or
   at the key-locked input.
4. **Datums** (Alonzo on). A spent input locked by a Plutus script of a
   version the era has, or by a native script, with no datum, a datum hash
   or (from Babbage) an inline datum; the witness datums are any subset of
   the input's, an output's, a reference input's (from Babbage) and a stray
   one.
5. **Integrity hash** (Alonzo on). A PlutusV1 spending script may run, a
   supplemental datum may be carried, and (from Babbage) a reference input
   may hold an unneeded PlutusV2 script; the declared hash is absent or
   covers any language set.

## The questions

1. **`GoAgrees`**: in each era and environment, does gOuroboros accept
   exactly the transactions the reference accepts, in all five families?
2. **`KeysAuthorized`**: does every accepted input, withdrawal, delegation
   and retirement carry its key's witness?
3. **`TimelockSound`**: is an accepted start leaf inside a present lower
   bound?
4. **`ScriptsExact`**: is every accepted transaction's script supplied
   exactly once?
5. **`DatumsJustified`**: does no accepted transaction carry a stray datum?
6. **`IntegrityMatches`**: does every accepted declared hash cover exactly
   the needed languages?

## The answers

| Config | Result | Distinct states |
|---|---|---|
| `WitnessesTableShelley` | all hold | 8 |
| `WitnessesTableAllegra` .. `WitnessesTableDijkstra` | all hold | 200 each |

`GoAgrees` holds with gOuroboros' genesis-quorum fix in place (see the
finding). The whole directory checks in under 20 seconds.

**Finding, fixed on gOuroboros branch
`fix/ledger-witnesses-genesis-bootstrap`.** The reference counts the
address root of a bootstrap witness among the witness key hashes
(`keyHashWitnessesTxWits`, `Core.hs` 545-552), and takes both the MIR
genesis quorum (`validateMIRInsufficientGenesisSigs`, `Shelley/Rules/Utxow.hs`
460-490; Babbage 294-317) and the update-proposal delegates
(`witsVKeyNeededGenDelegs`, `Shelley/UTxO.hs` 191-204, checked by
`validateNeededWitnesses`) over that set. A genesis delegate hash is
whatever a genesis key delegation certificate names, so it can be a
bootstrap root. gOuroboros' `ValidateMIRGenesisQuorum` and
`ValidateClassicProtocolParameterUpdates` counted only vkey witnesses, so
from Shelley to Babbage they rejected a MIR certificate or update proposal
the reference accepts. `WitnessesGoGenesisVkeyOnly{Shelley,Babbage}Bug`
put the old code back and fail `GoAgrees`. Reaching it needs a genesis key
holder to delegate to a bootstrap root, so no chain is known to contain
one.

## Checking the checks

| Config | Mutation | Fails |
|---|---|---|
| `WitnessesGoGenesisVkeyOnlyShelleyBug`, `...BabbageBug` | the code before the fix | `GoAgrees` |
| `WitnessesGoOwnersAlwaysBug` | Dijkstra owners must always witness | `GoAgrees` |
| `WitnessesGoNativeCountsBootstrapBug` | a bootstrap witness satisfies a native signature | `GoAgrees` |
| `WitnessesGoStartAbsentOkBug` | an absent lower bound satisfies a start leaf | `GoAgrees` |
| `WitnessesGoExpireExclusiveBug` | an expiry needs the upper bound strictly before it | `GoAgrees` |
| `WitnessesGoRefAndWitOkBug` | a script supplied both ways is allowed | `GoAgrees` |
| `WitnessesGoExtraWitOkBug` | an unneeded witness-set script is allowed | `GoAgrees` |
| `WitnessesGoV2NoDatumOkBug` | a PlutusV2 input needs no datum | `GoAgrees` |
| `WitnessesGoRefNotSupplementalBug` | a reference input's datum does not justify a witness datum | `GoAgrees` |
| `WitnessesGoLangsAllProvidedBug` | the views cover unneeded reference scripts too | `GoAgrees` |
| `WitnessesSpecIgnoreWdrlBug` | a withdrawal needs no witness | `KeysAuthorized` |
| `WitnessesSpecStartAbsentOkBug` | an absent lower bound satisfies a start leaf | `TimelockSound` |
| `WitnessesSpecRefAndWitOkBug` | a script may be supplied twice | `ScriptsExact` |
| `WitnessesSpecAnyDatumOkBug` | any witness datum is allowed | `DatumsJustified` |
| `WitnessesSpecIgnoreLangsBug` | the hash covers no language views | `IntegrityMatches` |

Reachability probes, each failing as required: a bootstrap witness
authorizes something (Mary); Dijkstra excuses a pool owner; a signature and
expiry script is accepted (Allegra); a script supplied only by reference is
accepted (Babbage); an input with an inline datum is spent (Conway).

## Go tests and mutations (gOuroboros)

Branch `test/ledger-witnesses-model`, `ledger/witness_rule_model_test.go`.
Each family builds real transactions of every era it applies to (the era's
own body, witness-set and redeemer types), runs only the era's witness
rules, selected by id from its own rule list and in its order, and checks
acceptance against the model's rule restated in Go. Signatures are real
ed25519 signatures over the body hash, except the one a cell marks bad.
Plutus scripts are never run.

| Test | Eras | Cells |
|---|---|---|
| `TestWitnessRuleModelKeys` | all seven | 1,968 |
| `TestWitnessRuleModelNative` | all seven | 115,400 |
| `TestWitnessRuleModelScripts` | all seven | 1,144 |
| `TestWitnessRuleModelDatums` | Alonzo to Dijkstra | 560 |
| `TestWitnessRuleModelIntegrity` | Alonzo to Conway | 80 |

On `main` the key family records the genesis-quorum difference
(`wmGenesisVkeyOnly`); with the fix the constant is false and every cell
passes. The Go test's bounds are lower 0-2 and upper 1-3 with start leaves
at 0 and 1 and an expiry at 2, a subset of the model's.

Mutations of gOuroboros, each killed (first failing cell):

| Mutation | First failing cell |
|---|---|
| `witnessKeyHashes` drops bootstrap roots | Shelley, Byron input witnessed by `b`, refused |
| vkey signature failures ignored | Shelley, extra badly signed witness accepted |
| tag-0 registration needs a witness | Shelley, `reg0` with no witnesses refused |
| pool owners not required | Shelley, owner unwitnessed, accepted |
| voters not required | Conway, unwitnessed voter accepted |
| expiry exclusive | Allegra, `expire 2` with upper bound 2 refused |
| absent start satisfies | Allegra, `start 0` with no lower bound accepted |
| at-least strict | Shelley, `atleast(0)[]` refused |
| Babbage native env counts bootstrap | Babbage, `sig b` with `b` witnessed accepted |
| script supplied both ways allowed | Babbage, native script in witness set and by reference accepted |
| unneeded witness script allowed | Babbage, extra witness-set script accepted |
| PlutusV2 needs no datum | Babbage, V2 input without datum accepted |
| reference inputs do not justify datums | Babbage, reference input's datum refused |
| datum-only transaction needs no hash (Babbage) | Babbage, undeclared hash with a datum accepted |

One mutation survives by design: dropping the native-purpose redeemer check
in `ValidateScriptWitnesses` alone, or together with
`ValidateExactExtraneousRedeemers`, leaves `ValidateRedeemerAndScriptWitnesses`
rejecting the redeemer (no Plutus script is reachable), so the cell stays
refused.

## Specification, reference and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
|---|---|---|---|---|
| Needed key witnesses | `witsVKeyNeeded ⊆ witsKeyHashes` | inputs, collateral, withdrawals, certificate authors, pool owners, genesis delegates of updates; Alonzo adds required signers, Conway voters and drops the genesis delegates | same sources | agree |
| Witness key hashes | vkey hashes | vkey hashes and bootstrap roots | same, except MIR and updates | fixed branch agrees |
| MIR quorum | `|genSig| ≥ Quorum` | over vkey hashes and bootstrap roots | vkey hashes only; fixed branch: both | agree after the fix |
| Superfluous witnesses | allowed, signature checked | `validateVerifiedWits` checks every one | every signature checked | agree |
| Native signatures | `vk ∈ dom(txwitsVKey)` | vkey witnesses only | vkey witnesses only | agree |
| Timelock bounds | start ≤ lower, upper ≤ expiry, absent fails | `lteNegInfty`, `ltePosInfty` | presence tracked per bound | agree |
| Which native scripts run | Shelley/Alonzo: all supplied; Babbage: needed | same | same (extra ones are rejected as extraneous first) | agree |
| Missing/extra scripts | `needed - refs = wits` | `babbageMissingScripts` | a reference script makes the witness one extraneous | agree |
| Redeemers | exactly the needed Plutus purposes | `hasExactSetOfRedeemers` | three rules together | agree |
| Required datums | datum hash of a Plutus spend; V1/V2 need one | `getInputDataHashesTxBody` | same, V3 exempt | agree |
| Supplemental datums | outputs; Babbage adds reference inputs and the return | same | same | agree |
| Integrity languages | `languages tx utxo` | needed Plutus scripts | needed purposes only | agree |
| Dijkstra pool owners | - | excused when phase-2 invalid or only the BLS key changes | same | agree (phase-2 case tested in Go) |

## Sources

All IntersectMBO/cardano-ledger commit
`1210d37fe6bdef32e85179ae08b7e1e8cfd75273`.

| Tag | File | Lines | What |
|---|---|---|---|
| R1 | `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Utxow.hs` | 281-338, 377-436, 460-490 | UTXOW, scripts, signatures, needed witnesses, MIR |
| R2 | `eras/shelley/impl/src/Cardano/Ledger/Shelley/UTxO.hs` | 191-277 | witsVKeyNeeded |
| R3 | `libs/cardano-ledger-core/src/Cardano/Ledger/Core.hs` | 545-552 | witness key hashes |
| R4 | `eras/shelley/impl/src/Cardano/Ledger/Shelley/Scripts.hs` | 307-334 | multisig |
| R5 | `eras/allegra/impl/src/Cardano/Ledger/Allegra/Scripts.hs`, `Allegra/Tx.hs` | 492-521; 111-116 | timelock |
| R6 | `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs` | 222-385 | datums, redeemers, integrity |
| R7 | `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/UTxO.hs` | 246-311, 444-459 | datum hashes, required signers |
| R8 | `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Tx.hs`, `Alonzo.hs` | 463-482; 168-169 | mkScriptIntegrity, languages used |
| R9 | `eras/babbage/impl/src/Cardano/Ledger/Babbage/Rules/Utxow.hs` | 206-245, 294-401 | Babbage and Conway UTXOW |
| R10 | `eras/babbage/impl/src/Cardano/Ledger/Babbage/UTxO.hs`, `Babbage/TxInfo.hs` | 92-173; 256-262 | supplemental datums, reference scripts, V1 context |
| R11 | `eras/conway/impl/src/Cardano/Ledger/Conway/UTxO.hs` | 189-221 | Conway needed witnesses |
| R12 | `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Utxow.hs`, `Dijkstra/UTxO.hs` | 510-525; 171-196 | Dijkstra pool owners |

gOuroboros commit `756a9a89`: see `[G1]`-`[G8]` in `Witnesses.tla`.

## Not modelled

Signature and hash arithmetic; Dijkstra sub-transactions, guards and the
cross-level script and datum checks (Dijkstra's top level is modelled; its
BLS-only re-registration exemption is modelled but not tested in Go,
because the mock ledger has no pending pool parameters); the Dijkstra
integrity hash (its rule hashes only preserved CBOR, so the Go test cannot
build it in memory); governance proposal policy scripts (model 15);
Plutus evaluation, well-formedness and cost-model contents; metadata
hashes; more than one needed key or script per cell.

## Running it

```sh
scripts/run-model.sh specs/22-ledger-witnesses   # every config, Bug configs expected to fail
make ledger-witnesses
```
