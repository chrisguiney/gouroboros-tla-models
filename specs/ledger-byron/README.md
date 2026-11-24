# 19: the Byron ledger — UTxO and heavyweight delegation

gOuroboros validates Byron ledger content in two places:

- `ledger/byron/byron.go` `ByronTransaction.ValidateAgainstUtxo`, which
  `ledger/verify_block.go` calls for each transaction of a Byron main block
  and then folds into the block's `BlockLedgerState`;
- `consensus/byron/pbft_delegation.go` `PBFTDelegationState`, the
  heavyweight-delegation map that PBFT header validation reads.

The block envelope and the PBFT signature window are in
[consensus](../consensus/README.md) and are not repeated here.

gOuroboros keeps no ledger state. For the UTxO rule the caller supplies a
UTxO view and a fee policy. For delegation the caller must call
`ApplyPayloadCbor` once per main block, in slot order, with that block's
epoch and slot, and keep the returned value only if the block is adopted.
Both models make those contracts their steps.

Sources are pinned to cardano-ledger `1210d37fe6bd`
(`eras/byron/ledger/formal-spec`, `eras/byron/ledger/impl`) and gOuroboros
`d0b95845`. Each `.tla` lists them with file and line.

## Slice 1: the UTxO rule (`ByronUtxo.tla`)

The model runs a chain on gOuroboros' verdicts from a UTxO holding one
pay-to-key and one redeem output. In every state it asks the specification,
the reference and gOuroboros about every candidate transaction: inputs any
list of up to two references (including a missing one and a repeat),
outputs any list of up to two values in 0..2, and 0 to 2 witnesses.

| Rule | Specification [S1-S3] | Reference [R1-R5] | gOuroboros [G1-G2] |
| --- | --- | --- | --- |
| Inputs non-empty | required | `NonEmpty` decoder | **not checked** (fixed on branch) |
| Outputs non-empty | required | `NonEmpty` decoder | **not checked** (fixed on branch) |
| Inputs exist | `txins ⊆ dom utxo` | `validateTxIn` | `ResolveInputUtxo` |
| Repeated input | impossible (a set) | allowed, counted once | rejected |
| Output value | `0 < c` | 0 allowed | 0 allowed |
| Fee | `a + b·size ≤ fee` | `round(a) + ⌈b·size⌉` over the TxAux bytes | `⌈(a + b·size)/1e9⌉` over the TxAux bytes |
| Redeem-only spend | no exemption in the spec | min fee 0 (`isRedeemUTxO`) | exempt (all witnesses redeem) |
| maxTxSize | `txSize ≤ maxTxSize` | `TxValidationTxTooLarge` | **not checked** |
| Witnesses | one per input | `zip`: unpaired inputs or witnesses unchecked | count must equal input count |

Invariants:

- `ValuePreserved`: UTxO plus fees is always the starting value, fees never
  negative.
- `GoSound`: gOuroboros accepts nothing the reference rejects.
- `GoComplete`: gOuroboros accepts everything the reference accepts, apart
  from its two deliberate tightenings (repeated input, witness count).
- `RefMatchesSpec`: the reference departs from the specification only by
  zero-valued outputs and short witness lists.

| Config | States | Result |
| --- | --- | --- |
| `ByronUtxo.cfg` (2 transactions, non-empty fix, size checked) | 106 | passes |
| `ByronUtxoDeep.cfg` (3 transactions) | 175 | passes |
| `ByronUtxoEmptyTxBug.cfg` | gOuroboros main: no inputs is vacuously redeem-only, so a no-input zero-output transaction is free | `GoSound` |
| `ByronUtxoNoSizeLimitBug.cfg` | gOuroboros main: no maxTxSize check | `GoSound` |
| `ByronUtxoFeeRoundingBug.cfg` | a summand of half a lovelace | `GoComplete` |
| `ByronUtxoNoBalanceBug.cfg` | mutation: outputs may exceed inputs | `ValuePreserved` |
| `ByronUtxoKeepInputsBug.cfg` | mutation: spent inputs stay | `ValuePreserved` |
| `ByronUtxoRedeemAnyBug.cfg` | mutation: no minimum fee | `GoSound` |
| `ByronUtxoRefNoMinFeeBug.cfg` | mutation on the reference side | `RefMatchesSpec` |

Probes (expected violated): `ProbeChained` (a transaction spends an output
made by an earlier one), `ProbeRedeemExempt`, `ProbeDupDeviation`,
`ProbeUnderwitnessed`, `ProbeZeroOutput`.

### Findings

1. **Empty transactions (defect, fixed).** The reference cannot decode a
   transaction with no inputs or no outputs. gOuroboros accepted both, and a
   transaction with no inputs and zero-valued outputs pays no fee, because
   "every input is a redeem input" is true of no inputs. Branch
   `fix/ledger-byron-nonempty-tx` rejects both in `ValidateAgainstUtxo`.
2. **No maxTxSize check (open).** `ValidateAgainstUtxo` takes no size limit
   and `VerifyConfig` has no Byron one, so an oversized transaction passes.
   Adding it changes the API.
3. **Fee rounding (latent).** The reference rounds the summand to lovelace
   before adding the rounded-up per-byte part; gOuroboros rounds the sum.
   They differ only for a summand that is not a whole lovelace, which no
   network has. gOuroboros is then the stricter.
4. **Repeated inputs and witness counts (deliberate).** The reference
   accepts a repeated input (counted once) and zips witnesses with inputs,
   so a short witness list leaves inputs unchecked. gOuroboros rejects both,
   following the specification.

## Slice 2: heavyweight delegation (`ByronDelegation.tla`)

Two copies of the delegation state, the reference's (`Interface.hs`,
`Scheduling.hs`, `Activation.hs`) and gOuroboros', run over the same chain.
Each block is one or two slots after the last and carries up to two
certificates from any of the genesis keys g1 and g2 or the outsider d1, to
any key, for any epoch up to two ahead. g1 starts delegated to d1.

| Rule | Specification [S1-S2] | Reference [R1-R4] | gOuroboros [G1-G4] |
| --- | --- | --- | --- |
| Delegator | genesis key | genesis key | genesis key |
| Epoch | current or next | current or next | current or next |
| Once per epoch | `(e, vk) ∉ eks` | `keyEpochDelegations` | `keyEpochDelegations` |
| Once per slot | `(s+2k, vk) ∉ sds` | same | same |
| Activation | after 2k slots | same | same |
| Delegate free | `vk_d ∉ range dms` | `notMemberR` (self included) | main: free of *other* delegators; PR 3174: self included |
| Earlier slot | `s_p < s` | `s_p < s` or `s = 0` | same as reference |
| Pruning | — | schedules `≥ s+1`, key-epochs `≥ e` | same |

Invariants: `VerdictsAgree`, `MapsAgree`, `SlotsAgree`, `GoInjective`,
`GoPruned`, `OncePerEpoch`, `GoDelayed`.

| Config | States | Result |
| --- | --- | --- |
| `ByronDelegation.cfg` (to slot 4) | 21,587 | passes |
| `ByronDelegationDeep.cfg` (to slot 5) | 49,448 | passes |
| `ByronDelegationOwnEntryBug.cfg` | main: own entry exempt | `SlotsAgree` |
| `ByronDelegationWideEpochBug.cfg` | epoch + 2 accepted | `VerdictsAgree` |
| `ByronDelegationNoDelayBug.cfg` | activates in its own block | `MapsAgree` |
| `ByronDelegationNoInjectivityBug.cfg` | delegate collision ignored | `GoInjective` |
| `ByronDelegationNoPruneBug.cfg` | tick keeps old entries | `GoPruned` |
| `ByronDelegationNoKeyEpochBug.cfg` | key-epoch not recorded | `OncePerEpoch` |
| `ByronDelegationLongDelayBug.cfg` | activation at 2k + 1 | `GoDelayed` |

Probes: `ProbeRevoke`, `ProbeMove`, `ProbeRejected`.

Activation slots (PR 3174 head `faad03cd`). On main, `activate` checked
only that no *other* delegator held the delegate, so a re-delegation to the
delegate already active rewrote the activation slot where the reference
does nothing. The maps agreed in every state and the slot is read only by
the earlier-slot check, which a later schedule always passes, so the
difference was harmless; but the model only probed for it
(`ProbeSlotsDiffer`), and the Go table test required it to happen, which
would have failed the suite on a fix. Review follow-up: `activate` now
follows `Activation.hs` (`delegateIsActive`, own entry included), the model's
gOuroboros side does the same, `SlotsAgree` checks it, and
`ByronDelegationOwnEntryBug.cfg` reproduces main (`Mutation =
"OwnEntryExempt"`). The state counts fell because the two sides' slots no
longer diverge.

A second review follow-up changes only the Go test, not the model:
`TestPBFTDelegationModelTable` compared the activation slots by looking up
the genesis keys, so a missing entry read as slot 0 and an extra entry went
unseen. It now compares the whole map, as `SlotsAgree` (`gDws = rDws`)
always did; a code mutation dropping a genesis zero-slot entry fails the new
check and passed the old one.

The earlier-slot check itself is unreachable while slots increase: two
schedules of one delegator always have increasing activation slots. The Go
model test confirms it (a mutation removing it survives).

## The update mechanism

gOuroboros checks update proposals and votes only statelessly
(`ledger/byron/payload.go` `ValidateUpdatePayload`,
`ValidateUpdatePayloadStructure`): signatures, wire shape, at most one
proposal per block, parameter ranges. Registration (the proposer is a
genesis delegate, the version follows the adopted one), vote tallying,
confirmation, endorsement and adoption are left to the caller and are not
modelled here.

## Go tests

Branch `test/ledger-byron-model`:

- `ledger/byron_utxo_model_test.go` `TestByronUtxoModelTable`: every
  non-empty cell of the starting state (inputs over pay-to-key, redeem and
  missing; outputs over four values; witnesses one short, exact, one over)
  against a transcription of `RefAccepts`; `TestByronUtxoModelChained` for
  the block fold. Mutations removing the duplicate, redeem, fee, size,
  witness-count and balance checks are each caught.
- `consensus/byron/pbft_delegation_model_test.go`
  `TestPBFTDelegationModelTable`: a breadth-first walk of the
  `ByronDelegation.cfg` chains (2,779 states, about 48,000 blocks) comparing
  verdicts, maps, schedules and key-epochs with a transcription of the
  reference. Mutations of the epoch window, key-epoch, same-slot, genesis,
  injectivity, 2k delay and both prunes are each caught. Since PR 3174 head
  `faad03cd` it also compares activation slots (`require.Equal`), which
  fails on main's `activate`.
