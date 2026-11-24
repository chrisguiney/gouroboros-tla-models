# protocol parameter updates (PPUP) and move instantaneous rewards (MIR)

From Shelley to Babbage, two things only the genesis keys can do go through
ordinary transactions:

- **Propose protocol parameter changes** (PPUP). A transaction carries an
  update: for each proposing genesis key, the change it wants, and the epoch
  the proposal is for. At the epoch boundary a change that a quorum of
  genesis keys proposed with the same value is adopted.
- **Move instantaneous rewards** (MIR). A certificate pays stake credentials
  from the reserves or the treasury, or (from Alonzo) moves coin between the
  two pots. A quorum of genesis delegates must sign it. The ledger collects
  the payments during the epoch and pays them at the boundary.

Conway replaced both with governance (model `ledger-governance`): the update field and the
MIR certificate no longer exist.

Sources are pinned to cardano-ledger `1210d37fe6bd`, gOuroboros `756a9a89`
and Dingo `2fc7975d3`. Each `.tla` file lists them with file and line.

## How it fits with the other models

- **Model `ledger-shelley`** covers the certificate lifecycle (registration, delegation,
  pools, deposits). A MIR certificate is a DELEG certificate too, but it
  touches none of that state, only the pots and the pending rewards, so it
  is modelled here. Model `ledger-shelley`'s value-preservation question is answered for
  MIR by `ValuePreserved` in `Mir.tla`.
- **Model `ledger-witnesses`** covers key witnesses. PPUP needs the witness of each proposing
  key's delegate, and MIR needs a quorum of delegate witnesses. This model
  assumes PPUP's witnesses are present and models only the MIR quorum count,
  because the quorum is a separate rule from the ordinary witness check.
- **Model `ledger-utxo`** covers IsValid in general. This model checks the two PPUP and
  MIR rules whose phase-2 gating was wrong.
- **Model `ledger-governance`** covers Conway governance, which replaced both mechanisms.

## What each implementation does

| | Specification | Reference (cardano-ledger) | gOuroboros | Dingo |
|---|---|---|---|---|
| Who may propose | `dom pup ⊆ dom genDelegs` (update.tex) | `NonGenesisUpdatePPUP` (Ppup.hs 163) | `ProtocolParameterUpdateDelegateError` | stores the rows gOuroboros accepted |
| Target epoch | this epoch before `firstSlot(e+1) - 2·SW`, else the next | the same, with `getTheSlotOfNoReturn` (Slot.hs 106) | the same; the slot of no return comes from the caller | `ProtocolParameterUpdateWindow` computes `2·ceil(3k/f)` |
| Empty proposal map | the epoch is still checked (only `up = Nothing` skips) | the same | **skips every check** (`len(updates) == 0`) | n/a |
| Version can follow | `pvCanFollow` | the same (PParams.hs 338) | `protocolVersionCanFollow` | `classicProtocolVersionCanFollow` |
| IsValid false (Alonzo, Babbage) | n/a (Alonzo spec) | PPUP runs only on the valid branch of UTXOS | **PPUP runs anyway** | rows only for valid txs |
| Combining proposals | right override per key | `Map.union pup pupS` | n/a (no state) | latest row per key and target epoch |
| Adoption | exactly one value with ≥ Quorum votes | `votedFuturePParams` | n/a | `selectClassicPParamUpdate` |
| Future proposals at the boundary | become current if all versions can follow the new parameters | `updatePpup` (Newpp.hs 97) | n/a | checked against the submission epoch's parameters at the next boundary: the same result |
| MIR deadline | `firstSlot(e+1) - SW` | `checkSlotNotTooLate` | `validateMirNotTooLate` | `mirCertificateCutoff` |
| MIR before Alonzo | delta replaces, no negatives, no transfers | the same | the same, from totals | the same at the boundary |
| MIR from Alonzo (major > 4) | not in the Shelley spec | deltas add, pending ≥ 0, transfers bounded by `availableAfterMIR` | the same, from totals | the same at the boundary |
| MIR pot bound | Σ credits ≤ pot | the same (+ pending transfers from Alonzo) | the same | pays nothing if a pot cannot cover |
| MIR quorum | `|genSig| ≥ Quorum ∧ d > 0` | `|genSig| ≥ Quorum` in UTXOW, every tx | **skipped for IsValid false** | n/a |
| Conway | no MIR | no MIR cert in `ConwayTxCert` | rejected at block decode | n/a |

Where the specification and the reference differ (the `d > 0` condition in
the MIR quorum), the model follows the reference.

## Part 1: PPUP (`Ppup.tla`)

### What the model contains

Three genesis keys `g1`-`g3` and one outsider `x`, quorum 2, epochs of three
slots whose last slot is past the slot of no return, three epochs. The
updates are `a` (no version), `a21` (version 2.1), `a3` (3.0) and `a4` (4.0),
starting from 2.0. One transaction per slot names at most two keys, any
update, this epoch or the next, and from Alonzo IsValid true or false.

Three halves decide each transaction or boundary: the ledger (`RefOk`,
`Tick`), gOuroboros (`GoOk`, with the constants `GoEmptyFixed` and
`GoPhase2Fixed`), and Dingo's boundary selection (`DingoVotes`), which works
from rows keyed by target epoch rather than from current and future maps.

### The questions

1. `ProposersAreGenesis`: only genesis keys ever have a proposal recorded.
2. `AdoptedHadQuorum`: every adoption had at least Quorum votes.
3. `VersionFollows`: the protocol version only moves to one that can follow.
4. `CurFrozenAfterNoReturn`: nothing joins the current proposals after the
   slot of no return, so the adopted change is fixed 2·SW before the boundary.
5. `GoAgrees`: gOuroboros accepts exactly what the ledger accepts.
6. `DingoAgrees`: Dingo adopts exactly what the ledger adopts.

### The answers

| Config | Result | Distinct states |
|---|---|---|
| `Ppup.cfg` (Shelley to Mary, fixed) | all hold | 373,476 |
| `PpupAlonzo.cfg` (Alonzo, Babbage, fixed) | all hold | 373,476 |
| `PpupAlonzoDeep.cfg` (two late slots per epoch) | all hold | 4,501,475 |
| `PpupEmptyMapBug.cfg` (gOuroboros today) | **`GoAgrees` fails** | 146 |
| `PpupPhase2InvalidBug.cfg` (gOuroboros today) | **`GoAgrees` fails** | 8 |
| `PpupQuorumOneBug.cfg` | `AdoptedHadQuorum` fails | |
| `PpupNoCarryCheckBug.cfg` | `VersionFollows` fails | |
| `PpupAnyVersionBug.cfg` | `VersionFollows` fails | |
| `PpupLateIntoCurrentBug.cfg` | `CurFrozenAfterNoReturn` fails | |
| `PpupNoGenesisCheckBug.cfg` | `ProposersAreGenesis` fails | |
| `PpupDingoNoCarryCheckBug.cfg` | `DingoAgrees` fails | |
| `PpupProbe*Bug.cfg` | adoption, a dropped carry-over, an adopted carry-over and two successive version bumps are all reachable | |

Dingo agrees with the ledger in every reachable state: checking the carried
proposals at the boundary that ends their epoch, against that epoch's
parameters, gives the same answer as the ledger's check at the boundary that
starts it.

**Defect 1 (`PpupEmptyMapBug`).** An update with an empty proposal map and
the wrong target epoch. The ledger runs PP-Update-Current or -Future, both of
which check the epoch, and rejects the transaction (`PPUpdateWrongEpoch`).
gOuroboros returns early on `len(updates) == 0` and accepts it.

**Defect 2 (`PpupPhase2InvalidBug`).** An Alonzo or Babbage transaction with
IsValid false whose update targets the wrong epoch. The reference runs PPUP
only in `alonzoEvalScriptsTxValid` and `babbageEvalScriptsTxValid`, so it
accepts the transaction (collateral is taken, the update is ignored).
gOuroboros runs the PPUP rule in its always-run group and rejects the block.
Only the UTXOW witness requirement (`witsVKeyNeededGenDelegs`) still applies.

## Part 2: MIR (`Mir.tla`)

### What the model contains

Two credentials, `c1` registered and `c2` not; reserves 3 and treasury 1;
deltas -1, 1 and 2; transfers of 1 or 2; one or two delegate signatures with
quorum 2; epochs of three slots whose last slot is past the deadline. One
transaction per slot carries one MIR certificate. The boundary pays
registered credentials if both pots cover them, and clears the pending state.
The constant `Era` is `Mary` (before the Alonzo hard fork), `Alonzo` or
`Conway`.

### The questions

1. `ValuePreserved`: reserves + treasury + reward balances never change, and
   pending transfers net to zero.
2. `PendingNonNegative`: no pending credit is negative.
3. `WithinBudget`: each pot always covers its pending credits, so the
   boundary's pay-nothing branch is unreachable.
4. `QuorumHeld`: every applied MIR had the quorum.
5. `BeforeCutoff`: no MIR was applied in the last StabilityWindow slots.
6. `NoMirInConway`: nothing moves in Conway.
7. `GoAgrees`: gOuroboros, working from totals and per-credential pending
   amounts, accepts exactly what the ledger accepts.

### The answers

| Config | Result | Distinct states |
|---|---|---|
| `Mir.cfg` (before Alonzo) | all hold | 524 |
| `MirAlonzo.cfg` (fixed) | all hold | 2,373 |
| `MirAlonzoDeep.cfg` (larger pots, three epochs) | all hold | 40,501 |
| `MirConway.cfg` | all hold | 12 |
| `MirQuorumPhase2InvalidBug.cfg` (gOuroboros today) | **`GoAgrees` fails** | 2 |
| `MirNoNegCheckBug.cfg` | `PendingNonNegative` fails | |
| `MirNoPotCheckBug.cfg` | `WithinBudget` fails | |
| `MirTransferIgnoresIRBug.cfg` | `WithinBudget` fails | |
| `MirLateBug.cfg` | `BeforeCutoff` fails | |
| `MirNoQuorumBug.cfg` | `QuorumHeld` fails | |
| `MirProbe*Bug.cfg` | a paid reward, a pending transfer, a dropped credit to an unregistered credential and a payout from the reserves are all reachable | |

gOuroboros's reformulation (accumulated totals, the replaced amount before
Alonzo, pot plus transfers) agrees with the ledger's map arithmetic in every
reachable state.

**Defect 3 (`MirQuorumPhase2InvalidBug`).** An Alonzo or Babbage transaction
with IsValid false carrying a MIR certificate signed by one delegate. The
reference checks the quorum in UTXOW (`validateMIRInsufficientGenesisSigs`),
which runs for every transaction, and rejects it. gOuroboros put the quorum
rule in the phase-2-valid-only group with DELEG and accepts it.

## The Go tests

`ledger/ppup_mir_model_test.go` (branch `test/ledger-ppup-mir-model`) runs
every transaction step of both models through each era's composed
`UtxoValidationRules`, so the phase-2 gating is part of what is tested:
896 PPUP cells (five eras, two parameter versions, four key sets, four
updates, in-window or late, this epoch or next, valid or not) and 2,048 MIR
cells (five eras, five pot states, sixteen certificates, one or two
signatures, valid or not, before or after the deadline). The expected
verdict is the model's `GoOk`; three constants mirror the configs' fix
flags. With them false the table passes on `main`; set true, 112, 152 and
320 cells fail, the three defects. Code mutations each fail cells: the PPUP
window off by one (140), any major bump (28), no genesis check (224), the
MIR quorum off by one (136), the MIR cutoff off by one (136), negatives
before Alonzo (48), negative pending from Alonzo (30), transfers ignoring
pending credits (8), no pot bound (72), the pot ignoring transfers (8) and
the transfer gate at major 6 (24).

Each defect has a fix branch with a regression test that fails without it:
`fix/ledger-ppup-empty-update`, `fix/ledger-ppup-phase2-invalid` and
`fix/ledger-mir-quorum-phase2-invalid`. With all three merged and the
constants set true, every cell matches the ledger.

## Not modelled

- The `maxTxSize + maxBlockHeaderSize < maxBlockBodySize` guard on an
  adopted update (Dingo implements it), and the per-era parameter domains
  and cost-model checks on proposals.
- Several MIR certificates in one transaction: gOuroboros folds them in
  order, which the model's one-certificate transactions approximate.
- The decoder's bounds on a proposed protocol version (gOuroboros allows
  16-bit values; the reference's `Version` is bounded by its own maximum).
- Dingo's epoch-boundary MIR payment is compared by reading the code
  (`ledger/mir.go`), not in the model; it follows `Rules/Mir.hs`.
