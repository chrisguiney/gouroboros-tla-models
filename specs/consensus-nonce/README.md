# 21: consensus — the epoch nonce

Every VRF check in an epoch uses that epoch's nonce, η0. It is made from the
chain itself:

- every block folds its VRF-derived nonce into the **evolving nonce** ηv;
- the **candidate nonce** ηc follows ηv until a stabilisation window before
  the end of the epoch, then stays frozen while ηv keeps moving;
- at the first block of a later epoch (the **tick**), η0 becomes
  ηc ⭒ ηh ⭒ extraEntropy, and ηh becomes the current **lab nonce**, the hash
  the last applied block names as its predecessor.

gOuroboros keeps no chain state. It provides the nonce functions and
everything else is the caller's (Dingo's): holding the nonces, deciding when
to tick and freeze, choosing what to pass, and restoring the state on
rollback. The model makes that contract its caller and checks it against the
reference. gOuroboros has two sets of functions, and the constant `GoApi`
picks one:

- `"Bytes"`, now deprecated: `CalculateRollingNonce` (one block into ηv) and
  `CalculateEpochNonce` (the tick's η0) in `ledger/common/nonce.go`, and the
  VRF input builders `vrf.MkInputVrf`, `vrf.MkSeedTPraos` and
  `consensus.ComputeVRFInput`. They take `[]byte`, so they cannot spell
  `NeutralNonce`.
- `"Nonce"`: `NonceFromTPraosVRF`, `NonceFromPraosVRF` and `CombineNonces`
  (main `756a9a89`), and `EpochNonceFromNonces`, `vrf.MkInputVrfFromNonce`,
  `vrf.MkSeedTPraosFromNonce` and `consensus.ComputeVRFInputFromNonce`
  (branch `fix/nonce-neutral-epoch-and-vrf-input`). They take
  `common.Nonce`, whose `NonceTypeNeutral` is the reference's `NeutralNonce`.

Sources are pinned to cardano-ledger `1210d37fe6bd`
(`eras/shelley/formal-spec`, `libs/cardano-protocol-tpraos`,
`libs/cardano-protocol`, `libs/cardano-ledger-core`), ouroboros-consensus
`ec239d57f618`, and gOuroboros `d0b95845` (the `[]byte` functions), `756a9a89`
and branch `fix/nonce-neutral-epoch-and-vrf-input` (the `common.Nonce`
functions). `EpochNonce.tla` lists them with
file and line.

## The model (`EpochNonce.tla`)

Hashing is symbolic: a nonce is a term, `Hash(x)` is blake2b-256, and two
terms are equal only when built the same way (an injective hash).

The chain grows by one block in any later slot, or rolls back up to
`MaxRollback` blocks. In every state the model computes the reference's nonce
state from scratch (`RefFold`), so the reference needs no rollback logic. The
caller keeps its own state incrementally through gOuroboros' functions, keeps
a snapshot per block, and restores the tip's snapshot on rollback.

Constants choose the start (`Genesis`: Shelley from slot 0; `Byron`: Shelley
from epoch 1 after a Byron chain), the initial nonce (`GenesisHash` or
`Neutral`), the era's block nonce (`TPraos` or `Praos`), the window, the epochs
with extra entropy, the caller (`Contract`, `Dingo`, `Direct`), what the
caller passes `CalculateRollingNonce` (`Nonce`: 32 bytes; `Raw`: the 64-byte
VRF output), the hypothetical `[]byte` fixes in force (`GoFix`), and which
functions the caller uses (`GoApi`). `Caller`, `Operand` and `GoFix` matter
only for `"Bytes"`; with `"Nonce"` every caller derives the block nonce from
the raw output and passes typed nonces.

| Rule | Specification | Reference | gOuroboros (main at `756a9a89`; the branch's additions marked) |
| --- | --- | --- | --- |
| ⭒ | `seedOp`, abstract | `Nonce a ⭒ Nonce b = Nonce (blake2b (a‖b))`, `NeutralNonce` identity on both sides (BaseTypes 607-612) | rolling: `CombineNonces` has `NonceTypeNeutral` as identity on both sides, and 32 zero bytes are an ordinary nonce (before `756a9a89`: zero bytes were neutral but the result was `blake2b(x)`); epoch: no neutral at all, zero bytes are hashed |
| Block nonce | `bnonce` | TPraos `blake2b(output)` (BaseTypes 615-619); Praos `blake2b(blake2b("N"‖output))` (Praos/VRF.hs 121-134) | `NonceFromTPraosVRF` and `NonceFromPraosVRF` derive it as the reference does; `CalculateRollingNonce` rejects a 64-byte operand (before `756a9a89`: concatenated raw) |
| Freeze | `s < firstSlot(e+1) − StabilityWindow` (chain.tex 600-640), meant 4k/f (errata 17.3) | strict `<`; 3k/f for TPraos and Babbage, 4k/f from Conway (Node.hs 590-597, 692-702) | caller's |
| Tick | `η0 := ηc ⭒ ηh ⭒ ηe`, `ηh := ηph` (chain.tex 514-533) | same (Tickn.hs 71-81); Praos without ηe (PolyPraos 606-640); once per block, however many epochs passed (Util.hs 22-42) | `CalculateEpochNonce` (deprecated): `blake2b(ηc‖ηh)`, then `‖ ηe` unless empty. Branch: `EpochNonceFromNonces(ηc, ηh, ηe)` is `CombineNonces` twice, the reference's formula with `NonceTypeNeutral` as identity |
| ηph | hash of the last applied block itself (chain.tex 1748, 1809) | **its predecessor's hash** (`prevHashToNonce (bheaderPrev …)`, API.hs 563, 599; PolyPraos 713) | caller's; the parameter is named `prevEpochFirstBlockHash` |
| Start | `toShelley` (chain.tex 1975-2010) | η0 = ηv = ηc = initial nonce, ηh = lab = `NeutralNonce` (CanHardFork.hs 393-423, API.hs 451-468) | caller's |
| VRF input | `slotToSeed s ⭒ η0` | a `NeutralNonce` η0 adds no bytes (Praos/VRF.hs 64-78, BlockHeader.hs 422-435) | `MkInputVrf`, `MkSeedTPraos`, `ComputeVRFInput` (deprecated): η0 must be 32 bytes, always appended. Branch: `MkInputVrfFromNonce`, `MkSeedTPraosFromNonce`, `ComputeVRFInputFromNonce` append nothing for `NonceTypeNeutral` |

Invariants:

- `StateAgrees`: the caller's ηv, ηc, η0, lab, ηh and last epoch are the
  reference's, after every block and every rollback (so a rollback across the
  freeze point restores the candidate).
- `EpochNonceAgrees`: the caller's η0 is the reference's.
- `VrfInputAgrees`: the VRF input gOuroboros builds from that η0 is the
  reference's.
- `CandidateFrozen`: the reference's ηc is ηv as it stood after the last block
  before a freeze point; later blocks do not change it.
- `EpochNonceDenotation`: the reference's η0 is, in closed form, the candidate
  before the last tick ⭒ the lab nonce before the tick before that ⭒ the
  extra entropy. So it depends only on blocks before the freeze point and the
  previous epoch's lab nonce, and the first two ticks after the start use
  `NeutralNonce` for ηh.

| Config | States | Result |
| --- | --- | --- |
| `EpochNonce.cfg` (Shelley from slot 0, TPraos, contract caller) | 8,930 | passes |
| `EpochNonceDeep.cfg` (6 blocks, 4 epochs, rollback 3) | 79,396 | passes |
| `EpochNonceByron.cfg` (Byron start, Dingo) | 9,251 | passes |
| `EpochNoncePraos.cfg` (Praos, wider window, Dingo) | 7,430 | passes |
| `EpochNonceDirectFixed.cfg` (Byron start, raw operand, direct caller, both fixes) | 9,251 | passes |
| `EpochNonceNeutralInitFixed.cfg` (neutral initial nonce, direct, neutral fix) | 8,930 | passes |
| `EpochNonceNeutralInitContract.cfg` (neutral initial nonce, main's contract) | 8,930 | passes |
| `EpochNonceNewByron.cfg` (`common.Nonce` functions, Byron start, raw output, extra entropy) | 9,251 | passes |
| `EpochNonceNewNeutral.cfg` (`common.Nonce` functions, neutral initial nonce, VRF input included) | 8,930 | passes |
| `EpochNonceNewPraos.cfg` (`common.Nonce` functions, Praos, neutral initial nonce) | 7,430 | passes |
| `EpochNonceNewLabBug.cfg` | mutation: `EpochNonceFromNonces` hashes a neutral ηh in | `EpochNonceAgrees` |
| `EpochNonceNewVrfInputBug.cfg` | mutation: the nonce VRF input appends a neutral η0 as zeros | `VrfInputAgrees` |
| `EpochNonceDirectLabBug.cfg` | `CalculateEpochNonce`: zero ηh is hashed in | `EpochNonceAgrees` |
| `EpochNonceRawOperandBug.cfg` | main before `756a9a89`: 64-byte output concatenated raw | `StateAgrees` |
| `EpochNonceNeutralInitBug.cfg` | main before `756a9a89`: neutral ηv hashes the block nonce again | `StateAgrees` |
| `EpochNonceVrfInputBug.cfg` | `MkInputVrf`/`MkSeedTPraos`: neutral η0 appended as zero bytes | `VrfInputAgrees` |
| `EpochNonceFreezeLEBug.cfg` | mutation: `<=` | `StateAgrees` |
| `EpochNonceNoFreezeBug.cfg` | mutation: never freeze | `StateAgrees` |
| `EpochNonceOtherWindowBug.cfg` | mutation: the other era's window | `StateAgrees` |
| `EpochNonceSpecLabBug.cfg` | mutation: ηph from the block's own hash (the spec's reading) | `EpochNonceAgrees` |
| `EpochNonceNoRestoreBug.cfg` | mutation: rollback restores ηv only | `StateAgrees` |
| `EpochNonceRefNoFreezeBug.cfg` | reference mutation: never freeze | `CandidateFrozen` |
| `EpochNonceRefLabSelfBug.cfg` | reference mutation: lab from the block's own hash | `EpochNonceDenotation` |

Probes (expected violated): `ProbeTickLab` (an η0 built with a real ηh),
`ProbeSkippedEpoch` (one tick across an empty epoch), `ProbeEntropy`,
`ProbePostFreeze`, `ProbeRollbackCand` (a rollback that changed ηc).

Every config before the `New` ones sets `GoApi = "Bytes"`. `make
consensus-nonce` runs all 28 configs in about 25 seconds.

### What the caller must do (the contract on main)

1. Pass `CalculateRollingNonce` the block's 32-byte nonce, derived per era
   (TPraos `blake2b(nonce VRF output)`, Praos `blake2b(blake2b("N"‖output))`).
   gOuroboros has no helper for either.
2. Start ηv at the initial nonce, never 32 zero bytes (or apply ⭒ by hand).
3. Tick once at the first block of a later epoch; freeze with a strict `<` and
   the era's window.
4. Carry ηh as `prevHashToNonce` of the previous epoch's last block's
   predecessor, `NeutralNonce` for the first two ticks after the start, and
   apply ⭒ by hand whenever ηc or ηh is `NeutralNonce`: `CalculateEpochNonce`
   cannot express it.
5. Keep a snapshot per block and restore it whole on rollback.

Dingo does 1-5 for the public networks (`ledger/eras/*.go`,
`ledger/extra_entropy.go` `assembleEpochNonce`, `ledger/epoch_lab_nonce.go`).
It does not handle a neutral ηc with a real ηh, which needs a neutral initial
nonce.

With the `common.Nonce` functions (`GoApi = "Nonce"`), items 2 and 4 reduce
to holding `NonceTypeNeutral` where the reference holds `NeutralNonce`: derive
the block nonce with `NonceFromTPraosVRF` or `NonceFromPraosVRF`, fold it with
`CombineNonces`, tick with `EpochNonceFromNonces`, and build the VRF input
with `MkInputVrfFromNonce` or `MkSeedTPraosFromNonce`. The freeze, the tick
condition, the lab nonce and the rollback (items 3-5) stay the caller's.

### Findings

1. **64-byte operand (defect, fixed on branch).** `CalculateRollingNonce`
   accepts a 64-byte VRF output and hashes `prev ‖ output` (96 bytes). Its
   comment says Haskell coerces the raw output into a nonce; it does not:
   `mkNonceFromOutputVRF` hashes the output first. The test vectors were
   rewritten to the 96-byte result in gOuroboros `aeebf7ed`; the earlier
   vectors equal the reference's value. Branch
   `fix/ledger-nonce-raw-vrf-operand` hashes a 64-byte operand to its TPraos
   nonce and restores the earlier vectors.
2. **NeutralNonce identity (fixed additively).** From a zero ηv,
   `CalculateRollingNonce` returned `blake2b(x)` for a 32-byte nonce `x`,
   where ⭒ gives `x`; `CalculateEpochNonce` hashes a zero or rejects an empty
   ηc or ηh, where ⭒ skips it. The second case is reached on every chain, at
   the second tick after the start. `CombineNonces` (main `756a9a89`) fixed
   the rolling part; branch `fix/nonce-neutral-epoch-and-vrf-input` adds
   `EpochNonceFromNonces` for the tick and deprecates `CalculateEpochNonce`,
   whose behaviour is unchanged (`EpochNonceDirectLabBug` still reproduces
   it; `EpochNonceNewByron` passes).
3. **Neutral η0 in the VRF input (fixed additively).** `MkInputVrf` and
   `MkSeedTPraos` need 32 bytes, so a neutral η0 is appended as zeros; the
   reference appends nothing. Only a chain with a neutral initial nonce
   reaches it, during its first epoch. The same branch adds
   `MkInputVrfFromNonce`, `MkSeedTPraosFromNonce` and
   `ComputeVRFInputFromNonce` and deprecates the `[]byte` builders
   (`EpochNonceVrfInputBug` still reproduces them; `EpochNonceNewNeutral`
   passes). gOuroboros' own callers (`consensus` leader election, header
   validation and block building, `ledger` VRF verification) now call the new
   builders with an ordinary nonce made from their 32-byte η0, so their
   exported `[]byte` APIs still cannot express a neutral η0.
4. **Naming (open).** `CalculateEpochNonce`'s `prevEpochFirstBlockHash` is
   neither the reference's ηh (the previous epoch's last block's predecessor)
   nor the spec's (that block's own hash). `EpochNonceSpecLabBug` shows the
   spec's reading diverging from the network.

Not covered: the leader-VRF threshold, KES and opcerts (model `consensus`), the
Byron-era chain, extra entropy changing within an epoch, and Peras' previous
epoch nonce.
