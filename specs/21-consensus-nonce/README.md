# 21: consensus — the epoch nonce

Every VRF check in an epoch uses that epoch's nonce, η0. It is made from the
chain itself:

- every block folds its VRF-derived nonce into the **evolving nonce** ηv;
- the **candidate nonce** ηc follows ηv until a stabilisation window before
  the end of the epoch, then stays frozen while ηv keeps moving;
- at the first block of a later epoch (the **tick**), η0 becomes
  ηc ⭒ ηh ⭒ extraEntropy, and ηh becomes the current **lab nonce**, the hash
  the last applied block names as its predecessor.

gOuroboros keeps no chain state. It provides two functions in
`ledger/common/nonce.go`, `CalculateRollingNonce` (one block into ηv) and
`CalculateEpochNonce` (the tick's η0), and the VRF input builders that use η0
(`vrf.MkInputVrf`, `vrf.MkSeedTPraos`, `consensus.ComputeVRFInput`, and
`verifyNonceVrf` in `ledger/verify_block.go`). Everything else is the
caller's (Dingo's): holding the nonces, deciding when to tick and freeze,
choosing what to pass, and restoring the state on rollback. The model makes
that contract its caller and checks it against the reference.

Sources are pinned to cardano-ledger `1210d37fe6bd`
(`eras/shelley/formal-spec`, `libs/cardano-protocol-tpraos`,
`libs/cardano-protocol`, `libs/cardano-ledger-core`), ouroboros-consensus
`ec239d57f618`, and gOuroboros `d0b95845`. `EpochNonce.tla` lists them with
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
VRF output), and the gOuroboros fixes in force (`GoFix`).

| Rule | Specification | Reference | gOuroboros (main at `756a9a89`) |
| --- | --- | --- | --- |
| ⭒ | `seedOp`, abstract | `Nonce a ⭒ Nonce b = Nonce (blake2b (a‖b))`, `NeutralNonce` identity on both sides (BaseTypes 607-612) | rolling: `CombineNonces` has `NonceTypeNeutral` as identity on both sides, and 32 zero bytes are an ordinary nonce (before `756a9a89`: zero bytes were neutral but the result was `blake2b(x)`); epoch: no neutral at all, zero bytes are hashed |
| Block nonce | `bnonce` | TPraos `blake2b(output)` (BaseTypes 615-619); Praos `blake2b(blake2b("N"‖output))` (Praos/VRF.hs 121-134) | `NonceFromTPraosVRF` and `NonceFromPraosVRF` derive it as the reference does; `CalculateRollingNonce` rejects a 64-byte operand (before `756a9a89`: concatenated raw) |
| Freeze | `s < firstSlot(e+1) − StabilityWindow` (chain.tex 600-640), meant 4k/f (errata 17.3) | strict `<`; 3k/f for TPraos and Babbage, 4k/f from Conway (Node.hs 590-597, 692-702) | caller's |
| Tick | `η0 := ηc ⭒ ηh ⭒ ηe`, `ηh := ηph` (chain.tex 514-533) | same (Tickn.hs 71-81); Praos without ηe (PolyPraos 606-640); once per block, however many epochs passed (Util.hs 22-42) | `blake2b(ηc‖ηh)`, then `‖ ηe` unless empty |
| ηph | hash of the last applied block itself (chain.tex 1748, 1809) | **its predecessor's hash** (`prevHashToNonce (bheaderPrev …)`, API.hs 563, 599; PolyPraos 713) | caller's; the parameter is named `prevEpochFirstBlockHash` |
| Start | `toShelley` (chain.tex 1975-2010) | η0 = ηv = ηc = initial nonce, ηh = lab = `NeutralNonce` (CanHardFork.hs 393-423, API.hs 451-468) | caller's |
| VRF input | `slotToSeed s ⭒ η0` | a `NeutralNonce` η0 adds no bytes (Praos/VRF.hs 64-78, BlockHeader.hs 422-435) | η0 must be 32 bytes, always appended |

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
| `EpochNonceDirectLabBug.cfg` | main: zero ηh is hashed in | `EpochNonceAgrees` |
| `EpochNonceRawOperandBug.cfg` | main before `756a9a89`: 64-byte output concatenated raw | `StateAgrees` |
| `EpochNonceNeutralInitBug.cfg` | main before `756a9a89`: neutral ηv hashes the block nonce again | `StateAgrees` |
| `EpochNonceVrfInputBug.cfg` | main: neutral η0 appended as zero bytes | `VrfInputAgrees` |
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

`make consensus-nonce` runs all 23 configs in about 20 seconds.

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

### Findings

1. **64-byte operand (defect, fixed on branch).** `CalculateRollingNonce`
   accepts a 64-byte VRF output and hashes `prev ‖ output` (96 bytes). Its
   comment says Haskell coerces the raw output into a nonce; it does not:
   `mkNonceFromOutputVRF` hashes the output first. The test vectors were
   rewritten to the 96-byte result in gOuroboros `aeebf7ed`; the earlier
   vectors equal the reference's value. Branch
   `fix/ledger-nonce-raw-vrf-operand` hashes a 64-byte operand to its TPraos
   nonce and restores the earlier vectors.
2. **NeutralNonce identity (defect, fixed on branch).** From a zero ηv,
   `CalculateRollingNonce` returns `blake2b(x)` for a 32-byte nonce `x`, where
   ⭒ gives `x`; `CalculateEpochNonce` hashes a zero or rejects an empty ηc or
   ηh, where ⭒ skips it. The second case is reached on every chain, at the
   second tick after the start. Branch `fix/ledger-nonce-neutral-identity`
   applies the identity in both.
3. **Neutral η0 in the VRF input (open).** `MkInputVrf` and `MkSeedTPraos`
   need 32 bytes, so a neutral η0 is appended as zeros; the reference appends
   nothing. Only a chain with a neutral initial nonce reaches it, during its
   first epoch. Fixing it changes the API.
4. **Naming (open).** `CalculateEpochNonce`'s `prevEpochFirstBlockHash` is
   neither the reference's ηh (the previous epoch's last block's predecessor)
   nor the spec's (that block's own hash). `EpochNonceSpecLabBug` shows the
   spec's reading diverging from the network.

Not covered: the leader-VRF threshold, KES and opcerts (model 13), the
Byron-era chain, extra entropy changing within an epoch, and Peras' previous
epoch nonce.
