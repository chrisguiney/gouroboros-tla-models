# the in-block ledger view and VerifyBlock's issuer check

`ledger.VerifyBlock` validates one block: header cryptography, body size
and hash, the transactions in order, and the issuer. The transactions are
checked against `common.BlockLedgerState`, a view that lays the block's
earlier transactions over the caller's ledger state. This directory models
two things the other models leave out:

- `GovOverlay.tla`: the Conway governance part of that view (DRep
  registrations, vote delegations, proposals, committee hot keys), across
  blocks that are accepted or rejected;
- `VerifyBlockIssuer.tla`: which blocks VerifyBlock accepts compared with
  the reference's block application, the TPraos overlay schedule in
  particular, and which checks it leaves to its caller.

It composes with, and does not repeat:

- `ledger-bbody` (`BlockBody.tla`): body size and hash, execution units,
  reference-script bytes, invalid-transaction indexes, the UTxO part of the
  overlay (later transactions see earlier outputs, spent inputs disappear,
  an invalid transaction moves only its collateral);
- `consensus-eras` (`HeaderValidation.tla`): the order of the header checks
  and the overlay inside `consensus.ValidateHeader`;
- `ledger-shelley` (`CertLifecycle.tla`): the account and pool part of the
  overlay;
- `ledger-utxo`, `ledger-witnesses`, `ledger-conway-dijkstra`,
  `ledger-governance`: each transaction's own rules.

## What the reference does

cardano-ledger `1210d37f`, ouroboros-consensus `ec239d57f618`.

- Applying a block validates its header against the protocol state, then
  applies the body (`Ouroboros/Consensus/Ledger/Extended.hs`;
  `Shelley/Ledger/Ledger.hs` `applyBlock`). Re-applying a block already
  validated skips the checks (`reapplyBlock`).
- For TPraos the header rule is PRTCL: OVERLAY, then OCERT. OVERLAY
  (`libs/cardano-protocol-tpraos/.../Rules/Overlay.hs` 219-282) classifies
  the slot (`Cardano/Ledger/Slot.hs` 117-130). A non-active overlay slot
  fails; an active one checks the scheduled genesis delegate's cold key,
  VRF key and the VRF proofs, with no stake; any other slot checks the
  pool's VRF key, the proofs and the leader threshold.
- BBODY (`eras/conway/impl/.../Rules/Bbody.hs`) checks size and hash and
  runs LEDGERS (`Rules/Ledgers.hs`): each transaction against the state the
  previous one left. A failure rejects the whole block, and the ledger
  stays as it was.
- LEDGER (`Rules/Ledger.hs` 390-448) gives CERTS the committee proposals of
  the current state (line 393), so GOVCERT's potential-member test
  (`Rules/GovCert.hs` 190-205) sees an UpdateCommittee proposal an earlier
  transaction of the same block made. A phase-2-invalid transaction runs
  only UTXOW, which takes its collateral.

## What gOuroboros does

- `verifyBlock` (`ledger/verify_block.go`): leader VRF (and the nonce VRF
  for TPraos), opcert cold signature, KES window, KES signature, declared
  body size, body hash; then `VerifyBlockState`: Dijkstra and Conway header
  rules, block limits, the transactions (`verifyBlockTransactions`, a fresh
  `BlockLedgerState` per call), the reference-script total, and last the
  issuer against `VerifyConfig.LeaderPoolVrfKeyHash`.
- It does not check the envelope (block number, slot, previous hash,
  protocol version against the node's maximum), the leader threshold or
  the opcert counter: its doc comment leaves them to the caller.
- `BlockLedgerState` keeps maps of what the block changed and asks the
  wrapped state for the rest. It applies nothing of a phase-2-invalid
  transaction but its collateral.

## Comparison

| Question | Reference | gOuroboros main | Verdict |
|---|---|---|---|
| Active overlay slot (d > 0) | genesis delegate, its VRF key, no stake | issuer looked up in the pool distribution, so a valid delegate block is rejected | does not conform; fixed on `fix/ledger-verify-block-tpraos-overlay` |
| Non-active overlay slot | rejected | a pool block is accepted | does not conform; same fix |
| Committee certificate after an in-block UpdateCommittee proposal | accepted (potential member) | rejected: the view asks only the wrapped state | does not conform; fixed on `fix/ledger-block-state-proposed-committee` |
| DRep registration, delegation, deregistration clearing, proposals, hot keys within a block | sequential | overlay maps | conforms (`GovOverlay`) |
| Invalid transaction | collateral only | collateral only | conforms (`NoLeak`) |
| Rejected block | ledger unchanged | fresh overlay per call, caller commits only on success | conforms (`FreshOverlay`) |
| First error reported | issuer before body | issuer after the transactions | differs in the error only, not the verdict (`VerifyBlockIssuerFirstErrorBug`) |

## The caller contract

VerifyBlock is correct only together with what its caller supplies. Read
from Dingo (`ledger/verify_header.go` `verifyBlockHeaderHex`;
`utxoref/state_overlay.go`; `ledger/view.go`), the contract is:

1. `config.LedgerState` is the ledger after the previous block, with no
   transaction of this block applied, and answers every query as the
   reference state would. In particular `CommitteeCredentialMember` answers
   potential members from stored UpdateCommittee proposals (Dingo:
   `LedgerView.proposedCommitteeMember`), `DRepDelegation` reflects earlier
   deregistrations, and `GovActionExists` covers stored proposals. The
   overlay adds only the block's own effects (the model's `GoView` reads
   `committed` this way).
2. The caller applies the block itself after acceptance, and validates the
   next block against the result; a rejected block leaves nothing behind
   because each call starts a fresh `BlockLedgerState`.
3. The caller runs the envelope, leader-threshold and opcert-counter checks
   (`consensus.ValidateHeader` or its own); in an active overlay slot it
   must not apply the threshold. `VerifyBlockIssuerProbeAloneBug` shows
   VerifyBlock alone accepts blocks the reference rejects.
4. `LeaderPoolVrfKeyHash` answers from the active leader distribution; with
   stake-pool validation on, a Shelley-to-Alonzo block also needs
   `TPraosOverlay` (the fix) for its epoch.
5. A long-lived wrapper that folds pending transactions into a
   `BlockLedgerState` (Dingo's `StateOverlay`) must drop it after a failed
   application, since a failed `ApplyTransaction` can leave a transaction
   half applied, and must refold when the base changes. Dingo does both
   (`o.state = nil`, generation check). Dingo folds only transactions for
   which `ChangesState` is true, which excludes phase-2-invalid ones, and
   strips their UTxO effects (`effectsOnly`): its mempool maps carry those.

Dingo calls VerifyBlock only for header cryptography, with
`SkipBodyHashValidation`, `SkipTransactionValidation`,
`SkipStakePoolValidation` and `SkipBlockLimitsValidation` all set, and does
its own overlay schedule check, so neither defect reaches Dingo through
VerifyBlock. The committee defect can reach Dingo through
`StateOverlay`, which is a `BlockLedgerState`, wherever its view is checked
with the committee rule: a transaction authorizing a
member proposed by an earlier pending transaction is rejected.

## GovOverlay.tla

A block is up to `MaxTxs` transactions, each one governance action
(register, unregister or delegate to a DRep; an UpdateCommittee proposal
naming `k2`, or an Info one; authorize a hot key for, or resign, `k1` or
`k2`; vote; withdraw), valid or phase-2-invalid. `k1` sits on the
committee with a hot key at the start. `Blocks` blocks are validated in a
row. The reference state is applied transaction by transaction; the
gOuroboros overlay is the record `BlockLedgerState` keeps (touched flags,
the certificate counter that times deregistrations), read through `GoView`
over the committed ledger.

Invariants: `OverlayMatches` (the view equals the reference state while a
block runs), `GoAgrees` (same verdict on every transaction), `NoLeak` (an
accepted invalid transaction leaves the view unchanged), `FreshOverlay` (a
block starts from the committed ledger alone).

| Config | What | Result | Distinct states |
|---|---|---|---|
| `GovOverlay` | 2 blocks of up to 2 transactions, with the fix | all hold | 2,427 |
| `GovOverlayDeep` | 2 blocks of up to 3 transactions, with the fix | all hold | 16,464 |
| `GovOverlayGoMainBug` | gOuroboros main | `GoAgrees` violated | |
| `GovOverlayGoMainViewBug` | gOuroboros main | `OverlayMatches` violated | |
| `GovOverlayLeakInvalidBug` | invalid transactions applied | `NoLeak` violated | |
| `GovOverlayNoDeregClearBug` | deregistration keeps delegations | `OverlayMatches` violated | |
| `GovOverlayReuseBug` | rejected block's overlay reused | `FreshOverlay` violated | |
| `GovOverlayProbeInBlockAuthBug` | probe | an in-block-proposal authorization is accepted | |
| `GovOverlayProbeRejectedBug` | probe | a block is rejected | |
| `GovOverlayProbeDeregClearsBug` | probe | an in-block deregistration clears a delegation | |

## VerifyBlockIssuer.tla

A block is abstract: its slot's kind, its issuer (pool, scheduled genesis
delegate, stranger), whether its VRF key is its role's, and any subset of
the other checks it fails. Every shape is an initial state.

| Config | What | Result | Distinct states |
|---|---|---|---|
| `VerifyBlockIssuerTPraos` | TPraos with the fix | `AcceptAgrees`, `NoFalseRejects` hold | 18,432 |
| `VerifyBlockIssuerPraos` | Praos, gOuroboros main | hold | 6,144 |
| `VerifyBlockIssuerGoMainBug` | TPraos, main | `AcceptAgrees` violated | |
| `VerifyBlockIssuerGoMainRejectsBug` | TPraos, main | `NoFalseRejects` violated | |
| `VerifyBlockIssuerFirstErrorBug` | known difference | `FirstErrorAgrees` violated | |
| `VerifyBlockIssuerProbeAloneBug` | probe | VerifyBlock alone accepts a block the reference rejects | |
| `VerifyBlockIssuerProbeActiveBug` | probe | an active-overlay-slot block is accepted | |

## Go tests

- `ledger/common` `TestBlockLedgerStateGovernanceSequences` (branch
  `test/ledger-block-overlay-model`, stacked on the committee fix): walks
  every block of up to three of the model's transactions (6,073 blocks) and
  compares the overlay's answers with the reference state after every
  transaction; committee certificates go through
  `UtxoValidateCommitteeCertificates`. Mutations killed: no proposed
  members, invalid transactions applied, no deregistration clearing,
  resignation keeping the hot key.
- `ledger/common` `TestBlockLedgerStateTreatsInBlockCommitteeProposalAsPotentialMember`
  and `TestBlockLedgerStateIgnoresInvalidCommitteeProposal` (fix branch).
- `ledger` `TestVerifyBlockStateTPraosOverlay` (overlay fix branch): the
  model's slot kinds, issuers and VRF-key cells through `VerifyBlockState`,
  with d = 1, 1/2 and 0 and two genesis keys listed out of order.

## Not modelled

- Votes' effect on DRep expiry and on proposals' vote maps (no in-block
  validity depends on them); balances and withdrawal amounts.
- Script-hash and key-hash credentials with the same bytes: the hash-only
  `CommitteeMember` and `applyCommitteeAuthorization` match by hash.
- Dijkstra sub-transaction levels (`ledger-conway-dijkstra`).
- Transactions are not run through VerifyBlock end to end in the Go test:
  building blocks that pass every phase-1 rule is out of scope; the walk
  uses the same `BlockLedgerState` sequence `verifyBlockTransactions` does.
