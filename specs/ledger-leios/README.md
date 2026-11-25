# the Leios ledger side

Linear Leios (CIP-0164) adds two things to a ranking block (RB): its
header may **announce** an endorser block (EB), a list of transaction
references, and the next RB may **certify** that EB with a certificate
signed by a stake-based voting committee. The certified EB's transactions
join the ledger just before the certifying RB (a "CertRB"), and a CertRB
carries no transactions of its own.

The network side (LeiosNotify, LeiosFetch, LeiosVotes) is in
[Model `leios-peras`](../leios-peras/README.md). This model covers what happens
once the blocks have arrived. It has two parts:

- `LeiosLedger.tla`: announcement, certification, EB application and
  rollback across a short chain.
- `LeiosCommittee.tla`: whether one certificate verifies against the
  committee.

Leios is a draft. Where the CIP, the reference ledger, and the prototype
node disagree, the model records each and says which one gOuroboros
follows.

## What gOuroboros does, and does not, implement

gOuroboros holds no ledger state and has no EB rule. It provides:

- **Header rules** (`ledger/dijkstra/leios_header.go`):
  `ValidateLeiosAnnouncementSize` (announced size bound),
  `ValidateLeiosCertificateTiming` (a header with the certificate flag set
  must follow a header that announced an EB, by at least
  `LeiosMinCertificationSlot`).
- **Body rules** (`validateLeiosBlockBody`): the header flag is set exactly
  when the body has a certificate; a certificate excludes transactions,
  except over node-to-client where a CertRB arrives with its EB's
  transactions inlined; no Peras certificate.
- **Certificate verification** (`ledger/leios/certificate.go`
  `VerifyDijkstraCertificateForMessage`), with the committee supplied by the
  caller through `DijkstraLeiosCertificateState`.
- **EB decoding** (`ledger/common/leios_endorser_block.go`): no duplicate
  references within one EB, and a size bound. `protocol/leiosfetch`
  checks fetched transactions against an EB's references.
- `VerifyBlockState` (`ledger/verify_block.go`) wires these together and
  validates a node-to-client CertRB's inlined transactions at the
  announcing slot.

It does **not** apply an EB to any state, remember the last announcement,
check that a fetched EB matches the announced hash and size, or roll
anything back. Those belong to the caller (Dingo). So `LeiosLedger.tla`
models the reference's state machine and states the caller's obligations;
the gOuroboros part is its stateless acceptance predicate, `GoChecks`.

## Part 1: announcement, certification and rollback (`LeiosLedger.tla`)

### What the model contains

Two transactions (`t1`, `t2`), each spending its own input once. Two EBs a
block may announce: `<<t1, t2>>` and `<<t2>>`, so an EB can conflict with an
RB transaction or with another EB. Slots 1-5 (1-7 in the deep run), a
certification delay of 2 slots, epochs of 4 slots, chains of at most three
blocks (four in the deep run).

The ledger keeps the transactions applied in order (`log`), the announcing
slots of the EBs applied (`endorsed`), and the remembered announcement
with its `applied` bit, as cardano-ledger's `lsLastEbAnnouncement` does.
The model keeps one ledger snapshot per block, so a rollback restores the
state before the rolled-back block, and holds the result of applying the
tip's EB aside (`pending`) until a CertRB uses it.

Steps:

- **AddRB**: any block after the tip: announcing an EB or not, flag set or
  not, a certificate (valid or not) or not, zero or one transaction. It is
  added if accepted. A block that does not certify drops `pending`.
- **FetchApplyEB**: the EB rule. The announced EB arrives and is applied on
  top of the tip's state, if it is the announced one, not yet applied, and
  its transactions are valid in order.
- **Rollback**: the tip block goes, its snapshot goes, `pending` goes.

Who decides acceptance is the constant `Impl`: `"ref"` uses the reference
rules, `"go"` uses `GoChecks` plus the caller (`GoCallerAppliesEb`: the
caller refuses a CertRB whose EB it has not applied, as the prototype node
does by resolving the EB closure first). `RefSameEpoch` selects ledger
1210d37f (TRUE) or the prototype (FALSE).

### The questions

1. Is an EB applied at most once, and only while a valid certificate for it
   is on the chain?
2. Do the EB's transactions resolve to the announced EB, in its order, and
   is no transaction applied twice across RBs and EBs?
3. Does rolling back a CertRB take its EB's transactions out again?
4. Does gOuroboros, with a caller that applies the EB, accept exactly the
   blocks the reference accepts?

### The answers

| Invariant | Meaning | Holds |
| --- | --- | --- |
| `LedgerMatchesChain` | the ledger equals a replay of the chain: per block, the predecessor's EB if certified, then the block's transactions | yes (Q1, Q2, Q3) |
| `CertifiedChainWellFormed` | every CertRB follows an announcing block, late enough, same epoch under 1210d37f, valid certificate, flag set, no transactions | yes |
| `NoTxTwice` | no transaction in the log twice | yes (Q2) |
| `EbAppliedAtMostOnce` | no announcing slot endorsed twice | yes (Q1) |
| `GoAgrees` | gOuroboros accepts exactly what the reference accepts, for every candidate block in every reachable state | yes against the prototype; **no** against ledger 1210d37f |

`GoAgrees` fails against 1210d37f for one reason: the ledger's LEIOSCERT
rule refuses a certificate for an EB announced in the previous epoch
(`LeiosCertAnnouncedInPreviousEpoch`), and gOuroboros has no epoch rule.
Neither does the prototype node gOuroboros follows (ouroboros-consensus
5cc95f4c, which pins cardano-ledger 505fa72 where LEIOSCERT does not exist
yet). CIP-0164 sizes the certificate by "the epoch in which the announcing
RB was produced", which implies certificates may cross an epoch. Three
sources, three answers; `LeiosLedgerProbeCrossEpochBug` shows the prototype
accepting a cross-epoch certificate. This needs a decision, not a fix.

`LeiosLedgerGoNoCallerBug` shows the caller obligation: gOuroboros alone
accepts a CertRB whose EB was never applied, and the ledger loses the EB's
transactions. The reference refuses it (`LeiosCertEbNotApplied`).

### Checking the checks

Every invariant fails under some mutation:

| Config | Mutation | Fails |
| --- | --- | --- |
| `LeiosLedgerNoTimingBug` | no certification delay | `CertifiedChainWellFormed` |
| `LeiosLedgerTxsWithCertBug` | a CertRB may carry transactions | `CertifiedChainWellFormed` |
| `LeiosLedgerKeepAnnouncementBug` | a silent block keeps the old announcement | `CertifiedChainWellFormed` |
| `LeiosLedgerNoHashCheckBug` | the EB rule takes any EB | `LedgerMatchesChain` |
| `LeiosLedgerEagerEbBug` | the EB lands in the tip state before any certificate | `LedgerMatchesChain` |
| `LeiosLedgerRollbackKeepsStateBug` | rollback keeps the rolled-back state | `LedgerMatchesChain` |
| `LeiosLedgerRollbackKeepsPendingBug` | rollback keeps the old tip's applied EB | `LedgerMatchesChain` |
| `LeiosLedgerReapplyUncheckedBug` | EB rule without `EbAlreadyApplied` or transaction checks | `EbAppliedAtMostOnce` |
| `LeiosLedgerReapplyTxsBug` | the same | `NoTxTwice` |
| `LeiosLedgerGoNoCallerBug` | caller never applies the EB | `LedgerMatchesChain` |
| `LeiosLedgerGoEpochBug` | gOuroboros against 1210d37f | `GoAgrees` |

Probes (expected to be violated, proving the behaviour is reachable):
`LeiosLedgerProbeCertBug` (a CertRB is accepted),
`LeiosLedgerProbeRollbackBug` (a CertRB is rolled back),
`LeiosLedgerProbeDiscardBug` (an applied EB is dropped by a block that
does not certify it), `LeiosLedgerProbeCrossEpochBug` (the prototype
certifies across an epoch).

State counts: `LeiosLedger` 19,408 distinct states; `LeiosLedgerPrototype`
and `LeiosLedgerGo` 20,452; `LeiosLedgerGoDeep` 353,500.

## Part 2: certificate verification (`LeiosCommittee.tla`)

### What the model contains

`Pools` registered pools with descending stake, a committee-size
parameter `Nc`, a set of keyed seats, a quorum of 3/5 of active stake, and
2 bits per bitfield byte (8 in reality; 2 makes the byte rounding visible
with three or four seats). The model has no steps: each initial state is
one certificate (bitfield length, set bits, and the seats whose signatures
were aggregated), and the invariants are checked on all of them.

The reference ([R1] `selectLeiosCommittee`, [R2] `verifyLeiosCert`): the
committee has `min(Nc, Pools)` seats; the bitfield must be exactly
`ceil(seats/8)` bytes; padding bits past the last seat are ignored; no
keyless signer; quorum; signature over exactly the signers' keys.

gOuroboros today: `VerifyDijkstraCertificateForMessage` is called with
`committeeSize = LeiosCommitteeSize` (the parameter `Nc`), requires the
committee to have exactly `Nc` seats, and requires a `ceil(Nc/8)`-byte
bitfield. `validateDijkstraBlockCertificatesWith` checks the same length
before it even looks the committee up.

### The answer: a gOuroboros defect

With at least as many pools as seats, gOuroboros and the reference agree
(`LeiosCommittee`, `LeiosCommitteeMorePools`). With fewer pools than `Nc`
they do not (`LeiosCommitteeFewPoolsBug`): the reference seats every pool
and sizes the bitfield by them; gOuroboros refuses every valid
certificate. A caller that pads the committee to `Nc` keyless seats does
not help (`LeiosCommitteeFewPoolsPaddedBug`): the bitfield length still
differs.

This is not hypothetical. The prototype testnet genesis
(`ouroboros-leios` `testnet/config/dijkstra-genesis.json`) sets
`leiosCommitteeSize` to 900, and the rc-2026w41 certifying block in
gOuroboros's own test data has a one-byte bitfield over a two-seat
committee. Under that genesis, `VerifyBlockState` rejects a certificate of
that shape with "leios signer bitfield must be 113 bytes for committee size
900, got 1" (shown by the fix branch's test, with a synthetic block).

The fix (`LeiosCommitteeFewPoolsFixed`): accept a committee of at most `Nc`
seats and size the bitfield by the committee handed over. The caller must
hand over the seated committee, not `Nc` padded seats
(`LeiosCommitteeFewPoolsFixedPaddedBug`).

| Config | Expectation |
| --- | --- |
| `LeiosCommittee`, `LeiosCommitteeMorePools` | pass (340 and 84 states) |
| `LeiosCommitteeFewPoolsFixed` | pass (340 states) |
| `LeiosCommitteeFewPoolsBug`, `...PaddedBug`, `...FixedPaddedBug` | `AcceptAgrees` fails |
| `LeiosCommitteeNoKeylessCheckBug` | `GoSound` fails |
| `LeiosCommitteeNoQuorumBug` | `GoSound` fails |
| `LeiosCommitteeCountPaddingBug` | `AcceptAgrees` fails |
| `LeiosCommitteeProbeBug` | some certificate is accepted |

## Go tests and mutations (gOuroboros)

Branch `test/leios-ledger-model` (tests only):

- `ledger/dijkstra/leios_ledger_model_test.go`
  `TestLeiosLedgerModelGoChecks`: all 192 cells of `GoChecks` (predecessor
  origin, announcing, silent or pre-Dijkstra; flag; certificate;
  transactions; slot gap one under, at, and one over the delay;
  node-to-client or not) through `ValidateLeiosCertificateTiming` and the
  body rule, against the model's predicate. Mutations killed: delay off by
  one, announcement check dropped, certificate-with-transactions allowed,
  each direction of the flag check dropped.
- `ledger/leios/certificate_model_test.go` `TestCertificateModelCells`:
  the two passing committee scenarios with real BLS keys; every set of the
  bits up to one past the last seat against every set of keyed signers,
  and wrong bitfield lengths, against the reference's acceptance.
  Mutations killed: keyless signer skipped, quorum dropped, bitfield
  length unchecked, signature over a different message. Dropping the
  "no signers" check is an equivalent mutant (quorum already fails).

Branch `fix/leios-committee-size`: `TestVerifyDijkstraCertificateCommitteeSmallerThanParameter`
and `TestValidateDijkstraBlockCertificatesSmallCommittee` fail before the
fix ("got 2 seats, want 900"; "must be 113 bytes for committee size 900,
got 1") and pass after it.

## Specification, reference and gOuroboros

| Rule | CIP-0164 (a2cac180) | Reference | gOuroboros (d0b95845) |
| --- | --- | --- | --- |
| Certificate only for the predecessor's EB | yes [Step 5] | ledger: remembered announcement, replaced every block; prototype: predecessor's chain-dep state | predecessor header |
| Certification delay | `ceil((3Lhdr+Lvote+Ldiff)/slotLength)` | same (LEIOSCERT; PolyPraos header check) | same (`LeiosMinCertificationSlot`) |
| Same epoch as announcement | implied not required (bitfield sized by the announcing epoch) | ledger 1210d37f: required; prototype: not checked | not checked |
| CertRB has no transactions | Step 5: none; Ledger Management: "RBs can include both certificates and their own transactions" (the CIP contradicts itself) | none (`LeiosCertBlockBodyHasTxs`) | none, except node-to-client inlined EB transactions |
| EB applied before the CertRB, at the announcing slot | yes | EB rule, then BBODY needs `ebIsApplied` | caller's job; node-to-client inlined transactions validated at the announcing slot |
| EB applied at most once | implied | `EbAlreadyApplied` | caller's job |
| EB matches announced hash and size | announced_eb_size wrong: header still valid, no vote | `EbAnnouncementHashMismatch`, `...SizeMismatch` | caller's job (`LeiosEndorserBlock.Hash`, leiosfetch checks transactions against references) |
| EB encoding | `[omap<hash32, uint16>]` (array around a map) | bare map, `uint32` sizes | bare map, `uint32` sizes (follows the node) |
| Duplicate references in one EB | forbidden (omap) | forbidden | forbidden at decode |
| Committee size | `min(Nc, pools)` | `min(Nc, pools)` | **exactly `Nc`** (defect; fixed on `fix/leios-committee-size`) |
| Bitfield length | `ceil(N/8)`, N the committee | `ceil(n/8)`, n the committee | `ceil(Nc/8)` (same defect) |
| Padding bits | not specified | ignored | ignored |
| Keyless signer | ineligible | `SignerWithoutKey` (invalid proofs seated keyless) | `ErrKeylessSigner`; invalid proof `ErrInvalidProof` (both reject) |

## Sources

- CIP-0164, cardano-foundation/CIPs `a2cac18039d7bab6c0dc1a806ad8a96b8b0546fc`,
  `CIP-0164/README.md`: Step 5 (393-438), Ranking Blocks (732-761),
  Endorser Blocks (763-779), Committee Structure (851-860), Certificate
  Validation (911-930), Ledger Management (1117-1132), Committee
  Selection (1146-1158), CDDL (3378-3423).
- cardano-ledger `1210d37fe6bdef32e85179ae08b7e1e8cfd75273`:
  `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Bbody.hs` 464-504,
  `Rules/LeiosCert.hs` 106-140, `Rules/Eb.hs` 192-293, `Block.hs` 86-89
  (the EB is applied to the state the announcing block left, unticked),
  `libs/cardano-ledger-core/src/Cardano/Ledger/State/Leios.hs` 93-108
  (`selectLeiosCommittee`) and 137-150 (`EbAnnouncement`).
- ouroboros-consensus `5cc95f4caf294751318f8637ab2fb60d5de6eb29` (the
  rc-2026w41 prototype gOuroboros cites):
  `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LedgerDB/Forker.hs`
  630-686 (CertRB apply path; note its own FIXME that the delay is not
  checked there, it is checked in the header rules of
  `ouroboros-consensus-protocol/.../Protocol/PolyPraos.hs` 711-765);
  `cabal.project` pins cardano-ledger `505fa72` and cardano-base
  `c1e1ed8d`.
- cardano-ledger `505fa72260632fca6df33e18e18719730bf9a460`:
  `libs/cardano-ledger-core/src/Cardano/Ledger/State/LeiosCommittee.hs` 99.
- cardano-base `c1e1ed8d7ae39c111c73fc5f59ac37ce5933b83c`:
  `cardano-crypto-leios/src/Cardano/Crypto/Leios.hs` 289-326
  (`verifyLeiosCert`).
- input-output-hk/ouroboros-leios `e04ab5561c1d96c10bd8758d17de0b04599a04f2`:
  `testnet/config/dijkstra-genesis.json` (`leiosCommitteeSize: 900`). Its Agda
  (`leios-trace-verifier/`) checks simulation traces and was not read for
  this model; the executable reference above is what the rules follow.
- gOuroboros `d0b95845`: `ledger/dijkstra/leios_header.go` 49-247,
  `ledger/verify_block.go` 155-454, `ledger/leios/certificate.go`
  102-235, `ledger/common/leios_endorser_block.go` 121-138.

## Not modelled

- The voting protocol and vote aggregation (Model `leios-peras` covers the wire side).
- Committee selection itself (ranking, ties, key age): the caller supplies
  the committee; only its size and keys matter to verification.
- BLS cryptography: a certificate's signature is valid exactly when it
  aggregates the signers' keys. The Go table test exercises the real
  curve.
- Announced EB size bounds, `maxEndorserBlockTxsSize` and the closure size
  check: arithmetic bounds already covered by unit tests.
- Fork choice and EB propagation for chain selection.
- Node-to-client inlined CertRBs in the TLA+ model: they change only the
  "no transactions" clause, which the Go table covers both ways.

## Changes that cannot affect the model

- #3192 `a21029c8` (after merging main, `8ccaf407`): a test asserts the
  validation error is set before reading its type, for a static nil check.

## Running it

```sh
make ledger-leios
# or one config:
cd specs/ledger-leios && ../../bin/tlc -config LeiosLedgerGo.cfg LeiosLedger.tla
```

The whole directory (29 configs) runs in about 15 seconds.
