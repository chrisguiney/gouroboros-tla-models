# the Leios ledger side

Linear Leios (CIP-0164) adds two things to a ranking block (RB): its
header may **announce** an endorser block (EB), a list of transaction
references, and the next RB may **certify** that EB with a certificate
signed by a stake-based voting committee. The certified EB's transactions
join the ledger just before the certifying RB (a "CertRB"), and a CertRB
carries no transactions of its own.

The network side (LeiosNotify, LeiosFetch, LeiosVotes) is in
[Model `leios-peras`](../leios-peras/README.md). This model covers what happens
once the blocks have arrived. It has three parts:

- `LeiosLedger.tla`: announcement, certification, EB application and
  rollback across a short chain.
- `LeiosCommittee.tla`: whether one certificate verifies against the
  committee.
- `LeiosVoting.tla`: seating the committee, collecting votes and forming
  certificates.

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

## Part 3: committee selection and vote aggregation (`LeiosVoting.tla`)

### What the reference does, and which reference

CIP-0164 at `db48da14bff1` seats the committee by **stake-based
truncation**: the top `Nc` pools by active stake, ties by ascending pool
id, every pool if fewer [C1][C2]. The persistent/non-persistent split
(wFA^LS: persistent voters plus per-EB sortition) appeared in earlier
drafts and is now only a recorded alternative ("Design Decisions",
2797-2869). ouroboros-consensus `ec239d57f618` still ships
`Ouroboros/Consensus/Committee/WFALS.hs`, but only Peras uses it
(`Peras/Vote/V1.hs`, `Peras/Cert/V1.hs`, `Peras/Voting/V1.hs`); Leios
takes its committee from cardano-ledger's `selectLeiosCommittee`
(truncation) through the ledger view, and votes and certificates from
cardano-base `cardano-crypto-leios`. So there is no persistent/
non-persistent split to model for Leios: a reference for it exists, but
not on the Leios path, and the CIP no longer specifies it.

The reference pieces, all at the revisions `ec239d57f618` builds:

- Seating: cardano-ledger `1210d37f` (identical at `b21c518e`, which
  `ec239d57f618` pins) `State/Leios.hs` 93-121. Weight is the pool's stake
  over the total active stake (`State/SnapShots.hs` 228). A key is offered
  only while honoured: `epoch < registeredIn + maxKeyAge`, with
  `maxKeyAge = ceil(maxKESEvo * slotsPerKESPeriod / epochLength) + 2`
  (`Dijkstra/Rules/Snap.hs` 157-180); a key whose proof of possession
  fails is seated keyless (cardano-base `242f1ebde40b`, the
  `cardano-crypto-leios` 0.3.0.0 that `ec239d57f618`'s CHaP index
  resolves, `Leios.hs` 156-170).
- Votes: `Leios/VoteState.hs` 224-399. A vote of a seat the node already
  holds a vote of, in that election slot, is dropped unverified
  (`AlreadyKnown`), whichever announcement it is for: duplicates and
  equivocations alike. Then `validateVote`: `SeatNotResolvable`,
  `SeatHasNoKey`, `BadSignature`. A kept vote adds its seat's weight to its
  announcement's tally; the first time a tally reaches the quorum
  (`quorum <= tally`) the votes for that announcement are aggregated
  (`aggregateLeiosCert`), once.
- Verification: `Leios.hs` 291-342 `verifyLeiosCert`.

gOuroboros does neither seating nor collection: `DijkstraLeiosCertificateState`
hands it the seated committee, and `VerifyDijkstraCertificateForMessage`
verifies a certificate (Part 2).

### What the model contains

The committee is chosen once, in `Init`, by ranking each pool by how many
pools beat it (more stake, or equal stake and a smaller id). Four
scenarios: `ties` (stakes 4,2,2,2,1, `Nc` 3, three pools tied at the seat
boundary, a badly proven key in seat 2, quorum 6/11 reachable exactly),
`wide` (four keyed seats), `few` (two pools, three seats, one keyless) and
`aged` (an aged-out key in seat 2). One election slot with two
announcements, `a` and `b` (an equivocating pair). A vote is a voter id
(including ids past the committee), an announcement and a good or bad
signature; votes arrive in any order, any number of times. `GoExactNc`
selects gOuroboros main's committee-size check (DRIFT L9);
`CallerDropsAgedKeys` says whether the caller withholds aged-out keys.

### The answers

| Invariant | Meaning | Holds |
| --- | --- | --- |
| `CommitteeSize`, `SeatOrder`, `TopStake`, `OnlyHonouredKeys` | the seating matches the CIP's rule | yes |
| `OneVotePerSeat` | one kept vote per seat per election | yes |
| `OnlyValidVotes` | kept votes are from keyed seats, well signed | yes |
| `TallyMatches` | each tally is the weight of its kept votes | yes |
| `CertAtQuorum` | a tally at quorum has its certificate | yes |
| `CertsVerify` | every formed certificate passes `verifyLeiosCert` | yes |
| `AtMostOneCert` | with tau > 1/2, at most one announcement per election is certified | yes |
| `GoAcceptsCerts` | gOuroboros accepts every formed certificate | yes, except with fewer pools than `Nc` on main (L9) |
| `GoAgrees` | over every signer set, gOuroboros accepts exactly what the reference does | yes if the caller withholds aged-out keys; **no** otherwise (L21) |

Two rules are invisible to a certificate and so to gOuroboros: one vote per
seat per election (break it and both announcements of an election are
certified, each certificate valid on its own), and key age (an aged-out key
verifies like any other). Both are the caller's.

### Checking the checks

| Config | Mutation | Fails |
| --- | --- | --- |
| `LeiosVotingNoTruncationBug` | every pool seated | `CommitteeSize` |
| `LeiosVotingTieBreakOrderBug` | ties by descending id | `SeatOrder` |
| `LeiosVotingTieBreakTopBug` | the same | `TopStake` |
| `LeiosVotingHonourAgedKeyBug` | aged-out key stays keyed | `OnlyHonouredKeys` |
| `LeiosVotingCountEquivocationBug` | a seat's vote for the other announcement kept | `OneVotePerSeat` |
| `LeiosVotingTwoCertsBug` | the same | `AtMostOneCert` |
| `LeiosVotingCountDuplicateBug` | a repeated vote counted again | `TallyMatches` |
| `LeiosVotingDuplicateCertBug` | the same | `CertsVerify` (certificate below quorum) |
| `LeiosVotingAcceptKeylessBug` | keyless seat's vote kept | `OnlyValidVotes` |
| `LeiosVotingKeylessCertBug` | the same | `CertsVerify` |
| `LeiosVotingAcceptBadSigBug` | signature not checked | `CertsVerify` |
| `LeiosVotingAggregateAllBug` | certificate aggregates the other announcement's votes | `CertsVerify` |
| `LeiosVotingStrictTallyBug` | aggregator waits for more than quorum | `CertAtQuorum` |
| `LeiosVotingStrictQuorumBug` | gOuroboros demands more than quorum | `GoAcceptsCerts` |
| `LeiosVotingGoExactNcBug` | gOuroboros main, fewer pools than `Nc` (L9) | `GoAcceptsCerts` |
| `LeiosVotingAgedKeyCallerBug` | caller hands over an aged-out key (L21) | `GoAgrees` |

Probes (expected to be violated): `LeiosVotingProbeCertBug`,
`...ProbeEquivocationBug`, `...ProbeDuplicateBug`, `...ProbeKeylessBug`,
`...ProbeUnresolvableBug`, `...ProbeBadSignatureBug`, `...ProbeSplitBug`
(both announcements hold votes).

State counts: `LeiosVoting` 264, `LeiosVotingWide` 690, `LeiosVotingFew`
72, `LeiosVotingAged` 164 distinct states.

### Go tests (gOuroboros)

Branch `test/leios-voting-model` (`eb73b151`, tests only),
`ledger/leios/voting_test.go`: the four scenarios with real BLS keys.

- `TestLeiosVotingCommitteeSeating`: the test's seating against seat lists
  read off the CIP by hand.
- `TestLeiosVotingReferenceCertificates`: walks every state of the
  reference vote collection (`ties` 9, `wide` 87, `few` 3, `aged` 11
  states; votes from every voter id, both announcements, good and bad
  signatures) and verifies every certificate formed.
- `TestLeiosVotingMutatedAggregation`: each dropped check
  (`CountDuplicate` 2,304 states, `AcceptKeyless` on `ties` and `few`,
  `AcceptBadSig`, `AggregateAllSeats`), gOuroboros against
  `verifyLeiosCert` on every certificate formed, and at least one rejected.
- `TestLeiosVotingEquivocationIsTheCallers`: counting equivocations
  certifies both announcements; gOuroboros accepts both.
- `TestLeiosVotingEverySignerSet`: every signer set, aged keys withheld
  (agrees) and handed over (disagrees only on `aged`: L21).
- `TestLeiosVotingKeylessBitsDoNotCount`: keyless seat bits beside keyed
  signatures are refused.
- `TestCertificateQuorumBoundary`: 13 threshold vectors computed from
  `verifyLeiosCert`'s rule (exact, one below, odd totals, tau 0 and 1, 2/3
  of 2^64-1).

Mutations of `certificate.go` killed: quorum `<` to `<=` (reference,
mutated and boundary tests), keyless signer counted without its key
(`KeylessBitsDoNotCount` on `few` and `aged`; on `ties` the keyless seat
has a badly proven key and fails its proof first), aggregate signature
unchecked (`AcceptBadSig`, `AggregateAllSeats`), invalid proof ignored
(`AcceptKeyless` on `ties`, `EverySignerSet`).

No BLS aggregation golden vectors exist at the pinned revisions:
`cardano-crypto-leios`'s tests are properties over generated keys, and
cardano-crypto-class's `bls12-381-test-vectors` cover the augmented
scheme, not proof-of-possession aggregation. The rc-2026w41 certificate
(Part 2) remains the only captured aggregate.

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
| Seating (Part 3; CIP `db48da14bff1`) | top `Nc` by active stake, ties by ascending pool id | same (`selectLeiosCommittee`) | caller's |
| Persistent/non-persistent voters | dropped: wFA^LS is a recorded alternative only | wFA^LS exists in consensus `ec239d57f618` but only Peras uses it | none |
| Key age | keys rotate with a time-to-live | keyless after `ceil(maxKESEvo * slotsPerKESPeriod / epochLength) + 2` epochs | caller's; not in `DijkstraLeiosCertificateState`'s contract (L21) |
| Vote weight | the pool's active stake | stake / total active stake | stake, compared with the total by cross-multiplying (same) |
| Quorum | prose "exceeds"; formula `>=` | `>=` | `>=` |
| One vote per seat per election | "at most one vote per committee member per slot" forwarded | first vote kept, later ones dropped unverified, any announcement | caller's (a certificate cannot show it) |
| Vote shape | `[announcing_rb_hash, voter_id, signature]` | same, `voter_id` a `Word16` | `LeiosPrototypeVote` same (`uint64` id); `LeiosVote` (LeiosFetch) `[slot, eb_hash, voter_id, signature]` (L22) |

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

- For Part 3: CIP-0164 at cardano-foundation/CIPs `db48da14bff1`,
  `CIP-0164/README.md`: Step 4 (374-391), Key Registration and Rotation
  (800-849), Committee Structure (851-887), Vote Structure (889-909),
  Certificate Validation (911-930), Voting & Certification (1074-1103),
  Committee Selection (1146-1158), Design Decisions (2797-2869), CDDL
  (3397-3440). ouroboros-consensus `ec239d57f618`
  `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Leios/VoteState.hs`
  224-399, `.../MiniProtocol/LeiosNotify/Client/State.hs` 397-416
  (`InvalidVoteReason`, `AcceptedVote`), `.../Leios/Types.hs` 254-278 (vote
  encoding), `.../Committee/WFALS.hs` (Peras only); `cabal.project` pins
  cardano-ledger `b21c518e` and CHaP index 2026-10-22 (cardano-crypto-leios
  0.3.0.0 = cardano-base `242f1ebde40b`). cardano-base `242f1ebde40b`
  `cardano-crypto-leios/src/Cardano/Crypto/Leios.hs` 156-170, 229-265,
  291-342. cardano-ledger `1210d37f` `State/Leios.hs` 93-121,
  `State/SnapShots.hs` 228 and 453-466, `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Snap.hs`
  157-180. gOuroboros `ebc63eab` `ledger/leios/certificate.go` 102-235,
  `ledger/common/state.go` 193-217, `ledger/common/leios.go` 71-90.

## Not modelled

- Vote timing: voting windows, late votes, pruning and the deadline (the
  wire side is in Model `leios-peras`); `LeiosVoting.tla` has one open
  election.
- Which announcements a node relays (at most two per election, OCIN), and
  the reference's thread race between recording a vote and aggregating.
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

The whole directory (56 configs) runs in about 40 seconds.
