# 25: consensus eras — era transitions, era history, header check order

Three questions about how gOuroboros handles Cardano's eras and the
headers inside them:

1. When does a protocol-version update move the chain into the next era,
   and how do slots convert to epochs and times when eras have different
   epoch sizes and slot lengths? (`EraHistory.tla`)
2. In what order does `consensus/validate.go` check a header, and does it
   report the error the reference reports? (`HeaderValidation.tla`)
3. Does gOuroboros' chain selection implement the Peras certificate
   boost? (No; see [Not covered](#not-covered).)

The sources are the hard-fork combinator chapter of the consensus report
and the reference `ouroboros-consensus` and `cardano-ledger`. Where they
differ from gOuroboros, this model follows the reference.

## Slice 1: era transitions and the era history (`EraHistory.tla`)

### What the code does

gOuroboros does not compute an era history. It decodes the
local-state-query `GetEraHistory` reply (`EraHistoryResult` in
`protocol/localstatequery/queries.go`) and leaves time conversion to the
caller. Its only slot-to-epoch formula is Byron's
`ByronConfig.SlotToEpoch` (`slot / SlotsPerEpoch`) and its inverse
`ledger/byron.SlotNumberFromEpochAndSlot`. Each era package declares
`MinProtocolVersion*` and `MaxProtocolVersion*`, and `ledger/common`
names the hard-fork versions (`ProtocolVersionShelley` ...
`ProtocolVersionDijkstra`). `ledger/verify_block.go` orders the eras
(`eraOrder`, `eraAtLeast`) and names each era's starting major
(`ProtoMajor*`).

### The reference

- An era's next era starts at the epoch in which updated protocol
  parameters take effect, when their major version **equals** the next
  era's trigger and the update is stable (`ShelleyHFC.hs` 198-255,
  `isTransition`: `guard $ SL.pvMajor protVer == transitionMajorVersion`).
  The default trigger is the next era's lowest protocol version
  (`Cardano/Node.hs` 363-382).
- A `Summary` holds each known era's start and end bound (time, slot,
  epoch). An era's end is its start plus whole epochs of its own size
  (`mkUpperBound`); the last known era ends at the epoch boundary at or
  after `max(tip + 1, start) + safeFromTip` (`summarize`).
- A conversion tries each era in order; the first whose bounds admit the
  slot answers it, dividing by that era's epoch size and multiplying by its
  slot length (`Qry.hs`). Upper bounds are inclusive when epoch-aligned.
- The report requires conversions to be stable: once defined, they never
  change as blocks are applied (`time.tex` 142-177, 222-260).

### The model

The chain walks one slot at a time; each slot's block may vote to raise
the protocol major by one (the ledger lets a version follow only by one
major). The vote is adopted at the next epoch boundary, and if it is the
next era's trigger the next era starts there. Votes close once the
block's slot plus the safe zone reaches the coming boundary, which is
what "the update is stable" buys. The walk keeps the true epoch and time
of the next slot. The Summary is computed in closed form from the known
era starts and the tip, as `summarize` does, and every conversion it ever
gives is remembered.

Two era tables: `Two` (3 slots of length 3 per epoch, then 4 slots of
length 1; triggers 1 and 3) and `Three` (2/4, 3/2, 4/1; triggers 1, 2, 4).
Era 1 is Byron-like: long slots, short epochs. A major between two
triggers is an intra-era version (Alonzo 6, Babbage 8).

### The questions

1. **`SummaryMatchesWalk`**: does the closed-form conversion of the next
   slot equal walking the chain?
2. **`ConversionsStable`** ([S1], [S3]): once a slot converts, does it
   stay convertible with the same answer?
3. **`SummaryInvariants`** (`invariantSummary`): bounds line up, no empty
   era, INV-1b, INV-2b.
4. **`SummaryNonEmpty`**: the Summary names at least one era.
5. **`EraMatchesVersion`**: the chain is in the era its protocol version
   belongs to.
6. **`EraChangesAtBoundary`** (property): an era changes only at an epoch
   boundary.
7. **`GoByronFormulaInFirstEra`**: gOuroboros' Byron formula is right while
   the chain is in the first era.
8. **`GoByronSound`**: every epoch gOuroboros' Byron conversion gives, for
   a slot the Summary can convert, is the Summary's epoch.
9. **`GoByronAnswersInFirstEra`**: the fixed conversion still answers
   every slot while the chain is in the first era.

`GoByron = "Main"` is `ByronConfig.SlotToEpoch` on `main`; `"Fixed"` is
`fix/consensus-byron-slot-epoch`, where the caller sets
`ByronConfig.EndSlot` from the era history and `SlotToEpochChecked`
refuses a slot at or past it.

### The answer

| Config | Eras | States | Result |
| --- | --- | --- | --- |
| `EraHistory.cfg` (safe zone 2, 10 slots) | Two | 52 | passes |
| `EraHistoryThree.cfg` (safe zone 1, 12 slots) | Three | 157 | passes |
| `EraHistoryDeep.cfg` (16 slots) | Two | 121 | passes |

| Config (expected to fail) | Change | Invariant broken |
| --- | --- | --- |
| `EraHistoryNextEraSizeBug.cfg` | an era's bounds use the next era's epoch size | `SummaryInvariants` |
| `EraHistoryNextEraSizeWalkBug.cfg` | the same | `SummaryMatchesWalk` |
| `EraHistoryLateVoteBug.cfg` | a vote after the safe-zone deadline | `ConversionsStable` |
| `EraHistoryHorizonPlusOneBug.cfg` | one slot past the epoch-aligned horizon converts | `ConversionsStable` |
| `EraHistoryAnyBumpBug.cfg` | any version bump starts the next era | `EraMatchesVersion` |
| `EraHistoryGoByronFormulaBug.cfg` | none: gOuroboros' Byron formula past the first era | `GoByronFormulaEverywhere` |
| `EraHistoryGoByronSoundBug.cfg` | `main`'s `SlotToEpoch` (`GoByron = "Main"`) | `GoByronSound` |

Probes: `EraHistoryProbeTransitionBug.cfg` (the chain reaches the second
era), `EraHistoryProbeIntraEraBumpBug.cfg` (a bump inside an era),
`EraHistoryProbeKnownFutureEraBug.cfg` (the Summary knows the next era
before the chain is in it, the safe zone's case iii).

`ByronConfig.SlotToEpoch` (`consensus/byron/byron.go`) divides any slot
by the Byron epoch length, so past Byron it is wrong: TLC's shortest
`GoByronSoundBug` trace has the Summary know the second era (starts
`<<0, 2>>`, era 2 from slot 6) and the Byron formula give slot 9 epoch 3
where the Summary gives 2. On mainnet, slot 4514400 is Shelley epoch 208;
the formula gives 209. No production code in gOuroboros or Dingo calls it
(only tests), so nothing is wrong today, but the method's name and
receiver invite the mistake. The fix adds `EndSlot` and
`SlotToEpochChecked` (`ErrSlotAfterByron`); `SlotToEpoch` returns zero
past the end, as `EpochFirstSlot` does for its errors. With `EndSlot`
unset the fix behaves as `main`: a slot past the Summary's horizon is not
refused, which the model cannot see (it checks convertible slots only).

The decode side has one defect: the reference rejects a `GetEraHistory`
reply with no era (`Summary.hs` 630-679, "expected at least one era
summary"); gOuroboros returned an empty history for `[]` or `null`.
Fixed on `fix/localstatequery-era-history-empty`.

## Slice 2: header check order (`HeaderValidation.tla`)

### What the code does

`HeaderValidator.ValidateHeader` runs every check and returns every
error. On `main` its order is: slot, block number, previous hash, leader
VRF proof, eligibility (skipped after a failed proof), nonce VRF (TPraos),
KES period, KES signature, certificate signature, counter, VRF key
registration. When the certificate starts after the header's KES period,
the KES signature check repeats the period error and does not verify the
signature.

### The reference

- The envelope first: block number, slot, previous hash, then the era's
  extra checks (ObsoleteNode, header size, body size); the first failure
  ends validation ([H1], [H2], [H3]).
- Praos: the KES side (period window, certificate signature, KES
  signature, counter), then the VRF side (unknown pool, wrong VRF key,
  bad proof, leader value too big); the first failure ends validation
  ([P1]-[P3]).
- TPraos: the VRF side first, as one group that stops at its first
  failure (unknown pool, wrong VRF key, nonce VRF, leader VRF, leader
  value), then the OCERT rule, whose failures are all collected; before
  the certificate's start the KES signature is verified at evolution 0
  ([T1]-[T4]).

### The overlay schedule and the envelope inputs

For TPraos epochs with decentralisation d > 0 (mainnet Shelley, Allegra
and early Mary) the reference first places the slot in the overlay
schedule [T5][T7][T8][F1]. The slot at offset s in its epoch is an
overlay slot when ceiling(s·d) < ceiling((s+1)·d); its position
ceiling(s·d) makes it active when the position is a multiple of
floor(1/f), and then it belongs to genesis key number
(position / floor(1/f)) mod 7 in key order. A non-active overlay slot
fails (`NotActiveSlotOVERLAY`). In an active one the issuer must be that
genesis key's delegate (`WrongGenesisColdKeyOVERLAY`, collected), its VRF
key the delegation's (`WrongGenesisVRFKeyOVERLAY`), and both VRF proofs
valid; there is no stake and no leader value [T6]. Outside the overlay,
and for every slot when d = 0, the ordinary Praos VRF checks apply. The
OCERT rule runs in every case.

The envelope also checks ObsoleteNode (protocol major at most the node's
maximum: the header's own version in TPraos, the ledger view's in Praos
[H4]), the header size and the declared body size against the protocol
parameters [H3][F2].

On `main`, `ValidateHeaderInput` has none of these inputs. The branch
`fix/consensus-tpraos-overlay` adds `Envelope` (every mode) and `Overlay`
(TPraos), and returns `ErrMissingHeaderInput` as the only error when one
is missing.

### The model

A header is its set of defects, each named after the reference error it
causes, plus its slot offset and the epoch's d, from which the reference's
schedule gives the slot's kind (a 6-slot epoch, f = 1/2, two genesis
keys; d ranges over 0, 1/3, 1/2 and 1). The reference program runs, one
check per step, then gOuroboros' program, and the reports are compared.
`GoOrder = "Today"` is `main`'s order; `"Fixed"` is the order of
`fix/consensus-header-check-order`. `GoInputs = "Main"` is `main`'s
inputs; `"Fixed"` is `fix/consensus-tpraos-overlay`. `Inputs = "Missing"`
is a caller that leaves a required input out.

### The questions

1. **`VerdictsAgree`**: gOuroboros accepts exactly what the reference
   accepts.
2. **`GoSound`**: gOuroboros reports only defects the header has.
3. **`GoReportsEveryRefError`**: every reference error is reported.
4. **`FirstErrorAgrees`**: gOuroboros' first error is the reference's.
5. **`NoDuplicateErrors`**: no error is reported twice.
6. **`RefSound`**: the transcription of the reference reports only
   defects.
7. **`GenesisDelegateAccepted`**: a genesis delegate's header the reference
   accepts in its active overlay slot, gOuroboros accepts.
8. **`NonActiveRejected`**: gOuroboros rejects every header in a
   non-active overlay slot, with `NotActiveSlot`.
9. **`MissingInputReported`**: when the caller leaves an input out, that
   is the only error.
10. **`DZeroIsPraos`**, **`FullDAllOverlay`**, **`OverlayCount`** (an
    epoch has ceiling(E·d) overlay slots), **`EveryGenesisKeyScheduled`**
    (d = 1 reaches every genesis key): the schedule itself.

Questions 1-4 are asked only when the caller gave every input.

### The answer

| Config | Mode, order, defects | States | Result |
| --- | --- | --- | --- |
| `HeaderValidation.cfg` | Praos, Fixed, 2 | 2,124 | passes |
| `HeaderValidationTPraos.cfg` | TPraos, Fixed, 2 | 2,959 | passes |
| `HeaderValidationDeep.cfg` | Praos, Fixed, 3 | 7,832 | passes |
| `HeaderValidationTPraosDeep.cfg` | TPraos, Fixed, 3 | 11,283 | passes |
| `HeaderValidationToday.cfg` | Praos, Today, 2: questions 1-3, 6 | 2,424 | passes |
| `HeaderValidationTodayTPraos.cfg` | TPraos, Today, 2: questions 1, 2, 6 | 2,959 | passes |
| `HeaderValidationOverlay.cfg` | TPraos, Fixed, Fixed inputs, overlay and extras, 2: questions 1-8, 10 | 98,112 | passes |
| `HeaderValidationOverlayToday.cfg` | TPraos, Today, Fixed inputs, overlay and extras, 2: questions 1, 2, 6-8, 10 | 98,112 | passes |
| `HeaderValidationExtras.cfg` | Praos, Fixed, Fixed inputs, extras, 2: questions 1-6 | 3,286 | passes |
| `HeaderValidationExtrasToday.cfg` | Praos, Today, Fixed inputs, extras, 2: questions 1-3, 6 | 3,730 | passes |
| `HeaderValidationMissingInput.cfg` | TPraos, Fixed inputs, an input missing: question 9 | 6,552 | passes |
| `HeaderValidationMissingInputPraos.cfg` | Praos, the same | 225 | passes |

So on `main` gOuroboros accepts and rejects exactly what the reference
does (for the checks it makes), but:

| Config (expected to fail) | What it shows | Invariant broken |
| --- | --- | --- |
| `HeaderValidationTodayOrderBug.cfg` | Praos: a bad VRF proof is reported before a KES error | `FirstErrorAgrees` |
| `HeaderValidationTodayOrderTPraosBug.cfg` | TPraos: slot before block number; leader VRF before the VRF key | `FirstErrorAgrees` |
| `HeaderValidationTodayDuplicateBug.cfg` | an unknown pool (zero stake and no key) or a future certificate is reported twice | `NoDuplicateErrors` |
| `HeaderValidationTodayKESMissedBug.cfg` | TPraos: a future certificate hides a bad KES signature | `GoReportsEveryRefError` |
| `HeaderValidationExtrasBug.cfg` | `main`: ObsoleteNode, header and body size are not checked | `VerdictsAgree` |
| `HeaderValidationOverlayBug.cfg` | `main`: TPraos with d > 0, no overlay schedule | `VerdictsAgree` |
| `HeaderValidationOverlayGenesisBug.cfg` | `main`: a valid genesis delegate's header (offset 0) is rejected as an unknown pool, twice | `GenesisDelegateAccepted` |
| `HeaderValidationOverlayNonActiveBug.cfg` | `main`: a header with no defect in a non-active slot is accepted | `NonActiveRejected` |
| `HeaderValidationMissingInputBug.cfg` | `main`: the inputs do not exist, so a missing one is never reported | `MissingInputReported` |
| `HeaderValidationSkipGenColdBug.cfg` | mutation of the fix: the genesis cold key is not checked | `VerdictsAgree` |
| `HeaderValidationFloorPositionBug.cfg` | mutation of the fix: the overlay position rounds down (offset 2 under d = 1/2 is non-active; the fix accepts) | `VerdictsAgree` |
| `HeaderValidationSkipCounterBug.cfg` | mutation: no counter check | `GoReportsEveryRefError` |
| `HeaderValidationSkipCounterVerdictBug.cfg` | the same | `VerdictsAgree` |
| `HeaderValidationSpuriousKESBug.cfg` | mutation: an expired certificate also reports a bad KES signature | `GoSound` |

Probes: `HeaderValidationProbeKESBeforeVRFBug.cfg` (Praos reports the KES
error while the VRF proof is also bad), `HeaderValidationProbeAccumulatesBug.cfg`
(the TPraos reference reports more than one error),
`HeaderValidationProbeEnvelopeHaltsBug.cfg` (a failed envelope hides
another defect from the reference),
`HeaderValidationProbeOBFTAcceptedBug.cfg` (the reference accepts a
genesis delegate's header), `HeaderValidationProbeNonActiveBug.cfg` (a
non-active slot is reached).

TLC's shortest `TodayOrderBug` trace: D = {KESBefore, VRFBadProof}; the
reference reports `KESBefore`, gOuroboros `VRFBadProof` first. The
`TodayKESMissedBug` trace: D = {KESBefore, KESSig}; the reference reports
both, gOuroboros `KESBefore` twice.

On `main` every rejection the reference makes is reachable in gOuroboros
except the extra envelope checks (`ObsoleteNode`, `HeaderSizeTooLarge`,
`BlockSizeTooLarge`) and the overlay rejections (`NotActiveSlotOVERLAY`,
the genesis-delegate checks), whose inputs `ValidateHeaderInput` does not
carry. Without an overlay schedule, a valid genesis-delegate header in an
active overlay slot is rejected (it has no pool stake or pool VRF key),
and a pool header in a non-active overlay slot is accepted. This matters
for TPraos headers from epochs with d > 0. With `GoInputs = "Fixed"` the
verdicts agree in both orders, and in the order fix's order the first
error agrees too. The decision was to require the inputs rather than
guess, so a caller that leaves one out gets `ErrMissingHeaderInput`.

## Go tests and mutations

| Branch | Test | What it checks |
| --- | --- | --- |
| `test/consensus-eras-model` | `ledger/era_model_test.go` `TestEraProtocolVersionsMatchReference` | each era's lowest and highest version against `ProtVerLow`/`ProtVerHigh`; ranges tile 2..12; `EraForPV` agrees for every major |
| | `TestNamedProtocolVersionsLieInTheirEra` | `common.ProtocolVersion*` and `ProtoMajor*` lie in their era; `ProtoMajor*` is each era's start |
| | `TestEraOrderFollowsHardForkSequence` | `eraOrder` is era-id order; `eraAtLeast` for every pair |
| | `protocol/localstatequery/era_history_model_test.go` `TestEraHistoryMatchesSummaryModel` | replies built by the model's `summarize` (one to three eras, Origin to post-transition tips, mainnet Byron to Shelley) decode to the model's bounds and satisfy `invariantSummary` |
| | `TestEraHistorySummaryModelMainnetShelleyStart` | the arithmetic gives mainnet's Shelley start (epoch 208, slot 4492800, 89856000 s) |
| `fix/consensus-header-check-order` | `consensus/header_order_model_test.go` `TestValidateHeaderMatchesReferenceOrderTable` | every header with at most two consistent defects, both modes, real VRF, KES and Ed25519 keys: questions 1-5 |
| `fix/consensus-kes-before-start-evolution` | `consensus/validate_kes_before_start_test.go` | a future certificate: signature verified at evolution 0, a bad one rejected, no repeated period error |
| `fix/localstatequery-era-history-empty` | `protocol/localstatequery/era_history_empty_test.go` | `[]`, indefinite `[]`, null, undefined, tagged `[]` are errors; one era decodes |
| `fix/consensus-tpraos-overlay` | `consensus/validate_overlay_test.go` `TestOverlayScheduleMatchesModel` | the model's `Classify`/`GenesisIndex` cells (6-slot epoch, f = 1/2, d in 0, 1/3, 1/2, 1) and mainnet-like cells (f = 1/20, seven keys) |
| | `TestValidateHeaderTPraosOverlay` | real keys, f = 1/20, seven genesis keys: a pool header at slot 5 accepted for d = 0 and 1/2, rejected only with `ErrNotActiveSlot` for d = 1; a genesis delegate's header at slot 20 (index 1) accepted with no stake; in another key's slot `ErrWrongGenesisColdKey` and `ErrWrongGenesisVRFKey`; a wrong delegation VRF key; a bad nonce proof |
| | `TestValidateHeaderRequiresInputs` | 13 missing or unusable inputs each give only `ErrMissingHeaderInput`; Praos does not need `Overlay` but needs `Envelope` |
| | `TestValidateHeaderEnvelopeLimits` | every limit inclusive; `ErrObsoleteNode`, `ErrHeaderSizeTooLarge`, `ErrBlockSizeTooLarge` |
| `fix/consensus-byron-slot-epoch` | `consensus/byron/validate_test.go` `TestSlotToEpochStopsAtByronEnd` | mainnet boundary 4492800: slot 4492799 is epoch 207; 4492800 and 4514400 give `ErrSlotAfterByron` |

Mutations, each applied, the tests run, and the file restored:

| Mutation | Test that fails |
| --- | --- |
| `MinProtocolVersionBabbage` 7 to 8 | `TestEraProtocolVersionsMatchReference` |
| `MaxProtocolVersionConway` 11 to 10 | `TestEraProtocolVersionsMatchReference` |
| `eraOrder` ranks Conway with Babbage | `TestEraOrderFollowsHardForkSequence` |
| bound epoch decoded from the slot field | `TestEraHistoryMatchesSummaryModel` |
| slot length decoded from the epoch-length field | `TestEraHistoryMatchesSummaryModel` |
| CPraos order: VRF side before KES side | order table (29 cells) |
| TPraos order: KES side before VRF side | order table (73 cells) |
| slot checked before block number | order table (3 cells) |
| eligibility not skipped after a failed VRF key | order table (`VRFUnknown` reported twice) |
| KES evolution 1, not 0, before the certificate start | KES test |
| overlay position rounded down | schedule table, overlay test (plain slot) |
| overlay slot never non-active | schedule table, overlay test (non-active) |
| genesis cold key not checked | overlay test (another key's slot) |
| inputs, envelope and overlay disabled (`main`'s behaviour) | overlay test (4 subtests), inputs test, envelope test |
| Byron end not checked | `TestSlotToEpochStopsAtByronEnd` |

Before the order fix the table fails in 55 cells (first error and
duplicates); verdicts and soundness pass in every cell.

## Spec, reference, and gOuroboros

| Question | Report / spec | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Era transition trigger | Stable, at an epoch boundary [S3] | Next era's lowest version, exact equality, at the epoch the update takes effect [R9][R10] | Not computed (caller's job) | Not applicable |
| Era version ranges | — | `ProtVerLow`/`High` per era [R10] | Same, except Dijkstra's highest is 13 (12 in the reference, also on cardano-ledger `master`) | Deviation, unused constant; decision needed |
| `ProtocolVersionAlonzo` 6, `Babbage` 8 | — | Alonzo starts at 5, Babbage at 7 | Constants name the intra-era version; `ProtoMajor*` name the start | Agree (named differently) |
| Slot to epoch and time | Defined for past points, monotone [S1] | `Summary` and `Qry` [R1]-[R8] | Byron formula only; era history decoded, not interpreted | Byron agrees; later eras: caller's job |
| Era history with no era | — | Decoder fails [R6] | Accepted as empty | **Defect, fixed** |
| Era history with more eras than known | — | Extra eras dropped [R6] | All returned | Deviation (gOuroboros has no fixed era list) |
| Envelope order | — | Block number, slot, previous hash [H1] | Slot first | **Defect, fixed** (order branch) |
| Praos protocol order | — | KES side, then VRF side [P1] | VRF side first | **Defect, fixed** (order branch) |
| TPraos protocol order | — | VRF key, nonce VRF, leader VRF, leader value; then OCERT [T1][T2] | Leader VRF first, VRF key last | **Defect, fixed** (order branch) |
| Errors reported | Praos: one; TPraos: one per VRF group plus every OCERT failure [T4] | — | Every check's error | Superset; agree on the first error after the fix |
| KES signature before certificate start | — | Verified at evolution 0 [T3] | Not verified; period error repeated | **Defect, fixed** (KES branch) |
| Extra envelope checks | `chainChecks` [F2] | ObsoleteNode, header size, body size [H3][H4] | Not in `ValidateHeader` | **Defect, fixed** (`fix/consensus-tpraos-overlay`: required `Envelope`) |
| TPraos overlay schedule (d > 0) | OVERLAY rule [F1] | Non-active and genesis-delegate slots [T5]-[T8] | Genesis delegates rejected, non-active slots accepted | **Defect, fixed** (same branch: required `Overlay`) |
| Byron slot to epoch past Byron | — | `Summary` [R7][R8] | Byron formula for any slot | **Defect (unused API), fixed** (`fix/consensus-byron-slot-epoch`) |
| Peras certificate boost | CIP-0140 | `ChainSel` weight with certificates | Not implemented | Not covered |

## Sources

ouroboros-consensus pinned at
[`ec239d57`](https://github.com/IntersectMBO/ouroboros-consensus/tree/ec239d57f618d698b6350b48bf017b02c0c96a5f);
cardano-ledger at
[`1210d37f`](https://github.com/IntersectMBO/cardano-ledger/tree/1210d37fe6bdef32e85179ae08b7e1e8cfd75273).

| Tag | File | Lines | What |
| --- | --- | --- | --- |
| S1 | `docs/tech-reports/report/chapters/hfc/time.tex` | 142-177 | time conversion defined for past points, monotone |
| S2 | same | 179-217 | forecast range and safe zone |
| S3 | same | 222-260 | era transitions must be stable |
| R1 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/History/Summary.hs` | 90-161 | `Bound`, `mkUpperBound` |
| R2 | same | 164-173 | `slotToEpochBound` |
| R3 | same | 175-224 | INV-1b, INV-2b |
| R4 | same | 400-470 | `summarize`, the safe zone |
| R5 | same | 487-560 | `invariantSummary` |
| R6 | same | 630-679 | decoder: at least one era, unknown eras dropped |
| R7 | `.../HardFork/History/Qry.hs` | 296-345, 366-378 | bounds guards, in-era arithmetic |
| R8 | same | 496-523 | eras tried in order |
| R9 | `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/ShelleyHFC.hs` | 198-255 | `TriggerHardForkAtVersion`, exact equality |
| R10 | `ouroboros-consensus-cardano/src/ouroboros-consensus-cardano/Ouroboros/Consensus/Cardano/Node.hs`; cardano-ledger `libs/cardano-ledger-core/internal/Cardano/Ledger/Internal/Definition/Era.hs` | 363-382; 87-141 | default trigger; `ProtVerLow`/`ProtVerHigh` |
| H1 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HeaderValidation.hs` | 369-391 | `validateEnvelope` |
| H2 | same | 515-534 | `validateHeader`: envelope, then protocol |
| H3 | `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Protocol/EnvelopeChecks.hs` | 60-91 | ObsoleteNode, header and body size |
| P1 | `ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/PolyPraos.hs` | 650-694 | KES side, then VRF side |
| P2 | same | 1046-1087 | KES window, signatures, counter |
| P3 | same | 953-996 | VRF checks |
| T1 | cardano-ledger `libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/Rules/Overlay.hs` | 236-282 | overlay classification, VRF, then OCERT |
| T2 | same | 164-232 | VRF group |
| T3 | `.../Rules/OCert.hs` | 74-107 | OCERT predicates, evolution 0 before start |
| T4 | `.../TPraos/API.hs` | 543-575 | `applySTS`: every predicate failure |
| T5 | `.../Rules/Overlay.hs` | 238-282 | `overlayTransition`: Praos, non-active, or genesis-delegate slot; then OCERT |
| T6 | same | 219-236 | `pbftVrfChecks` |
| T7 | same | 314-344 | `classifyOverlaySlot`, `lookupInOverlaySchedule` |
| T8 | cardano-ledger `libs/cardano-ledger-core/src/Cardano/Ledger/Slot.hs` | 117-130 | `isOverlaySlot` |
| H4 | `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Protocol/TPraos.hs`; `.../Protocol/Praos.hs` | 69-80; 82-106 | ObsoleteNode on the header's version (TPraos) or the ledger view's (Praos) |
| F1 | cardano-ledger `eras/shelley/formal-spec/chain.tex` | 1170-1192, 1198-1274, 1280-1305 | OVERLAY: schedule functions, rules, predicate failures |
| F2 | same | 1682-1687 | `chainChecks` |
| L1 | cardano-ledger `eras/shelley/impl/src/Cardano/Ledger/Chain.hs` | 65-82 | `chainChecks` in the ledger |

## Not covered

- **Peras chain weight.** gOuroboros' chain selection (`consensus/selection*.go`)
  compares block numbers, issue numbers and VRF outputs only; nothing in
  `consensus/` or `ledger/dijkstra` adds certificate weight
  (`ledger/dijkstra` only decodes and validates the Peras protocol
  parameters). Not implemented, so there is nothing to model yet.
- Leios header checks (`leiosHeaderChecks`, Dijkstra/Praos2): covered by
  `specs/ledger-leios`.
- `VerifyBlock` (`ledger/verify_block.go`) runs its own header checks
  and stops at the first failure; it was not modelled here.
- The safe-zone size (3k/f) and the stability rule `afterVoting >= k`:
  the model uses a slot deadline that has the same effect on the Summary.
- Peras rounds in `Bound` (`boundNextPerasRound`): decoded by gOuroboros,
  not interpreted.

## Running it

```sh
scripts/run-model.sh specs/consensus-eras   # every config; *Bug ones must fail
make consensus-eras
```
