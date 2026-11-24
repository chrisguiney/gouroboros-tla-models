# 13: consensus — chain selection, operational certificates, Byron PBFT

gOuroboros' `consensus/` package decides which chain a node prefers
(`selection.go`, `selection_preference.go`), validates Praos headers
(`validate.go`: slot and block-number order, the KES period window, the
operational-certificate counter), and validates Byron PBFT headers
(`byron/pbft.go`, `byron/validate.go`: the signature-threshold window and the
header envelope).

None of this is in the network specification. Its sources are the reference
`ouroboros-consensus` and `cardano-ledger`, and the consensus technical
report. Where they differ, this model follows the reference implementation.

Two parts are state machines and are modelled in TLA+:

- `ChainSelection.tla`: a node's selection under offered forks, with
  rollback and the counter rule applied to every block it adopts.
- `PBFTWindow.tla`: Byron's rolling signature window as gOuroboros stores
  it, an immutable value over a shared append-only log.

The rest is pure functions over data (the KES window, the counter
comparison, the Byron envelope). Those are checked by table-driven Go tests
against transcriptions of the reference, not forced into TLA+. The Shelley
envelope after Origin is the exception: `ShelleyEnvelope.tla` states it as
a table, because a review found a defect in it (slice 3).

## Slice 1: chain selection (`ChainSelection.tla`)

### What the code does

`Compare(a, b)` orders two tips: the higher block number wins; at equal
height, when the tips share slot and issuer, the higher operational
certificate issue number wins; otherwise the lower VRF output wins.
`PreferCandidate(current, candidate)` is `Compare(candidate, current) > 0`,
except that from Conway (protocol major 9) two equal-height tips more than
five slots apart never switch. `PreferCandidateWithDensity` adds a fork point:
a fork more than k blocks deep is decided by the Genesis window block count
when the counts differ, and by `PreferCandidate` otherwise.

`validateOpCertSequence` checks the issuer's recorded counter `m` against
the header's issue number `n`: `m <= n`, and in CPraos also `n <= m + 1`.

### The questions

The model offers the node every one- and two-block fork from every point of
its selection, each block valid against the fork's own prefix (slot after
the previous one, counter rule against that prefix's counters). On every
offer both the reference rule and the gOuroboros rule decide.

1. **`DecisionsAgree`**: does gOuroboros ever decide an offer differently
   from the reference?
2. **`NoRollbackBeyondK`**: does a switch ever roll back more than k blocks?
3. **`OpCertCountersOnChain`**: does every block on the selection pass the
   reference counter rule against the blocks before it, across rollbacks?
4. **`SlotsIncrease`**: are slots strictly increasing along the selection?
5. Deadlock: none is possible (an offer of one block from genesis is always
   valid), and TLC confirms it.

The VRF output is a function of issuer and slot, as on a real chain (it is
computed from the VRF key, the slot and the epoch nonce). Without that, two
blocks of the same issuer and slot could carry different VRFs, which no real
chain has.

### The answer

All four hold when gOuroboros is used as `PreferCandidate` with the caller
dropping forks deeper than k ("GoPlain"):

| Config | Era rule | States | Result |
| --- | --- | --- | --- |
| `ChainSelection.cfg` (k 1, 3 blocks, 3 slots) | Babbage, unrestricted VRF | 476 | passes |
| `ChainSelectionConway.cfg` | Conway, VRF within MaxDist 1 | 480 | passes |
| `ChainSelectionTPraos.cfg` | TPraos counter (no upper bound) | 943 | passes |
| `ChainSelectionDeep.cfg` (k 2, 4 blocks, 5 slots, MaxDist 2) | Conway | 9,899 | passes |
| `ChainSelectionReference.cfg` | the reference rule alone | 480 | passes |

So `Compare` and `PreferCandidate` agree with `comparePraos` and
`SelectView`'s `preferCandidate` on every reachable pair, in both eras.

`PreferCandidateWithDensity` does not keep the k bound
(`ChainSelectionGoDensityBug.cfg`, 197 states, `NoRollbackBeyondK`
violated). TLC's shortest trace: the node holds two blocks of pool b
(issue 0, slots 1 and 2); a peer offers a fork from genesis whose second
block is pool b at slot 2 with issue 1. The rollback is 2 > k = 1, the window
counts are equal, so the call falls back to `PreferCandidate`, which prefers
the higher issue number, and the node rolls back two blocks. With unequal
counts the denser fork wins at any depth. The reference never adopts a
candidate that intersects deeper than k: candidates are built from the
VolatileDB, which holds only the last k blocks, and the report states the
precondition [R5]. Genesis in the reference keeps that bound (the Limit on
Eagerness holds the selection back instead of rolling back past k). This is
a documented design choice in gOuroboros ("the density comparison here is an
ORDERING derived from the Genesis density rule"), not a slip, so it is
recorded as a deviation and not fixed: changing it is a design decision for
the callers.

### Checking the checks

| Config (expected to fail) | Change to the gOuroboros side | Invariant broken |
| --- | --- | --- |
| `ChainSelectionLowerIssueNoBug.cfg` | lower issue number wins | `DecisionsAgree` |
| `ChainSelectionAnyIssuerBug.cfg` | issue numbers compared across issuers | `DecisionsAgree` |
| `ChainSelectionAnySlotBug.cfg` | issue numbers compared across slots | `DecisionsAgree` |
| `ChainSelectionDistanceGEBug.cfg` | Conway guard refuses at distance `>= MaxDist` | `DecisionsAgree` |
| `ChainSelectionNoUpperBoundBug.cfg` | CPraos counter without "skipped ahead" | `OpCertCountersOnChain` |
| `ChainSelectionGoDensityBug.cfg` | none: today's `PreferCandidateWithDensity` | `NoRollbackBeyondK` |

Reachability probes (also `*Bug.cfg`, each must be violated):
`ChainSelectionProbeOCertBug.cfg` (a replacement hot key does win on its
issue number), `ChainSelectionProbeVRFBug.cfg` (the VRF does decide a switch
under the Conway rule), `ChainSelectionProbeDistanceBug.cfg` (the Conway
distance rule does refuse a switch the unrestricted rule would make).

## Slice 2: the PBFT signature window (`PBFTWindow.tla`)

### What the code does

Each Byron main block charges its genesis issuer. `PBFTState` keeps the last
k issuers and refuses a block whose issuer would then appear more than
`T = floor(threshold * k)` times (`Transition`); `Observe` appends without
the check. A state is a window `[start, end)` onto an append-only log shared
with the states derived from it, with per-issuer counts cached for the log's
newest window. Extending the newest state appends in place while the log has
capacity (2k); extending an older one, as a rollback does, copies its window
into a new log.

### The questions

Every step extends any state handed out so far, by any issuer.

1. **`WindowsMatch`**: does a later step ever change a window already handed
   out (shared-log aliasing)?
2. **`CountsCacheCorrect`**: is the cached count always the count of the
   log's newest window?
3. **`AgreesWithReference`**: does gOuroboros accept and refuse exactly what
   the reference's plain window [P1][P2] does?
4. **`ThresholdHolds`** (Transition only) and **`WindowBounded`**.

### The answer

All hold, with k 3 and T 2:

| Config | States | Result |
| --- | --- | --- |
| `PBFTWindow.cfg` (Transition, 6 steps) | 12,437 | passes |
| `PBFTWindowObserve.cfg` (Transition and Observe, 6 steps) | 56,343 | passes |
| `PBFTWindowDeep.cfg` (both, 7 steps: fills a log to capacity and copies) | 530,443 | passes |

| Config (expected to fail) | Change | Invariant broken |
| --- | --- | --- |
| `PBFTWindowNoPlusOneBug.cfg` | count leaves out the block being added | `ThresholdHolds` |
| `PBFTWindowAlwaysInPlaceBug.cfg` | an older state appends to the shared log | `WindowsMatch` |
| `PBFTWindowNoDecrementBug.cfg` | cached count keeps the issuer that dropped out | `CountsCacheCorrect` |

Probes: `PBFTWindowProbeCopyBug.cfg` (an older state is extended by
copying), `PBFTWindowProbeThresholdBug.cfg` (a window holds an issuer exactly
T times), `PBFTWindowProbeFullBug.cfg` (a window fills to k),
`PBFTWindowProbeCapacityBug.cfg` (a log fills to its capacity).

The threshold arithmetic also agrees: the reference computes
`floor(0.22 * k)` in `Double`, gOuroboros `floor(22k / 100)` exactly; they
are equal for every k from 1 to 2,000,000 (checked with a script, not in the
repository).

### The modelling mistake

The first PBFT configs used T 1 with two issuers. With k 3, no window can then
hold three entries without one issuer twice, so a window never filled and
the drop-oldest path was never taken: the NoDecrement mutation and the
"window fills" probe both passed. Raising T to 2 made full windows reachable;
both now fail as they should. That is what the probes are for.

## Slice 3: the Shelley envelope after Origin (`ShelleyEnvelope.tla`)

The reference's `validateEnvelope` [R8] checks the block number, the slot
and the predecessor hash against the block before, or against Origin for
the first header: block 0, any slot, and the predecessor must be
`GenesisHash`. A Shelley header encodes `GenesisHash` as null, which
gOuroboros decodes to the zero hash.

The module compares the reference verdict with gOuroboros'
`validateSlotOrdering`, `validateBlockNumber` and `validatePrevHash` on
every predecessor (Origin or a block), slot, block number and named
predecessor (absent, zero, the previous block's hash, another hash).

| Config | Mutation | Result |
|---|---|---|
| `ShelleyEnvelope` | none (PR #3111 at `64573df5`) | `EnvelopeAgrees`, `OriginNeedsGenesis` hold |
| `ShelleyEnvelopeOriginAnyPrevBug` | PR #3111 at `1bc529c6`: `PrevIsOrigin` skips the predecessor | `OriginNeedsGenesis` fails: block 0 naming another block is accepted |
| `ShelleyEnvelopeNoOriginBug` | main at `d0b95845`: no Origin | `EnvelopeAgrees` fails: block 0 is refused |
| `ShelleyEnvelopeProbeOriginBug` | probe | `NoOriginAccepted` fails: a first header is accepted |

**The modelling mistake.** The first version of this slice (the README row
for C4) stated only the block number and slot after Origin, and so did the
fix: `PrevIsOrigin` returned early from `validatePrevHash`. Review found that
block 0 with any 32-byte predecessor then passed the whole envelope. The
invariant `OriginNeedsGenesis` would have caught it; `TestPrevHashAfterOrigin`
and `TestShelleyEnvelopeMatchesReferenceTable` (`consensus/origin_envelope_test.go`)
restate the table in Go and fail at `1bc529c6`.

Byron is not covered by this slice. Its first block names the genesis
file's hash, which gOuroboros' Byron validator does not hold, so the Byron
validator still accepts any predecessor after Origin.

## Slice 4: the Byron envelope and its predecessor kind (`ByronEnvelope.tla`)

The Byron slot and block-number rules [B1][R8], over every predecessor
kind (Origin, main, EBB), every way the caller passes the predecessor (as a
header or as a whole block), every header kind, and slots and numbers
around the predecessor's. The reference takes the predecessor's kind from
the block itself (`getTipInfo` reads `byronHeaderIsEBB`, [B1] 30-32).

| Config | gOuroboros | Result |
| --- | --- | --- |
| `ByronEnvelope` | PR #3111 at `b137d455` | `EnvelopeAgrees`, `ReprIrrelevant` hold |
| `ByronEnvelopeEBBHeaderOnlyBug` | PR #3111 at `094aeac6`: only a `*ByronEpochBoundaryBlockHeader` counts as an EBB | `EnvelopeAgrees` fails: a main block after an EBB block in the same slot is refused |
| `ByronEnvelopeProbeSharedSlotBug` | probe | `NoMainSharesEBBSlot` fails: the shared slot is reachable |

**The modelling gap.** The earlier Byron work was a Go table only
(`TestByronEnvelopeMatchesReferenceTable`), and it passed every predecessor
as a header, so it shared the defect: `ValidateByronBlockHeader` accepts
any value with a slot, number and hash, and a `*ByronEpochBoundaryBlock`
predecessor counted as a main block. Review (CodeRabbit on
`consensus/byron/validate.go:1242`) found it. The table now runs with the
predecessor as a header and as a block; at `094aeac6` the block run fails
three rows (EBB then main in the EBB's slot; EBB then EBB at the next
number, and at the same number accepted). `b137d455` classifies both
representations.

## Go tests and mutations

Branch `test/consensus-state-model` (gOuroboros, from `61046085`):

- `consensus/selection_model_test.go`:
  `TestPreferCandidateMatchesReferenceTable` (every ordered pair over a grid
  of heights, slots 0/5/6 apart, issuers, issue numbers and VRFs, at PV 8, 9,
  10; `PreferCandidate` and `Compare`), `TestPreferCandidateTableReachesEveryCase`
  (the grid reaches each rule), `TestPreferredCandidateMatchesReferenceTable`
  (every ordered list of three distinct candidates against the reference's
  filter, stable sort and pick).
- `consensus/validate_model_test.go`: `TestOpCertCounterMatchesReferenceTable`
  (both modes, counters near 0 and near the top of `uint64`),
  `TestKESPeriodMatchesReferenceTable` (both sides of each KES bound).

Each mutation was applied, the new tests run, and the file restored:

| Mutation | New tests that fail | Existing tests that fail |
| --- | --- | --- |
| `Compare`: lower issue number wins | both selection tables | (not run) |
| `Compare`: issue numbers across slots | both selection tables | `TestCompareOperationalCertificates` |
| `Compare`: issue numbers across issuers | both selection tables | (not run) |
| `Compare`: higher VRF wins | both selection tables | (not run) |
| Conway guard `>` to `>=` | `PreferCandidate` table | `TestPreferCandidateVRFDistance`, one more |
| Conway from PV 10, not 9 | both selection tables | three `PreferCandidate*` tests |
| `selectPreferredCandidate` tests against best, not current | `PreferredCandidate` table | three tests |
| counter "skipped ahead" at 2 | counter table | (not run) |
| upper bound applied in TPraos, not CPraos | counter table | `TestValidateOpCertSequence` |
| counter may go back by one | counter table | (not run) |
| KES expiry `>=` to `>` | KES table | **none** |
| KES start `<` to `<=` | KES table | six tests |

The KES expiry boundary had no covering test before. One mutation is
equivalent: weakening the "in the future" check to `kp + 1 < c0` changes no
verdict, because the expiry check then sees an underflowed evolution and
still rejects. That check only chooses the error message.

Branch `fix/consensus-byron-envelope` (from `61046085`): the Byron envelope
fix described below, with `consensus/byron/envelope_model_test.go`
(`TestByronEnvelopeMatchesReferenceTable`: origin, main or EBB predecessor;
main or EBB header; earlier, same or later slot; three block numbers).
Before the fix it reports 16 disagreements. Mutating the fix (an EBB always
shares the predecessor's number; a main block may always share the slot)
makes it fail again.

## Spec, reference, and gOuroboros

| Question | Report / spec | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Longer chain first? | Yes | Yes [R2] | Yes | Agree |
| Issue-number tie-break | — | Higher wins, only for the same slot and issuer [R1] | Same | Agree (a lower-number rule, if expected, is not what the reference does) |
| VRF tie-break | — | Lower wins; Conway: only within 5 slots [R1][R3] | Same, keyed by `ProtocolMajor >= 9` | Agree; the reference takes the flavour from the newer tip's era [R9], gOuroboros from the caller's protocol version |
| Choosing among several candidates | — | Filter by preference over current, stable sort by unrestricted order [R4] | Same, in one pass | Agree |
| Rollback bound k | Never more than k [R5] | Candidates only from within k | Not enforced by `PreferCandidate` (caller's job); `PreferCandidateWithDensity` adopts deep forks | Deviation (design), not fixed |
| Missing VRF | Cannot happen | — | Ranks below any VRF | gOuroboros-only, unreachable from valid headers |
| Counter rule | — | Praos `m <= n <= m+1`; TPraos `m <= n`; `m = 0` for a registered pool with no entry [R6][R7] | Same; the caller supplies `m` (a pointer to 0 for no entry) | Agree, except at `m = 2^64-1`, where the reference's `m + 1` wraps and refuses; unreachable |
| KES window | — | `c0 <= kp < c0 + maxKESEvo` [R6] | Same | Agree |
| Shelley slot/number order | — | Slot > previous, number = previous + 1; after Origin number 0, any slot [R8] | main: `ValidateHeaderInput` cannot express Origin, block 0 is always refused; PR #3111: `PrevIsOrigin` | **Fixed** on PR #3111 (`ShelleyEnvelope.tla`) |
| Shelley predecessor after Origin | — | `GenesisHash` only [R8] | PR #3111 at `1bc529c6`: any predecessor; at `64573df5`: absent or the zero hash | **Defect, fixed** on PR #3111 at `64573df5` |
| PBFT window | — | Last k issuers, refuse when count > floor(t*k) [P1][P2] | Same | Agree |
| Byron slot order | — | Strictly later, except a main block after an EBB [B1] | Any main block could share its predecessor's slot, an EBB too | **Defect, fixed** on `fix/consensus-byron-envelope` |
| Byron block number | — | EBB after main shares its number; all else +1; Origin 0 [B1] | Any EBB could take either number; Origin main needed 1 | **Defect, fixed** (same branch) |

## Sources

ouroboros-consensus pinned at
[`ec239d57`](https://github.com/IntersectMBO/ouroboros-consensus/tree/ec239d57f618d698b6350b48bf017b02c0c96a5f);
cardano-ledger at
[`1210d37f`](https://github.com/IntersectMBO/cardano-ledger/tree/1210d37fe6bdef32e85179ae08b7e1e8cfd75273).

| Tag | File | Lines | What |
| --- | --- | --- | --- |
| R1 | `ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/Praos/Common.hs` | 138-180, 199-283 | `comparePraos`, `ChainOrder` instance and its rules |
| R2 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Protocol/Abstract.hs` | 363-398 | `SelectView`: block number first |
| R3 | `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Config.hs` | 86-93 | Restricted VRF (5 slots) from Conway |
| R4 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/ChainDB/Impl/ChainSel.hs` | 1260-1266 | candidates sorted best first |
| R5 | `docs/tech-reports/report/chapters/storage/chainselection.tex` | 94-98 | candidates intersect within k |
| R6 | `ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/Ouroboros/Consensus/Protocol/PolyPraos.hs` | 1049-1087 | KES window, counter rule, `m = 0` for a registered pool |
| R7 | cardano-ledger `libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/Rules/OCert.hs` | 86-107 | TPraos: KES window, `m <= n` only |
| R8 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HeaderValidation.hs` | 378-423 | envelope: block number, slot, prev hash, Origin |
| R9 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Protocol/ChainSel.hs` | 40-45 | cross-era: the newer era's tiebreaker config |
| B1 | `ouroboros-consensus-cardano/src/byron/Ouroboros/Consensus/Byron/Ledger/HeaderValidation.hs` | 39-52 | Byron first block, next block number, next slot |
| P1 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Protocol/PBFT.hs` | 355-388, 428-460 | PBFT update, window size k, threshold |
| P2 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Protocol/PBFT/State.hs` | 212-233 | append, then drop the oldest |

The Praos paper was not consulted; every rule here is from the reference.

## Not modelled

- The Genesis Density Disconnection governor and the Limit on Eagerness
  (the reference's own deep-fork machinery); only the k bound they preserve.
- VRF leader eligibility (`eligibility.go`, `e34.go`, `leader.go`): pure
  arithmetic, already pinned by the shared E34 fixture corpus and the
  existing eligibility tests.
- Tachys schedules, block construction (`block.go`), KES and VRF
  cryptography (`kes/`, `vrf/`), the Byron delegation map and signatures.
- Byron PBFT's slot rule inside the protocol (`slot >= lastSignedSlot`):
  subsumed by the envelope rule above.
- Ledger conformance vectors (`internal/test/conformance/`) cover ledger
  rules and Byron blocks; none of them exercises chain selection or the
  counter rule, so nothing here duplicates them.

## Running it

```sh
scripts/run-model.sh specs/consensus      # every config; *Bug ones must fail
bin/tlc -config specs/consensus/ShelleyEnvelope.cfg specs/consensus/ShelleyEnvelope.tla
bin/tlc -workers auto -config specs/consensus/ChainSelection.cfg specs/consensus/ChainSelection.tla
bin/tlc -workers auto -config specs/consensus/ChainSelectionConway.cfg specs/consensus/ChainSelection.tla
bin/tlc -workers auto -config specs/consensus/ChainSelectionTPraos.cfg specs/consensus/ChainSelection.tla
bin/tlc -workers auto -config specs/consensus/ChainSelectionDeep.cfg specs/consensus/ChainSelection.tla
bin/tlc -workers auto -config specs/consensus/ChainSelectionReference.cfg specs/consensus/ChainSelection.tla
bin/tlc -workers auto -config specs/consensus/PBFTWindow.cfg specs/consensus/PBFTWindow.tla
bin/tlc -workers auto -config specs/consensus/PBFTWindowObserve.cfg specs/consensus/PBFTWindow.tla
bin/tlc -workers auto -config specs/consensus/PBFTWindowDeep.cfg specs/consensus/PBFTWindow.tla
```

Each `*Bug.cfg` runs the same way with its own module and must report a
violated invariant.
