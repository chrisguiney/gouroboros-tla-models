# 18: consensus/genesis — Ouroboros Genesis density

gOuroboros' `consensus/genesis` package offers the Genesis density rule as a
chain ordering: `GenesisSelector.Compare` and `Preferred` over
`ChainFragment`s, `ComputeGenesisWindow` (sgen = ceiling(3k/f)),
`SimpleChainFragment` (a fragment described only by its intersection slot,
tip slot and block count), and `ShouldUseGenesis` (a slots-behind threshold).
Nothing else in gOuroboros calls it; the tip-level ordering that does route
on fork depth, `consensus.PraosChainSelector.CompareWithDensity`, is in
model 13.

The reference, ouroboros-consensus, has no density ordering. Genesis there is
three mechanisms around ordinary Praos selection: the Genesis Density
Disconnection governor (GDD) drops peers whose chains lose on density, the
Limit on Eagerness (LoE) keeps the selection within k blocks of the prefix
all candidates share, and ChainSync Jumping (CSJ) limits how many peers send
headers. This model puts gOuroboros' ordering beside GDD and the LoE and asks
where they agree.

## The model (`GenesisDensity.tla`)

A syncing node has two or three peers. Each peer sends the headers of its
chain one at a time (any slot after its last one) and may go idle (it has
nothing more for now). A chain is its list of block slots after the
immutable tip at slot 0; equal prefixes are shared blocks. In every state:

- the reference side computes the LoE fragment (the prefix every candidate
  shares), each peer's window lower and upper bounds, and the peers GDD
  would drop, transcribed from `densityDisconnect`. GDD compares two peers
  only when their clipped fragments start with different blocks
  (`AF.lastPoint` is a fragment's oldest point, or its anchor when empty);
- the gOuroboros side builds one `ChainFragment` per peer and runs
  `Preferred`: most blocks in the window, then most blocks in total, then
  the earlier candidate. It runs `Preferred` a second time on the
  candidates trimmed to at most k blocks past the LoE tip, as the
  reference's chain selection sees them (`trimToLoE`).

Switches pick the variant: `Anchoring` (fragments start at the LoE tip, or at
each one's own intersection with our selection, as the `ChainFragment`
contract says), `Counter` (exact count or `SimpleChainFragment`'s estimate),
`Adopt` (the reference LoE trim, or the caller adopting `Preferred` whole) and
`KGuard` (the reference's `offersMoreThanK` guard; off is a mutation).

### Invariants

1. **`GoPicksDensest`**: `Preferred` picks a chain with the most blocks in
   the window after the intersection, as the reference counts them.
2. **`GoChoiceLosesOnlyOnTie`**: GDD drops the chain `Preferred` picked only
   when another chain ties it exactly. A tie drops both in the reference
   ("the honest chain is expected to have a strictly higher density").
3. **`GoTrimmedPicksDensest`**: on the candidates trimmed to the LoE,
   `Preferred` picks one with the most window blocks among the trimmed
   candidates.
4. **`LoEBound`**: the node never selects more than k blocks past the prefix
   all candidates share.
5. **`KGuardHolds`**: a peer still sending its window is dropped only
   because some peer offers more than k blocks after the intersection (so
   competing honest peers near the tip survive).

### Configurations

| Config | Setting | States | Result |
| --- | --- | --- | --- |
| `GenesisDensity.cfg` | 2 peers, k=1, sgen=3, slots 1..5 | 2,704 | all five hold |
| `GenesisDensityThree.cfg` | 3 peers, k=1, sgen=3, slots 1..4 | 27,000 | all five hold |
| `GenesisDensityWideK.cfg` | 2 peers, k=2, sgen=6, slots 1..7, 4 blocks | 39,204 | all five hold |
| `GenesisDensityOwnAnchorBug.cfg` | fragments at their own intersection with our selection | | `GoPicksDensest` fails |
| `GenesisDensityTrimOwnAnchorBug.cfg` | trimmed candidates, fragments at their own intersection | | `GoTrimmedPicksDensest` fails |
| `GenesisDensitySimpleCounterBug.cfg` | `SimpleChainFragment` estimate | | `GoChoiceLosesOnlyOnTie` fails |
| `GenesisDensityGoNoLoEBug.cfg` | caller adopts `Preferred` whole | | `LoEBound` fails |
| `GenesisDensityNoKGuardBug.cfg` | reference without `offersMoreThanK` (mutation) | | `KGuardHolds` fails |
| `GenesisDensityProbeTieBug.cfg` | probe | | GDD drops two tied peers at once |
| `GenesisDensityProbeShorterBug.cfg` | probe | | `Preferred` picks a shorter, denser chain |
| `GenesisDensityProbeDropWhileSendingBug.cfg` | probe | | GDD drops a peer still sending |
| `GenesisDensityProbeSameFirstBlockBug.cfg` | probe, 3 peers | | two clipped fragments start with one block and end at different ones |
| `GenesisDensityProbeTrimBug.cfg` | probe | | trimming to the LoE changes `Preferred`'s pick |

sgen is ceiling(3k/f), so never below 3k; the configs use f = 1.

The counterexamples, in slots after the immutable tip:

- Own anchor: our selection is `<1, 2>`, peer a has sent nothing yet, peer
  b sent `<1>`. b's block is on our selection, so its fragment after its own
  intersection is empty; the two fragments tie at zero and `Preferred` keeps
  a, although b has one block in the window at the shared anchor.
- Simple counter: a = `<4, 5>`, b = `<1>`, window slots 1..3. a has no block
  in the window, b has one. The estimate gives both one (a: 2 x 3 / 5 = 1),
  the tie goes to the longer a, and GDD would drop a.
- No LoE: a has sent nothing, b = `<1, 2>`; the shared prefix is empty and
  adopting b goes two blocks past it, with k = 1.
- Trimmed, own anchor: our selection is `<1>`, a has sent nothing, b =
  `<1>`; b's trimmed fragment after its own intersection is empty, so the
  tie keeps a although b has one trimmed block in the window.
- Same first block (probe): a = `<1, 2>`, b = `<1>`, c has sent nothing.
  The LoE is the immutable tip; a and b start with the same block, so GDD
  never compares them.
- Trim (probe): a = `<1>`, b = `<2, 3>`, k = 1. Whole, b has two window
  blocks and wins; trimmed to `<1>` and `<2>` they tie and a wins.
- No k guard: a = `<1, 2>`, b = `<2>` (k = 2, sgen = 6). b is still sending
  and could reach two blocks; a offers only two (not more than k). Without
  the guard GDD drops b.

## Go tests

Branch `test/consensus-genesis-model`,
`consensus/genesis/genesis_model_test.go`:

- `TestGenesisModelPreferredAgainstGDD` enumerates every state of the
  three passing configurations (2,704, 140,608 and 106,276 states; the last
  two use one more slot than the TLA+ configs, which TLC is too slow for)
  and checks `Preferred` on fragments anchored at the LoE tip against a Go
  transcription of `densityDisconnect`: the pick is the reference's densest
  (then longest, then first) chain, GDD drops it only on an exact tie, and a
  peer still sending is dropped only when some peer offers more than k. A
  second pass runs `Preferred` on the candidates trimmed to k blocks past
  the LoE tip and checks it picks the densest trimmed candidate. It
  requires that the density-beats-length, tie-drops-both,
  dropped-while-sending and trim-changes-the-pick cells are reached.
- `TestGenesisModelCompareCells`: `Compare`'s table, window count by total
  length.

Mutations of `genesis.go` each fail the tests and were reverted: ignoring the
window count, preferring the shorter chain on a tie, dropping the length
tie-break, `>=` in `Preferred` (last candidate wins ties), and a window one
slot short.

Branch `fix/genesis-window-estimate-rounding`: `SimpleChainFragment`
computed `uint64(float64(Blocks) * (float64(window) / float64(span)))`.
The float quotient rounds down before the multiply, so an exact case such as
22 blocks, window 15, span 22 gave 14 instead of 15, and counts near 2^64
converted out of range (2^63 for an expected 2^64 - 2). The fix computes
floor(Blocks x window / span) with `bits.Mul64` and `bits.Div64`;
`TestSimpleChainFragmentEstimateIsExactFloor` fails before it (four of six
cases) and passes after.

## Spec, reference, and gOuroboros

| Question | Genesis paper | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Window | sgen slots after the intersection | Slots after the LoE tip, before succ(tip) + sgen [G3] | `BlockCountInWindow(sgen)` from the fragment's intersection | Agree when anchored at the LoE tip |
| sgen (Shelley) | — | `computeStabilityWindow` = ceiling(3k/f) [W1] | `ComputeGenesisWindow`, ceiling | Agree |
| sgen (Byron) | — | 2k [W2] | No Byron variant; 3k/f with f = 1 gives 3k | gOuroboros-only gap; nothing calls it for Byron |
| Anchor | Common intersection | LoE tip, shared by all candidates [G1] | Each fragment's own intersection with our selection | **Deviation**: windows can start at different slots (`OwnAnchorBug`); a caller must anchor every fragment at one point |
| Denser wins | Yes | Sparser peer dropped [G3] | Higher count ordered first | Agree (with a common anchor and an exact count) |
| Exact tie | — | Both peers dropped [G3 478-486] | Longer total wins, then the first candidate | Deviation (design: an ordering cannot drop both); see `ProbeTieBug` |
| Unknown tail of a window | — | Upper bound: a peer still sending is not dropped until it cannot win [G2] | Only the count received so far | Deviation: gOuroboros decides early; harmless only if the caller waits |
| Near the tip | Falls back to longest chain | `offersMoreThanK` guard [G2][G3]; GDD and LoE off once caught up (GSM) | `Compare` always uses density; `ShouldUseGenesis` is a slots-behind threshold the caller applies | No guard in `GenesisSelector`; model 13's `CompareWithDensity` routes on fork depth instead |
| LoE | Selection never commits past the common prefix + k | `trimToLoE` [G4] | None | **Gap** (`GoNoLoEBug`): a caller adopting `Preferred` whole can go further |
| Window count source | Exact | Exact header count | `SimpleChainFragment` estimates from the span | **Deviation** (`SimpleCounterBug`); the estimate's float rounding **fixed** |

## Sources

ouroboros-consensus pinned at
[`ec239d57`](https://github.com/IntersectMBO/ouroboros-consensus/tree/ec239d57f618d698b6350b48bf017b02c0c96a5f).

| Tag | File | Lines | What |
| --- | --- | --- | --- |
| G1 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Genesis/Governor.hs` | 294-319 | `sharedCandidatePrefix`: the LoE fragment |
| G2 | same | 387-447 | `densityDisconnect`: clipped fragment, bounds, `offersMoreThanK` |
| G3 | same | 448-501 | `densityDisconnect`: losing peers, window end |
| G4 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/ChainDB/Impl/ChainSel.hs` | 907-950 | `trimToLoE`: at most k blocks past the LoE tip |
| G5 | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Client/State.hs` | 72-76 | `csLatestSlot`: unset until a header arrives |
| W1 | `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Ledger.hs` | 162-179 | Shelley `eraGenesisWin` = stability window |
| W2 | `ouroboros-consensus-cardano/src/byron/Ouroboros/Consensus/Byron/Ledger/Ledger.hs` | 338, 351 | Byron `eraGenesisWin` = 2k |

## Not modelled

- ChainSync Jumping: gOuroboros has none.
- The Genesis State Machine (PreSyncing, Syncing, CaughtUp), which switches
  GDD and the LoE off: it depends on wall-clock tip age and peer idleness;
  gOuroboros' `ShouldUseGenesis` is a pure threshold, covered by the
  existing unit tests.
- Headers beyond the forecast horizon (`csLatestSlot` ahead of the
  candidate): the model takes a peer's latest slot to be its candidate's
  tip.
- GDD's re-evaluation after a disconnection (the LoE moving as peers
  leave): every state is one evaluation.
- Praos tie-breakers between equal-length chains: model 13.
- The float helpers `Density` and `ExpectedDensity`: retained for
  compatibility, not used by `Compare`.

## Running it

```sh
scripts/run-model.sh specs/18-consensus-genesis   # every config; *Bug ones must fail
bin/tlc -workers auto -config specs/18-consensus-genesis/GenesisDensity.cfg specs/18-consensus-genesis/GenesisDensity.tla
```
