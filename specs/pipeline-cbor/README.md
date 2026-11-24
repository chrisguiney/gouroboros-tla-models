# 16: the block pipeline, and preserved CBOR bytes

This directory covers two parts of gOuroboros that the network specification
does not: the block pipeline (`pipeline/`), which chain-sync's client feeds,
and the CBOR layer (`cbor/`) as the ledger uses it to keep a decoded value's
original bytes.

Only the pipeline is a state machine, so only it has a TLA+ model
(`BlockPipeline.tla`). The CBOR work is about pure functions over bytes, so it
was done as Go tests in gOuroboros, and is described under
[CBOR: preserved bytes and decoder limits](#cbor-preserved-bytes-and-decoder-limits).

## What the pipeline does

A caller submits raw blocks in chain order with `Submit`. Each gets the next
sequence number. Parallel decode and validate workers process blocks, so they
can finish out of order. A single apply runner puts them back in order: a
block that is next in sequence is applied at once, along with any buffered
successors; a later block waits in a buffer of at most `MaxPendingBlocks`.
For each block the runner calls the caller's `ChainContextValidator`, the
ordered ledger validation, and then `ApplyFunc`, which commits it. Any
rejection stops the pipeline. Committed blocks are then handed to the
`Results` channel.

A caller waits for an ordering boundary with `Fence` (everything submitted so
far is applied) or `WaitForDrain` (the same, documented as the step before a
rollback, so that "no earlier block is applied afterward"). chain-sync's
client calls `Submit` then `Fence` for each roll-forward, and `WaitForDrain`
before its rollback callback. `Stop` cancels the pipeline, waits for the
workers and the runner, and drains `Results`.

## The questions

1. Are blocks applied in chain order, each exactly once, however the workers
   reorder them?
2. Is anything applied after a rejected block?
3. Does `Submit`'s backpressure keep the apply buffer within
   `MaxPendingBlocks`, so that the fatal `ErrPendingLimitExceeded` never fires?
4. After a successful `WaitForDrain` and a rollback, can a block from before
   the drain boundary still be applied?
5. Can the pipeline deadlock, including when nobody reads `Results`?
6. Does shutdown drain or report every in-flight block?

## The answers

All runs: three blocks (four in the deep run), any block may be bad, `Stop`
may happen at any time, the client may `Submit`, `Fence` and `WaitForDrain`
in any order. TLC also checks for deadlock.

| Config | Result | Distinct states |
|---|---|---|
| `BlockPipeline.cfg` (with the `WaitForDrain` fix) | passes | 4,052 |
| `BlockPipelineDeep.cfg` (N=4, buffer 2, results queue 2) | passes | 19,059 |
| `BlockPipelineNoConsumer.cfg` (Results fix, nobody reads Results) | passes | 213 |
| `BlockPipelineResults.cfg` (Results fix, N=4, a reader, failures and Stop) | passes | 20,724 |
| `BlockPipelineDrainStopBug.cfg` (gOuroboros 61046085) | `NoCommitAfterRollback` violated | 1,568 |
| `BlockPipelineNoConsumerBug.cfg` (gOuroboros 61046085, nobody reads Results) | deadlock | 139 |
| `BlockPipelineCapacityBug.cfg` (mutation) | `PendingBounded` violated | 1,062 |
| `BlockPipelineFailContinuesBug.cfg` (mutation) | `AppliedInOrderOnce` violated | 1,697 |
| `BlockPipelineFailContinuesOnlyBug.cfg` (mutation) | `NoApplyAfterFailure` violated | 1,810 |
| `BlockPipelineProbeReorderBug.cfg` (probe) | violated: out-of-order arrival is reachable | 480 |
| `BlockPipelineProbeStopApplyingBug.cfg` (probe) | violated: Stop can begin during ApplyFunc | 403 |
| `BlockPipelineProbeRollbackBug.cfg` (probe) | violated: a rollback is reachable | 653 |
| `BlockPipelineProbeAllAppliedBug.cfg` (probe) | violated: a run can end with blocks unapplied | 411 |
| `BlockPipelineProbeDropBug.cfg` (probe, Results fix) | violated: a lagging reader loses a result | 341 |

1. **Yes.** `AppliedInOrderOnce` holds in every passing run. The single runner
   and the `nextSequence` check give the order; `Submit` hands out sequence
   numbers under one gate and only after a successful enqueue, so there are no
   gaps for the runner to wait on.
2. **No.** `NoApplyAfterFailure` holds: a rejection cancels the pipeline and
   the runner exits. The reference behaves the same for a linear chain: an
   invalid block is recorded and its successors are ignored [R3].
3. **Yes.** `PendingBounded` holds. `Submit` waits while
   `submitted - completed > MaxPendingBlocks`; the extra one it admits is the
   missing earliest block. Admitting one more (`CapacityBound = MaxPending + 1`)
   overflows the buffer in 1,062 states.
4. **Yes, in gOuroboros 61046085.** Once `Stop` has begun, `WaitForDrain`
   reports success at once, while the runner may still be inside `ApplyFunc`
   for an earlier block. Cancellation does not interrupt `ApplyFunc`, so that
   block commits after the caller's rollback. The counterexample is seven
   states: submit, runner starts applying, Stop, WaitForDrain succeeds,
   rollback, commit. The fix makes the drain wait for the runner to exit
   (`DrainWaitsForApply = TRUE`); with it, `NoCommitAfterRollback` holds.
   chain-sync's client itself is not exposed, because it fences every
   roll-forward before reading the next message, so no block of its own is in
   flight at a rollback; a direct caller of `WaitForDrain` with an `ApplyFunc`
   is.
5. **Only when nobody reads `Results`.** The runner hands each committed block
   to `Results` and blocks when the hand-off buffer is full, so it takes no
   more input. A later `Fence` then never returns: with the chain-sync pattern
   (`Submit`, `Fence`, repeat) and no `Results` reader, the model deadlocks in
   139 states, and the Go reproduction below stalls on the fourth block with
   a one-slot buffer. With the default 1,000-slot buffer and 64 MiB
   retained-CBOR budget it stalls after roughly 1,000 blocks, or earlier for
   large blocks, because undelivered results also keep their CBOR budget. The
   `Results` doc calls the channel "observational" and chain-sync's
   `Config.Pipeline` doc does not say it must be read.

   The fix (`ResultsNonBlocking = TRUE`) follows the reference, where
   ChainDB followers pull and never hold back chain selection: handing a
   result off never waits, and a full results buffer drops its oldest
   entry. `NoConsumer.cfg`, the `NoConsumerBug` scenario with the fix,
   has no deadlock. Two new invariants cover readers: `ReadInCommitOrder`
   (a reader sees committed blocks in commit order, each once) and
   `ReadLosslessWithoutDrops` (until a result is dropped, a reader has seen
   exactly the first blocks committed). `ProbeDropBug` shows that drops do
   happen, so the second is not vacuous. In gOuroboros the bound is
   `PrefetchBufferSize` results and `MaxRawCborBytes` bytes, separate from
   the admission budget, and drops are counted in
   `PipelineStats.ResultsDropped`.
6. **Only in aggregate.** `Stop` drains `Results` and releases every item, and
   a waiting `Fence` returns `ErrPipelineStopped`, so no caller is left
   waiting (no deadlock with `StopAllowed`). But blocks that `Submit` accepted
   and that were never applied are not reported one by one. The reference
   fulfils every queued block's promise with `FailedToAddBlock` on close [R4].
   `ProbeAllApplied` shows such runs exist.

## Checking the checks

Every invariant has a config in which it fails: `PendingBounded`
(`CapacityBug`), `AppliedInOrderOnce` (`FailContinuesBug`),
`NoApplyAfterFailure` (`FailContinuesOnlyBug`), `NoCommitAfterRollback`
(`DrainStopBug`), and deadlock freedom (`NoConsumerBug`).
`CompletedMeansApplied` has no failing config. The probes show that the
interesting situations are reached: out-of-order arrival, Stop during
`ApplyFunc`, a rollback, and runs that end with blocks unapplied.

## Modelling choices and mistakes

- The decode and validate stages are one unordered set. The runner may take
  any block from it, which covers every arrival order the workers and the
  inter-stage channels can produce. Their buffer sizes are not modelled.
- `Submit`, including its gate, capacity wait and enqueue, is one step: it is
  serialised under `submitGate`.
- `ApplyFunc` is split into "runner starts applying" (`Receive`) and
  "commit" (`Commit`), so that `Stop` and `WaitForDrain` can fall between them,
  which is exactly where the drain defect lives.
- A first draft made a rejected block's mutation trip only
  `AppliedInOrderOnce`; `FailContinuesOnlyBug` was added so that
  `NoApplyAfterFailure` is shown failing on its own.

## Go tests and fixes (gOuroboros, local branches from 61046085)

| Branch | Commit | What it does | Fails without |
|---|---|---|---|
| `fix/pipeline-drain-during-stop` | `1c1e8e8c` | `WaitForDrain` waits for the apply runner to exit before succeeding during `Stop`; test `TestBlockPipelineWaitForDrainDuringStopWaitsForApply` | the fix: "WaitForDrain returned while ApplyFunc was still committing" |
| `test/pipeline-state-model` | `5d9fc470` | `TestApplyStageCancellationStopsBufferedChain`: the model's `Commit` with `canceled`; the next buffered block is neither applied nor taken | removing `applyPending`'s context check (pending count 1, not 2) |
| `fix/ledger-body-id-without-cbor` | `625f801c` | the CBOR finding below | the fix: all seven eras fail |
| `fix/pipeline-results-do-not-block-commits` | `14fe27f8` | the result forwarder always accepts from the runner; undelivered results have their own bound and drop the oldest; tests `TestBlockPipelineFenceDoesNotWaitForResultsReader`, `TestBlockPipelineUnreadResultsDoNotHoldSubmitBudget` | the fix: the fence after block 3 and the second `Submit` time out |

Already covered by existing tests, so not duplicated: sequence-order
reordering (`TestApplyStageOrdering_OutOfOrderReordering`), the pending bound
under backpressure (`TestBlockPipelineSubmitBoundsOutOfOrderApplyBuffer`), the
committed prefix on failure
(`TestApplyStageRunner_OutOfOrderErrorPreservesAppliedPrefix`), Fence
cancellation and precedence, and the vacuous drain while `Stop` waits for the
submit gate (`TestBlockPipelineWaitForDrainConcurrentStopWithSubmitGateHeld`,
which still passes with the fix, since the runner is idle there).

The unread-`Results` stall was reproduced with a scratch test (validated
pipeline, `PrefetchBufferSize(1)`, `Submit` then `Fence` with a 500 ms
timeout, no reader): the fence after the fourth block times out with three
blocks applied. `fix/pipeline-results-do-not-block-commits` turns this into
`TestBlockPipelineFenceDoesNotWaitForResultsReader`.

## Comparison: reference and gOuroboros

The network specification has nothing on this; the comparison is with the
ChainDB add-block queue in ouroboros-consensus.

| Question | Reference (ouroboros-consensus) | gOuroboros 61046085 | Verdict |
|---|---|---|---|
| Queue and order | bounded FIFO, one thread runs chain selection per block [R1, R2] | parallel decode/validate, single in-order apply runner | same order guarantee |
| Backpressure | `addBlockToAdd` blocks when the queue is full [R1] | `Submit` waits on pending capacity and retained-CBOR budget | equivalent |
| Invalid block | recorded; it and successors ignored, thread continues [R3] | pipeline stops (fatal) | stricter; documented in chain-sync's `Config.Pipeline` |
| Close with blocks queued | every queued block gets `FailedToAddBlock` [R4] | blocks dropped; waiting `Fence` gets `ErrPipelineStopped` | aggregate report only |
| Rollback | part of chain selection, serialised with adds | caller's job after `WaitForDrain` | defect during `Stop` (fixed on a branch) |
| Result consumption | promises are optional to read; followers pull | unread `Results` stalls the runner | defect (fixed on a branch: bounded, drop-oldest, never blocks commits) |
| Decode-only `Results` (header-only, trusted decode-only) | n/a: ChainDB always applies | PR #3161 at `805d32abd`: drop-oldest like full mode, so a slow reader lost committed blocks; PR head `0dbc3775`: always lossless | defect on the PR, fixed at `0dbc3775` |

## CBOR: preserved bytes and decoder limits

**Finding (fixed on `fix/ledger-body-id-without-cbor`).** The transaction id
of every Shelley-to-Dijkstra body came from `TransactionBodyBase.Id`, which
hashes `Cbor()` unconditionally. A body with no stored CBOR, built in code or
cleared with `SetCbor(nil)` after a mutation (the workflow gOuroboros'
CLAUDE.md prescribes for re-encoding), got `Blake2b256("")`
(`0e5751c0...`) as its id: the same id for every such body. The reference
cannot reach this state: a memoized body always carries its serialization.
The fix hashes the body's current encoding when it holds no CBOR (decoded
bodies still hash their preserved bytes), and routes `DijkstraTransaction.Id`
through it. The test decodes a body whose wire form is non-preferred
(indefinite-length inputs, a four-byte fee) in each era, checks the id is the
hash of those bytes, then clears the CBOR and checks the id is the hash of the
re-encoding. An existing Babbage memo test asserted the empty-input hash and
was updated.

Audited and found consistent (no change):

- Byron `ByronTransactionBody.Id` deliberately re-encodes a canonical body,
  separate from `WireId` (the preserved bytes used for witnesses and Merkle
  proofs); this matches the reference's `serializeCborHash` transaction id and
  is covered by `ledger/byron/transaction_id_test.go`.
- `DijkstraBlockBody.Hash` re-encodes only when it has no stored CBOR, and
  flips `TxIsValid` with `SetCbor(nil)` first.
- Public setters that change encoded state (`Set*Presence`,
  `SetValidityIntervalUpperBound`) clear stored CBOR and the id memo.
- Decoder limits: blocks and ledger data allow 16,384 levels of nesting
  (`MaxNestedLevels`), peer protocol messages 1,024
  (`MaxUntrustedNestedLevels`). Indefinite lengths are accepted, as RFC 8949
  and the reference's cborg allow. Non-preferred integers are accepted and
  their bytes preserved (exercised by the new test). Duplicate map keys are
  rejected by default and resolved last-wins in `DecodeLenient`, which is used
  for pre-Conway structures where the reference used `Map.fromList`
  (protocol version < 9). One observation: 16,384 levels sits just above what
  a transaction can hold under today's 16,384-byte `maxTxSize`; raising that
  parameter would let a valid transaction nest deeper than gOuroboros
  accepts. Not a defect today.

Not covered: a full search for every site that mutates a decoded value and
then marshals it. Spot checks of setters, the `TxIsValid` paths and block
transaction reconstruction found no case.

## Sources

| Tag | Source |
|---|---|
| R1 | IntersectMBO/ouroboros-consensus `ec239d57f618d698b6350b48bf017b02c0c96a5f`, `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/ChainDB/Impl/Types.hs` 602-618 (`ChainSelQueue`), 664-696 (`addBlockToAdd`) |
| R2 | same commit, `.../ChainDB/Impl/Background.hs` 755-815 (`addBlockRunner`) |
| R3 | same commit, `.../ChainDB/Impl/ChainSel.hs` 506-516 (ignore a known invalid block), 1487-1495 (`addInvalidBlock`), 1588-1595 (`ignoreInvalidSuc`) |
| R4 | same commit, `Background.hs` 779-800 (`bracketOnError` handler) and `Types.hs` 786-798 (`closeChainSelQueue`) |
| G | blinklabs-io/gouroboros `61046085`, `pipeline/pipeline.go`, `pipeline/apply_stage.go`, `protocol/chainsync/client.go` 1720-1770 and 1870-1910 |
| C | RFC 8949 sections 3 and 5 (well-formedness, indefinite lengths, preferred serialization) |

## Not modelled

Metrics, the retained-CBOR byte budget (other than as a reason the stall comes
sooner), validation in trusted decode-only and header-only modes (their
`Results` delivery is modelled by `HasApplyFunc`), panics in stages (parent
context cancellation without `Stop` is in `PipelineLifecycle.tla`), more than one client, and Leios or Peras
messages in the reference queue.

## Lossless results (`WithLosslessResults`)

A caller that receives decoded blocks through `Results`, as Dingo does in
trusted decode-only mode where no `ApplyFunc` runs, needs one result per
submitted block. The non-blocking default drops the oldest undelivered result
when a reader falls behind, which would lose blocks for such a caller, and a
Dingo test that waits for every result deadlocked against it. The opt-in
`WithLosslessResults` restores lossless delivery. Switch `LosslessResults`:
while the Results buffer is full the forwarder takes nothing more, so the
runner waits for the reader. Drops are allowed only once Stop has begun.

| Config | States | Result |
| --- | --- | --- |
| `BlockPipelineLossless.cfg` (reader, failures, Stop) | 19,838 | passes, including `LosslessNeverDropsBeforeStop` |
| `BlockPipelineLosslessStop.cfg` (no reader, Stop available) | 15,089 | passes: Stop always completes |
| `BlockPipelineLosslessNoConsumerBug.cfg` (no reader, no Stop) | | deadlocks, as documented: committing waits for a reader |
| `BlockPipelineProbeLosslessHoldsBackBug.cfg` | | probe violated: the runner is held back |

Ignoring the switch (letting the forwarder drop while not stopping) violates
`LosslessNeverDropsBeforeStop`; checked by a temporary mutation.

This does not change anything on the wire. A slower commit only delays the
chain-sync client's next request, which the protocol allows; the reference
also applies backpressure to block fetching through its bounded add-block
queue, and never makes chain selection wait on a follower, which the default
mode still follows.

### Decode-only modes are lossless by default

Review of PR #3161 at `805d32abd` found that `WithHeaderOnly()` and
`WithTrustedDecodeOnly()` pipelines, which have no `ApplyFunc` and whose only
output is `Results`, used the drop-oldest default: with a one-result bound and
a reader 300 ms late, 1 of 8 blocks arrived. The model shared the defect: it
had no notion of a pipeline without an `ApplyFunc`, so no invariant could see
it. Switch `HasApplyFunc` (FALSE: header-only or trusted decode-only) and
switch `DecodeOnlyLossless` (TRUE: the fix at `0dbc3775`, where `Start`
makes `Results` lossless when there is no `ApplyFunc`) now feed `Lossless`,
which `Forward` uses. Invariant `DecodeOnlyNeverDropsBeforeStop` says a
pipeline without an `ApplyFunc` drops nothing before Stop, whether or not the
caller asked for `WithLosslessResults`.

| Config | States | Result |
| --- | --- | --- |
| `BlockPipelineDecodeOnly.cfg` (no `ApplyFunc`, no `WithLosslessResults`, reader, Stop) | 19,838 | passes, including `DecodeOnlyNeverDropsBeforeStop` |
| `BlockPipelineDecodeOnlyDropBug.cfg` (`805d32abd`: `DecodeOnlyLossless = FALSE`) | | `DecodeOnlyNeverDropsBeforeStop` violated |

Every other config sets `HasApplyFunc = TRUE`, so its results are unchanged.
Go test `TestDecodeOnlyResultsAreLosslessByDefault` reproduces the drop at
`805d32abd` (7 of 8 dropped in both modes) and passes at `0dbc3775`. Dingo's
trusted decode-only pipeline already passes `WithLosslessResults()`, which is
now redundant there but harmless. The `ARCHITECTURE.md` rewrite of the result
accounting in the same commit is documentation and cannot affect the model.

## Running it

```sh
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipeline.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineDeep.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineNoConsumer.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineResults.cfg specs/pipeline-cbor/BlockPipeline.tla
# expected to fail:
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineDrainStopBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineNoConsumerBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineCapacityBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineFailContinuesBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineFailContinuesOnlyBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineProbeReorderBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineProbeStopApplyingBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineProbeRollbackBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineProbeAllAppliedBug.cfg specs/pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/pipeline-cbor/BlockPipelineProbeDropBug.cfg specs/pipeline-cbor/BlockPipeline.tla
# or all at once:
scripts/run-model.sh specs/pipeline-cbor
```

## Lifecycle at goroutine granularity (`PipelineLifecycle.tla`)

`BlockPipeline.tla` checks what the pipeline decides. `PipelineLifecycle.tla`
checks how its goroutines finish: one step per lock acquire or release, per
channel send, receive, close or `select` choice, per WaitGroup wait and per
context cancel, with each goroutine (submitter, decode worker, apply runner,
result forwarder, metrics collector, Stop and its runner-joining helper, a
`Results` reader, a `WaitForDrain` caller) as its own process. `ApplyFunc`
may return, block forever, call `Stop`, or call `WaitForDrain`. Switch
`PR3161` swaps in open PR #3161's forwarder, `Stop` and `WaitForDrain`
(`0dbc3775`). Read at gOuroboros `5c4f31c1`; `pipeline/` is unchanged since
the inventory's `d8f5bc2a`. Deadlock checking is on: a state where nothing
moves while an API call (`Stop`, `Submit`, `WaitForDrain`) is still waiting is
a deadlock; one where only parked goroutines remain is judged by
`NoLeakWhenQuiescent`.

| Config | Result | Distinct states |
| --- | --- | --- |
| `PipelineLifecycle.cfg` (2 blocks, reader, owner and second `Stop`, parent cancel) | passes | 17,752 |
| `PipelineLifecycleDeep.cfg` (3 blocks, no reader) | passes | 25,596 |
| `PipelineLifecycleNoReader.cfg` | passes | 4,341 |
| `PipelineLifecyclePR.cfg` (PR #3161) | passes | 16,374 |
| `PipelineLifecyclePRNoReader.cfg` (PR #3161, 3 blocks) | passes | 9,378 |
| `PipelineLifecycleDrainPR.cfg` (PR #3161, a drainer) | passes, with `NoCommitAfterDrain` | 48,588 |
| `PipelineLifecycleApplyCallsDrain.cfg` (`ApplyFunc` calls `WaitForDrain`) | passes | 4,603 |
| `PipelineLifecycleDrainStopBug.cfg` (gOuroboros `5c4f31c1`, a drainer) | `NoCommitAfterDrain` violated | 8,336 |
| `PipelineLifecycleBlockingApplyBug.cfg` (`ApplyFunc` never returns) | deadlock: `Stop` waits forever holding `mu` | 2,619 |
| `PipelineLifecycleApplyCallsStopBug.cfg` (`ApplyFunc` calls `Stop`) | deadlock | 578 |
| `PipelineLifecycleApplyCallsStopOwnerBug.cfg` (same, owner's `Stop` holds `mu`) | deadlock | 2,909 |
| `PipelineLifecycleApplyCallsDrainPRBug.cfg` (PR #3161, `ApplyFunc` calls `WaitForDrain`) | deadlock | 3,657 |
| `PipelineLifecycleParentCancelLeakBug.cfg` (parent cancel, no `Stop`) | `NoLeakWhenQuiescent` violated | 814 |
| `PipelineLifecycleParentCancelLeakPRBug.cfg` (same, PR #3161) | `NoLeakWhenQuiescent` violated | 311 |
| `PipelineLifecycleMuAcrossApplyBug.cfg` | `MuNotHeldAcrossApply` violated (by design) | 3,065 |
| `PipelineLifecycleCloseBeforeJoinBug.cfg` (mutation) | `NoPanic` violated | 1,789 |
| `PipelineLifecycleSkipRunnerJoinBug.cfg` (mutation) | `JoinedAfterStop` violated | 3,388 |
| `PipelineLifecycleNoReleaseActiveBug.cfg` (mutation) | `AllReleasedAfterStop` violated | 4,375 |
| `PipelineLifecycleReleaseTwiceBug.cfg` (mutation) | `BudgetMatchesActive` violated | 4,151 |
| `PipelineLifecycleProbeGateWaitBug.cfg` (probe) | violated: `Stop` waits for the gate a `Submit` holds | 644 |
| `PipelineLifecycleProbeStopDrainBug.cfg` (probe) | violated: `Stop` takes results while it waits | 3,416 |

Invariants that hold in every passing config: `NoPanic` (no send on a closed
channel, no double close), `BudgetMatchesActive` (`rawBytesInUse` is one
reservation per tracked item plus the submitter's own), `AllReleasedAfterStop`
and `JoinedAfterStop` (once `Stop` returns, every reservation is back and the
worker, runner, forwarder, metrics collector and helper have exited), and no
deadlock. Lock order: `mu` -> `submitGate` is the only edge between the two
non-leaf locks; nothing takes `mu` while holding the gate, so no cycle exists
on locks alone. The deadlocks below are cycles through a join, not through
lock order.

Findings:

- **`Stop` waits behind `ApplyFunc`, holding `mu` (inventory C5, confirmed).**
  `ApplyFunc` has no context, so `Stop`'s cancel cannot reach it; `Stop`
  waits for it while holding `mu`, and a second `Stop` (or `Start`) waits on
  `mu` behind it. With an `ApplyFunc` that returns this is a join, not a
  defect; with one that never returns, `Stop` never returns. The reference
  interrupts its add-block thread with an asynchronous exception on close,
  which Go cannot do.
- **New: an `ApplyFunc` that calls `Stop` deadlocks.** `Stop` waits for the
  runner, which is running that `ApplyFunc`; if the owner's `Stop` already
  holds `mu`, the inner one waits for `mu` instead. Either way neither returns.
  Reproduced on `5c4f31c1` and on PR #3161 with a scratch test (inner `Stop`
  had not returned after 2 s). Nothing documents that `ApplyFunc` must not
  call `Stop`.
- **New, PR #3161 only: an `ApplyFunc` that calls `WaitForDrain` during
  `Stop` deadlocks.** #3161 makes `WaitForDrain` wait for the runner once
  `Stop` has begun, and the runner is the caller. On `5c4f31c1` the same call
  returns nil. Reproduced on `0dbc3775` (both the drain and `Stop` hang past
  2 s) and not on `5c4f31c1`. A conflict for #3161 to resolve, not a reason to
  revert its drain fix, which `DrainStopBug`/`DrainPR` confirm.
- **A parent cancel without `Stop` leaks (inventory C4, confirmed, on both
  heads).** Workers, runner and metrics collector exit; `forwardResults`
  never does (it exits only when `Stop` closes `resultsQueue`; #3161 notices
  the cancel but still waits for the close), and items stranded in the
  channels keep their budget. A scratch run held 6,414 retained bytes and the
  forwarder goroutine until `Stop`. `Stop` afterwards cleans up completely,
  which the new test pins. Exiting the forwarder on the cancel alone would not
  release the stranded items; making the pipeline clean up without `Stop`
  means running `Stop`'s cleanup on the cancel.
- **C6 (a `Submit` holds the gate while `Stop` waits for it) is reachable but
  never a deadlock**, because `Stop` cancels before taking the gate.
- **C7 (the budget clamp at zero hides a double release)**: no double release
  is reachable; `ReleaseTwice` shows the clamp would hide one from the budget
  but not from `BudgetMatchesActive`.

Go tests, on `test/pipeline-lifecycle-model` (`081686a1`, from `5c4f31c1`):
`TestBlockPipelineStopAfterParentCancelReleasesEverything` (budget, active
items and goroutines after a parent cancel and `Stop`, with `goleak`) and
`TestBlockPipelineStopWaitsForApplyFuncInProgress` (`Stop` does not return
while `ApplyFunc` runs, then joins everything). Killed mutations: removing
`releaseActiveItems` (12,828 bytes left), removing the runner join (`Stop`
returned while `ApplyFunc` ran). No fix branch: the two new deadlocks need a
decision (document "`ApplyFunc` must not call `Stop` or `WaitForDrain`", or
give `ApplyFunc` a context), and the second belongs in #3161.

```sh
scripts/run-model.sh specs/pipeline-cbor
```
