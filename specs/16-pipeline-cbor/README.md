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
| `BlockPipeline.cfg` (with the `WaitForDrain` fix) | passes | 3,846 |
| `BlockPipelineDeep.cfg` (N=4, buffer 2, results queue 2) | passes | 18,238 |
| `BlockPipelineDrainStopBug.cfg` (gOuroboros 61046085) | `NoCommitAfterRollback` violated | 1,568 |
| `BlockPipelineNoConsumerBug.cfg` (gOuroboros 61046085, nobody reads Results) | deadlock | 139 |
| `BlockPipelineCapacityBug.cfg` (mutation) | `PendingBounded` violated | 1,062 |
| `BlockPipelineFailContinuesBug.cfg` (mutation) | `AppliedInOrderOnce` violated | 1,697 |
| `BlockPipelineFailContinuesOnlyBug.cfg` (mutation) | `NoApplyAfterFailure` violated | 1,810 |
| `BlockPipelineProbeReorderBug.cfg` (probe) | violated: out-of-order arrival is reachable | 480 |
| `BlockPipelineProbeStopApplyingBug.cfg` (probe) | violated: Stop can begin during ApplyFunc | 403 |
| `BlockPipelineProbeRollbackBug.cfg` (probe) | violated: a rollback is reachable | 653 |
| `BlockPipelineProbeAllAppliedBug.cfg` (probe) | violated: a run can end with blocks unapplied | 411 |

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
blocks applied. It is not fixed: making the commit path independent of the
observational channel, or requiring a reader, is a design decision.

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
| Result consumption | promises are optional to read | unread `Results` stalls the runner | defect (written up) |

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
sooner), trusted decode-only and header-only modes, panics in stages, parent
context cancellation without `Stop`, more than one client, and Leios or Peras
messages in the reference queue.

## Running it

```sh
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipeline.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineDeep.cfg specs/16-pipeline-cbor/BlockPipeline.tla
# expected to fail:
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineDrainStopBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineNoConsumerBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineCapacityBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineFailContinuesBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineFailContinuesOnlyBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineProbeReorderBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineProbeStopApplyingBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineProbeRollbackBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
bin/tlc -workers auto -config specs/16-pipeline-cbor/BlockPipelineProbeAllAppliedBug.cfg specs/16-pipeline-cbor/BlockPipeline.tla
# or all at once:
scripts/run-model.sh specs/16-pipeline-cbor
```
