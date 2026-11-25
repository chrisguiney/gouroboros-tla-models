# The ledger's lock-free hash cache and transaction-scoped memo

Two small concurrent memos in `ledger/common`, modelled one atomic operation
or one lock step at a time:

- `HashCacheSpin.tla`: `Blake2b256Cache` (`hash_cache.go`), which every block
  header hash and transaction id goes through. It claims the computation
  with a compare-and-swap, and other callers spin on `runtime.Gosched()`.
- `TxScopedMemo.tla`: `cachedLedgerState.TransactionScopedMemo`
  (`rules.go` 227-253), which shares one build of a value (today the
  transaction's script view) between the rules validating one transaction.

Both were read at gOuroboros `5c4f31c1`; neither file changed since the
concurrency inventory's `d8f5bc2a`, so its line numbers still hold.

## The questions

1. Does `compute` run at most once per transition to Ready?
2. Does every caller between two `SetCbor` calls return the same value, the
   hash of the current bytes?
3. After a `compute` panic, can the next caller retry?
4. Can a waiter return before the value is Ready?
5. Is the order of the plain `value` write and the atomic Ready store right
   under the Go memory model?
6. What happens when `compute` never returns, and can any caller reach that?
7. Can the scoped memo return a success with no value?

## The answers

| Config | Result | Distinct states |
| --- | --- | --- |
| `HashCacheSpin.cfg` (2 callers, 2 Gets each, 1 panic, 1 `SetCbor` under contract; liveness) | passes | 30,335 |
| `HashCacheSpinThree.cfg` (3 callers race the first fill) | passes | 138,485 |
| `HashCacheSpinRacingSetCbor.cfg` (`SetCbor` races `Get`, against its contract) | passes | 218,240 |
| `HashCacheSpinNoCasBug.cfg` (mutation: load then plain store) | `AtMostOneComputer` violated | 553 |
| `HashCacheSpinNoCasTwiceBug.cfg` (same) | `ComputeOncePerObject` violated | 890 |
| `HashCacheSpinReadyBeforeValueBug.cfg` (mutation: Ready, then value) | `NoRacyRead` violated | 686 |
| `HashCacheSpinReadyBeforeValueStaleBug.cfg` (same) | `ReturnsCurrentHash` violated | 778 |
| `HashCacheSpinNoSpinBug.cfg` (mutation: return on Computing) | `NoReturnBeforeReady` violated | 235 |
| `HashCacheSpinPanicKeepsComputingBug.cfg` (mutation: no Empty store on panic) | `NoOrphanComputing` violated | 412 |
| `HashCacheSpinPanicKeepsComputingSpinBug.cfg` (same) | `WaitersReturn` violated | 434 |
| `HashCacheSpinResetBeforeBytesBug.cfg` (mutation, racing `SetCbor`: reset first) | `CachedMatchesBytes` violated | 1,403 |
| `HashCacheSpinBlockingComputeBug.cfg` (a `compute` that never returns) | `WaitersReturn` violated | 250 |
| `HashCacheSpinProbeSpinBug.cfg` (probe) | violated: a caller spins | 319 |
| `HashCacheSpinProbePanicRetryBug.cfg` (probe) | violated: a retry after a panic computes | 1,220 |
| `TxScopedMemo.cfg` (the fix, 2 callers, 2 calls, 1 panic) | passes | 259 |
| `TxScopedMemoThree.cfg` (the fix, 3 callers, 2 panics) | passes | 969 |
| `TxScopedMemoNoPanic.cfg` (gOuroboros `5c4f31c1`, no panic) | passes | 86 |
| `TxScopedMemoPanicBug.cfg` (gOuroboros `5c4f31c1`) | `NoSilentEmptySuccess` violated | 134 |
| `TxScopedMemoNoShareBug.cfg` (mutation: never find the entry) | `BuildOnce` violated | 68 |
| `TxScopedMemoBuildUnderLockBug.cfg` (mutation: build under `memoMu`) | `NoLockAcrossWaitOrBuild` violated | 12 |
| `TxScopedMemoProbeWaitOnPanicBug.cfg` (probe) | violated: a caller waits on a build that panics | 221 |

1. **Yes.** `AtMostOneComputer` and `ComputeOncePerObject` hold: the
   compare-and-swap from Empty to Computing has one winner, and nothing moves
   an object out of Ready. A load followed by a plain store (`NoCas`) lets two
   callers compute.
2. **Yes, under the setters' contract.** `ReturnsCurrentHash` holds when
   `SetCbor` runs only while no `Get` is in flight, which its comments require.
   When `SetCbor` races `Get` anyway, a racing `Get` may return either hash (the
   bytes themselves are raced), but `CachedMatchesBytes` still holds: because
   `SetCbor` stores the bytes before `Reset`, no stale Ready object is ever left
   in the pointer. Resetting first (`ResetBeforeBytes`) would cache the old
   hash for good.
3. **Yes.** `NoOrphanComputing` holds: the deferred function stores Empty
   before re-panicking, and `ProbePanicRetry` shows the next caller computing.
   On the same bytes the retry panics again, which is what every caller of a
   pure function that fails would see.
4. **No.** `NoReturnBeforeReady` holds; `NoSpin` breaks it.
5. **Yes.** `value` is written with a plain store before the atomic Ready
   store, and read only after an atomic load has observed Ready. The Go memory
   model makes the store synchronized before that load, so the write
   happens before the read and there is no data race; `NoRacyRead` is the
   interleaving form of that. Swapping the two (`ReadyBeforeValue`) both races
   and lets a reader return the zero hash. A Go mutation of the same swap
   fails the new tests with wrong hashes and four race-detector reports.
6. **Waiters spin forever, at full CPU.** With a `compute` that never returns,
   `WaitersReturn` fails with a lasso: every other caller loops through
   `Gosched` with no timeout and no context. No caller can reach it: every
   `compute` is a Blake2b hash of bytes already in memory (`shelley.go` 352,
   `babbage.go` 519, `tx.go` 720, `byron.go` 298 and 2049); Byron's
   transaction id (`byron.go` 472-505) also CBOR-decodes its attributes and
   re-encodes the body, which can panic but takes no lock and does no I/O
   beyond the `sync.Once` that builds the CBOR modes. None calls `Get` on the
   same cache. A preempted `compute` only costs latency. Not a defect.
7. **Yes, in gOuroboros `5c4f31c1`.** If `build` panics, the deferred
   `close(entry.done)` publishes a nil value and a nil error, and the entry
   stays in the memo: a waiter, or any later caller on the same scoped state,
   gets `(nil, nil)`, which `NewTxScriptView` (`script/needed.go` 143-149)
   turns into an empty script view with no error. It needs a recovered panic
   and a reused scoped state, both possible for a library caller. The fix
   follows the hash cache: the panicking builder removes its entry and marks
   it abandoned before closing `done`, and waiters go round again.

## Reference comparison

| Question | Specification | Reference (cardano-ledger `1210d37f`) | gOuroboros `5c4f31c1` |
| --- | --- | --- | --- |
| Header hash, transaction id | a hash of the serialized bytes | pure functions over memoized bytes (`Cardano.Ledger.Hashes`, each era's `txIdTxBody`); no cache | `Blake2b256Cache`: same value, computed once |
| A failing computation | n/a | a lazily evaluated value re-raises its failure to everyone who forces it | hash cache: retried by the next caller (equivalent); scoped memo: `(nil, nil)` to later callers (defect, fixed on a branch) |
| A slow computation | n/a | other threads block on the thunk (blackholing), they do not spin | waiters spin on `Gosched`; bounded only by `compute` returning |

## Go tests

| Branch | Commit | What it shows | Fails without |
| --- | --- | --- | --- |
| `test/ledger-hash-cache-model` | `5b08a8e1` | `TestBlake2b256CacheWaitersWaitForReady`, `TestBlake2b256CachePanicHandsOverToWaiter`, `TestBlake2b256CacheConcurrentFirstFillComputesOnce` | killed mutations: return on Computing (zero hash), no Empty store on panic (waiter never takes over), load-then-store claim (compute ran 14-15 times), Ready before value (wrong hashes and data races) |
| `fix/ledger-scoped-memo-panic` | `2c619f5d` | `TestTransactionScopedMemoRetriesAfterBuildPanic`, `TestTransactionScopedMemoWaiterRetriesAfterBuildPanic`, and the fix | the fix: both return `<nil>` instead of `"built"` |

Existing tests already cover the sequential retry after a panic, the
first-fill value, a struct copy during a compute, and concurrent `Reset`.

## Not modelled

The struct-copy case (inventory D5: a copy made before `Reset` shares the
state object), which is a contract on callers rather than an interleaving; a
`build` that calls `TransactionScopedMemo` for its own key (inventory D2:
it would wait on itself; no caller does); and the other leaf-locked caches in
`ledger/common`, whose read-compute-write races only duplicate work.

## Changes that cannot affect the model

- #3234 `aeccd05f` (after merging main, `49845b74`): the memo lookup skips a
  nil entry, for a static nil check. Only non-nil entries are ever added, so
  the model's memo, a set of entries, is unchanged.

## Running it

```sh
scripts/run-model.sh specs/ledger-hash-cache
```
