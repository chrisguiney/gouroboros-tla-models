# Wakeups: close-and-replace broadcasts

`BroadcastWakeup.tla` models the close-and-replace broadcast channel that
gOuroboros uses at four sites to wake goroutines waiting for shared state.
The sites share one shape, so one module covers all four; each site's
protocol directory links here.

| Site (v0.222.0 `0c00b799`) | Notifier | Waiter | Config |
| --- | --- | --- | --- |
| `pipeline/pipeline.go` `completionChan` | `markProcessed` :1032-1037 (atomic store, then lock, close, replace) | `Fence` :1001-1012, `waitForPendingCapacity` :537-556 | `BroadcastWakeupStore.cfg`, `BroadcastWakeupStoreLive.cfg` |
| `pipeline/pipeline.go` `rawBytesFreed` | `releaseRawCborBytes` :448-462 | `reserveRawCborBytes` :409-445 | `BroadcastWakeupLocked.cfg`, `BroadcastWakeupLive.cfg` |
| `protocol/localmessagenotification/server.go` `messageAdded` | `AddMessage` :153-181 | `WaitForMessage` :216-224, `handleBlockingRequest` :303-322 | same |
| `protocol/leiosfetch/client.go` `drainedCh` | `freeLocked` :495-507, `abandon` :361-379 | `acquireWithRangeLimits` :178-243 | same |

## Questions

- `NoLostWakeup` (safety): no waiter is parked on an open channel while the
  state changed after it looked and the notifier has finished its step.
- `WakeupDelivered` (liveness, weak fairness, no timer): a waiter parked
  after a change eventually wakes.

## Verdicts

| Config | Expected | Distinct states |
| --- | --- | --- |
| `BroadcastWakeupLocked.cfg` | pass | 64 |
| `BroadcastWakeupStore.cfg` | pass | 97 |
| `BroadcastWakeupLive.cfg` | pass | 92 |
| `BroadcastWakeupStoreLive.cfg` | pass | 137 |
| `BroadcastWakeupTakeAfterUnlockBug.cfg` | `NoLostWakeup` violated | 142 |
| `BroadcastWakeupLiveTakeAfterUnlockBug.cfg` | `WakeupDelivered` violated | 270 |
| `BroadcastWakeupCloseBeforeStoreBug.cfg` | `NoLostWakeup` violated | 109 |

All four sites hold at v0.222.0. The two mutations give the invariant teeth:
`TakeAfterUnlock` is the shape of the localmessagenotification lost wakeup
before its fix (the waiter read `messageAdded` after unlocking), kept as its
regression; `CloseBeforeStore` shows why `markProcessed` must store
`completedSequence` before it closes `completionChan`.

## Reference

The reference implementations wait with STM `retry` (io-classes, used across
ouroboros-network and ouroboros-consensus): a transaction that read a TVar and
retried runs again when that TVar changes, so a change between the check and
the block cannot be missed by construction. gOuroboros rebuilds that guarantee
from a mutex plus the channel's generation, which is only correct when the
waiter checks and takes the channel in one critical section and the notifier
closes after the change is visible. Those two orderings are what the
mutations break.

## Primitives

No shared Go-concurrency module exists on `main` yet. This module defines its
primitives in place with the names a shared module would use (`gen` for a
broadcast channel's generation, `IsClosed(g)` for its closed state, a lock
holder), so it can be refitted onto `specs/common/GoConcurrency.tla` when that
lands.
