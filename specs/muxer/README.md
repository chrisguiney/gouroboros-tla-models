# the muxer: receiver stop, start gate and egress

The muxer (`muxer/muxer.go`, `muxer/egress.go` in gOuroboros) carries every
mini-protocol on a connection. [The connection](../connection/README.md)
models what crosses it (bytes across a restart, the shared ingress budget,
the connection's teardown); this directory models the muxer's own goroutines
and its write scheduler. Read [Model `keepalive`](../keepalive/README.md) and
the connection first.

| Part | Module | Question |
| --- | --- | --- |
| 1 | `MuxReceiverStop.tla` | Does every receiver goroutine end on `Stop` or a bearer error, with no lost `sync.Cond` wakeup and no callback after `Stop`? |
| 2 | `MuxStartGate.tla` | Is nothing read before `Start`/`StartOnce` opens the gate, and does a `Start` always open it for good? |
| 3 | `MuxEgress.tla` | Is the turn to write shared fairly between Praos and Leios mini-protocols, and in order within each? |

`make muxer` runs all of them.

## Overlap with other models

`specs/connection/ConnectionTeardown.tla` treats `Muxer.Stop` as one process
("mc") and checks `MuxerJoinedAfterClose` and `NoMetricsCallbackAfterClose`
from the connection's side. It does not model the read loop's exit sweep,
re-registration, or the `Cond`; `MuxReceiverStop.tla` does, below that level.
`specs/connection/MuxHandover.tla` models suspend and resume across a restart;
here a receiver is either replaced or resumed, and suspend is left out.
`specs/engine` models the protocol side of registration and sending, not the
muxer's.

## Sources

| Ref | Source | What the model takes from it |
| --- | --- | --- |
| R1 | [`network-mux/src/Network/Mux.hs`, lines 241-287](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L241-L287) | A mux is run once and starts its muxer and demuxer together; there is no gate. The handshake runs before the mux that carries the other mini-protocols, so gOuroboros's `StartOnce` has no reference counterpart. |
| R2 | [`network-mux/src/Network/Mux/Egress.hs`, lines 36-104 and 288-313](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux/Egress.hs#L36-L104) | Fairness is "no starvation" and equal service for equal demand; one egress queue shared by every mini-protocol, at most one entry each; after each SDU a mini-protocol with more data goes back to the tail (`processSingleWanton`): round-robin. |
| R3 | [`network-mux/src/Network/Mux.hs`, lines 278-287](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L278-L287) | The muxer and demuxer jobs run in a job pool; outstanding jobs are shut down, and waited for, when the pool's scope ends. |
| G1 | gOuroboros `muxer/egress.go` at `7cd17437` (`release`, lines 141-164) | The Praos-first, bounded-burst rule; not in the reference (UNSOURCED there: the reference has no traffic classes). |

## Part 1: receiver stop (`MuxReceiverStop.tla`)

Each `RegisterProtocol` makes a receiver: a queue the read loop appends to and
a `forward` goroutine that parks on the receiver's `sync.Cond` while the queue
is empty. The read loop, after `doneChan` or a bearer error, sweeps the map of
receivers and stops each one; the cleanup goroutine waits on the muxer's
`WaitGroup` (the read loop and every forwarder) and `Stop` waits for it.

The `Cond` is modelled with a flag: `forward` checks its predicate and parks
in one step (it holds `mu` across both), a `Broadcast` under `mu` sets the
flag, and a parked `forward` moves only once it is set.

### What it found

1. **`Stop` returns before the read loop has finished.** The read loop's
   deferred function calls `waitGroup.Done()` first and then sweeps the
   receivers under `protocolReceiversMutex`. The cleanup goroutine's `Wait`
   can return, and `Stop` with it, while the read loop is still sweeping and
   holding that lock. `Stop`'s documentation says it waits until the read
   loop has returned. `MuxReceiverStopJoinBug.cfg`;
   `TestStopWaitsForReadLoopSweep`.
2. **Re-registering a live role leaks its receiver and hangs `Stop`.** A
   second `RegisterProtocol` for a role that is still registered (not
   suspended) makes a new receiver and overwrites the map entry. Nothing stops
   the old one: the sweep finds only mapped receivers. Its `forward` stays
   parked on the `Cond`, the `WaitGroup` never reaches zero, `ErrorChan` is
   never closed and `Stop` never returns (with a context, it returns
   `ctx.Err()`). `MuxReceiverStopReplaceBug.cfg`;
   `TestReregisterLiveRoleStopsReplacedReceiver`. gOuroboros's own protocols
   register once per instance and suspend before a restart, so the path needs
   two instances of one role registered at once or a direct muxer user.

The `Cond` itself is correct on `main`: `MuxReceiverStopMain.cfg` passes
`NoLostWakeup`, `NoWaitAfterStop`, `NoCallbackAfterStop` and `StopCompletes`
when a role is not registered twice.

| Config | Expected | Checks |
| --- | --- | --- |
| `MuxReceiverStop.cfg` | pass | both fixes, re-registration allowed: every invariant |
| `MuxReceiverStopMain.cfg` | pass | `main`, single registration: the `Cond` and callback invariants |
| `MuxReceiverStopJoinBug.cfg` | fail | `main`: `StopJoinsReadLoop` |
| `MuxReceiverStopReplaceBug.cfg` | fail | `main` replacement: `StopCompletes` |
| `MuxReceiverStopNoStopBroadcastBug.cfg` | fail | mutation, no `Broadcast` in `stop`: `NoLostWakeup` |
| `MuxReceiverStopNoEnqueueBroadcastBug.cfg` | fail | mutation, no `Broadcast` in `enqueue`: `NoLostWakeup` |
| `MuxReceiverStopNoJoinBug.cfg` | fail | mutation, `Stop` only closes `doneChan` (the muxer before `Stop` joined): `NoCallbackAfterStop` |

## Part 2: the start gate (`MuxStartGate.tla`)

`New` starts the read loop, which waits at a gate. `StartOnce` admits one
segment, for the handshake reply; `Start` admits everything from then on.

### What it found

3. **A `Start` called while a `StartOnce` is pending is lost.** Both make a
   non-blocking send into the one-slot `startChan`. If `StartOnce`'s token is
   still in the slot, `Start`'s send is dropped; the read loop takes the
   token, reads one segment, and waits at the gate until `Stop`.
   `MuxStartGateLostStartBug.cfg`; `TestStartGateTransitions` ("Start while
   a StartOnce is pending reads all"). `Connection` cannot reach it: it calls
   `Start` only after the handshake reply was read, which needed the token.
   This is CONCURRENCY.md's muxer hazard 1.

Writes are not gated, by design: the handshake client must send its proposal
before anything can be read. `MuxStartGateWriteBeforeGateProbeBug.cfg` shows
it is reachable.

| Config | Expected | Checks |
| --- | --- | --- |
| `MuxStartGate.cfg` | pass | fix (`Start` closes its own channel): `NoReadBeforeGate`, `StartIsSticky`, `StoppedAtGate` |
| `MuxStartGateMain.cfg` | pass | `main`: `NoReadBeforeGate`, `StoppedAtGate` |
| `MuxStartGateLostStartBug.cfg` | fail | `main`: `StartIsSticky` |
| `MuxStartGateSkippedBug.cfg` | fail | mutation, read without the gate: `NoReadBeforeGate` |
| `MuxStartGateWriteBeforeGateProbeBug.cfg` | fail | probe: a write before the gate opens |

## Part 3: egress (`MuxEgress.tla`)

One segment is written at a time. On release the turn goes to the head of the
Praos queue, unless a Leios segment waits and either no Praos segment waits or
`praosBurst` Praos turns in a row have passed it. Each mini-protocol role has
one sender goroutine, so it has at most one segment in `Send`: inside a class
the FIFO queue is then the reference's round-robin [R2]. The class priority is
gOuroboros's own [G1]. The model uses two mini-protocols per class and a burst
of 2.

No defect: `main` passes every invariant and, with demand that never ends,
`EveryQueuedSegmentEventuallySent`. Each invariant has a mutation that breaks
it.

| Config | Expected | Checks |
| --- | --- | --- |
| `MuxEgress.cfg` | pass | `main` with `Stop`: `OneHolder`, `LeiosNotStarved`, `PraosNotStarved`, `WithinClassFIFO`, `NoWriteAfterStop`, `StopDrains` |
| `MuxEgressLive.cfg` | pass | `main`, no `Stop`, weak fairness: `EveryQueuedSegmentEventuallySent` |
| `MuxEgressNoBurstBug.cfg` | fail | mutation, no burst bound: `LeiosNotStarved` |
| `MuxEgressNoBurstLiveBug.cfg` | fail | same, as liveness |
| `MuxEgressLeiosFirstBug.cfg` | fail | mutation, Leios first: `PraosNotStarved` |
| `MuxEgressLifoBug.cfg` | fail | mutation, newest first: `WithinClassFIFO` |
| `MuxEgressNoDoneCheckBug.cfg` | fail | mutation, no `doneChan` re-check after the grant: `NoWriteAfterStop` |
| `MuxEgressIgnoreBusyBug.cfg` | fail | mutation, fast path ignores `busy`: `OneHolder` |

Go tests bound to it: `TestEgressReleaseMatchesModel` (each release state),
`TestEgressPraosWaitsForAtMostOneLeiosTurn`,
`TestEgressPraosGrantedInQueueOrder`, and the existing
`TestEgressLeiosIsNotStarved` and `TestEgressStopReleasesWaiter`.

## Not modelled

Suspend and carry (in `MuxHandover.tla`), ingress limits and backpressure (in
`MuxIngress.tla`), the segment sender's stop window, write deadlines, and a
`net.Conn` whose `Close` does not end a pending read or write.
