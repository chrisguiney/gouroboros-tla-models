# the block-fetch client

Block-fetch is how a node downloads block bodies: the client asks for an
inclusive range of blocks (`MsgRequestRange`), and the server answers either
`MsgNoBlocks`, or `MsgStartBatch`, one `MsgBlock` per block, and
`MsgBatchDone`. The client ends the protocol with `MsgClientDone`.

The gOuroboros client (`protocol/blockfetch/client.go`, about 1,800 lines)
keeps many ranges in flight at once when it is configured with
`RequestPipelining` (`RequestRange`), or one at a time (`GetBlockRange`,
`GetBlock`). The engine's part of pipelining, sending a request while the
server still holds agency and applying its state change later, is
[Model `engine`](../engine/README.md)'s slice 2, which already passes for
block-fetch (`EnginePipeliningBlockFetch.cfg`, 10,091 states; the deep config
105,743). Its conclusion is reused here and not re-modelled: with an honest
server, the engine delivers every answer in order and refuses none, and the
final message waits for every answer. This model is about the client's own
bookkeeping on top of that.

Read [Model `chainsync`](../chainsync/README.md)'s slice 2 first; slice 2 here is the
same problem in block-fetch.

## Slice 1: matching answers to requests (`BlockFetchQueue.tla`)

### What the code does

- **`sendRequestRange`** takes a send token, appends the request to a FIFO
  queue, queues its `MsgRequestRange` on the protocol, and gives the token
  back. The token covers the append and the send together, so queue order
  is wire order. If the send fails (the protocol has stopped), the caller
  removes its request if it is still queued and `RequestRange` returns an
  error.
- **The handler** applies every answer to the head of the queue
  (`headForResponse`). `MsgStartBatch` and `MsgNoBlocks` need a head that has
  not started, `MsgBlock` and `MsgBatchDone` one that has; anything else is
  refused as a peer talking out of turn. `MsgNoBlocks` and `MsgBatchDone`
  remove the head and resolve it: `RangeDoneFunc` runs once (`resolve`,
  guarded by `resolveOnce`). `MsgNoBlocks` resolves with `ErrNoBlocks` and is
  not a protocol error, as in the reference (`rejectedFetchBatch`).
- **On shutdown** (a protocol error, a range deadline, `Stop`), a watcher
  drains the queue and resolves every entry with `ErrProtocolShuttingDown`
  (`failOutstandingForProtocol`, `failOutstanding`, `watchRangeDeadline`).

### The questions

1. **`AnswersReachTheirRequest`**: is every answer applied to the request that
   asked for it, including a `MsgNoBlocks` in the middle of a pipeline?
2. **`HonestAnswersAccepted`**: does the handler ever refuse an honest answer?
3. **`ResolvedAtMostOnce`**: does `RangeDoneFunc` run at most once per request?
4. **`EveryReturnedIdResolved`**: once everything is over, was every request
   that `RequestRange` returned an id for resolved?
5. **`NoCallbackForRefused`**: does `RangeDoneFunc` ever run for a request
   whose `RequestRange` returned an error?
6. Does anything deadlock?

### The answers

Three callers, an honest server that may answer any range with
`MsgNoBlocks` or a batch, and a shutdown that can happen at any step:

| Config | States | Result |
| --- | --- | --- |
| `BlockFetchQueue.cfg`: gOuroboros today, questions 1-4 | 9,448 | passes |
| `BlockFetchQueueRefusedBug.cfg`: gOuroboros today, question 5 | | **fails** |
| `BlockFetchQueueSkipUnsent.cfg`: the drain leaves unsent requests to their callers, all five | 6,657 | passes |
| `BlockFetchQueueDeferSending.cfg`: the fix on branch `fix/blockfetch-no-callback-for-unsent`, all five | 71,962 | passes |
| `BlockFetchQueueSendFails.cfg`: the same, with sends that fail while the protocol runs (PR #3114 at `d10daf24`) | 74,702 | passes |

Questions 1-4 hold. Answer order is wire order, so the head of the queue is
always the request being answered, and `MsgNoBlocks` mid-pipeline resolves
only its own request (the probe shows that case is reached).

Question 5 does not. The trace is four steps: a caller appends its request;
the protocol stops; the watcher drains the queue and calls `RangeDoneFunc`
with `ErrProtocolShuttingDown` for that request; the caller's send then
fails, and `RequestRange` returns an error. The application gets a
completion for a request id it was never given. This is a contract wart, not
a protocol fault: the wire is never involved. Dingo already works around it
(`ouroboros/blockfetch.go`, `blockfetchClientRangeDone`: "gouroboros can drain
a queued request during protocol shutdown while its send is still failing"),
by leaving a marker that the failing `RequestRange` path then never removes.
`BlockFetchQueueSkipUnsent.cfg` shows one design that closes it; returning the
id with a nil error once the request has been resolved is another.

### Fixed

Branch `fix/blockfetch-no-callback-for-unsent` (gOuroboros) marks a request
as sending from its queue append until its send returns. A drain that finds
a request still sending takes it out of the queue without resolving it and
records the drain's error on it; the caller then drops it if its send failed,
or resolves it with that error if its send succeeded, before returning the
id. In the model (`DrainDefersSending`) the send's outcome and the caller
clearing its mark are separate steps (`Send`, `SendFinish`), because in Go a
drain can run between them; `BlockFetchQueueDeferSending.cfg` passes all
five questions, and `ProbeNeverHandedOverAndSent` shows the path where the
caller resolves a handed-over request is reached.
`TestRequestRangeRefusedAtShutdownGetsNoRangeDone` fails on `61046085` with
`RangeDoneFunc` called for the refused request;
`TestRequestRangeDrainedBeforeSendIsResolvedOnce` guards the other outcome.
`RangeDoneFunc`'s doc comment now says it runs exactly once for each id
`RequestRange` returned and never for a call that returned an error.

### Refused sends keep the token until they leave the queue

Review of PR #3114 at `395b9c2e` found that `RequestRange` handed the send
token back, in a deferred function, as soon as `SendMessageContext` returned,
and only then took a refused request out of the queue. A send can fail while
the protocol still runs (the caller's context or the range deadline ends), so
another `RequestRange` could take the token, queue its request behind the
never-sent entry and send it; `headForResponse` then gave that range's
`MsgStartBatch` to the stale entry, and the later `MsgBatchDone` tore the
connection down. The model shared the gap: a send failed only once the
protocol had stopped, and its failure, removal and token release were one
step, so no interleaving could put another request behind the stale one.

A failed send is now two steps, `SendFail` and `SendRefused`, and
`SendCanFail` lets it fail while the protocol runs. `TokenCoversRemoval`
(TRUE: the fix at `d10daf24`, as on `61046085`) places the token's release
after the removal; FALSE places it at `SendFail`, as at `395b9c2e`. A request
whose send has failed counts as still sending for the drain, because Go clears
`sending` under `queueMutex` in the same section as the removal. Splitting the
step raises the state counts of the existing configs; their results are
unchanged.

| Config | States | Result |
| --- | --- | --- |
| `BlockFetchQueueSendFails.cfg` (`TokenCoversRemoval = TRUE`) | 74,702 | passes all five questions |
| `BlockFetchQueueSendFailsEarlyTokenBug.cfg` (`395b9c2e`) | | `AnswersReachTheirRequest` violated |
| `BlockFetchQueueProbeFailsWhileUpBug.cfg` | | probe violated: a send does fail while the protocol runs |

Go test `TestRequestRangeRefusedHoldsTokenUntilRemoved` holds `queueMutex`
while a send fails on a canceled context and checks whether the token is
free: it fails 3/3 at `395b9c2e` (token free, refused request still queued)
and passes at `d10daf24`.

### Checking the checks

Each safeguard has a switch; turning it off must break an invariant:

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `BlockFetchQueueNoTokenBug.cfg` | the send token covers append and send | `AnswersReachTheirRequest` |
| `BlockFetchQueueKeepHeadBug.cfg` | `MsgNoBlocks` removes its request | `AnswersReachTheirRequest` |
| `BlockFetchQueueKeepHeadTwiceBug.cfg` | the same | `ResolvedAtMostOnce` |
| `BlockFetchQueueNoStartBug.cfg` | `MsgStartBatch` marks its request started | `HonestAnswersAccepted` |
| `BlockFetchQueueNoDrainBug.cfg` | the shutdown drain | `EveryReturnedIdResolved` |
| `BlockFetchQueueDeferSendingNoResolveBug.cfg` | with the fix, the caller resolves a request a drain handed to it | `EveryReturnedIdResolved` |
| `BlockFetchQueueSendFailsEarlyTokenBug.cfg` | a refused caller keeps the token until its request leaves the queue | `AnswersReachTheirRequest` |

The probes at the bottom of the `.tla` each claim something never happens,
and TLC finds each one with the `BlockFetchQueue.cfg` constants: more than one
request queued (`ProbeNeverPipelined`), a refused caller
(`ProbeNeverRefused`), and `MsgNoBlocks` arriving with another request
queued behind it (`ProbeNoBlocksMidPipeline`); with the
`BlockFetchQueueDeferSending.cfg` constants, a request handed over by a drain
whose send then succeeds (`ProbeNeverHandedOverAndSent`). To run one, copy the config and
replace its `INVARIANT` lines with the probe's name.

### Covered by existing Go tests

The safeguards of questions 1-4 are already pinned by
`client_queue_internal_test.go` and `client_pipelined_test.go`:
`TestRequestRangeNoBlocksResolvesOnlyItsOwnRequest`,
`TestRequestRangeExcessBatchDoneNotAppliedToNextRequest`,
`TestQueueRejectsBlockBeforeStartBatch`,
`TestQueueRejectsResponseWithNoOutstandingRequest`,
`TestConcurrentRequestResolutionCallsRangeDoneOnce`,
`TestRequestRangeShutdownResolvesOutstanding`, and
`TestOldProtocolShutdownDoesNotFailRestartedRequests`. No new Go test was
needed for them.

## Slice 2: stopping with ranges outstanding (`BlockFetchLifecycle.tla`)

### What the code does

`Stop` queues `MsgClientDone` and gives it 250 ms to be written, then
unregisters the protocol either way. `MsgClientDone` is legal only in
`StIdle`, so while a range is outstanding it waits in the send queue for the
range's last answer (the engine's `n = Zero` rule, Model `engine`). A range that
takes longer than 250 ms is abandoned: `Stop` returns `context deadline
exceeded`, and the server still owes its answer. `Start` then registers a
fresh instance in `StIdle`, which receives that answer.

### The question

**`NoViolation`**: after a stop and a restart, does either side ever receive a
message its state does not allow?

### The answer

| Config | States | Result |
| --- | --- | --- |
| `BlockFetchLifecycleStopBug.cfg`: gOuroboros today | | **fails** |
| `BlockFetchLifecycleRefuse.cfg`: `Start` refuses after an abandoning `Stop` | 423 | passes |
| `BlockFetchLifecycleCloseOnlyBug.cfg`: the connection is closed, nothing more | | **fails** `NoViolation` |
| `BlockFetchLifecycleCloseOnlyLive.cfg`: the same, checking only open connections | 3,129 | passes `NoViolationOnLiveConnection` |
| `BlockFetchLifecycleClose.cfg`: the fix: close **and** refuse `Start` | 537 | passes both |

The failing trace: request a range, `Stop` (the timer fires with the answer
owed), `Start`, the server answers, and the new instance in `StIdle` refuses
it. This is exactly chain-sync's Stop problem (Model `chainsync`, slice 2), and the fix
is the same: report `ErrStoppedWithoutDone` so the connection closes, as the
reference does when a hot peer's protocols do not finish, and refuse `Start`
meanwhile, because the close happens on another goroutine. Probes show an
abandoning stop, a restart, and a clean stop that delivers `MsgClientDone`
are all reached.

### Reproduced in Go, and fixed

A test with a real gOuroboros server over `net.Pipe`: the server holds its
answer, the client calls `Stop` (returns `context deadline exceeded`), then
`Start`, then the server answers. 20 runs out of 20 with `-race`:

```
block-fetch: received message type 3 without peer agency, an allowed
pipelined message, or an outstanding pipelined request in state Idle
```

Branch `fix/blockfetch-stop-without-done` (gOuroboros) mirrors the chain-sync
fix: `TestStopWithRangeOutstandingReportsError` and
`TestStartAfterStopWithoutDoneStaysStopped` fail before the change and pass
after it; removing only the `Start` refusal fails the second test again.

## Slice 3: locks, callbacks and Stop (`BlockFetchBusyDelivery.tla`)

Item 4 of [`CONCURRENCY.md`](../../CONCURRENCY.md)'s top five: hazards B1,
B3 and X1, the only lock cycle in the inventory. Written against gOuroboros
`origin/main` `f9ba2d3c`; every `client.go` line the inventory cites for
block-fetch was re-read there and still matches.

### What the code does

One step per lock acquire or release, channel wait, `sync.Once` entry and
exit, in the goroutine style of
[`ConnectionShutdown.tla`](../connection/ConnectionShutdown.tla). Six
goroutines: two `Stop` callers; `recvLoop` running `handleBlock`
(`queueMutex`, then `deliveryMu` hand over hand, `pipelineContext` ->
`lifecycleMutex`, `recordBlock` under `queueMutex`, `BlockFunc` under
`deliveryMu`) and `handleBatchDone`; `watchRangeDeadline`; the shutdown
watcher; and PR #3114's `sendRequestRange` (`sending` mark, token back before
a deferred `RangeDoneFunc`). Each goroutine is a stack of frames, so a user
callback can call `Stop` (a new frame) or `RequestRange` (the token and
`queueMutex`) exactly as Go code can.

Deadlock is checked two ways: TLC's own check, and `NoWaitCycle`, which
follows who-waits-for-whom (a lock's owner, `recvLoop` for a `Stop` waiting
on `DoneChan`, the goroutine inside a `resolveOnce`) and fails on any cycle,
including a goroutine re-taking a lock it holds.

### The answers

| Config | States | Result |
| --- | --- | --- |
| `BlockFetchBusyDelivery.cfg`: main, one `Stop`, callbacks return or call `RequestRange` | 22,569 | passes all eight invariants |
| `BlockFetchBusyDeliveryX1.cfg`: main, two `Stop`s, **every** callback may call `Stop` | 356,880 | passes `NoX1Shape`: **X1 is unreachable** |
| `BlockFetchBusyDeliveryFixed.cfg`: the fix, two `Stop`s, callbacks off `recvLoop` may call `Stop` or `RequestRange` | 531,003 | passes all eight |
| `BlockFetchBusyDeliverySender.cfg`: the fix composed with PR #3114's sender | 1,873,292 | passes all eight |
| `BlockFetchBusyDeliveryNoOnceAlone.cfg`: `resolveOnce` removed | 22,569 | passes `RangeDoneOnce` |
| `BlockFetchBusyDeliveryRecvStop.cfg`: the fix; `recvLoop` callbacks stop the client with `StopContext` and their own context | 37,484 | passes all eight |
| `BlockFetchBusyDeliveryJoin.cfg`: the same and `JoinWatchers`, two `Stop`s, every callback may stop the client | 56,947 | passes all eight and `StopJoinsWatcher` |
| `...StopLockBug.cfg` (main, two `Stop`s) | | **fails** `NoCallbackUnderLifecycle`: B1 |
| `...OrderBug.cfg` (main, two `Stop`s) | | **fails** `NoResolveDuringDelivery`: new |
| `...ReenterBug.cfg` (main, callback calls `Stop`) | | **fails** `NoWaitCycle`: B1 deadlocks |
| `...RecvStopBug.cfg` (first fix only, `recvLoop` callback calls `Stop`) | | **fails** `NoWaitCycle`: new |
| `...JoinNoSelfBug.cfg` (joining the watchers; callbacks call plain `Stop`) | | **fails** `NoWaitCycle`: a watcher's callback waits for itself |
| `...JoinOtherCtxBug.cfg` (callbacks pass another client's context) | | **fails** `NoWaitCycle`: the marker is compared by identity |
| `...StopJoinBug.cfg` (origin/main) | | **fails** `StopJoinsWatcher`: B3 |
| `...X1ReachableBug.cfg` (deadline resolves before removing) | | **fails** `NoX1Shape` |
| `...QueueCallbackBug.cfg` (resolve under `queueMutex`) | | **fails** `NoCallbackUnderQueue` |
| `...TokenCallbackBug.cfg`, `...TokenDeadlockBug.cfg` (#3114 resolving before the token is back) | | **fail** `NoCallbackUnderToken`, `NoWaitCycle` |
| `...NoOnceBug.cfg` (no `resolveOnce` and deadline resolves before removing) | | **fails** `RangeDoneOnce` |
| `...DropDeferredBug.cfg` (#3114 sender ignores a deferred drain) | | **fails** `AllResolvedAtEnd` |
| `...Probe{ReentrantStop,Deferred,Deadline}Bug.cfg` | | violated: a callback's `Stop` returns, #3114's deferred resolve and the deadline's resolve are all reached |

- **X1 cannot happen, even with reentrant callbacks.** The cycle needs
  `recvLoop` holding `queueMutex` and waiting for a `deliveryMu` that the
  deadline watcher holds. The watcher takes its requests out of the queue
  under `queueMutex` before it takes any `deliveryMu`, and `recvLoop` only
  locks the `deliveryMu` of the queue head, so it never waits for one the
  watcher holds. `X1ReachableBug` reverses that order and finds the
  three-goroutine cycle. The inventory's X1 row is overturned; its "Ruled out"
  reasoning was right.
- **B1 is real, and worse than listed.** A second `Stop` (or any `Stop` in
  the New or Starting state) runs `RangeDoneFunc` under `lifecycleMutex`; a
  callback that calls `Stop` or `Start` deadlocks on its own goroutine. The
  same `Stop` also resolves a range while `recvLoop` is still in that range's
  `BlockFunc`, without the `deliveryMu` that a range deadline uses for exactly
  this: completion is reported ahead of a block.
- **`resolveOnce` is not what gives exactly-once.** Every resolver removes the
  request under `queueMutex` first; that alone keeps `RangeDoneFunc` to one
  call. `resolveOnce` is a second guard.
- **A callback on `recvLoop` that calls `Stop` waits for itself.** `Stop`
  waits for `DoneChan`, which closes only when `recvLoop` returns, so a
  `BlockFunc`, or a `RangeDoneFunc` from `handleBatchDone` or
  `handleNoBlocks`, that calls `Stop` never returns (`RecvStopBug`). Each
  callback's `CallbackContext` now carries a context marked with its client,
  and `StopContext` given a context carrying *this* client's marker
  (`OwnStop`, `CbStopCtx = "own"`) requests shutdown and returns without
  waiting, joining or draining (`RecvStop`). It must not drain either: a
  `BlockFunc`'s goroutine holds that range's `deliveryMu`, which the fixed
  drain takes. Another client's marker is not recognized (`JoinOtherCtxBug`).
- **B3:** nothing joins the shutdown or deadline watchers, so `Stop` can
  return before their `RangeDoneFunc` calls (`StopJoinBug`). `JoinWatchers`
  makes every other stop wait for them, after `DoneChan` (`Join`). The join
  needs callbacks to use `StopContext` with their own context: a watcher's
  callback that calls plain `Stop` waits for its own goroutine
  (`JoinNoSelfBug`).

### The fix (gOuroboros branch `fix/blockfetch-stop-callbacks-unlocked`)

`Stop` in a not-running state now releases `lifecycleMutex` before resolving,
fails only the stopped protocol's requests (a concurrent `Start` may install a
new one once the lock is free), and resolves each behind its `deliveryMu`, as
`watchRangeDeadline` does. This follows the reference, which hands blocks to
the consumer with no client lock held. `TestStopNotRunningCallbackMayCallStop`
(New and Stopped) and `TestStopNotRunningWaitsForActiveDelivery` fail on
`origin/main` (a `Stop` from `RangeDoneFunc` never returns; `RangeDoneFunc`
runs while the block callback is active) and pass with it. It conflicts
textually with PR #3114 in four places: the `Client` fields and `Stop`'s doc
comment (keep both sides); `sendRequestRange`'s tail (take #3114's unlock,
token return and deferred resolve, then start the deadline watcher with
`group.Go`); and `takeOutstandingForProtocol`, which must take `err` and
apply #3114's `resolvableLocked` before returning. That composition is what
`BlockFetchBusyDeliverySender.cfg` checks.

### The follow-up (same branch)

`Stop` now tracks the goroutines started for each protocol instance (the
shutdown watcher, the pipeline stop watcher, each deadline watcher, the
`GetBlockRange` busy releaser) and waits for them after `DoneChan`; a group
closed for the wait refuses new goroutines, which a `sync.WaitGroup` cannot
do safely. `CallbackContext.Context()` returns a context carrying the
client's `*Client` under an unexported key, and `StopContext(ctx)` skips the
waits only when that value is this client. `Stop()` always waits, so a
callback must use `StopContext`. `TestStopFromReceiveLoopCallbackReturns`
(each of `BlockRawFunc`, `BlockFunc`, `RangeDoneFunc`, `BatchDoneFunc` calls
`StopContext`) hangs when the marker is ignored, and
`TestStopWaitsForDeadlineWatcher` (plain `Stop`, and `StopContext` with
another client's context) fails at the first fix and when any client's
marker is accepted.

### Not modelled in this slice

The `busyMutex`/`busyStateMutex` handoff and the :606 releaser, `Start` and a
second generation, `Pipeline.Submit` blocking (it ends when `Stop` cancels the
pipeline context), `failRequest` from `handleBlock` (a resolve on `recvLoop`
under its own `deliveryMu`, the same shape as `BlockFunc`), the 250 ms
`MsgClientDone` write (one non-blocking step: it is bounded), and the server.

## Slice 4: a fetch during a restart (`BlockFetchClientReader.tla`)

Hazard B4, gOuroboros #3264 (`fix/blockfetch-client-protocol-race`).

`GetBlockRange` and `GetBlock` logged through the embedded `c.Protocol` and
read `c.DoneChan()` with no lock, before `sendRequestRange` read the
instance under `protocolMu` and sent on it. The fix logs through
`ProtocolInstance()` and watches `req.protocol.DoneChan()`, the instance the
request went out on. Initial state as in the Go test: the client was started
and stopped once, and `Start` installs a second instance while the fetch runs.

| Config | Behaviour | Result |
| --- | --- | --- |
| `BlockFetchClientReaderUnlockedBug` | main | **fails** `NoRacingRead`: the fetch reads the field while `Start` writes it (`TestFetchDuringRestartReadsProtocolUnderLock` under `-race`) |
| `BlockFetchClientReaderOtherInstanceBug` | main | **fails** `WatchesOwnInstance`: the done channel read before sending is the stopped instance's, the request goes out on the new one, and the fetch fails at once while its request is live |
| `BlockFetchClientReader` | the fix | passes `NoRacingRead`, `WatchesOwnInstance`, `FetchReturns` |

The second failure is the one the fix's comment names ("a concurrent Start
may already have installed a newer one"); the Go test checks only the race.

## Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Which answer belongs to which request? | Answers come in request order [P1] | Each pipelined request carries its own receiver [R3] | Head of a FIFO queue; token keeps it in wire order | Agree |
| `MsgNoBlocks` | "does not have all of the blocks" [B1] | Not an error; the fetch logic records it [R4] | Resolves with `ErrNoBlocks`; not a protocol error | Agree |
| Too few or too many blocks | Not stated | `TooFewBlocks` / `TooManyBlocks` abort [R4] | "batch completed before requested range end", "beyond requested range end" abort | Agree |
| Stop with ranges outstanding | `MsgClientDone` only from `StIdle` [B1] | Collects every answer, then `MsgClientDone` [R3][R4]; a demotion that times out closes the connection | Abandons after 250 ms and allows `Start`: **defect**, fixed on the branch above | Fixed to match the reference |
| Size limit, `StIdle` | 65,535 [B1] | `smallByteLimit` 65,535 [R2] | 65,535; 2,500,000 for a pipelining client, which can see an early `MsgBlock` there | Deviation, needed by gOuroboros's engine |
| Size limit, `StBusy` | 65,535 [B1] | `smallByteLimit` 65,535 [R2] | 2,500,000: an early `MsgBlock` can be judged against `StBusy` | Deviation, needed by gOuroboros's engine |
| Size limit, `StStreaming` | 2,500,000 [B1] | `largeByteLimit` 2,500,000 [R2] | 2,500,000 | Agree |
| Timeout, `StIdle` | none [B1] | `waitForever` [R2] | none | Agree |
| Timeout, `StBusy` | 60 s [B1] | `longWait` 60 s [R2] | `StateMap` 60 s, but `NewConfig`'s `BatchStartTimeout` default of **5 s** replaces it in both client and server | Deviation: stricter; an honest server slower than 5 s loses the connection. Fixed on branch `fix/blockfetch-busy-timeout`: the default is `BusyTimeout`, 60 s (`TestNewConfigTimeoutsMatchReference`) |
| Timeout, `StStreaming` | 60 s [B1] | `longWait` 60 s [R2] | 60 s (`BlockTimeout`) | Agree |
| Who is timed? | "how much time the receiver side can wait" [B1] | Only `recvMessage` arms the timer [R5] | The engine arms it in every state with agency, so a **server** whose `RequestRangeFunc` takes longer than `BatchStartTimeout` times itself out (checked: "timeout waiting on transition from protocol state Busy" on the server) | Deviation, engine-wide; reported, not fixed |
| Server reading a pipelined `MsgRequestRange` | The server follows its state machine, unaware of pipelining [P1] | Read when back in `StIdle` | Admitted at once (`PipelinedMessageTypes`), served after the current range | Agree in effect |
| Total time for one range | Not stated | Not stated | `RangeTimeout`, default about 36 hours | gOuroboros extra |
| Callbacks and client locks | Not stated | No completion callback; blocks go to `addFetchedBlock` on the protocol thread with no client lock [R4] | `Stop` in a not-running state ran `RangeDoneFunc` under `lifecycleMutex` and ahead of an active `BlockFunc` | Fixed on branch `fix/blockfetch-stop-callbacks-unlocked` to match the reference |

## Go tests (`test/blockfetch-state-model`)

`protocol/blockfetch/statemap_model_test.go`, after the keep-alive template:

- `TestStateMapMatchesModel`: the full role x state x message table (2 x 4 x
  7, with an oversized message) derived from the specification and reference,
  checked against `StateMap`.
- `TestReceiveMatchesModel`: the same 56 cells against a running client or
  server driven into each state, including the server answering a pipelined
  `MsgRequestRange` only after the current range, a restarted server after
  `MsgClientDone`, and a stopped client ignoring late messages.
- `TestStateMapEntryAndExitRules`: every edge into each state; `StDone` is
  entered only by `MsgClientDone` from `StIdle` and never left.
- `TestStateMapLimitsAgainstSpec`: size limits and timeouts, with the `StBusy`
  deviation pinned.
- `TestClientTimesOutInServerAgency`: the client gives up in `StBusy` and
  `StStreaming`.

Each was shown to fail under a mutation of the code:

| Mutation | Tests that fail |
| --- | --- |
| `StBusy` no longer lists `MsgRequestRange` as pipelined | `TestStateMapMatchesModel/server/inBusy/MsgRequestRange`, `TestReceiveMatchesModel/server/inBusy/MsgRequestRange` |
| `BusyMaxPendingMessageBytes` = 65,535 | `TestStateMapLimitsAgainstSpec` |
| `MsgNoBlocks` moves to `StStreaming` | `TestStateMapMatchesModel`, `TestStateMapEntryAndExitRules`, `TestReceiveMatchesModel` |
| client ignores `BatchStartTimeout` | `TestClientTimesOutInServerAgency/Busy` |
| server does not restart after `MsgClientDone` | every `TestReceiveMatchesModel/server/inDone/*` cell |

## Sources

Pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c)
and gOuroboros `origin/main` at `61046085`.

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | [`docs/network-spec/miniprotocols.tex` lines 27-36](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36) | An unexpected message aborts the connection. |
| B1 | [Same file, lines 1139-1241](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1139-L1241) | Block-fetch state machine, agencies, messages, transition table (1190-1204), size limits (1206-1223), timeouts (1225-1241). |
| P1 | [Same file, lines 2180-2208](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L2180-L2208) | Pipelining, using block-fetch as the example; answers in request order. |
| R1 | [`Protocol/BlockFetch/Type.hs` lines 57-83](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/BlockFetch/Type.hs#L57-L83) | Messages and agencies. |
| R2 | [`Protocol/BlockFetch/Codec.hs` lines 34-68](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/BlockFetch/Codec.hs#L34-L68), with [`Protocol/Limits.hs` lines 107-120](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs#L107-L120) | Byte limits (small 65,535 / large 2,500,000) and time limits (`waitForever`, `longWait` 60 s). |
| R3 | [`Protocol/BlockFetch/Client.hs` lines 98-175](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/BlockFetch/Client.hs#L98-L175) | Pipelined client: a receiver per request; `SendMsgDonePipelined` only at `Z`. |
| R4 | [`BlockFetch/Client.hs` lines 95-299](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/lib/Ouroboros/Network/BlockFetch/Client.hs#L95-L299) | The node's fetch client: collects before terminating (182-190), `MsgNoBlocks` (210-215), too few / too many blocks (295-299). |
| R5 | [`Driver/Limits.hs` lines 120-131](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/framework/lib/Ouroboros/Network/Driver/Limits.hs#L120-L131) | The time limit is applied when receiving. |
| G1 | gOuroboros `protocol/blockfetch/client.go` | `sendRequestRange`, `headForResponse`, `handleStartBatch`, `handleNoBlocks`, `handleBatchDone`, `resolve`, `failOutstanding*`, `watchRangeDeadline`, `Stop`, `Start`, `protocolStateMap`. |
| G2 | gOuroboros `protocol/blockfetch/blockfetch.go`, `server.go`, `protocol/protocol.go` | `StateMap`, limits, `NewConfig` defaults; `serverStateMap`; state timers in `setState`. |

## Not modelled

The in-flight byte bound and ingress allowance (covered by
`TestRequestRangeInFlightByteBound`, `TestConcurrentAdmissionRespectsInFlightBound`
and others), range continuity and block validation, the block processing
pipeline, compressed blocks (CIP-0150), `RangeTimeout`, and requests made
after `Stop` has queued `MsgClientDone`.

## After merging main into #3114

Merge `a93b4116` (main at `71ea8189`, with #3159) conflicted only in
`protocol/PROTOCOL_LIMITS.md`: the text now says both that only the client
enforces the Busy and Streaming timeouts and that they default to 60 s. A
documentation change, which cannot affect the model. The one red job at the
previous head, `TestReceiveMatchesModel/server/inBusy/Oversized` on Go 1.27
amd64, passed on the other jobs there and `-race -count=5` here.

## Timeout defaults as a table (`BlockFetchLimits.tla`)

A table model, written bug-first for #3114 (N17): a state (`StBusy`,
`StStreaming`) and the seconds an honest server takes; the peer is dropped
when that exceeds the state's timeout. The state map's timeouts are
replaced by `NewConfig`'s `BatchStartTimeout` and `BlockTimeout`, so the
defaults are what counts.

| Config | Rule | Result | Counterexample, and the Go check it matches |
| --- | --- | --- | --- |
| `BlockFetchLimitsMainBug` | main before #3114: `BatchStartTimeout` 5 s | fails `DropsAsTimeLimitsBlockFetch` | `Busy`, reply after 6 s: dropped, the reference waits 60 s (`TestNewConfigTimeoutsMatchReference`) |
| `BlockFetchLimits` | #3114 (`5a2a11c3`): 60 s in both | passes, 124 states | |

Sources: `miniprotocols.tex` 1235-1237 (`StBusy`, `StStreaming` 60 s);
`BlockFetch/Codec.hs` 54 and `Protocol/Limits.hs` 116-117 (`longWait`).
A caller's own option still overrides the default; that is not modelled.

## Running it

```sh
cd specs/blockfetch
../../bin/tlc -config BlockFetchQueue.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueSkipUnsent.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueDeferSending.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueSendFails.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchLifecycleRefuse.cfg BlockFetchLifecycle.tla
../../bin/tlc -config BlockFetchLifecycleCloseOnlyLive.cfg BlockFetchLifecycle.tla
../../bin/tlc -config BlockFetchLifecycleClose.cfg BlockFetchLifecycle.tla
../../bin/tlc -config BlockFetchBusyDelivery.cfg BlockFetchBusyDelivery.tla
../../bin/tlc -config BlockFetchBusyDeliveryX1.cfg BlockFetchBusyDelivery.tla
../../bin/tlc -config BlockFetchBusyDeliveryFixed.cfg BlockFetchBusyDelivery.tla
../../bin/tlc -config BlockFetchBusyDeliverySender.cfg BlockFetchBusyDelivery.tla
# expected to fail
../../bin/tlc -config BlockFetchQueueRefusedBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueNoTokenBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueKeepHeadBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueKeepHeadTwiceBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueNoStartBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueNoDrainBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueDeferSendingNoResolveBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueSendFailsEarlyTokenBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchQueueProbeFailsWhileUpBug.cfg BlockFetchQueue.tla
../../bin/tlc -config BlockFetchLifecycleStopBug.cfg BlockFetchLifecycle.tla
../../bin/tlc -config BlockFetchLifecycleCloseOnlyBug.cfg BlockFetchLifecycle.tla
../../bin/tlc -config BlockFetchBusyDeliveryStopLockBug.cfg BlockFetchBusyDelivery.tla
../../bin/tlc -config BlockFetchBusyDeliveryOrderBug.cfg BlockFetchBusyDelivery.tla
../../bin/tlc -config BlockFetchBusyDeliveryRecvStopBug.cfg BlockFetchBusyDelivery.tla
../../bin/tlc -config BlockFetchBusyDeliveryX1ReachableBug.cfg BlockFetchBusyDelivery.tla
```

The rest of slice 3's `*Bug.cfg` configs are listed in its table; `make blockfetch` runs every config.
