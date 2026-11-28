# Leios and Peras mini-protocols

gOuroboros implements four experimental mini-protocols for Leios and Peras:

| Protocol | ID | gOuroboros package | Model |
| --- | --- | --- | --- |
| LeiosNotify | 18 | `protocol/leiosnotify/` | `LeiosNotify.tla` |
| LeiosFetch | 19 | `protocol/leiosfetch/` | `LeiosFetch.tla` |
| LeiosVotes | 20 | `protocol/leiosvotes/` | `LeiosVotes.tla` |
| Peras vote diffusion (ObjectDiffusion) | 17 | `protocol/perasvotes/` | `PerasVotes.tla` |

None of them is in the pinned network specification. The specification
mentions Peras only as "`NodeToNodeV_17`: Experimental, support Peras
mini-protocols" [S1], and Leios not at all. So this model leans on other
sources, and they are not equally authoritative:

| Source | What it covers | How authoritative |
| --- | --- | --- |
| ouroboros-consensus `ec239d57f618`, `LeiosNotify/` and `LeiosFetch/` [R1-R5] | The reference node's LeiosNotify and LeiosFetch: types, codecs, limits, client and server | The strongest source for those two: the code IOG's Leios release-candidate node runs. Its own header says the states follow the cardano-blueprint and CIP-0164. |
| ouroboros-network `5f356486ab3e`, `ObjectDiffusion/` [R6-R7] | The ObjectDiffusion protocol Peras votes travel over | Reference code at the pinned commit. It changed on 2026-11-11 (`MsgAwaitReply`, `MsgServerIdle`), twelve days before this model. |
| CIP-0164, cardano-foundation/CIPs `03387471` [C1-C3] | Leios mini-protocols, including LeiosVotes | Status "Proposed". It says its protocols are "not the only feasible solution" and should be "amended as implementors refine" them. Its LeiosFetch and LeiosNotify already differ from the reference node's (below). It is the **only** source for LeiosVotes. |
| CIP-0140, same commit [C4] | Peras | Status "Proposed". Asks for "two new mini-protocols for vote and certificate diffusion" and says nothing about their state machines. |
| gOuroboros' own state maps | LeiosFetch's votes and block-range messages (tags 10-14) | No outside source. They are checked for internal consistency only. |

Read [Model `chainsync`](../chainsync/README.md) first: the "answer reaches the
wrong call" and "Stop abandons, Start restarts" questions come from there.

## The questions

For every protocol:

1. Is every state reachable, and are the states that must not be entered
   (out of `Done`, back into `Init`) unreachable?
2. Is every message legal only where the state map allows it, with agency
   always on exactly one side or none?
3. Is every request answered?
4. Does an answer always reach the call that asked (Model `chainsync`, slice 3)?
5. Can a stop leave requests outstanding and let a restart meet their late
   answers (Model `chainsync`, slice 2)?

Questions 1 and 2 are answered state by state in Go (the state-table tests
below). The TLA+ models answer 3 to 5, which depend on how the client's
goroutines interleave.

On question 5, none of these clients can be restarted: each `Start` runs
once (`onceStart`). The LeiosNotify, LeiosFetch and LeiosVotes clients' `Stop`
does not abandon requests: it queues `MsgQuit` or `MsgDone`, which the
protocol only writes when the state allows. The servers restart after
`MsgDone` (LeiosNotify after answering `MsgQuit`), except Peras, whose server
stays in `Done` on `main` (`PerasVotesNoRestartBug.cfg`; fixed on
`fix/perasvotes-server-restart`). The Peras client's `Stop` and a context that ends mid-request
stop the protocol for good. So the slice 2 defect has no way in here.

## LeiosNotify (`LeiosNotify.tla`)

### What the code does

`Sync` sends one `NotificationRequestNext` and starts `notificationLoop`. The
loop takes one notification at a time. While earlier requests are still owed,
it waits for the next. When none are, it checks `quitting` and sends
`PipelineLimit` requests, one `SendMessage` at a time. `Stop` sets `quitting`
and sends `MsgQuit`. The server answers each request with a notification, or
with `MsgCanceled` once `MsgQuit` has arrived, and then sends `MsgDone`.

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LeiosNotifyQuitRaceBug.cfg`: today | 124 | **fails** `NoRequestAfterQuit` |
| `LeiosNotify.cfg`: the fix (one lock around the check and the sends, and in `Stop`) | 160 | passes |
| `LeiosNotifyDeep.cfg`: the fix, refills of three | 386 | passes |
| `LeiosNotifyDry.cfg`: the fix, a server with nothing to notify | 13 | passes |
| `LeiosNotifyRogueCancel.cfg`: the fix, a server that cancels before `MsgQuit` | 192 | passes (the client refuses it) |
| `LeiosNotifyRogueCancelBug.cfg`: today's client and that server | 93 | **fails** `LoopCanProgress` |
| `LeiosNotifyNoCancelBug.cfg`: mutation, a dry server that does not cancel on `MsgQuit` | 8 | **fails**: deadlock |
| `LeiosNotifyProbesBug.cfg`: probe, `Stop` during a refill | 80 | violated, as expected |
| `LeiosNotifySyncOrderBug.cfg`: the fix at PR #3160 `cfa1edeb`, `Sync` checks the running loop before `quitting` | 6 | **fails** `SyncAfterStopReportsShutdown` |
| `LeiosNotifyProbeLoopAfterStopBug.cfg`: probe, the loop still running after `Stop` | 6 | violated, as expected |

**Defect 1: a request after `MsgQuit`.** Nothing orders `Stop` against the
loop's refill. The loop checks `quitting`, finds it false, and starts sending.
`Stop` then sets `quitting` and sends `MsgQuit` between two of those sends.
The rest of the refill follows `MsgQuit` onto the wire. The client's state is
still Busy, which lets it pipeline requests, so they are written. The
reference client sends nothing after `MsgQuit` [R2]. A gOuroboros or reference
server sends `MsgDone`, restarts, and takes the stray request as the first of
a new run the client does not know about. `Sync` after `Stop` also queued a
request (the probe `ProbeNeverHeld` finds it). With the fix it is refused.

**Which refusal `Sync` reports after `Stop` (found in review of PR #3160).**
After `Stop` the loop stays in Wait until the protocol ends. At `cfa1edeb`
`Sync` checked "notification loop is already running" first, so a client
stopped while syncing got that error rather than `ErrProtocolShuttingDown`.
The model shared it by leaving the error out: `Sync` was simply not enabled
in either case. `SyncAnswer` now gives what `Sync` returns in each state,
ordered by `SyncChecksQuitFirst`, and `SyncAfterStopReportsShutdown`
requires the shutdown once `Stop` has run; the passing configs check it,
with unchanged state counts. PR #3160 head `ad0d48de` checks `quitting`
first; Go: `TestSyncAfterStopWhileSyncingIsRefused`, which fails before the
fix. The same order is in the LeiosVotes client's `Sync` and `RequestNext`
on `main` (the vote loop also waits for a vote after `Stop`); this PR does
not change that client's code, and `LeiosVotes.tla` does not model its
errors.

**Defect 2: an early `MsgCanceled` stalls the loop.** The client ignored
`MsgCanceled` whatever its state. It never reaches the loop, which counts on
one notification per request. So a `MsgCanceled` before `MsgQuit` leaves the
loop waiting for a notification that will never come, with nothing owed by
the server. The reference client disconnects such a peer
(`ExnLeiosNotifyUnexpectedCancel`, [R2]). Only a misbehaving server sends it.

Other probes, each violated as expected under `LeiosNotify.cfg`:
`ProbeNeverDone` (27 states), `ProbeNeverCanceled` (47). `ProbeNeverHeld`
holds under the fix (160) and is violated today (30).

## LeiosNotify pipelined requests and quit (`LeiosNotifyPipelinedQuit.tla`)

### What the code does

The server's read loop fires its quit signal as soon as it reads `MsgQuit`,
before the message is queued. The receive loop hands the next request to a
handler goroutine only once the previous one is answered. The handler
(`serveRequestNext`) answers `MsgCanceled` without asking the notification
source when the signal has already fired, and otherwise asks the source. A
client that writes its whole burst and `MsgQuit` back to back can therefore
get every request canceled with the source asked zero times or once, depending
on whether the handler goroutine ran before the read loop reached `MsgQuit`.
The reference states only that every outstanding request is answered with
`MsgCanceled`, then `MsgDone` [R3].

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LeiosNotifyPipelinedQuit.cfg`: today, back to back | 47 | passes `EveryRequestCanceled`, `SourceAskedAtMostOnce` |
| `LeiosNotifyPipelinedQuitAssumptionBug.cfg`: assert the source is asked exactly once | 45 | **fails** `SourceAskedOnce` (asked zero times) |
| `LeiosNotifyPipelinedQuitHandshake.cfg`: the client sends the rest once the source was asked | 20 | passes `SourceAskedOnce` |
| `LeiosNotifyPipelinedQuitNoCheckBug.cfg`: mutation, the handler skips the quit check | 38 | **fails** `SourceAskedAtMostOnce` |
| `LeiosNotifyPipelinedQuitHandshakeNoCheckBug.cfg`: the same mutation, the client sends the rest once the source was asked | 17 | **fails** `SourceAskedAtMostOnce` |

The server is correct: it answers every request. The failing assertion is the
test's, not the protocol's: asking the source exactly once holds only when the
client waits for the first request to reach the source. That waiting client
also catches a handler that skips the quit check: each later request is taken
only after the one before it is answered, which is after the quit signal
fired, so the mutation asks the source again.

## LeiosFetch (`LeiosFetch.tla`)

### What the code does

The client keeps one request slot. A call acquires it, sends its request, and
waits on its own channel. Replies name no request, so the slot is what binds a
reply to its call. A call whose context ends abandons the slot, which stays
busy until the late reply arrives and is dropped. A call that finds the slot
abandoned waits up to a second, then fails the connection. `Stop` queues
`MsgDone`, which is written once no reply is owed.

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LeiosFetch.cfg`: two calls, abandonment, the grace period, `Stop` | 251 | passes |
| `LeiosFetchDeep.cfg`: three calls | 1,626 | passes |
| `LeiosFetchAbandonFreesBug.cfg`: mutation, abandon frees the slot | 119 | **fails** `OwnAnswer` |
| `LeiosFetchProbesBug.cfg`: probe, a late reply drains an abandoned slot while another call waits | 21 | violated, as expected |

`OwnAnswer`, `OneOutstanding`, `DoneOnlyWhenIdle` and `NoStrayReply` all
hold. The slot is the reason. The mutation shows why it must stay busy after
abandonment: freed, it hands the abandoned request's late reply to the next
call. The same mutation in Go (`abandon` calls `freeLocked`) fails four
existing tests, including `TestRequestSlotAbandonWakesExistingAcquirer` and
`TestBlockRequestSubsequentAfterAbandonedNoResponse`. So no new Go test was
needed for this property. **No defect found.**

## LeiosVotes (`LeiosVotes.tla`)

### What the code does

CIP-0164's state machine: `MsgLeiosVotesRequestNext(N)` moves Idle to Busy
with N tokens; each vote takes one; the last returns to Idle [C1]. The CIP has
the client send its next request before the previous batch is delivered, by
ordinary protocol pipelining [C2]. gOuroboros' client never does: its state
map pipelines nothing, so `Sync`'s extra requests wait for Idle. The vote
loop and `RequestNext` read one channel.

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LeiosVotesToday.cfg`: gOuroboros client and server | 768 | passes |
| `LeiosVotes.cfg`: gOuroboros client, fixed server | 768 | passes |
| `LeiosVotesCipClient.cfg`: a client that pipelines per CIP-0164, fixed server | 1,208 | passes |
| `LeiosVotesCipClientBug.cfg`: that client, today's server | 41 | **fails** `NoServerViolation` |
| `LeiosVotesNoDrainBug.cfg`: mutation, the loop ends without draining | 117 | **fails** `OwnVotes` |
| `LeiosVotesProbesBug.cfg`: probe, `RequestNext` completes after a loop ran | 130 | violated, as expected |

**Defect 3: the server refuses a pipelined request.** The server's Busy state
listed no pipelined message, so a `VotesRequestNext` that arrives while it is
sending a batch failed the connection. That is exactly what CIP-0164 tells a
client to do. gOuroboros against itself never hits it, because its own client
does not pipeline (`LeiosVotesToday.cfg`). `ProbeNeverHeld` confirms the fixed
server holds requests only for a pipelining client.

The package README's state machine listed only `Vote` out of Busy; PR #3160
`c14a2569` adds the held pipelined `VotesRequestNext`. Documentation only:
the model already has the edge, so nothing here changes.

`OwnVotes` holds: a loop stopped by its callback drains the votes it is owed
before `RequestNext` can run. No existing test pinned this. Removing the drain
in Go passed the whole package, so a new test does
(`TestRequestNextAfterStoppedSyncGetsOwnVote`).

## Peras vote diffusion (`PerasVotes.tla`)

### What the code does

ObjectDiffusion: Init, Idle (client agency), a blocking or non-blocking
request for identifiers, a request for objects, Done. gOuroboros' `Sync`
acknowledges every identifier of the last round, makes a blocking request,
fetches every object, and repeats. Its server answers a blocking request with
whatever `ObjectIDsFunc` returns and fails the connection if that is empty.

### The answers

| Config | States | Result |
| --- | --- | --- |
| `PerasVotes.cfg`: gOuroboros both sides, the server always has a vote | 58 | passes |
| `PerasVotesReferenceServerBug.cfg`: the reference server | 55 | **fails** `NoClientViolation` |
| `PerasVotesEmptyServerBug.cfg`: a gOuroboros server with no vote yet | 46 | **fails** `NoServerFailure` |
| `PerasVotesFixed.cfg`: gOuroboros with the fix against the reference server (and against its own fixed server, which awaits the same way) | 127 | passes |
| `PerasVotesFixedDeep.cfg`: the fix, a window of three, five rounds | 347 | passes |
| `PerasVotesProbesBug.cfg`: probe, a Sync round completes | 18 | violated, as expected |
| `PerasVotesFixedIdleProbesBug.cfg`: probe, under the fix `MsgServerIdle` gives the client agency back | 23 | violated, as expected |
| `PerasVotesRestart.cfg`: two runs on one connection, the server restarts after `MsgDone` (the reference, and the restart fix) | 69 | passes |
| `PerasVotesNoRestartBug.cfg`: the same against gOuroboros `main` `d8f5bc2a`, whose server stays in `Done` | 39 | **fails** `NewRunServed` |
| `PerasVotesProbeNoSecondRunBug.cfg`: probe, a second run starts | 35 | violated, as expected |

`NewRunServed` says a client message waiting for the server can be read
(`c2s nonempty => ENABLED ServerRead`). The other configs keep `MaxRuns = 1`.
The reference runs this server, the outbound side, as a responder
(consensus `ec239d57f618` `NodeToNode.hs` 522-536), and the inbound governor
restarts a responder that ended cleanly (ouroboros-network `InboundGovernor.hs`
455-470; `connection-manager.tex` 492-496).

**Deviation, fixed on a branch: no `MsgAwaitReply` or `MsgServerIdle`.** Since
2026-11-11 the reference server may answer a blocking request with
`MsgAwaitReply` (tag 7), and must then send identifiers or `MsgServerIdle`
(tag 6) [R6]. gOuroboros has neither message nor the `MustReply` state, so its
client refuses the reference server's await, and its server, with nothing to
offer, can only block inside `ObjectIDsFunc` or fail the connection. The
reference client waits 10 s (`shortWait`) in that state [R7]; gOuroboros sets
no timeout there. Votes come once a round, so a gOuroboros server that blocks
for new votes will be timed out by a reference client. The fix is two
messages, a state and a timeout, a protocol change rather than a small fix.

The fix, gOuroboros branch `fix/perasvotes-await-reply` (`f7ebba9b`) [G2],
does what the reference does. Messages 6 and 7 encode as `[6]` and `[7]`
[R7, Codec.hs lines 166-171, 239-242]. `ObjectIDsBlocking` (CanAwait) takes a
non-empty reply or `MsgAwaitReply`; the new `ObjectIDsBlockingMustReply`
takes a non-empty reply or `MsgServerIdle`, both back to Idle. The client
waits 10 s in the first and 60 s in the second [R7]. `Sync` asks again after
`MsgServerIdle`, acknowledging nothing, since the idle request's
acknowledgement already counted. A server with no vote sends `MsgAwaitReply`
at once, then waits up to `AwaitTimeout` (30 s by default, always below the
client's 60 s) through an optional `AwaitObjectIDsFunc`, and sends the
identifiers that arrive or `MsgServerIdle`. `PerasVotesFixed.cfg` checks it:
`ReferenceServer` and `ClientKnowsAwait` both describe the fixed code, and
`PerasVotesFixedIdleProbesBug.cfg` shows the idle path is reached.

## LeiosFetch range delivery (`LeiosFetchRangeDelivery.tla`)

Hazard C8, gOuroboros #3232 (`fix/leiosfetch-range-delivery-leak`).

### What the code does

A block-range request gets several replies, the last one terminal. The
receive loop hands each to the request slot (`deliverRange`), which queues it
on the request's delivery; the delivery goroutine (`requestDelivery.run`)
moves the queue into the caller's one-slot channel. The terminal reply clears
the slot's waiter and frees the slot at once, while earlier replies may still
be unread. A caller that leaves early calls `abandon(w)` (its context ended)
or `release(w)` (the protocol ended); both act only while `w` is the live
waiter.

### The answers

| Config | Behaviour | Result |
| --- | --- | --- |
| `LeiosFetchRangeDeliveryLeakBug` | main, the caller leaves through `abandon` after the terminal reply | **fails** `DeliveryEndsWhenCallerLeaves`: `run` holds a reply, blocked on the full channel |
| `LeiosFetchRangeDeliveryLeakReleaseBug` | main, the protocol ends (`release`) after the terminal reply | **fails** the same way |
| `LeiosFetchRangeDeliverySecondLeakBug` | main, with a second request on the freed slot | **fails** the same way |
| `LeiosFetchRangeDelivery` | the fix: the slot keeps a finished range's delivery, keyed by its waiter, until its caller's `abandon` or `release` stops it | passes `DeliveryEndsWhenCallerLeaves`, `OwnDeliveryOnly` |
| `LeiosFetchRangeDeliverySecond` | the fix, with a second request taking the freed slot | passes: a late `abandon`/`release` by the first caller stops only its own range, never the newer waiter |

The counterexample is the Go test's: three replies queued, the terminal one
frees the slot, the caller leaves, and the delivery goroutine stays blocked
(`TestRangeDeliveryEndsWhenCallerLeavesAfterLastReply`, subtests `abandon` and
`release`; goleak finds `run`). TLC's shortest trace leaves before reading any
reply; the test reads one first, which changes nothing.

## Peras client exchange lock and server await (`PerasClientOpMu.tla`)

Hazards C13, C14, C15, gOuroboros #3276
(`fix/perasvotes-op-lock-and-await-panic`).

### What the code does

Every client call holds one lock for its whole exchange; `Sync` holds it for
its whole life and runs `VoteFunc` under it. On main the lock is a
`sync.Mutex` (`opMu`). The fix makes it a one-slot channel taken in a select
with the caller's context, and a call whose context carries the client's
`VoteFunc` marker fails at once with `ErrCalledFromVoteFunc`. On the server,
`AwaitObjectIDsFunc` ran on a bare goroutine; the fix starts it through
`RunLoop`, which recovers a panic and puts the goroutine in `Stop`'s join.

### The answers

| Config | Behaviour | Result |
| --- | --- | --- |
| `PerasClientOpMuReentryBug` | C13, main: `VoteFunc` calls the client with its callback context | **fails** `VoteFuncCallReturns` (`TestVoteFuncCallingItsClientReturnsAtOnce`) |
| `PerasClientOpMuReentryCancelBug` | C13 sibling, main: the call back's context ends | **fails** `VoteFuncCallReturns`: a mutex ignores the context |
| `PerasClientOpMuDoneCtxBug` | C14, main: `Sync` holds the lock while the server withholds its answer; `Done` with an ended context | **fails** `CancelledDoneReturns` (`TestDoneHonoursContextWhileSyncRuns`) |
| `PerasClientOpMuAwaitPanicBug` | C15, main: `AwaitObjectIDsFunc` panics on a bare goroutine | **fails** `NoProcessCrash` (`TestAwaitObjectIDsPanicIsContained` crashes the binary) |
| `PerasClientOpMuAwaitUnjoinedBug` | C15 unjoined part (C11), main: `Stop` returns nil while the await goroutine runs | **fails** `StopJoinsAwait` |
| `PerasClientOpMu` | the fix, own-context call back, `Done` caller, await that returns, panics or ignores its context | passes all five invariants |
| `PerasClientOpMuAnswered` | the fix, server answering, call back on another context that ends | passes, including `EveryCallReturns` |
| `PerasClientOpMuForeignBackgroundProbeBug` | probe, the fix: a call back on another context that never ends | **fails** `EveryCallReturns`: it waits for the `Sync` running it, as `Sync`'s doc says. Contract, not a defect |

## LeiosNotify server restart and Stop (`LeiosNotifyServerRestart.tla`)

Hazards C18 and C19 (CONCURRENCY.md), README gap "`ResponseSentFunc` and late
notifications".

### What the code does

The server runs `RequestNextFunc` (the source) on a `RunLoop` goroutine of the
instance that read the request, and a second `RunLoop` goroutine waits for the
source's answer, the client's `MsgQuit` (`QuitChan`) or the instance's
`DoneChan`. An answer is sent and then handed to `ResponseSentFunc`; a quit
first sends `MsgCanceled` and leaves a third goroutine that hands a
notification the source returns later to `ResponseSentFunc` with
`ErrRequestCanceled`. `MsgQuit` is handled only once the request is answered;
`handleQuit` sends `MsgDone`, stops the instance with `StopForRestart` (which
does not wait) and installs a new one. `Server.Stop` stops the current
instance and waits for its goroutines.

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LeiosNotifyServerRestartRetiredBug.cfg`: gOuroboros `7cd17437` | 95 | **fails** `NoCallbackAfterStop` |
| `LeiosNotifyServerRestart.cfg`: the fix, `Stop` also waits for retired instances | 90 | passes |
| `LeiosNotifyServerRestartQuitUnheldBug.cfg`: mutation, `MsgQuit` handled before the reply | 149 | **fails** `ReplyOnOwnInstance` |
| `LeiosNotifyServerRestartProbeBug.cfg`: probe, `Stop` after the restart while the retired source runs | 90 | violated, as expected |
| `LeiosNotifyServerRestartCallbackStopWaitsBug.cfg`: `bf0d7a47`, callbacks call `Stop` | 87 | **fails** `CallbackStopDoesNotWait` |
| `LeiosNotifyServerRestartCallbackStopDeadlockBug.cfg`: `bf0d7a47`, without that invariant | 217 | **fails**: deadlock |
| `LeiosNotifyServerRestartCallbackStop.cfg`: `97045bac`, a callback's `Stop` only signals | 305 | passes all five invariants, no deadlock |
| `LeiosNotifyServerRestartCallbackStopProbeBug.cfg`: probe, both callbacks call `Stop` after the restart | 167 | violated, as expected |

**Defect: `Stop` returns before a retired run's callbacks.** After a restart,
`Stop` joins only the new instance. A source that ignores `QuitChan` is still
running on the retired one, and its notification reaches `ResponseSentFunc`
after `Stop` returned. `TestStopWaitsForSourceOfRetiredRun` fails on
`7cd17437` ("Stop returned before the late ResponseSentFunc ran") and passes
on `fix/leios-dmq-lifecycle` `bf0d7a47`, where `handleQuit` records the
retired instance and `Stop` waits for it. `ReplyOnOwnInstance` and
`ResponseSentOnce` hold at `7cd17437`: the answer always precedes the restart,
because `MsgQuit` is held back until the reply is sent, so the request
goroutine's later `ProtocolInstance()` calls cannot reach the new instance
with a send.

**Defect in the fix: `Stop` from a callback waits (review of `bf0d7a47`).**
`Stop`'s doc says that with a callback's `Context` it returns without
waiting. At `bf0d7a47` it passed that context to every instance's join, and
`Protocol.join` skips only the instance the callback belongs to, so a
callback's `Stop` waited for the current and retired instances. With
`CallbackStop` the first run's `ResponseSentFunc` (on the retired instance
after the restart) and the second run's `RequestNextFunc` may each call
`Stop` with their own context: at `bf0d7a47` (`"skipOwn"`) the first waits
for the second instance and the second for the retired one, a deadlock; two
retired runs whose callbacks call `Stop` form the same cycle. `97045bac`
(`"signal"`): a callback context of the current or any retired instance only
signals stop, and the user's `Stop` still waits for both instances
(`NoCallbackAfterStop` now covers the second instance's source). Go:
`TestStopFromCallbackDoesNotWaitForRetiredRun`.

## LeiosVotes and LeiosNotify client lifecycle (`LeiosVotesLifecycle.tla`)

Hazards C10, C11, C21. The two clients share a shape (`busyMutex` for the loop
flag, `sendMutex` from the shutdown check through the sends, a loop started by
`RunLoop`), so one model covers both.

| Config | States | Result |
| --- | --- | --- |
| `LeiosVotesLifecycleRunLoopBug.cfg`: gOuroboros `7cd17437` | 105 | **fails** `SyncReportsLoop` |
| `LeiosVotesLifecycle.cfg`: the fix, `Sync` honours `RunLoop`'s result | 105 | passes |
| `LeiosVotesLifecycleStopUnlockedBug.cfg`: mutation, `Stop` without `sendMutex` | 64 | **fails** `NoRequestAfterDone` |
| `LeiosVotesLifecycleProbeBug.cfg`: probe, loops close while `Sync` starts its loop | 98 | violated, as expected |

**Defect: `Sync` reports a loop that never started.** `RunLoop` starts nothing
once the connection has begun to close, but both clients' `Sync` marked the
loop running before calling it and ignored its result, so `Sync` returned nil
and later calls saw "already running". `TestSyncOutcomeFollowsLifecycle`
(leiosvotes) and `TestSyncReportsNotificationLoopThatCannotStart`
(leiosnotify) fail on `7cd17437` and pass on `fix/leios-dmq-lifecycle`
`3088a839`. C10 (`busyMutex` held across the vote waits) and C11/C21 (unjoined
loops) are closed on `7cd17437`: the waits end on `DoneChan`, and `RunLoop`
goroutines are in `Stop`'s join (`NoCallbackAfterStop` passes).

## LeiosNotify and LeiosVotes client teardown (`LeiosNotifyClientTeardown.tla`)

gOuroboros v0.222.0 `0c00b799`, `protocol/leiosnotify/client.go` and
`protocol/leiosvotes/client.go`; the engine is `protocol/protocol.go`.

### What the code does

The receive loop's handler hands each notification (vote) to the client's
own loop (`notificationLoop`, `voteLoop`, started through `RunLoop`) over an
unbuffered channel, in a select whose only other case is `DoneChan`. The
engine closes `DoneChan` only after `recvLoop` and `sendLoop` return, so that
case can never fire while the handler runs. If the callback fails, the loop
calls `SendError` and returns at once; with pipelining (LeiosNotify
`PipelineLimit` > 1, or one LeiosVotes request for several votes) a later
message may already be in the handler, and nothing will ever receive it.
`recvLoop` never returns, `DoneChan` never closes, and `Stop` (and the
connection's `Close`, which joins the same loops) waits for ever. The
`ErrStopNotificationProcess` / `ErrStopVoteProcess` path drains the owed
messages first and is safe.

The reference clients run the callback on the mini-protocol's own thread and
collect each pipelined reply there (typed-protocols pipelined peers), so a
failing callback ends the whole thread and no reply is left half-handed.

### The answers

| Config | Expected | Distinct states |
| --- | --- | --- |
| `LeiosNotifyClientTeardownBug.cfg` | deadlock (v0.222.0) | 393 |
| `LeiosNotifyClientTeardownVotesBug.cfg` | deadlock (LeiosVotes, same shape) | 393 |
| `LeiosNotifyClientTeardownLiveBug.cfg` | `StopReturns` violated | 393 |
| `LeiosNotifyClientTeardownToday.cfg` | pass: callbacks that succeed or stop cleanly | 360 |
| `LeiosNotifyClientTeardown.cfg` | pass: the fix (handler also ends on `StopChan`) | 452 |
| `LeiosNotifyClientTeardownLive.cfg` | pass: `StopReturns`, `AllGoroutinesExit` | 452 |
| `LeiosNotifyClientTeardownCloseOnStopBug.cfg` | `NoSendOnClosed` violated (mutation: closer on `StopChan`) | 256 |
| `LeiosNotifyClientTeardownCloserOutlivesStopBug.cfg` | `NothingOutlivesStop` violated (probe) | 354 |

`NoSendOnClosed` holds today because the closer waits for `DoneChan`; the
mutation shows that ordering is what keeps it. The probe records that `Stop`
can return before the closer goroutine has run: it is unjoined but bounded
(the liveness config shows it always ends), so it is reported, not fixed.

Go: local branches `fix/leiosnotify-handler-stop`
(`TestClientStopsAfterCallbackErrorWithPipelinedNotification`) and
`fix/leiosvotes-handler-stop`
(`TestClientStopsAfterVoteCallbackErrorWithVoteInFlight`); each fails on
v0.222.0 with `Stop` hitting its 2 s deadline and passes with the fix.

## The three servers' promoted methods (C9, C12, C20)

The leios-fetch, leios-votes and leios-notify servers embedded the
`*protocol.Protocol` they replace on restart, so a promoted method read it
with no lock (gOuroboros #3273, `fix/leios-server-protocol-race`). Their
restart is the same as keep-alive's (`StopForRestart`; install under
`protocolMu`; `Start`), so `specs/keepalive` `KeepAliveLifecycle.tla`, which
names all three in its header, covers it: `KeepAliveLifecycleReaderUnlockedBug`
fails `NoRacingRead`, `KeepAliveLifecycleReader` passes. The join of their
`RunLoop` goroutines (C11, C18, C21) is a separate change, modelled in
`specs/engine` (`EngineLifecycleCtxRunLoopUnjoinedBug`).

## Spec, reference, and gOuroboros

| Question | Specification / CIP | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| LeiosNotify states | CIP: separate LeiosAnnounce and LeiosBlockNotify with tokens [C1] | One LeiosNotify: Idle, Busy, Quit, Done; `MsgQuit`, `MsgCanceled` [R1] | As the reference | Follows the reference |
| Request after `MsgQuit` | Not stated | Never: `drainThePipe` [R2] | Possible when `Stop` races a refill | **Defect 1**, fixed |
| `MsgCanceled` before `MsgQuit` | Not stated | Disconnect [R2] | Ignored; the loop stalls | **Defect 2**, fixed |
| LeiosNotify timeouts | Not stated | Idle, Busy forever; Quit 60 s [R1] | Same | Agree |
| LeiosNotify reply size | Not stated | 1,536 bytes, at most 16 votes [R1] | 655,350 bytes, 1,000 votes | Differs; byte limits are out of this model's scope |
| LeiosFetch states | CIP: `MsgLeiosMultiBlockRequest`, `MsgLeiosNoMoreBlocks` [C3] | Block, BlockTxs only [R3] | Reference states, plus Votes and BlockRange (tags 10-14) | Follows the reference; extensions consistent |
| LeiosFetch pipelining | "possibly with mini-protocol pipelining" [C3] | Client pipelines up to a depth; replies to the job that sent each [R4] | Server holds pipelined requests; client sends one at a time through a slot | Agree on the wire |
| LeiosFetch Block, BlockTxs timeouts | Not stated | 60 s (`longWait`) [R3] | None in the client; the caller's context bounds the wait | Differs: a caller without a deadline waits forever |
| LeiosVotes pipelined request in Busy | Expected [C2] | No reference | Refused by the server | **Defect 3**, fixed |
| LeiosVotes count limit | Unbounded N | No reference | 1 to 1,000 | Differs; recorded |
| ObjectDiffusion await | Not stated | `MsgAwaitReply`, `MsgServerIdle`, `MustReply` [R6] | Missing at `61046085`; as the reference with the fix [G2] | **Deviation**, fixed on a branch |
| ObjectDiffusion blocking timeout | Not stated | 10 s, then 60 s after await [R7] | None at `61046085`; 10 s and 60 s with the fix [G2] | Fixed on a branch |
| Server restart after `MsgDone` | Spec 5.7: responders restart | Yes | LeiosNotify, LeiosFetch, LeiosVotes: yes. Peras: no on `main` | Peras **does not conform**; fixed on `fix/perasvotes-server-restart` |

## Go tests and mutations

On gOuroboros `origin/main` `61046085`. Each new test was run against a
mutation of the line it guards and failed; the table lists them.

| Branch | Test | Mutation that fails it |
| --- | --- | --- |
| `test/leiosnotify-state-model` | `TestStateMapMatchesModel` (both roles, every active state and message type), `TestClientPipelinesOnlyRequestsAndQuit`, `TestStatesThatCannotBeEntered`, `TestStateMapTimeoutsMatchReference` | `MsgQuit` dropped from Busy's pipelined types; Quit's `MsgDone` leading to Idle; `MsgCanceled`'s transition retyped; every state given the Quit timeout |
| `test/leiosfetch-state-model` | `TestStateMapMatchesModel`, `TestClientNeverWritesWithoutAgency`, `TestStatesThatCannotBeEntered` | `VotesRequest` made pipelined; `LastBlockAndTxsInRange` staying in BlockRange; Block allowing pipelined sends |
| `test/leiosvotes-state-model` (on the fix) | `TestStateMapMatchesModel` (Busy split by tokens), `TestTokensFollowTheModel`, `TestStatesThatCannotBeEntered`, `TestRequestNextAfterStoppedSyncGetsOwnVote` | last-vote check `<= 1` to `< 1`; zero count accepted; tokens not decremented; the fix reverted; `drainVotes` skipped |
| `test/perasvotes-state-model` | `TestStateMapMatchesModel` (each state reached through a real window), `TestStatesThatCannotBeEntered` | blocking rule dropped; empty blocking reply accepted; unrequested object accepted; non-outstanding identifier requestable |
| `fix/leiosnotify-request-after-quit` | `TestStopDuringRefillSendsNoRequestAfterQuit`, `TestSyncAfterStopIsRefused` | Fail without the fix: request 33 to 59 of a 100-request refill followed `MsgQuit` in 4 of 5 runs; `Sync` after `Stop` returned nil |
| `fix/leiosnotify-unexpected-cancel` | `TestClientRefusesCanceledBeforeQuit`, `TestClientAcceptsCanceledAfterQuit` | Fails without the fix |
| `fix/perasvotes-await-reply` (`f7ebba9b`, includes the state-model test with the MustReply row) | `TestClientAcceptsAwaitReplyThenIDs`, `TestSyncContinuesAfterServerIdle`, `TestClientBlockingRequestTimeouts`, `TestServerWithNoVoteSendsAwaitReply`, `TestStateMapMatchesModel` cell `client/inObjectIDsBlocking/AwaitReply` | Fail on `61046085`: "unknown message type 7"; Sync stops after the idle; Blocking timeout 0; the server fails with "blocking Peras object ID request requires a non-empty reply"; the cell is Violation |
| `fix/perasvotes-server-restart` (from `d8f5bc2a`, after the await fix merged) | `TestServerAnswersRequestAfterRestart`, `TestServerAnswersInitSentDuringRestart` | Fail on `d8f5bc2a`: "no reply from restarted server: ReplyObjectIDs"; "server never reached its Done handler" (the server ignored `MsgDone`). `TestClientServerObjectDiffusionFlow` now expects the restart |
| `fix/leiosvotes-pipelined-requests` | `TestServerAnswersPipelinedRequestNext` | Fails without the fix: "received message type 0 without peer agency ... in state Busy" |

Existing tests already covered the LeiosFetch slot (above), LeiosNotify's
drain on `ErrStopNotificationProcess` (`TestNotificationLoopDrainsOnStop`
fails when the drain is removed), server restarts after `MsgDone`, and the
ObjectDiffusion window rules (`TestObjectDiffusionWindowAndAgencyRules`).

## Sources

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | [ouroboros-network `5f356486ab3e`, `docs/network-spec/miniprotocols.tex` line 2231](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L2231) | `NodeToNodeV_17`: "Experimental, support Peras mini-protocols". Nothing else on Peras or Leios. |
| R1 | [ouroboros-consensus `ec239d57f618`, `.../MiniProtocol/LeiosNotify/Type.hs` lines 126-162, 187-227, 332-358](https://github.com/IntersectMBO/ouroboros-consensus/blob/ec239d57f618d698b6350b48bf017b02c0c96a5f/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LeiosNotify/Type.hs#L126-L162) | States, agencies and messages; reply byte limit and 16 votes; Idle and Busy wait forever, Quit `longWait`; the codec's legal (state, tag) pairs. |
| R2 | [`.../LeiosNotify/Client.hs` lines 95-236](https://github.com/IntersectMBO/ouroboros-consensus/blob/ec239d57f618d698b6350b48bf017b02c0c96a5f/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LeiosNotify/Client.hs#L95-L236) | `MsgCanceled` before `MsgQuit` throws `ExnLeiosNotifyUnexpectedCancel`; the client pipelines requests and `MsgQuit`, then only drains. |
| R3 | [`.../LeiosFetch/Type.hs` lines 78-104, 164-183, 240-246](https://github.com/IntersectMBO/ouroboros-consensus/blob/ec239d57f618d698b6350b48bf017b02c0c96a5f/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LeiosFetch/Type.hs#L164-L183) | Idle, Busy Block, Busy BlockTxs, Done; messages 0-4; Block and BlockTxs `longWait`. |
| R4 | [`.../LeiosFetch/Client.hs` lines 70-168](https://github.com/IntersectMBO/ouroboros-consensus/blob/ec239d57f618d698b6350b48bf017b02c0c96a5f/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LeiosFetch/Client.hs#L70-L168) | Pipelined requests up to a depth; each reply to its job's receiver; on stop, drain then `MsgDone`. |
| R5 | [`.../LeiosNotify/Server.hs` lines 51-134](https://github.com/IntersectMBO/ouroboros-consensus/blob/ec239d57f618d698b6350b48bf017b02c0c96a5f/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LeiosNotify/Server.hs#L51-L134) | After `MsgQuit` every outstanding request is answered with `MsgCanceled`, then `MsgDone`. |
| R6 | [ouroboros-network `5f356486ab3e`, `.../Protocol/ObjectDiffusion/Type.hs` lines 100-140, 190-393](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ObjectDiffusion/Type.hs#L263-L393) | States and agencies; the blocking rule; `MsgAwaitReply` (CanAwait to MustReply) and `MsgServerIdle` (MustReply to Idle). Added in commit `9e103eee6e77`, 2026-11-11. |
| R7 | [`.../ObjectDiffusion/Codec.hs` lines 60-92, 133-171](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ObjectDiffusion/Codec.hs#L60-L92) | Time limits (`shortWait` 10 s, `longWait` 60 s, from `Protocol/Limits.hs` lines 113-120) and wire tags 0-7. |
| C1 | [CIP-0164, cardano-foundation/CIPs `03387471`, lines 1386-1416](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0164/README.md?plain=1#L1386-L1416) | Figure 6b, LeiosVotes: tokens, votes, `MsgDone` from Idle. |
| C2 | [CIP-0164 lines 1376-1385, 1449-1477](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0164/README.md?plain=1#L1449-L1477) | The next request goes before the previous batch is delivered, by protocol pipelining. |
| C3 | [CIP-0164 lines 1480-1548](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0164/README.md?plain=1#L1480-L1548) | The CIP's LeiosFetch and its message table. |
| C4 | [CIP-0140 line 1515](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0140/README.md?plain=1#L1515) | Two new mini-protocols for vote and certificate diffusion. |
| G1 | gOuroboros `61046085`, `protocol/leiosnotify/`, `protocol/leiosfetch/`, `protocol/leiosvotes/`, `protocol/perasvotes/`, and `protocol/protocol.go` (`sendLoop`, `reserveInboundAdmission`, `recvLoop`) | The code modelled. |
| G3 | gOuroboros `7cd17437`, `protocol/leiosnotify/server.go`, `client.go`, `protocol/leiosvotes/client.go`, `protocol/protocol.go` (`RunLoop`, `join`, `StopForRestart`), `muxer/loops.go` | The code `LeiosNotifyServerRestart.tla` and `LeiosVotesLifecycle.tla` model. |
| R11 | [ouroboros-network `5f356486ab3e`, `ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs` lines 455-470](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L455-L470) | A responder that ended cleanly is run again. |
| R14 | [ouroboros-network `5f356486ab3e`, `network-mux/src/Network/Mux.hs` lines 280-287](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L280-L287) | The mux waits for a mini-protocol's threads before it returns. |
| G2 | gOuroboros `f7ebba9b` on local branch `fix/perasvotes-await-reply`, `protocol/perasvotes/` | The await fix: StateMap, `Sync`, `awaitObjectIDs`. |

## Not modelled

Byte and count limits, message validation (LeiosFetch reply binding, vote
decoding), timeouts beyond the table above, LeiosFetch's range streams beyond
one reply, Peras non-blocking requests and certificates.
`LeiosNotifyServerRestart.tla` models one request of the first run and,
with `CallbackStop`, the second run's source; a second restart and pipelined
requests are not modelled.

## Running it

```sh
cd specs/leios-peras
for c in LeiosNotify LeiosNotifyDeep LeiosNotifyDry LeiosNotifyRogueCancel; do ../../bin/tlc -config $c.cfg LeiosNotify.tla; done
for c in LeiosFetch LeiosFetchDeep; do ../../bin/tlc -config $c.cfg LeiosFetch.tla; done
for c in LeiosVotes LeiosVotesToday LeiosVotesCipClient; do ../../bin/tlc -config $c.cfg LeiosVotes.tla; done
for c in PerasVotes PerasVotesFixed PerasVotesFixedDeep; do ../../bin/tlc -config $c.cfg PerasVotes.tla; done
# Expected to fail:
for c in LeiosNotifyQuitRaceBug LeiosNotifyRogueCancelBug LeiosNotifyNoCancelBug LeiosNotifyProbesBug; do ../../bin/tlc -config $c.cfg LeiosNotify.tla; done
for c in LeiosFetchAbandonFreesBug LeiosFetchProbesBug; do ../../bin/tlc -config $c.cfg LeiosFetch.tla; done
for c in LeiosVotesCipClientBug LeiosVotesNoDrainBug LeiosVotesProbesBug; do ../../bin/tlc -config $c.cfg LeiosVotes.tla; done
for c in PerasVotesReferenceServerBug PerasVotesEmptyServerBug PerasVotesProbesBug PerasVotesFixedIdleProbesBug; do ../../bin/tlc -config $c.cfg PerasVotes.tla; done
# Range delivery (C8) and the Peras exchange lock (C13-C15), both ways:
for c in LeiosFetchRangeDelivery*.cfg; do ../../bin/tlc -config $c LeiosFetchRangeDelivery.tla; done
for c in PerasClientOpMu*.cfg; do ../../bin/tlc -config $c PerasClientOpMu.tla; done
# Server restart and Stop, and the clients' Sync and loop (C10, C11, C18, C21):
for c in LeiosNotifyServerRestart*.cfg; do ../../bin/tlc -config $c LeiosNotifyServerRestart.tla; done
for c in LeiosVotesLifecycle*.cfg; do ../../bin/tlc -config $c LeiosVotesLifecycle.tla; done
```
