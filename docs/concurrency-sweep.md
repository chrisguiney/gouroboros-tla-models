# Concurrency sweep of the models

This sweep asks, for every model under `specs/`, how much of the Go
concurrency in the code it models it represents: goroutines, channels, locks,
joins and timers, as opposed to protocol states and agency only. It feeds the
integration layer, which will compose these models into connection-level and
sync-path models.

- **Models:** this repository at `main` 271529d.
- **Code:** gOuroboros `integration/release-candidate` at `4473341`, non-test
  files. Every Go `file:line` below is at that commit and relative to the
  package named in the row. A `spec:N` reference is a line in the `.tla`
  being discussed.
- **Method:** a grep count of Go primitives per package, then reading each
  package's concurrency sites and every networking module's variables, actions,
  `Spec`/`FairSpec`, and configs. Nothing was run in TLC. The older
  inventory in [CONCURRENCY.md](../CONCURRENCY.md) (at `d8f5bc2`) was used
  as a map and checked against the release candidate.

## Classes

- **A, concurrency-faithful:** each goroutine has its own program counter
  and steps; locks are acquired and released as separate steps; channels have
  capacity, blocking and close; joins are explicit.
- **A−:** as A, with one or two primitives (usually a channel or one lock)
  folded into an atomic step.
- **B, partial:** some goroutines or locks are separate steps; channels are
  sequences, counters or flags without blocking or close semantics.
- **C, state machine:** protocol states, agency and messages; one action per
  message; no goroutine, lock or channel structure.

## TLC's deadlock check

TLC checks for deadlock unless a config sets `CHECK_DEADLOCK FALSE`. A
disjunct of `Next` that stutters also turns the check off in every state where
it is enabled. This sweep marks a stutter that is enabled only in genuine end
states as **honest**. It marks one that is enabled unconditionally, or
whenever nothing else is (`~ENABLED Progress`), as a **mask**.

## Summary

Counts are per Go package at the release candidate. They are grep counts:
`go` statements (plus `WaitGroup.Go`, `RunLoop`, `AfterFunc` where named),
`make(chan ...)` sites, and lines declaring `sync.Mutex`/`RWMutex`.

| Spec dir | Go goroutines / channels / locks | Processes | Channels | Locks | Joins | Timers | Liveness + fairness | Deadlock check | Class | Top gaps |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| connection | root `connection.go`: 1 + 1 `WaitGroup.Go` / 5 / 3 | not swept | not swept | not swept | not swept | not swept | ConnectionLifecycle (WF; `PROPERTY` in 2 cfgs) | default in every cfg | not swept | not swept |
| muxer | 3 + 2 `WaitGroup.Go` / 16 / 10, 2 `sync.Cond` | not swept | not swept | not swept | not swept | not swept | MuxEgress (WF; `MuxEgressLive` cfgs) | default in every cfg | not swept | not swept |
| handshake | 1 / 1 / 0 | not swept | not swept | not swept | not swept | not swept | HandshakeSimOpenDelivery (WF); `PROPERTY` in 23 cfgs | default in every cfg | not swept | not swept |
| keepalive | 1 + `AfterFunc` / 0 / 3 | not swept | not swept | not swept | not swept | not swept | none (`PROPERTY` in 3 KeepAlive cfgs) | default in every cfg | not swept | not swept |
| engine (`protocol`) | 2 + `RunLoop` / 15 / 6, 4 timers, 36 selects | not swept | not swept | not swept | not swept | not swept | EngineSendDrained (WF) | 5 EngineSendDrained cfgs FALSE | not swept | not swept |
| chainsync | 4 / 20 / 4 (+`TryLock` polling, 36 selects) | TipWorker 7 pcs; Client, Queries 3 pcs | ready chan as bounded Seq that flags `overflow` instead of blocking; want chans as one-slot values | `busy` explicit; `lifecycleMutex` explicit in Client, atomic in TipWorker | TipWorker `TipJoin`; stop finisher unjoined in model and code | `TryLock` deadline as ticks | TipWorker, TipWindow (WF + `~>`) | 2 cfgs FALSE (stream bugs, liveness reports); TipWindow masked | B (TipWorker A−) | close of `readyForNextBlockChan` vs handler sends; new stop-finisher goroutine; unbounded send queue |
| blockfetch | 2 + 3 group `Go` + `RunLoop` / 12 / 8 | BusyDelivery 6 goroutines with frame stacks; Admission, RangeCheck, BusyHandoff per caller | token, generation counter for `bytesFreed`; per-request chans absent | BusyDelivery: L, Q, T, D owners, wait-for graph | `JoinWatchers`/`StartJoinsGroup` flags | deadline as a nondeterministic step | BusyHandoff, OversizedRefusal | 5 cfgs FALSE; ClientReader, ServerSend masked | B (BusyDelivery A) | per-request non-blocking sends with `default:`; `goroutineGroup` fallback `go watch()`; send backpressure under `busyMutex` |
| txsubmission | 0 / 3 / 6 | ServerLocks: callers, handler, stopper | one-slot result `slot[i]`, blocking | RWMutex with writer preference, `reqMu`, `stMu` | `done[i]` | none in code | ServerLocks (WF, `StopTerminates`) | default; Pipelined `Quiet` stutters on a blocking wait | B (ServerLocks A−) | client restart waits on `oldDone` under `lifecycleMutex`; `requestMu` across a bounded send |
| peersharing | 0 / 1 / 3 | Exchange: callers | unbuffered reply as atomic rendezvous | `exchangeLock` explicit; `requestedMutex` folded | one `stopped` flag | abstract | Exchange (WF, `EveryCallerReturns`) | default | B | StopChan, DoneChan and timeout merged; `exchangeLock` across an unbounded send |
| localtx | 2 / 8 / 4 (+ server watcher goroutine) | ClientCalls one call; no per-caller pcs | `inbox[r]` Seq; result chans and closers absent | lock derived (`waiting /= {}`) or a string | none | abstract `Timeout` | none | 5 cfgs FALSE (rogue, agency); `WaitsForever` stutter | B− | result channel and closer at teardown; N callers on `busyMutex`; server cancel watcher leak |
| localstatequery | 1 / 2 / 2 | Client: per-caller `cpc`, handler `hpc` | unbuffered rendezvous; `done` only after handler idle | `busy` with separate Lock/Unlock | closer folded into `done` | Limits: abstract timer | none | default, honest `Finished` | A− (Client); rest C | check-then-send (:2042/:2058) atomic; no ctx; Limits one caller |
| dmq | 3 / 6 / 12 | ReplayShared per connection + cleaner; LMN handler + waiter | LMN one-slot signal (RC uses close-and-replace); `sendQ` Seq | replay lock one step; Prepare/Commit splits | ReplayShared `StopWaits` | DmqBlockingDeadline arithmetic | DmqReplayShared (WF, `~>`) | default; LMN `Quiet` accepts exhausted adds | B (ReplayShared A−) | LMN timer, Stop, broadcast; LMS `busyMutex`/`stopMutex` order; MessageSubmission protocol-only |
| leios-peras | 3 + 7 `RunLoop` + per-range / 12 / 10 | NotifyServerRestart, FetchRangeDelivery, VotesLifecycle, PerasClientOpMu per goroutine | `buf` one-slot, `stopped` close; others Seq or counter | explicit holders in A modules | join sets in A modules | `abandonedRequestWait` absent | none | PerasClientOpMu masked (`~ENABLED Progress`) | A/B | leiosfetch `drainedCh` broadcast and timer; unbuffered chans as counters; perasvotes dropped replies |
| pipeline-cbor | 6 + worker pool / 22 / 9 | PipelineLifecycle: one pc per goroutine | bounded `Len <= Cap`, close flags, `NoPanic` | `mu`, `submitGate` explicit; leaf locks one step | runner join, teardown | ticker absent | none | 1 cfg FALSE; partial mask judged by `NoLeakWhenQuiescent` | A (BlockPipeline B) | `rawBytesFreed`/`completionChan` as guards; `errorsChan`, validate pool absent; Cap=1, one worker |
| ledger-hash-cache | 0 / 1 / 8, CAS | HashCacheSpin per caller, one atomic op per step | `done` close in TxScopedMemo | memo lock as a step | `done` wait | none | HashCacheSpin (WF, `WaitersReturn`) | PooledEvalContext 5 cfgs FALSE, no reason stated | A (PooledEvalContext B) | `Reset` vs `Get` contract only; other leaf memos |
| limits-timeouts | (engine timers) | none | none | none | none | timer fires at any step | none | default, `Quiet` accepts a silent peer | C | no cfg for chainsync, blockfetch, txsubmission, peersharing |
| 20 ledger, consensus, cbor, hello dirs | leaf locks, Once, `sync.Map`, atomics | n/a | n/a | n/a | n/a | n/a | n/a | n/a | C (pure) | none needed |

**Class counts by spec directory** (36 directories): A 2 (pipeline-cbor, ledger-hash-cache); mixed A/B 2 (localstatequery, leios-peras); B 6 (chainsync, blockfetch, txsubmission, peersharing, dmq, localtx); C 21 (limits-timeouts and the 20 pure directories); not swept 5 (connection, muxer, handshake, keepalive, engine). By module, among the swept networking directories: A 8 (BlockFetchBusyDelivery, LeiosNotifyServerRestart, LeiosFetchRangeDelivery, LeiosVotesLifecycle, PerasClientOpMu, PipelineLifecycle, HashCacheSpin, TxScopedMemo) and A− 4 (ChainSyncTipWorker, TxSubmissionServerLocks, LocalStateQueryClient, DmqReplayShared).


**Top gaps, ranked by bug risk** (swept directories only):

1. **Lock held across a blocking send.** Every model's engine send queue is
   unbounded, but Go's has capacity 80. The deadlock class hidden is lock
   plus channel (finding 3).
2. **Send on a closed channel, and goroutine leaks at teardown.**
   - the chainsync ready channel;
   - the result channels and their closer goroutines in localtx,
     localstatequery, localmessagesubmission and leiosnotify.

   (Findings 4 and 7.)
3. **Lost wakeups.** No model has the close-and-replace broadcasts, or the
   non-blocking sends that drop a signal (findings 5 and 6).
4. **Unjoined goroutines added at the release candidate, and WaitGroup
   ordering.** Every model but PipelineLifecycle and DmqReplayShared treats a
   join as a flag (findings 7 and 9).
5. **Deadlock checks masked, and liveness rare.** A caller that blocks
   forever goes unreported (findings 2 and 8).

## Findings across the models

1. **No shared concurrency module.** No spec `INSTANCE`s another, and no
   module defines a Go channel, mutex, WaitGroup or timer. Each spec
   re-abstracts the engine, so the same Go object has many names:
   - the send queue: `sendQ`, `sq`, `toServer`, `c2s`, `inbox[r]`;
   - DoneChan: `recvExited`, `done[i]`, `up`, `protoDone`, `protoStopped`;
   - muxer registration: `reg` as a Bool (Lifecycle) or an instance id
     (BusyHandoff);
   - lock holders: `"free"`, `None`, `"none"`, or a derived predicate.
2. **Liveness is rare.** Modules with fairness and a temporal property:
   ChainSyncTipWorker, ChainSyncTipWindow, BlockFetchBusyHandoff,
   OversizedRefusal, TxSubmissionServerLocks, PeerSharingExchange,
   DmqReplayShared, HashCacheSpin, and in the unswept directories ConnectionLifecycle, MuxEgress, HandshakeSimOpenDelivery and EngineSendDrained (by grep for `WF_`/`SF_`). All other modules check safety
   invariants and the deadlock check only, so a caller that blocks forever
   is found only where the deadlock check is on and not masked.
3. **No model bounds the engine's send queue.** `sendQueueChan` has capacity
   80 (`protocol/protocol.go:346`) and `SendMessage` blocks when it is full.
   Every spec that has a send queue makes it unbounded, so "lock held across a
   send that blocks" is never explored. This matters for:
   - peersharing `exchangeLock` (`client.go:94`);
   - txsubmission `requestMu`;
   - blockfetch `busyMutex` and the range send token;
   - chainsync `Stop` holding `lifecycleMutex` across the 250 ms
     `SendMessageContextAndWait` for `MsgDone`.
4. **Only PipelineLifecycle checks a send on a closed channel or a double
   close** (`NoPanic`, spec:375-382). The most exposed unmodelled site is
   chainsync's `close(readyForNextBlockChan)` (`client.go:634`), with handler
   sends at `:1498`–`:2141` under `lifecycleMutex`. ChainSyncClient models a
   full channel as `overflow` (spec:279-298), not as a blocked send.
5. **Close-and-replace broadcast channels are not modelled as channels.**
   Lost wakeups on them go unchecked:
   - pipeline `rawBytesFreed` (`pipeline.go:431,459-461`) and `completionChan`
     (`:1034-1036`);
   - localmessagenotification `messageAdded` (`server.go:180-181`);
   - leiosfetch `drainedCh` (`client.go:242,363-364,478`).

   BlockFetchAdmission's generation counter with `NoLostWakeup` (spec:248) is
   the exception and the pattern to reuse.
6. **Non-blocking sends with a `default:` branch drop signals.** blockfetch's
   per-request `startChan`/`blockChan`/`doneChan` (cap 1; `default:` at
   `client.go:844, 900, 1451, 1456, 1607, 1805, 1832`) and perasvotes' reply
   slots (`client.go:336-357`) are absent from every model, as is the
   `GetBlockRange` waiter that reads them.
7. **Unjoined goroutines at the release candidate that no model has:**
   - chainsync stop finisher (`client.go:645`, new since `d8f5bc2`);
   - chainsync `WaitForDrain` (`:2080`);
   - blockfetch fallback `go watch()` when `RunLoop` refuses (`client.go:534`);
   - localtxmonitor server cancel watcher (`server.go:213-221`);
   - the localmessagenotification expiration ticker (`server.go:393-410`; it
     is joined by `Stop`, but not modelled).
8. **Deadlock checks masked.** These modules hide deadlock from TLC:
   ChainSyncTipWindow (`Finished == ~ENABLED ...`, spec:145),
   BlockFetchClientReader (spec:154; `FetchReturns` compensates),
   BlockFetchServerSend (unconditional `UNCHANGED vars`, spec:127-130),
   BlockFetchQueue under NoDrainBug, and PerasClientOpMu (`Rest == ~ENABLED
   Progress`, spec:349; `EveryCallReturns` is not in its passing config).
   PipelineLifecycle masks partially, and `NoLeakWhenQuiescent` judges the
   parked goroutines.
9. **Drift.** Several modules were written against `279ec482`, `c1bc50c6`,
   `61046085`, `7cd17437`, `5c4f31c1`, `f9ba2d3c` or `d10daf24`. Concurrency
   changes at the release candidate that no model reflects:
   - blockfetch `goroutineGroup` (`goroutines.go:29-84`);
   - the chainsync stop-finisher goroutine;
   - the leiosnotify `sendMutex`/`quitting` fix (LeiosNotify is at
     `61046085`);
   - localmessagenotification's close-and-replace `messageAdded` and
     `WaitForMessage` timer (only a `Broadcast` config flag).

## Connection, muxer, handshake, keep-alive and engine: not swept

The agent sweeping these five directories stopped making progress: its
transcript did not change for more than twelve minutes. Their per-module
classification, gaps and interface names are missing from this document. Only
the mechanical facts in the summary table are here: the Go counts, which
modules use fairness, which configs have `PROPERTY`, and which turn off the
deadlock check.

Section 7 of [CONCURRENCY.md](../CONCURRENCY.md) still lists the most
important concurrency elements of these components (at older commits):

- connection: Close during Dial, the WaitGroup rule, the handshake timer.
- muxer: the `sync.Cond`, receiver stop against metrics callbacks, the start
  gate, egress fairness.
- engine: every timer, `lifecycleMu` Start/Stop ordering, loop joins, sends
  before `Start`.
- keep-alive: the client's `AfterFunc` timer.

The integration layer depends on these directories more than on any other:
muxer ingress and egress, the engine's send and receive queues, and the gate
that starts the muxer after the handshake. Sweep them before the interface
module is written.


## Mini-protocols

### chainsync

Go: goroutines at `client.go:645` (stop finisher, unjoined), `:727`
(`GetCurrentTip` worker, joined by `requestWorkerDone`), `:1487` (`syncLoop`,
WaitGroup Add `:1462/1468/1479`, Wait `:647`), `:2080` (`WaitForDrain`,
unjoined), and a `RunLoop` pipeline watcher at `:248`.

Channels (20 `make(chan)`):
- `readyForNextBlockChan`, cap `PipelineLimit` (`:180`): closed at `:634`;
  received at `:946`, `:1514`.
- want channels, cap 1 (`:181-183`).
- per-call result channels, cap 1.
- worker channels `:723-725`.
- unbuffered stop and drain signals.

There are 11 closes and 36 selects, 12 of them with `default:`.

Locks: client `protocolMu`, `busyMutex`, and `lifecycleMutex` (about 40
sites); server `protocolMu`. `TryLock` polling in `stopRunning` (`:526`,
`:540`, timer `:528`, ticker `:530`) and in `lockBusy` (`:1362`, `:1376`).
Also an `atomic.Bool` and four contexts.

| Module | Represents | Class |
| --- | --- | --- |
| ChainSyncTipWorker | 7 pcs (GetCurrentTip, worker, range, Jump, Stop, sync loop, handler); `busy` owner; `TryLock` deadline as ticks with ctx and callback marker (spec:733-752); worker join; `recvExited`, `stopSig`; engine `sendQ` (unbounded); WF per group, `StopReturns`/`TipReturns`/`JumpReturns` (spec:1024-1030). Honest `AllDone`. `lifecycleMutex` atomic; ready and want channels as counters; RC stop finisher folded into `StopComplete` (spec:789). | A− |
| ChainSyncClient | `syncLoop`, handler, `Reintersect` pcs (spec:139-384); `busy`, `lc` owners; ready chan as `sig` with `overflow`. No close, no Stop/DoneChan. | B |
| ChainSyncQueries | GetCurrentTip, Jump, handler pcs; `busy`; one-slot want values. | B |
| ChainSyncLifecycle, ChainSyncProtocol | atomic lifecycle steps; wire legality. | C |
| ChainSyncTipWindow | counters; WF + `ReachesTip`; masked deadlock. | C |
| ChainSyncLimits | static table. | n/a |

### blockfetch

Go:
- Goroutines: group `Go` at `client.go:312` (pipeline stop watcher), `:776`
  (`releaseBusyOnProtocolDone`) and `:1251` (`watchRangeDeadline`); the
  `RunLoop` shutdown watcher `:531` with fallback `go watch()` `:534`.
  `goroutineGroup` (`goroutines.go:29-84`) has an `idle` channel and
  `closeAndWait(ctx)`.
- Channels (12): `bytesFreed` broadcast (`:258`, closed and replaced
  `:1405-1407`); `rangeSendToken` cap 1 (`:259`); per-request `startChan`,
  `blockChan`, `doneChan` cap 1 (`:1205-1207`) and `retired` (`:1209`,
  closed in `resolveOnce`).
- 18 selects, 9 with `default:`.
- Locks: `deliveryMu`, `protocolMu`, `busyMutex` (unlocked by another
  goroutine at `:394`), `busyStateMutex`, `lifecycleMutex`, `queueMutex`
  (13 sites), the group `mu`, and server `protocolMu`.
- Also a Once (`:138`), an atomic, a timer (`:1312`), and four contexts.

| Module | Represents | Class |
| --- | --- | --- |
| BlockFetchBusyDelivery | Six goroutines with frame stacks for callback re-entry (spec:87); L, Q, T, D lock owners step by step; `cbHeld`; `once[r]`; wait-for graph `NoWaitCycle` (spec:1001); restart; deadline as a step. Honest `AllDone`. 4 cfgs FALSE (known other deadlocks). No per-request channels, `goroutineGroup` a flag, `Pipeline.Submit` blocking absent. | A |
| BlockFetchAdmission | caller pcs, token, generation counter with `NoLostWakeup`; `queueMutex` sections atomic; no `WithDeadline` wait. | B |
| BlockFetchBusyHandoff | fetch processes; busy locks merged into `holder`; instances; WF, `CallerAlwaysReleased`, `BusyEventuallyFree`. | B |
| BlockFetchRangeCheck | handler and deadline watcher pcs; `deliveryMu` owner; timer as a step. | B |
| BlockFetchRestart | per-generation goroutine status, coarse joins, ctx expiry. | B |
| BlockFetchQueue, BlockFetchClientReader, OversizedRefusal | caller processes with atomic drain; Start under `protocolMu` vs an unlocked read (masked); demux vs reader over a counter (WF, `Refused`). | B− |
| BlockFetchLifecycle, BlockFetchClientDone, BlockFetchServerSend | atomic lifecycle; explicit send queue `sq`; server send order (masked). | C |
| BlockFetchLimits | static table. | n/a |

### txsubmission

Go: no goroutines.
- Client: channel `ch` (`client.go:136`, closed `:161`, `:183`); `Start`
  waits on `<-oldDone` (`:154`); locks `protocolMu`, `lifecycleMutex`,
  `unackedMu`.
- Server: result channels cap 1 (`server.go:109-110`) with selects at
  `:280`, `:293`, `:373`, `:381` (`default:` at `:299`, `:387`); locks
  `protocolMu`, `requestMu`, `stateMu`.

| Module | Represents | Class |
| --- | --- | --- |
| TxSubmissionServerLocks | callers, handler and stopper pcs; RWMutex with writer preference (spec:139-142); `reqMu`, `stMu`; one-slot `slot[i]` that blocks when full (spec:405); `done[i]`; `StopForRestart`/`initProtocol`/`Start` split (spec:376-475); WF (spec:555), `CallerAlwaysReleased`, `StopTerminates`, `LockOrderRespected`. Client side absent. | A− |
| TxSubmission, TxSubmissionPipelined, TxSubmissionReannounce | window and acknowledgement rules, one action per message. | C |
| TxSubmissionTable | constants. | n/a |

### peersharing

Go: no goroutines.
- Unbuffered `sharePeersChan` (`client.go:43`): sent at `:154`, received at
  `:107`, each in a select against DoneChan.
- Locks: `requestedMutex`, `exchangeLock` (held across the reply wait,
  `:94-95`), server `protocolMu`.

| Module | Represents | Class |
| --- | --- | --- |
| PeerSharingExchange | caller pcs; `exchangeLock` owner; engine `sendQ` (unbounded); rendezvous enabled only while a caller waits; one `stopped` flag for Stop, timeout, error and DoneChan; WF, `EveryCallerReturns` (spec:231). | B |
| PeerSharing | protocol, abstract timeout, action properties. | C |
| PeerSharingTable | constants. | n/a |

### localtx (localtxsubmission, localtxmonitor)

Go, localtxsubmission:
- A closer goroutine for `submitResultChan` (`client.go:98-100`).
- `stopRequested` closed in `Stop` under `onceStop` (`:129`).
- `busyMutex` held across the whole call (`:164`).

Go, localtxmonitor:
- Five unbuffered result channels and `stopRequested` (`client.go:62-67`).
- `deliverResult` selects at `:454-458`.
- `busyMutex` taken at `:146` (Stop) and six call sites.
- Atomics at `localtxmonitor.go:145-146`.
- A server cancel watcher (`server.go:213-221`) that nothing joins.

| Module | Represents | Class |
| --- | --- | --- |
| LocalTxMonitorClientCalls | one call in flight; `lock`, `waiting`, `abandoned`, `stopReq`; `queue` with `Len <= 1`; Stop split into steps (spec:298-330); honest `Finished`. | B |
| LocalTxSubmission, LocalTxMonitor | role inboxes; lock derived or freed atomically inside `Recv`; result handoff and closer folded into `Recv`; `WaitsForever` stutter; 5 cfgs FALSE for rogue and agency mutations. | B− |
| LocalTxMonitorTxIdCache | data cache. | C |

### localstatequery

Go:
- A closer goroutine for `queryResultChan` and `acquireResultChan`
  (`client.go:150-153`).
- The handler checks DoneChan with `default:` (`:2042`, `:2071`, `:2103`),
  then sends without a guard (`:2058`, `:2090`, `:2109`).
- `busyMutex` held across about 40 calls.

| Module | Represents | Class |
| --- | --- | --- |
| LocalStateQueryClient | per-caller `cpc`; Lock/Unlock as steps (spec:300, 513); handler `hpc`; unbuffered rendezvous (spec:403, 444, 545); `Teardown` closes `done` only when the handler is idle (spec:674); honest `Finished` (spec:687). No ctx; check-then-send is one step. | A− |
| LocalStateQueryClientLimits | one caller, abstract timer. | B− |
| LocalStateQuery, LocalStateQueryCodec, LocalStateQueryServerRelease, LocalStateQueryTable | protocol or static checks. | C |

### dmq (messagesubmission, localmessagenotification, localmessagesubmission)

Go:
- localmessagenotification: the expiration cleaner goroutine with a ticker
  (`server.go:392-410`), joined by `Stop` (`:374-387`, `:416-424`).
  `messageAdded` is closed and replaced under lock (`:153`, `:180-181`).
  `WaitForMessage` selects over six cases, including a timer (`:238-253`).
- localmessagesubmission: a closer goroutine (`client.go:94-96`). `Submit`
  takes `busyMutex` then `stopMutex` (`:154-155`); handler sends are
  unguarded (`:214`, `:248`).
- messagesubmission: locks and atomics only.
- A replay state is shared across connections through global init locks.

| Module | Represents | Class |
| --- | --- | --- |
| DmqReplayShared | per-connection pcs; cleaner goroutine; `stopSignal` close; `connDone`; `StopWaits => cleaner = "ended"` (spec:154); WF and `CleanerEndsWithOwner` (spec:183, 204). Replay lock one step. | A− |
| LocalMessageNotification | handler Check/Wait/Wake split (spec:212-246); waiter; one-slot signal; `WakeupNotLost`. RC broadcast only as a cfg flag; no timer, Stop or ticker; `Quiet` accepts exhausted adds. | B+ |
| LocalMessageSubmission, LmsReplayTokens, AuthOpCertCache, MessageIngress, MessageValidity | per-call or per-worker pcs; lock sections as one step or Prepare/Commit splits; no channels; closer and `stopMutex` absent. | B |
| DmqRestart, MessageSubmission, DmqBlockingDeadline, MempoolExpiry, MessagePayloadBytes | protocol, restart, timer arithmetic, data. | C |

### leios-peras (leiosfetch, leiosnotify, leiosvotes, perasvotes)

Go:
- leiosfetch: a delivery goroutine per range (`client.go:86-152`), with a
  cap-1 `signal` sent non-blocking and `stopped` closed by a Once. A request
  slot waits on `drainedCh` (close and replace), ctx, done, and a
  `NewTimer(abandonedRequestWait)` (`:185-228`).
- leiosnotify: a closer goroutine plus `RunLoop` client and server loops.
  `sendMutex` and `quitting` serialise `Stop` against the refill.
- leiosvotes: one `RunLoop` and an unbuffered `voteChan`.
- perasvotes: `opSem` cap 1 used as a lock (`client.go:64-66`). The handler
  sends with `default:`, which drops a reply when the slot is full
  (`:336-357`). There is an unjoined server watcher (`server.go:168-178`).

| Module | Represents | Class |
| --- | --- | --- |
| LeiosNotifyServerRestart | per-goroutine pcs, instances, join sets (spec:100-122); honest `Finished`. Cap-1 `results` implicit. | A |
| LeiosFetchRangeDelivery | delivery `run[r]`, one-slot `buf`, `stopped` close, `s.mu` sections as steps; honest `Finished` (spec:313). | A |
| LeiosVotesLifecycle | `busy`/`sendHeld`, loop goroutine, Stop signal, queue and join, `ConnClose`. | A |
| PerasClientOpMu | lock holder, five pcs, ctx cancel, panic, join; deadlock masked (spec:349); `EveryCallReturns` not in passing cfg. | A |
| LeiosFetch, LeiosNotifyPipelinedQuit | per-call pcs, slot as flags, Seq wire; read loop vs receive loop. No `drainedCh`, timer or ctx. | B |
| LeiosNotify, LeiosVotes | loops as small state machines; unbuffered channels as a counter or unbounded Seq; closers absent; LeiosNotify predates the RC fix. | B− |
| PerasVotes | protocol. | C |

### pipeline-cbor

Go:
- Goroutines: decode and validate workers (`worker_pool.go:107`, WaitGroup
  `:106-117`), the apply runner (`apply_stage.go:440`), `forwardResults`,
  `watchParentCancel`, `metricsCollector`, and `teardown` (`pipeline.go:714,
  717, 721, 1155`).
- Channels: 22, including stage channels of cap `bufSize` (`:628-666`),
  `submitGate` as a lock, and `rawBytesFreed`/`completionChan` broadcasts.
- Locks: 9.
- Also 17 atomics, about 29 selects (13 with `default:`), a ticker, and
  `recover` sites.

| Module | Represents | Class |
| --- | --- | --- |
| PipelineLifecycle | one pc per goroutine (spec:142-181); bounded channels `Len <= Cap` (spec:239); close flags with `NoPanic` (spec:375-382, 444-451); `mu`, `submitGate` holders; RC `requestStop` and teardown goroutine via flags; partial mask with `NoLeakWhenQuiescent` (spec:1236). Broadcasts as guards (`SubReserve` spec:296); no `errorsChan` or validate pool; one worker, Cap 1. | A |
| BlockPipeline | runner and client pcs; stages an unordered set; `Submit` one step. | B |

### ledger-hash-cache

| Module | Represents | Class |
| --- | --- | --- |
| HashCacheSpin | one step per atomic op or plain access over `hash_cache.go:38-82`; CAS, spin, panic reset, `SetCbor` goroutine; WF and `WaitersReturn` (spec:480, 545). | A |
| TxScopedMemo | lock acquire as a step, `done` close and receive, abandon and retry; matches `rules.go:234-300`. | A |
| PooledEvalContext | leaf locks and `sync.Map` as atomic steps; GC cleanup. All 5 cfgs set `CHECK_DEADLOCK FALSE` with no stated reason; the code has no blocking primitive. | B |

### limits-timeouts

StateLimits holds one side's `phase`, an armed `timer` that may fire at any
step, and a byte limit. Its configs cover LeiosFetch, LeiosNotify,
LeiosVotes, MessageSubmission V1 and V2, and PerasVotes only. It has no
goroutine, timer-stop or `stateLoop` versus `recvLoop` race. Class C.

### Ledger, consensus and CBOR

These model pure computation, and class C is the right class for them. The
Go they model is concurrent only through leaf locks and lazy caches, none of
which blocks on a channel or another lock:

- `ledger/common`: besides the two modules above, the script hash and script
  memos (`script_hash.go:39`, `script.go:710`), `langViewParamsMemo`
  (`rules.go:2394`), the program cache (`plutus_program_cache.go:73`) and the
  machine pool (`plutus_machine_pool.go:81, 200, 241`, `runtime.AddCleanup`).
  Leaf locks; duplicate work at worst.
- `ledger/leios`: an RWMutex over verified keys (`verified_keys.go:37`). Leaf.
- `consensus`: `eligibility_cache.go:40`, `byron/pbft.go:404` (PBFTWindow
  models the log sequentially) and a `*sync.Once` warning
  (`selection.go:95`). Leaf.
- `cbor`: six `sync.Once` decode and encode modes (`decode.go:33-49`,
  `encode.go:31`), a `sync.Map` (`decode.go:1054`), and a copy-on-write type
  cache (`type_cache.go:25-26`). Leaf.

Validation in the ledger runs per transaction and is not parallelised inside
gOuroboros; concurrency there belongs to the caller (Dingo).

## Interface points for composition

| Concern | Go at the release candidate | How the models expose it | Consistent? |
| --- | --- | --- | --- |
| Muxer ingress and egress, handshake to muxer start gate, connection `Close` joining goroutines | root `connection.go`, `muxer/` | not swept | not swept |
| Engine send | `sendQueueChan` cap 80 (`protocol.go:346`); `SendMessage` `:1003`, `SendMessageContext` `:1009`, `SendMessageContextAndWait` `:1023` | `sendQ` (TipWorker, PeerSharingExchange, LocalMessageSubmission), `sq` (BlockFetchClientDone, ServerSend), direct wire `toServer`/`c2s`/`inbox[r]`, flags `sent[i]`, `Send(c)` | No: Seq, flag or action; never bounded |
| Engine receive | `recvQueueChan` cap `RecvQueueSize` (`:476`); handlers on `recvLoop` (`:2471`, call `:2524`) | handler pc `hpc` (ChainSync Client, Queries, TipWorker, RangeCheck, TxServerLocks, LSQ Client), `"recv"` goroutine (BusyDelivery), atomic receive actions elsewhere; inbound `toClient`, `inbox[r]`, `s2c`, counter `pending` | No; only OversizedRefusal bounds it |
| Start, Stop, restart | `Start` `:457`, `Stop(ctx)` `:528`, `StopForRestart` `:544` | `cs`, `life`, `st.lstate`, `status[i]`, `stop` strings; instances `gen`, `current`, `inst`/`cur`; Stop as a pc (`spc`, `stopPc[s]`, `stopper`) or atomic | No |
| StopChan, DoneChan | `StopChan` `:758`, `DoneChan` `:717`; DoneChan closes after both loops exit | `stopSig`, `recvExited`, `done[i]`, `done`, `protoDone`, `protoStopped`, `connDone`, `up`; PeerSharingExchange merges both into `stopped` | No; only TipWorker, BusyDelivery and LSQ Client keep "DoneChan only after the handler returns" |
| Callbacks into user code | Config `*Func`; `CallbackContext` `:733` | BusyDelivery frames with `cbHeld`; TipWorker `StopFrom = "callback"`; `cbStop[o]`, `loop = "callback"`, `ApplyMode`; folded into the handler elsewhere | No |
| Pipeline handoff | `Pipeline.Submit`, `WaitForDrain` from chainsync and blockfetch | PipelineLifecycle `subPc`/`submitQ`/`resQ`; BlockPipeline `submitted`; no chainsync or blockfetch model blocks in `Submit` | No link exists |
| Connection close | connection closes on a muxer or protocol error | `closing`/`closed` + `ConnClose`, `muxErr`, `view[r] \in Failures`, `connDone`, `cli = "Failed"`, `CloseConnection` constant | No |

The A and A− modules are the ones closest to an engine-shaped interface:
TipWorker (`sendQ`, then `EngineSend`, then `inflight`, with `stopSig` and
`recvExited`), TxSubmissionServerLocks (per-instance `done[i]`, `status[i]`),
BusyDelivery and LocalStateQueryClient. Composition needs either a
refinement mapping per spec onto one engine interface, or a refit of each
spec onto a shared module.

## Extension plan

### A shared module

Add `specs/common/GoConcurrency.tla` (or one module per primitive). Each
operator returns the next value of a record, so a spec keeps its own
variables and writes `ch' = Send(ch, m)`:

- **GoChan(cap):** `[buf, cap, closed]`.
  - `CanSend` is `~closed /\ Len(buf) < cap`. Unbuffered is `cap = 0`, with
    a rendezvous helper.
  - `SendOnClosed` and `CloseClosed` are panic predicates for an invariant.
  - `CanRecv` is `Len(buf) > 0 \/ closed`; a receive on a closed channel
    yields the zero value.
- **Broadcast:** close and replace as a generation counter. A waiter
  records the generation it parked on, as BlockFetchAdmission does.
- **GoMutex / GoRWMutex:** a holder, readers and a waiting writer, with
  writer preference as in TxSubmissionServerLocks; `TryLock`.
- **WaitGroup:** a counter; `Wait` is enabled at 0. Includes the
  "Add while Wait may run" check.
- **Once.**
- **Timer:** armed, fired or stopped; it fires nondeterministically, and
  `Stop` returns whether it prevented the fire.
- **Engine:** the interface every mini-protocol model refines.
  - a bounded `sendQ` (capacity a constant, 80 in Go) whose send also ends
    on StopChan;
  - per instance, `stopChan` and `doneChan`, with `doneChan` closed only
    after `recvLoop` exits and no handler is running;
  - `handlerRunning`, `reg` as an instance id, and `connClosed`.

The Engine operator's shape should be checked against specs/engine and specs/muxer (EngineLifecycle, EngineTimer, MuxIngress, MuxStartGate) once those are swept; they may already hold the nearest form of it.

### Per spec, in order

1. Write the Engine interface and refit the A and A− modules onto it:
   ChainSyncTipWorker, TxSubmissionServerLocks, BlockFetchBusyDelivery,
   LocalStateQueryClient and PipelineLifecycle.
2. Bound the send queue, and check `SendOnClosed` and `CloseClosed`:
   - add a closed state to the chainsync ready channel, with handler sends
     that block;
   - model the result channels and closer goroutines in localtx,
     localstatequery, localmessagesubmission and leiosnotify.
3. Model the broadcast channels with the Broadcast operator:
   - `rawBytesFreed` and `completionChan` in PipelineLifecycle;
   - `messageAdded` and the timer in LocalMessageNotification;
   - `drainedCh` and `abandonedRequestWait` in LeiosFetch.

   Also model blockfetch's per-request channels with their `default:` sends,
   and the `GetBlockRange` waiter, in BusyDelivery.
4. Model the release candidate's goroutines with WaitGroup and group joins:
   - the chainsync stop finisher and `WaitForDrain`;
   - blockfetch `goroutineGroup` and its fallback `go watch()`;
   - the localtxmonitor server cancel watcher;
   - the localmessagenotification ticker.
5. Remove deadlock masks, or add the liveness property they stand in for:
   ChainSyncTipWindow, BlockFetchClientReader, BlockFetchServerSend,
   PerasClientOpMu (`EveryCallReturns` in its passing config). Also state a
   reason in PooledEvalContext's configs.
6. Add StateLimits configs for chainsync, blockfetch, txsubmission and
   peersharing, so the integration layer has a timer view of each.
