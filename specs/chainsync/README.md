# the chain-sync client

Chain-sync is how a node follows a peer's chain: the client asks "what comes
next?" (`MsgRequestNext`) and the server answers roll forward, roll backward,
or "wait" (`MsgAwaitReply`). The client can also ask the server to find where
their two chains meet (`MsgFindIntersect`).

The gOuroboros client (`protocol/chainsync/client.go`, about 2,000 lines)
keeps many requests in flight at
once, and lets the application change course in the middle (`Reintersect`,
`Stop`, `StopAfterDrain`, `Jump`). This model starts with the part every other
operation leans on: the **sync window** and **Reintersect** (slice 1), then
**stopping and restarting** on the same connection (slice 2), then the
one-shot **queries** `GetCurrentTip` and `Jump` (slice 3), and the
**protocol** itself with its limits and timeouts (slice 4).

Read [Model `engine`](../engine/README.md) first; the pipelining ideas carry over.

## Slice 1: the sync window and Reintersect (`ChainSyncClient.tla`)

### What the code does

Three goroutines share the client:

- **`syncLoop`** keeps `PipelineLimit` requests outstanding (75 by default; a
  zero limit becomes 75 in `NewClient`). It waits for a **ready signal**,
  meaning one reply has been consumed, takes `busyMutex`, and sends enough
  requests to refill the window. It counts what it has in flight itself.
- **The handler** (the engine's `recvLoop`) runs each reply: first the
  application's callback, then a ready signal on `readyForNextBlockChan`, then
  `requestNextAnswered`, which lowers the shared `outstandingRequestNext`. The
  signal is `true`, or `false` if the callback returned `ErrStopSyncProcess`.
  The send **blocks while holding `lifecycleMutex`** until the channel, which
  has `PipelineLimit` slots, has room.
- **`Reintersect`** stops the loop, takes `busyMutex`, waits until every
  outstanding request is answered, throws away leftover signals, gives up if
  a callback asked to stop meanwhile, sends `MsgFindIntersect`, and starts a
  new loop.

### The question

That blocking send is the risk. If the channel were ever full when a reply
arrived, the handler would wait forever while holding `lifecycleMutex`. Every
other operation needs that lock, so `Reintersect`'s drain would never finish
and `Stop` would hang. The model asks:

1. **`SignalsFit`**: does a handler ever find the channel full?
2. **`SignalBudget`**: do waiting signals plus not-yet-signalled requests stay
   within the channel's slots? This is the reason (1) holds, if it does.
3. **`FindOnlyWhenIdle`**: is `MsgFindIntersect` ever sent with a request
   outstanding?
4. **`NoStaleAfterReintersect`**: is a reply from before `Reintersect` ever
   delivered after it returns?
5. **`WindowBound`**: does the loop ever have more than the window
   outstanding?
6. Does anything deadlock? TLC checks this by default.

### The answer

All six hold, with windows of two and three, and with callbacks that may stop
the sync:

| Config | States | Result |
| --- | --- | --- |
| `ChainSyncClient.cfg` (window 2) | 2,649 | passes |
| `ChainSyncClientStop.cfg` (window 2, callbacks may stop) | 5,543 | passes |
| `ChainSyncClientDeep.cfg` (window 3, more requests) | 51,315 | passes |

The channel does fill to the last slot (probe below), but never past it. Each
reply's signal is matched by a request that refilled the window only after an
earlier signal was consumed, and `Reintersect` stops consuming only after the
loop has stopped sending. So the signals waiting can never exceed the requests
sent, and those never exceed the window.

### Checking the checks

A passing model only means something if the model can fail. Each safeguard in
the code has a switch; turning it off must break an invariant:

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `ChainSyncClientTopUpBug.cfg` | the loop subtracts what is in flight before refilling | `SignalBudget` |
| `ChainSyncClientNoDrainBug.cfg` | `Reintersect` waits for every reply | `FindOnlyWhenIdle` |
| `ChainSyncClientNoDiscardBug.cfg` | `Reintersect` discards leftover signals | `SignalBudget` |

The **reachability probes** at the bottom of the `.tla` file each claim
something never happens, and TLC shows that each one does: the channel fills
completely, `Reintersect` completes, `Reintersect` gives up because a callback
stopped the sync, and `Reintersect` starts draining with replies outstanding.
Without these, a passing invariant could just mean the model never got near
the edge. To run one, copy `ChainSyncClient.cfg` and replace its `INVARIANT`
lines with the probe's name.

### The same mutations in Go

The same three safeguards were removed from `client.go` (on `origin/main` at
`c1bc50c6`), one at a time, and the package's existing tests rerun. Each
mutation fails at least one test that names the property. The first and
third also leave a test hanging until the package's time limit:

| Mutation in `client.go` | Tests that fail |
| --- | --- |
| `syncLoop` refills `PipelineLimit` without subtracting `inFlight` | `TestSyncKeepsWindowFullAtLatency`, `TestSyncAtTipKeepsWindowBounded` |
| `Reintersect` skips `discardReadySignals` | `TestReintersectDrainsPipelinedRepliesBeforeFindIntersect`, `TestReintersectDrainsFullWindow` |
| `quiesceSync` does not wait for outstanding requests | `TestReintersectDrainsPipelinedRepliesBeforeFindIntersect`, `TestReintersectDrainsFullWindow`, `TestReintersectStopDuringDrain`, `TestReintersectStopSyncCallbackDuringDrain`, and two `StopAfterDrain` tests |

Unmutated, the package passes. So this slice needed **no new Go tests**: the
model's properties are already pinned down by the existing tests. That is a
result, not a gap.

### The modelling mistake

The first run reported `SignalBudget` violated: three requests counted as
outstanding with a window of two. The trace showed why. The handler sends its
ready signal *before* `requestNextAnswered` (`messageHandler`), so for a
moment a request already counted as signalled is still in
`outstandingRequestNext`. The loop can take the signal and refill in that
moment. The counter briefly reads one higher than the requests actually
unanswered. That is harmless, because nothing compares that counter with the
window. The invariant was wrong: it now counts that request once
(`Unsignalled`).

### Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Agree? |
| --- | --- | --- | --- | --- |
| When may `MsgFindIntersect` be sent? | From `StIdle` only [C1]; "free to use ... at any time later" [C1] | `SendMsgFindIntersect` is typed at `Z`: nothing pipelined outstanding [R2] | `Reintersect` drains every reply first | Yes. The spec's "any time" means any time the client is in `StIdle`; with pipelining that is only when nothing is outstanding. |
| Is chain-sync pipelined? | "pipelining is used by the clients of all mini-protocols except Chain-Sync" [P1] | Yes: `ClientPipelined.hs`, `PipelineDecision.hs` [R2][R3] | Yes, a window of `PipelineLimit` | No: the spec's sentence is out of date (also noted in Model `engine`). |
| Replies in request order? | Yes, the multiplexer keeps order [P1] | Yes, `CollectResponse` takes them in turn | Yes, one handler, in order | Yes |
| How deep a window? | Not stated | The application decides each step: `Request`, `Pipeline`, `Collect` [R3] | A fixed `PipelineLimit`, refilled after each consumed reply | Not comparable: a policy choice, not a protocol rule |
| What happens to replies already in flight when the client changes course? | Not stated | The types force them to be collected before `MsgFindIntersect` | They are delivered to the old sync's callback, then the new sync starts | Yes, in effect |

### Sources

Pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c)
and gOuroboros `origin/main` at `c1bc50c6`.

| Ref | Where | What it says |
| --- | --- | --- |
| C1 | [`docs/network-spec/miniprotocols.tex` lines 838-848, 893-908](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L838-L908), and [lines 1064-1076](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1064-L1076) | Chain-sync agencies and transitions; `MsgFindIntersect` only from `StIdle`; the client "is free to use `MsgFindIntersect` at any time later". |
| P1 | [`docs/network-spec/miniprotocols.tex` lines 2180-2208](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L2180-L2208) | Pipelining; replies in request order; "all mini-protocols except Chain-Sync". |
| R2 | [`ChainSync/ClientPipelined.hs` lines 60-84, 257-273](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ChainSync/ClientPipelined.hs#L60-L84) | `SendMsgFindIntersect` only at `Z`; it is a plain `Yield` then `Await`. |
| R3 | [`ChainSync/PipelineDecision.hs` lines 24-38](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ChainSync/PipelineDecision.hs#L24-L38) | The reference client's per-step choice: `Request`, `Pipeline`, `CollectOrPipeline`, `Collect`. |
| G1 | gOuroboros `protocol/chainsync/client.go` | `syncLoop`, `sendRequestNext`, `requestNextAnswered`, `messageHandler`, `handleRollForward`/`handleRollBackward`, `Reintersect`, `quiesceSync`, `discardReadySignals`, `NewClient`. |

### Not in this slice

`Stop`, `StopAfterDrain` and restarting (slice 2); `Jump`, `GetCurrentTip`
and `MsgIntersectNotFound` (slice 3); the protocol itself, limits and
timeouts (slice 4); `GetAvailableBlockRange` and the block pipeline behind
`RollForward`.

## Slice 2: stop and restart (`ChainSyncLifecycle.tla`)

### What the code does

The client can stop two ways:

- **`Stop`** queues `MsgDone`, waits up to 250 ms for it to be delivered,
  then unregisters the protocol either way. `MsgDone` is legal only in
  `StIdle` [C1], so while a `MsgRequestNext` is unanswered it waits in the
  send queue for the reply. At the chain tip the server answers
  `MsgAwaitReply` and then nothing until the next block, so the 250 ms runs
  out, `Stop` returns `context deadline exceeded`, and `MsgDone` is never
  sent. The server is left owing a reply.
- **`StopAfterDrain`** waits for every outstanding reply, then sends `MsgDone`
  from `StIdle`.

`Start` then registers a fresh protocol instance in `StIdle` and sets
`outstandingRequestNext` to 0, with the comment "Requests sent on the stopped
instance are never answered". While the protocol is unregistered, the muxer
drops its messages silently. Once `Start` registers the new instance, they are
delivered to it.

### The question

**`NoViolation`**: after a stop and a restart, does either side ever receive a
message its state machine does not allow? The server here behaves like the
reference: it takes messages in order and answers each one, possibly much
later. After `MsgDone` it restarts in `StIdle`.

### The answer

| Config | States | Result |
| --- | --- | --- |
| `ChainSyncLifecycleDrain.cfg`: only `StopAfterDrain` | 374 | passes |
| `ChainSyncLifecycleStopBug.cfg`: `Stop` too, as in gOuroboros today | | **fails** |
| `ChainSyncLifecycleRefuse.cfg`: `Start` refuses after a `Stop` that left requests unanswered | 677 | passes |
| `ChainSyncLifecycleCloseOnlyBug.cfg`: an abandoning `Stop` closes the connection, nothing more | | **fails** `NoViolation` (passes `NoViolationOnLiveConnection`, 9,943 states) |
| `ChainSyncLifecycleClose.cfg`: the fix in review; close the connection **and** refuse `Start` | 821 | passes `NoViolation` |

The failing trace is short. Sync, one `MsgRequestNext` unanswered at the tip,
`Stop` times out, `Start`. The server's late roll reaches the new instance,
which is in `StIdle` and expects nothing, and that is a protocol violation. It
happens even if the application never calls `Sync` again. A probe
(`ProbeNoRollViolation`) shows the roll path is reachable, not just the rarer
`Stop` during `MsgFindIntersect`.

The `Refuse` config shows that the violation comes only from restarting
after an abandoned run.

### Reproduced in Go

A test with a real gOuroboros chain-sync server over `net.Pipe` does the same
thing. The server answers `MsgRequestNext` with `MsgAwaitReply`. The client
calls `Stop` (it returns `context deadline exceeded`), then `Start`, and the
server then sends its roll. The restarted client fails in 20 runs out of 20
with `-race`:

```
chain-sync: received message type 3 without peer agency, an allowed
pipelined message, or an outstanding pipelined request in state Idle
```

As a control, the same setup with `StopAfterDrain` instead of `Stop` restarts
and syncs again cleanly in 10 runs out of 10.

This is the "Stop and restart" half of gOuroboros issue #2867. That issue was
closed when `StopAfterDrain` was added (pull request #2871), but `Stop`
followed by `Start` on the same connection still broke. Reported as gOuroboros
issue #3091.

### What the reference does, and the fix

The reference never leaves chain-sync half-finished on a connection it keeps:

- Asked to terminate, the consensus chain-sync client collects every
  outstanding pipelined reply (`drainThePipe`), then sends `MsgDone`
  (ouroboros-consensus `ec239d57f618`,
  `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Client.hs`,
  `nextStep` and lines 926-956).
- Demoting a hot peer waits up to `deactivateTimeout`, 300 s, for its hot
  protocols to finish, and if they do not, stops the multiplexer and so closes
  the connection (ouroboros-network `5f356486ab3e`,
  `ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs`
  lines 109-117 and 998-1030; `Diffusion/Policies.hs` lines 31-32).

Pull request #3092 (merged) does the same. When `Stop` cannot deliver
`MsgDone`, the client reports `ErrStoppedWithoutDone` and the connection
closes.

Closing alone was not enough, and the model showed why
(`ChainSyncLifecycleCloseOnlyBug.cfg`). The connection handles the error on
its own goroutine, so the close is not immediate. A `Start` in that gap could
still meet the late reply. On a connection that is already closing, that is
only a second error (`NoViolationOnLiveConnection` holds). But a client built
directly on a muxer has no connection to close it. If its owner drops the
error, nothing ever closes the muxer. So the client also remembers the
abandoned stop (`stoppedWithoutDone`): `Start` leaves it stopped, and `Sync`
returns `ErrProtocolShuttingDown`. That matches the reference, where a peer
whose demotion timed out is never promoted on the same connection.
`ChainSyncLifecycleClose.cfg` checks the two together against plain
`NoViolation`.

On the Go side, a test that calls `Stop` then `Start` back to back, then
releases the late reply, failed with the close alone and passes with both.

### Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros |
| --- | --- | --- | --- |
| Can a client end chain-sync with requests outstanding? | No: `MsgDone` only from `StIdle` [C1] | No: `SendMsgDone` is typed at `Z` (`ClientPipelined.hs` lines 81-83) [R2] | `StopAfterDrain`: no. `Stop`: yes, by abandoning the protocol without `MsgDone` |
| What happens to a message the state does not allow? | The connection is aborted (`miniprotocols.tex` lines 27-36) | Same | Same: the protocol reports an error |
| Restart on the same connection? | After `MsgDone`, the server restarts (spec 5.7) | Same, for responders | After `StopAfterDrain`: works. After an abandoning `Stop`: the late reply breaks the new run; with the fix in review, the connection is closed and the client is not restarted, as in the reference |

## Slice 3: queries (`ChainSyncQueries.tla`)

### What the code does

Two calls send a single `MsgFindIntersect` and wait for an answer:

- **`GetCurrentTip`** sends `MsgFindIntersect` with no points, so the server
  answers `MsgIntersectNotFound` carrying its tip. It registers on
  `wantCurrentTipChan` and returns on the **first tip any handler delivers**.
  The handlers for rolls and for both intersect answers all deliver tips
  (`sendCurrentTip`).
- **`Jump`** sends `MsgFindIntersect` with points, registers on
  `wantIntersectFoundChan`, and returns the first intersect answer a handler
  delivers.

Both hold `busyMutex` while they wait, so they never overlap. But neither
request is tagged. A handler gives an answer to whoever is registered when it
looks. `MsgIntersectNotFound`'s handler (`handleIntersectNotFound`) first
delivers the tip, then takes the registered intersect request, if any. With
no request registered it ignores the answer. `MsgIntersectFound` with no
request registered is a protocol error.

### The question

1. **`JumpGetsOwnAnswer`**: does `Jump` always get the answer to its own
   `MsgFindIntersect`?
2. **`NoOrphanAnswer`**: does a `MsgIntersectFound` ever arrive with nobody
   registered for it?

### The answer

No to (1), and yes to (2). `GetCurrentTip` can return **before the answer to
its own `MsgFindIntersect` has been handled**. That answer is then still on
its way, and the next call that registers for an intersect answer receives
it. There are two ways in:

- **A running sync.** The reply to a `MsgRequestNext` sent earlier arrives
  first, and the roll's handler delivers a tip. `GetCurrentTip` returns at
  once, before its own `MsgFindIntersect` has even been sent.
- **No sync at all.** In `handleIntersectNotFound`, `GetCurrentTip` gets the
  tip and returns. If a `Jump` registers before the handler's next statement,
  the handler gives `Jump` this `MsgIntersectNotFound`. The window is a few
  statements wide.

Either way `Jump` reports no intersection for a point the server knows. Then
`Jump`'s own `MsgIntersectFound` arrives with nobody registered, which is a
protocol error, and the connection closes.

| Config | States | Result |
| --- | --- | --- |
| `ChainSyncQueriesBug.cfg`: today, with a roll delivering the tip | | **fails** both |
| `ChainSyncQueriesNoSyncBug.cfg`: today, no sync | | **fails** |
| `ChainSyncQueriesPopFirst.cfg`: the handler takes the request before delivering the tip, no sync | 72 | passes |
| `ChainSyncQueriesPopFirstBug.cfg`: the same, with a roll delivering the tip | | **fails** |
| `ChainSyncQueriesWaitOwn.cfg`: `GetCurrentTip` returns only after its own answer is handled | 85 | passes |

Reordering the handler closes only the narrow window. The roll path needs
`GetCurrentTip` to wait for its own answer. These configs show which designs
survive the model; they are not a decision on the fix.

### The modelling mistake

The first version of this model had no sync, and only found the narrow
window. The "pop first" reordering looked like a complete fix. The Go
reproduction below goes through the roll path instead, and the reordering
cannot fix that path. Adding `RollTips` to the model showed it, and
`ChainSyncQueriesPopFirstBug.cfg` keeps the lesson.

### Reproduced in Go

A deterministic test against a real gOuroboros server:

1. A sync runs at the tip with the server holding its roll.
2. `GetCurrentTip` queues its `MsgFindIntersect`.
3. The roll is released. The callback stops the sync, so `Jump` can run, and
   `GetCurrentTip` returns on the roll's tip.
4. The server holds its `MsgIntersectNotFound` until `Jump` has registered.

In 10 runs out of 10 with `-race`, `Jump` returned "not found" for a point the
server finds, and the client then failed with:

```
chain-sync: received IntersectFound without a pending FindIntersect request
```

A loop of 2,000 plain `GetCurrentTip`-then-`Jump` rounds with no sync never
hit the narrow window. The model shows it is reachable, but it is very rarely
hit.

Reported as gOuroboros issue #3093. Pull request #3094 (in review) makes
`GetCurrentTip` wait for the answer to its own `MsgFindIntersect`, the design
`ChainSyncQueriesWaitOwn.cfg` checks. Its test holds both the roll and the
`MsgIntersectNotFound` at the server, and requires `GetCurrentTip` not to
return on the roll's tip. It fails 5 runs out of 5 without the change.

### Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros |
| --- | --- | --- | --- |
| How many answers does `MsgFindIntersect` get? | Exactly one, `MsgIntersectFound` or `MsgIntersectNotFound` [C1] | Same | Same on the wire |
| Who receives it? | The client that sent it; replies are in request order [P1] | The continuation that sent it: `Yield` then `Await` [R2], with no shared registry | Whoever is registered on `wantIntersectFoundChan` when the handler looks |
| Can a caller move on before its answer? | Not in the state machine: it is in `StIntersect` until the answer | No | Yes: `GetCurrentTip` returns on any tip |

## Slice 4: the protocol, limits and timeouts (`ChainSyncProtocol.tla`)

### What it models

The earlier slices model gOuroboros' client code. This slice models the
protocol itself, both sides, from the specification's agency and messages
tables, with `MsgRequestNext` pipelined as the reference client does. The
client keeps a list of the answers it is owed, oldest first. It pipelines up
to `Limit` requests, and sends `MsgFindIntersect` and `MsgDone` only when it is
owed nothing (the reference's "Z" rule). The server takes one message at a
time, in order, and answers it.

### The answer

| Config | States | Result |
| --- | --- | --- |
| `ChainSyncProtocol.cfg` | 209 | `NoViolation`, `OnlyAtZero`, `AgreeWhenQuiet` and `WindowBound` hold |
| `ChainSyncProtocolAwaitBug.cfg`: the server sends `MsgAwaitReply` twice | | **fails** `NoViolation` |
| `ChainSyncProtocolDoneBug.cfg`: the client sends `MsgDone` while owed answers | | **fails**; without `OnlyAtZero`, `NoViolation` fails too: a roll reaches a client whose run is over |
| `ChainSyncProtocolFindBug.cfg`: the client sends `MsgFindIntersect` while owed answers | | **fails** `OnlyAtZero` |

The probes show that the window fills, that the server reaches `StMustReply`,
and that a pipelined request waits at a server that holds agency.

One honest negative: a `MsgFindIntersect` sent while requests are owed causes
**no** violation on the wire. The server answers in order, so the answers still
match. The reference's Z rule keeps the client's view of the state machine
exact; it does not prevent a wire error. Without `OnlyAtZero`, the mutation
trips only `WindowBound`, because the model counts the intersect request in
the window.

### The same table in Go

`protocol/chainsync/statemap_model_test.go`, on the local branch
`test/chainsync-state-model`, holds the receive table: both roles, every
active state, every kind of message, 136 cells across `StateMapNtN` and
`StateMapNtC`. It also checks each state's agency, and every way into each
state: `StMustReply` only by `MsgAwaitReply` from `StCanAwait`, `StDone` only
by `MsgDone` from `StIdle`, and nothing leaves `StDone`. gOuroboros judges a
message on arrival, so a cell where the reference would leave a message
waiting is a refusal in gOuroboros. This difference is recorded, not treated
as a defect. Five mutations of the state maps each fail it:
- `MsgAwaitReply` allowed in `StMustReply`;
- pipelined `MsgRequestNext` dropped from `StMustReply`;
- pipelined `MsgRequestNext` admitted in `StIntersect`;
- `MsgDone` allowed from `StCanAwait`;
- no size limit in `StIdle`.

### Limits and timeouts: two deviations, both fixed on local branches

The specification's node-to-node tables
(`miniprotocols.tex` lines 910-950) and the reference agree; gOuroboros
differs in two places:

| Item | Specification | Reference | gOuroboros `origin/main` | Branch |
| --- | --- | --- | --- | --- |
| `StMustReply` timeout | random 601 s to 911 s | `minChainSyncTimeout` 601, `maxChainSyncTimeout` 911 (`ChainSync/Codec.hs` lines 54-63), drawn uniformly in `timeLimitsChainSync` | random 135 s to 269 s | `fix/chainsync-mustreply-timeout` |
| Size limit per state | 65535 bytes | `byteLimitsChainSync`: `smallByteLimit` (65535) in every state (`ChainSync/Codec.hs` lines 40-51; `Protocol/Limits.hs` line 111) | 462000 bytes, the ingress queue size, used as the message size limit | `fix/chainsync-ntn-message-size` |
| `StIdle`, `StCanAwait`, `StIntersect` timeouts | 3673 s, 10 s, 10 s | same (`cardano-diffusion/.../ChainSync/Codec/TimeLimits.hs`) | same | none needed |
| `StMustReply` timeout for a trusted peer | none | none (`IsTrustable` waits forever) | always applied; gOuroboros has no notion of a trusted peer | recorded, not changed |
| Node-to-client limits and timeouts | none | none | none (`StateMapNtC`) | none needed |

The reference's comment in `TimeLimits.hs` still says "135 - 269", the old
values. Its code uses 601-911, as the specification does. gOuroboros carried
the old values, and its own test asserted them as "per spec".

The size fix keeps 462000 bytes as each state's pending-receive budget, so
the bytes queued while a state is active are bounded as before. The muxer's
ingress limit does not change (it is at least 655350 bytes either way).
Branches:

- `fix/chainsync-mustreply-timeout` (`ab81e5aa`): the constants, the
  existing limits test corrected to the specified values, plus a check that
  every random draw lands in range. The docs are updated too.
- `fix/chainsync-ntn-message-size` (`fc33a544`): 65535-byte message limits.
  The existing map test, which asserted the old single limit, now asserts the
  split. A new test checks that the ingress queue still holds 462000 bytes.
  Both fail on `origin/main` where they assert the change.

Neither branch has been pushed or opened as a pull request.

## Slice 5: limits as a table (`ChainSyncLimits.tla`)

A table model of the node-to-node size limit and timeout of each state,
written bug-first for #3112 (N6, N7). An input is a state, a message size
(one point on each side of 65535 and 462000) and the timeout gOuroboros
draws there.

| Invariant | Says | Source |
| --- | --- | --- |
| `SizeAsByteLimitsChainSync` | a message is accepted exactly when it is at most 65535 bytes | `miniprotocols.tex` 910-924; `ChainSync/Codec.hs` 43-49 |
| `TimeoutAsTimeLimitsChainSync` | every timeout drawn is one the reference could draw (MustReply 601-911 s) | `miniprotocols.tex` 940-950; `ChainSync/Codec.hs` 54-63 |

| Config | Rule | Result | Counterexample, and the Go check it matches |
| --- | --- | --- | --- |
| `ChainSyncLimitsMainBug` | main before #3112 | fails `SizeAsByteLimitsChainSync` | `Idle`, 65536 bytes: main's limit was 462000 (the state-map test asserts 65535) |
| `ChainSyncLimitsMainTimeoutBug` | main before #3112 | fails `TimeoutAsTimeLimitsChainSync` | `MustReply`, draw 135 s (`protocol/limits_test.go` asserts a 601 s minimum) |
| `ChainSyncLimits` | #3112 (`4217b6d7`) | passes, 1,565 states | |

Not a deviation: gOuroboros draws from [601, 911) and the reference from
601 to 911, a subset. The 462000-byte pending-receive budget the fix keeps
is not a per-message limit, so it is not in the table.

## Running it

```sh
make chainsync        # every chain-sync config; the *Bug ones are expected to fail
make chainsync-deep   # window of three
```
