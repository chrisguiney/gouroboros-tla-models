# Model 04: the chain-sync client

Chain-sync is how a node follows a peer's chain: the client asks "what comes
next?" (`MsgRequestNext`) and the server answers roll forward, roll backward,
or "wait" (`MsgAwaitReply`). The client can also ask the server to find where
their two chains meet (`MsgFindIntersect`).

The gOuroboros client (`protocol/chainsync/client.go`, about 2,000 lines)
keeps many requests in flight at
once, and lets the application change course in the middle (`Reintersect`,
`Stop`, `StopAfterDrain`, `Jump`). This model starts with the part every other
operation leans on: the **sync window** and **Reintersect** (slice 1), then
**stopping and restarting** on the same connection (slice 2).

Read [Model 03](../03-engine/README.md) first; the pipelining ideas carry over.

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
| Is chain-sync pipelined? | "pipelining is used by the clients of all mini-protocols except Chain-Sync" [P1] | Yes: `ClientPipelined.hs`, `PipelineDecision.hs` [R2][R3] | Yes, a window of `PipelineLimit` | No: the spec's sentence is out of date (also noted in Model 03). |
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

`Stop`, `StopAfterDrain` and restarting (slice 2), `Jump`, `GetCurrentTip`,
`GetAvailableBlockRange`, the block pipeline behind `RollForward`,
`MsgIntersectNotFound`, and timeouts.

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

The failing trace is short. Sync, one `MsgRequestNext` unanswered at the tip,
`Stop` times out, `Start`. The server's late roll reaches the new instance,
which is in `StIdle` and expects nothing, and that is a protocol violation. It
happens even if the application never calls `Sync` again. A probe
(`ProbeNoRollViolation`) shows the roll path is reachable, not just the rarer
`Stop` during `MsgFindIntersect`.

The `Refuse` config is not a proposed fix. It shows that the violation comes
only from restarting after an abandoned run.

### Reproduced in Go

A test with a real gOuroboros chain-sync server over `net.Pipe` does the same
thing. The server answers `MsgRequestNext` with `MsgAwaitReply`. The client
calls `Stop` (it returns `context deadline exceeded`), then `Start`, and the
server then sends its roll. The restarted client fails, 3 runs out of 3:

```
chain-sync: received message type 3 without peer agency, an allowed
pipelined message, or an outstanding pipelined request in state Idle
```

This is the "Stop and restart" half of gOuroboros issue #2867. That issue was
closed when `StopAfterDrain` was added (pull request #2871), but `Stop`
followed by `Start` on the same connection still breaks.

### Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros |
| --- | --- | --- | --- |
| Can a client end chain-sync with requests outstanding? | No: `MsgDone` only from `StIdle` [C1] | No: `SendMsgDone` is typed at `Z` (`ClientPipelined.hs` lines 81-83) [R2] | `StopAfterDrain`: no. `Stop`: yes, by abandoning the protocol without `MsgDone` |
| What happens to a message the state does not allow? | The connection is aborted (`miniprotocols.tex` lines 27-36) | Same | Same: the protocol reports an error |
| Restart on the same connection? | After `MsgDone`, the server restarts (spec 5.7) | Same, for responders | After `StopAfterDrain`: works. After an abandoning `Stop`: the late reply breaks the new run |

## Running it

```sh
make chainsync        # every chain-sync config; the *Bug ones are expected to fail
make chainsync-deep   # window of three
```
