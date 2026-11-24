# the connection and the multiplexer

Every mini-protocol on a connection shares one multiplexer (the "mux"). It
cuts each mini-protocol's messages into segments, sends them over one socket,
and on the other side reassembles each mini-protocol's byte stream. Bugs here
affect every protocol at once, and they live in concurrent Go code that tests
rarely drive into its rare orderings. That is what TLA+ is good at.

This model is built in four parts. Read [Model `keepalive`](../keepalive/README.md)
first.

| Part | Module | Question |
| --- | --- | --- |
| 1 | `MuxHandover.tla` | Do messages survive a mini-protocol restart? |
| 2 | `MuxHandover.tla`, with a stopper | Does `Stop` or a connection shutdown during a restart leave anything behind? |
| 3 | `MuxIngress.tla` | What happens when several mini-protocols share one demultiplexer? |
| 4 | `ConnectionShutdown.tla` | Can errors and shutdown race into a panic or a hang? |
| 5 | `ConnectionTeardown.tla` | Can `Close` during `Dial` leak the muxer, or a late `waitGroup.Go` panic? |

`make connection` runs all of them.

## Part 1: bytes across a restart (`MuxHandover.tla`)

When a client sends `MsgDone`, a gOuroboros server stops that protocol
instance and starts a new one (the keep-alive fix does this, as chain-sync,
block-fetch, and the others already did). Bytes keep arriving the whole time,
and a segment can end halfway through a message or carry the end of one run
and the start of the next. The question:

> Is every message the client sends processed exactly once, in the order it
> was sent, by the right instance, across any number of restarts?

### Sources

| Ref | Source | What the model takes from it |
| --- | --- | --- |
| M1 | [`docs/network-spec/mux.tex`, lines 36-58](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/mux.tex#L36-L58) | Segments of a mini-protocol arrive in order, reliably; a mini-protocol is written "as if it would only communicate with its instance on the remote end". |
| M2 | [`docs/network-spec/mux.tex`, lines 113-121](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/mux.tex#L113-L121) | The mux may split a message across segments or merge several messages into one segment. |
| S4, S7, S8 | As in [Model `keepalive`](../keepalive/README.md#sources) | A finished run's unread bytes are kept for the next run; a server restarts after `MsgDone`; a new run's first message may share a chunk with the old run's last. |

In the [rendered specification PDF](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf),
M1 is section 2.1 "The Multiplexing Layer" (page 7) and M2 is section 2.1.2
"Fairness and Flow-Control in the Multiplexer" (page 8).

### How gOuroboros keeps the bytes (read from the code)

Bytes for a server can be in three places when it restarts, and all three
reach the new instance, oldest first:

1. **Bytes the old instance read but did not process.** Its read loop
   (`readLoop` in `protocol/protocol.go`) stops at the first message after
   `MsgDone`, leaving it unparsed. On a restart its read buffer becomes
   `carriedIngress`, and the new instance reads it first
   (`handoverIngress`).
2. **Segments in the receiver's channel and queue.** `StopForRestart`
   suspends the receiver instead of removing it (`SuspendProtocol` in
   `muxer/muxer.go`), and the new instance's `RegisterProtocol` resumes it.
3. **Segments still arriving**, which the suspended receiver keeps queueing.

A fourth place could lose a message: the old instance's queue of admitted
messages, which the restart discards. gOuroboros keeps it empty past
`MsgDone` by admitting **one message at a time**: the read loop does not
admit the next message until the previous one has been handled
(`reserveInboundAdmission`), and by then the instance's run is over, so the
read loop stops instead.

### The model

Messages are two bytes, so a one-byte segment splits a message in half, and
a two-byte segment can hold the end of one message and the start of the next.
The client follows the protocol and starts each new run as soon as the last
ends, so the new run's bytes chase the old run's `MsgDone` down the wire.

Three constants switch off one gOuroboros mechanism each, to show the model
notices:

| Constant | `TRUE` (gOuroboros) | `FALSE` |
| --- | --- | --- |
| `CarryReadBuffer` | Unprocessed bytes go to the next instance | They are dropped |
| `AdmitOneAtATime` | A message waits until the last one is handled | The read loop admits ahead |
| `ResumeReceiver` | The new instance gets the old receiver back | It gets a new, empty one |

### Run it

```sh
make connection
```

| Config | Result |
| --- | --- |
| `MuxHandover.cfg` | **Passes: 520 distinct states.** Every message is handled once, in order (`DeliveredInOrder`); no instance refuses an honest message (`NoViolation`); at most one message is admitted at a time; and nothing gets stuck. |
| `MuxHandoverNoCarryBug.cfg` | Deadlock: a ping that was in the old read buffer is lost, and the client waits forever for its answer. |
| `MuxHandoverAdmitAllBug.cfg` | Deadlock after 14 steps: the old instance admits the next run's ping before it has handled `MsgDone`; the restart discards it. |
| `MuxHandoverNoResumeBug.cfg` | Deadlock: segments queued in the old receiver are lost with it. |

The failing configs show why each mechanism exists. The passing one says the
three together are enough, for every way the bytes can be cut and every order
in which the client, the read loop, the receive loop, and the restart can
run.

## Part 2: `Stop` and shutdown during a restart (`MuxHandover.tla`)

The same module, with a stopper (constant `Stopper`): `Server.Stop()`, or a
connection shutdown (`stopProtocols` in `connection.go`, then `muxer.Stop()`),
at any moment, including halfway through a restart. The muxer's receiver slot
is now explicit, since the last keep-alive bug lived there: `Stop`
unregisters it, `StopForRestart` suspends it, `Start` registers or resumes
it, and bytes for an empty slot are dropped.

| Config | Result |
| --- | --- |
| `MuxHandoverServerStop.cfg` | **Passes: 1,846 distinct states.** With the keep-alive fix (the `Stop` guard and the release of a cancelled restart's receiver): nothing reordered, nothing handled after `Stop`, nothing left reading or registered. |
| `MuxHandoverClose.cfg` | **Passes: 2,619 distinct states.** With the fix for issue #3085 (`ShutdownStopsServer = TRUE`): during a connection shutdown, nothing is reordered or refused, nothing gets stuck, and nothing is handled after shutdown. |
| `MuxHandoverCloseWindowBug.cfg` | **Fails**, as gOuroboros did before that fix (`ShutdownStopsServer = FALSE`): a message can be handled after shutdown has stopped the protocols. |

The failing trace, step by step:

1. The server handles the client's `MsgDone`; its restart begins.
2. Shutdown reads the old instance, stops it, and unregisters its receiver.
3. Shutdown records no stop request, so the restart's guard does not fire.
   The restart installs a new instance and **registers it with the muxer
   again**, which is still running.
4. The client's next ping arrives, and the new instance handles it: its
   message handler runs after `stopProtocols` stopped the server.
5. Only then does the muxer stop.

For keep-alive the handler answers a ping. For chain-sync, block-fetch,
tx-submission, peer-sharing, and the Leios servers, which restart the same
way, it is application callbacks running after shutdown began.

**Reproduced and fixed.** A Go test held chain-sync's server inside its
`MsgDone` handler on gOuroboros's `main`, stopped its instance the way
`stopProtocols` did, and let the restart continue: a new instance answered the
next `FindIntersect` and called the application's `FindIntersectFunc`, 10
times out of 10. Reported as gOuroboros issue #3085; pull request #3087
(merged 2026-11-24) gives
each restarting server a `Stop` that records the request under its lock, so a
restart racing with it installs nothing (and releases its muxer receiver),
and makes `stopProtocols` call those servers' `Stop`. In the model that is
`ShutdownStopsServer`: connection shutdown now sets the same stop request
`Server.Stop` does.

**A lesson from that pull request's review.** Its first tests stopped each
server while it was held *before* `StopForRestart`. That ordering is the
model's `StopRead`-before-`StopForRestart` path, where `Stop` unregisters the
receiver itself, so they passed even with every server's release of a
cancelled restart deleted - the reviewer checked. The ordering that needs the
release is the one `KeepAliveLifecycleSlotBug.cfg` and part 2's `Install`
step show: `StopForRestart` first, then `Stop`, then the restart's guard. The
added chain-sync test stops the server from a hook at exactly that point.
When turning a trace into a Go test, hold the code at the trace's own
ordering, and prove the test fails without the step the trace is about.

Step 3 of the trace is where the fix bites: the restart's guard now fires,
because shutdown recorded the request.

## Part 3: several mini-protocols, one demultiplexer (`MuxIngress.tla`)

The muxer reads every segment of the connection in one loop, in the order the
peer sent them (`readLoop` in `muxer/muxer.go`), and puts each on its
mini-protocol's queue (`segmentChannel.enqueue`). A segment fits when its
queue stays within the protocol's limit and the connection-wide budget has
room. When it does not fit:

- **without backpressure** the connection ends with `ErrIngressOverflow`, as
  the specification requires: "If the demultiplexer detects an overflow of
  the buffer, it means that the peer violated the protocol and the MUX/DEMUX
  layer shuts down the connection" (M3, `mux.tex` lines 123-131, PDF section
  2.1.3);
- **with backpressure** the loop waits, which holds up **every** protocol on
  the connection. gOuroboros switches it on only while block-fetch has
  requests it cannot size in advance (`protocol/blockfetch/client.go`), and
  `SetIngressBackpressure` says so: "Pausing the read loop stops every
  protocol on the connection, keep-alive included". An empty backpressured
  queue always admits, past both its limit and the budget.

The model has two protocols: `Bulk` (like a block-fetch range) and `Ping`
(like keep-alive or a local state query), optionally with Bulk's reader
waiting for a Ping answer before taking its next segment (`Dependency`).

| Config | Result |
| --- | --- |
| `MuxIngress.cfg` | **Passes.** A peer that follows flow control never overflows anything, even when Bulk's reader waits on Ping. |
| `MuxIngressUnsizedBug.cfg` | Overflow: a request the reader cannot size, without backpressure, ends the connection. This is why block-fetch switches backpressure on. |
| `MuxIngressBackpressure.cfg` | **Passes: 891 distinct states.** The same request with backpressure: the loop waits instead, and everything is delivered. |
| `MuxIngressBackpressureDependencyBug.cfg` | **Deadlock**, see below. |
| `MuxIngressSharedBudget.cfg` | **Passes.** Bulk fills the shared budget while waiting on Ping; the empty-queue rule lets the Ping answer in. |
| `MuxIngressSharedBudgetBug.cfg` | Deadlock without the empty-queue rule. This is why it exists. |

**The hazard.** While backpressure holds the read loop, a reader that waits
on another mini-protocol of the same connection waits forever: the answer is
behind segments the loop cannot place. In gOuroboros terms: while block-fetch
has unsized requests outstanding, a block-fetch callback that synchronously
waits for another protocol's reply on the same connection deadlocks the
connection. gOuroboros's documentation says pausing stops every protocol; it
does not spell out this consequence. It is a hazard for applications, not a
bug in gOuroboros as such.

**The budget arithmetic.** For honest traffic the budget must cover every
protocol's limit at once. gOuroboros's node-to-node limits (each at least
`minIngressLimit`, 655,350 bytes) sum to about 15 MB across both directions,
against a `DefaultIngressBudget` of 64 MB. Payloads are allocated at exactly
their length (`make([]byte, header.PayloadLength)`), so the budget charges
bytes plus a fixed overhead of about 64 bytes per segment. The budget cannot
be hit by honest traffic.

## Part 4: errors and the shutdown order (`ConnectionShutdown.tla`)

Five goroutines from `connection.go`: setup (waiting for the handshake, then
starting the protocol-error forwarder with `waitGroup.Go`, then
`lockProtocolSetup`), the muxer-error forwarder, the protocol-error
forwarder, the shutdown goroutine (`stopProtocols`, `muxer.Stop`,
`waitGroup.Wait`, close `errorChan`, close `connClosedChan`), and a user
calling `Close`. Errors are forwarded with
`select { errorChan <- err; <-doneChan; default }`, and in Go a send on a
closed channel panics, even inside a `select`.

| Config | Result |
| --- | --- |
| `ConnectionShutdown.cfg` | **Passes: 420 distinct states.** Nothing sends on the closed `errorChan`, `Close` returns only after shutdown has finished, and nothing deadlocks. |
| `ConnectionShutdownLateErrorBug.cfg` | **Panics** if a protocol could report an error after the handshake finished. |

**A latent hazard.** The protocol-error forwarder is started after the
handshake, outside `lockProtocolSetup`, so it can start after
`waitGroup.Wait` has returned and `errorChan` is closed. Today that is safe
only because no protocol can have an error pending then: the handshake server
sends its accept and waits for the write before `FinishedFunc` signals
completion, a protocol in its `Done` state reports no read errors, a protocol
that reports an error stops itself, and the other mini-protocols start only
in `lockProtocolSetup`. The first version of this module let protocols fail
at any time and found the panic; reading the code removed that path. Any
change that lets a protocol fail between the handshake and
`lockProtocolSetup` would make it reachable.

**Overturned by part 5.** Two of those premises do not hold: a protocol in
its `Done` state does report read errors (an oversized message or the
read-buffer budget, `protocol/protocol.go:1946`, `:2073`, `:2109`, all
before the terminal-message check at `:2117`), and `SendError` checks
`stopChan` and then sends, so a protocol stopped by `stopProtocols` between
the two still queues its error. Part 5 shows the panic.

## Part 5: teardown while Dial runs (`ConnectionTeardown.tla`)

Part 4 starts after `doneChan` exists. This part starts at the top of
`setupConnection` (gOuroboros `5c4f31c1`, `connection.go:670`) and adds what
part 4 abstracts: the creation of `doneChan` (`:684`) and of the muxer
(`:701`) with its cleanup goroutine, a `Close` from another goroutine
(`:258`, a no-op while `doneChan` is nil), the WaitGroup at Go's rule (an
`Add` from zero must happen before `Wait`), the handshake's `SendError` as
two steps, and one mini-protocol callback. A fix is a constant: `fence`
(start a tracked goroutine under a mutex after checking `doneChan`; shutdown
takes the mutex before `Wait`, as `muxer.fenceRegistrations` does at
`muxer/muxer.go:1340`) and `muxerGuard` (create the muxer under a mutex
after checking `doneChan`; shutdown reads `c.muxer` under it).

Three-way comparison: the specification is silent; the reference's
connection handler runs the mux in `withJobPool` and every thread it starts
is waited for before `run` returns (`network-mux/src/Network/Mux.hs:280-287`
at `5f356486ab3e`), so there is no window where a thread starts after the
wait; gOuroboros starts goroutines with `waitGroup.Go` at `:704` and `:844`
without checking whether shutdown has begun.

| Config | States | Result |
| --- | --- | --- |
| `ConnectionTeardown.cfg` (gOuroboros, `Close` after `Dial`, no late error) | 1,020 | passes `NoPanic`, `CloseWaitsForShutdown`, `MuxerStoppedWhenClosed` |
| `ConnectionTeardownFixed.cfg` (both fixes, concurrent `Close`, late error) | 9,004 | passes those and `NoAddAfterWaitBegan` |
| `ConnectionTeardownWaitGroupBug.cfg` (gOuroboros) | | `NoAddAfterWaitBegan` violated, with no concurrent `Close`: a muxer error closes `doneChan` after the handshake select |
| `ConnectionTeardownLateErrorPanicBug.cfg` (gOuroboros) | | `NoPanic` violated: the late forwarder sends the handshake's queued error on the closed `errorChan` |
| `ConnectionTeardownCloseDuringDialBug.cfg` (gOuroboros) | | `MuxerStoppedWhenClosed` violated: shutdown saw no muxer, setup then made one |
| `ConnectionTeardownFenceOnlyBug.cfg`, `GuardOnlyBug.cfg` | | each fix alone leaves the other defect |
| `ConnectionTeardownCallbackAfterCloseBug.cfg` | | `NoCallbackAfterClose` violated even with both fixes (inventory A3; decision) |
| `ConnectionTeardownProbe*Bug.cfg` (two) | | probes reached: the handshake finishes after setup gave up (A4); `Close` before the muxer exists |

Go: `fix/connection-close-during-dial` (`2ed2f1f3`,
`TestCloseBeforeMuxerCreatedClosesConn`: without the fix the conn stays
open and goleak lists the muxer and handshake goroutines) and
`fix/connection-late-forwarder` (`264dc5be`,
`TestNoForwarderStartedAfterShutdown`: without the fix, 20 runs gave 11
"forwarder took the queued error" failures and 9 `panic: send on closed
channel`). The test queues the error by hand at the point the handshake's
`SendError` would; the end-to-end path from peer bytes was not reproduced.
The two branches conflict trivially in the `Connection` struct.

## What model `connection` found

- **Messages survive restarts.** Carrying the read buffer, admitting one
  message at a time, and resuming the receiver are each necessary, and
  together sufficient (part 1).
- **The keep-alive fix holds with bytes in flight** (part 2,
  `MuxHandoverServerStop.cfg`).
- **A shutdown bug**: during a connection close, a restarting server
  re-registered with the muxer and could handle a message after
  `stopProtocols` (part 2). Reproduced in Go with chain-sync, reported as
  gOuroboros issue #3085, fixed by pull request #3087 (merged), and checked
  here (`MuxHandoverClose.cfg`).
- **A backpressure hazard** for applications whose block-fetch callbacks wait
  on another protocol (part 3).
- **A panic in the shutdown order**, which part 4 judged unreachable and
  part 5 reaches: a forwarder started after shutdown's `Wait` sends a
  stopped protocol's queued error on the closed `errorChan`.
- **A leaked muxer and conn** when `Close` runs during `Dial` (part 5).
- Negative results, also worth knowing: the connection budget cannot be hit
  by honest traffic (part 3), and `Close` always returns after shutdown
  (part 4).

## Not modelled yet

Byte sizes beyond "fits or not", timeouts, and the egress side of the
muxer. Protocol goroutines outliving `Close` is modelled (part 5) but not
fixed: it needs a decision on where the join belongs.
