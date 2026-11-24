# Model 02: the connection and the multiplexer

Every mini-protocol on a connection shares one multiplexer (the "mux"). It
cuts each mini-protocol's messages into segments, sends them over one socket,
and on the other side reassembles each mini-protocol's byte stream. Bugs here
affect every protocol at once, and they live in concurrent Go code that tests
rarely drive into its rare orderings. That is what TLA+ is good at.

This model is built in parts. Read [Model 01](../01-keepalive/README.md) first.

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
| S4, S7, S8 | As in [Model 01](../01-keepalive/README.md#sources) | A finished run's unread bytes are kept for the next run; a server restarts after `MsgDone`; a new run's first message may share a chunk with the old run's last. |

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
| `MuxHandover.cfg` | **Passes: 476 distinct states.** Every message is handled once, in order (`DeliveredInOrder`); no instance refuses an honest message (`NoViolation`); at most one message is admitted at a time; and nothing gets stuck. |
| `MuxHandoverNoCarryBug.cfg` | Deadlock: a ping that was in the old read buffer is lost, and the client waits forever for its answer. |
| `MuxHandoverAdmitAllBug.cfg` | Deadlock after 14 steps: the old instance admits the next run's ping before it has handled `MsgDone`; the restart discards it. |
| `MuxHandoverNoResumeBug.cfg` | Deadlock: segments queued in the old receiver are lost with it. |

The failing configs show why each mechanism exists. The passing one says the
three together are enough, for every way the bytes can be cut and every order
in which the client, the read loop, the receive loop, and the restart can
run.

### What this part does not cover yet

- `Stop` and connection shutdown during a restart (Model 01's
  `KeepAliveLifecycle.tla` has them, without bytes).
- Several mini-protocols sharing the mux, the per-protocol ingress limits, and
  the connection-wide budget.
- Errors travelling to the connection, and the shutdown order.

Those are the next parts.
