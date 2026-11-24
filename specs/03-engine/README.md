# Model 03: the protocol engine

Every gOuroboros mini-protocol runs on the same engine, `protocol/protocol.go`:
the code that reads messages, decides whether to accept them, sends, and moves
the state machine along. It is also where gOuroboros has needed the most
fixes (23 in the six months to 2026-11-23, in one 2,500-line file). A bug here
is a bug in every protocol; a model of it is reused by every protocol model
that follows.

The engine is modelled in slices, simplest first:

| Slice | Module | What it covers |
| --- | --- | --- |
| 1 | `EngineAdmission.tla` | Admission for protocols that do not pipeline |
| 2 | (next) | Pipelined sends, with state changes applied later |
| 3 | (next) | Pipelined replies and their reservations |

Read [Model 01](../01-keepalive/README.md) first.

## Slice 1: admission (`EngineAdmission.tla`)

### What admission is

Four goroutines share each protocol instance: `readLoop` reads messages and
decides whether to **admit** each one; `recvLoop` takes admitted messages,
applies their state change, and calls the protocol's handler; `sendLoop` sends
this side's messages; and `stateLoop` applies every state change, one at a
time, bumping a counter called the **generation**.

Admission happens in two steps, because a message's bytes arrive over time:

1. When the message's first bytes arrive, `readLoop` takes a **snapshot** of
   the state and its generation.
2. When its type is known, `readLoop` asks to admit it against the state at
   that moment (`reserveInboundAdmission`):
   - **The peer has agency.** Refuse if the generation moved since the
     snapshot, unless it moved by exactly one and the snapshot's state had
     the peer talking too (`continuesPeerAgency`). Otherwise admit, and
     **reserve** (`peerAgencyReserved`) so the next message waits until this
     one has been applied; if a message is already reserved, wait and ask
     again (every millisecond).
   - **We have agency.** Refuse: the peer spoke out of turn.
   - **Nobody has agency** (`StDone`). Drain the message.

Every state change clears the reservation. `sendLoop` applies our own state
change before writing our message to the wire, so the peer's reply can never
arrive ahead of it.

Why the one-generation allowance exists: in chain-sync the server may send
`MsgAwaitReply` and then `MsgRollForward`, and in block-fetch `MsgStartBatch`,
then `MsgBlock` after `MsgBlock`, then `MsgBatchDone`. The second message's
snapshot can be taken before the first one's state change, which then moves
the generation by one.

### The question

> With an honest peer, is a message ever refused, or applied in a state where
> it is illegal, or does anything deadlock, for any interleaving of the four
> goroutines and the network?

The model plays the engine as the client, and an honest server that sends only
when it has agency, and only legal messages. The protocols are the
specification's own state tables for keep-alive, chain-sync, and block-fetch.

### Sources

| Ref | Source |
| --- | --- |
| S1 | [`docs/network-spec/miniprotocols.tex` lines 27-36](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36): one side has agency at a time. |
| C1 | [Same file, lines 838-849 and 894-907](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L838-L907): chain-sync agencies and transitions (PDF section 3.7). |
| B1 | [Same file, lines 1160-1202](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1160-L1202): block-fetch agencies and transitions (PDF section 3.8). |
| K1 | [Same file, lines 1575-1598](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1575-L1598): keep-alive. |
| G1 | gOuroboros `protocol/protocol.go` at commit `79786c01`: `reserveInboundAdmission`, `waitForInboundAdmissionWithWait`, `readLoop`, `recvLoop`, `stateLoop` (`setState`), `sendLoop`. |

The PDF section numbers for C1 and B1 come from the rendered specification's
table of contents and can move; the pinned source lines are the citation.

### Run it

```sh
make engine
```

| Config | Result |
| --- | --- |
| `EngineAdmissionKeepAlive.cfg` | **Passes: 21 distinct states.** |
| `EngineAdmissionChainSync.cfg` | **Passes: 354 distinct states**, including `MsgAwaitReply` then `MsgRollForward` back to back. |
| `EngineAdmissionBlockFetch.cfg` | **Passes: 540 distinct states**, including a batch streamed back to back. |
| `EngineAdmissionNoContinueBug.cfg` | Fails without the one-generation allowance: a `MsgBlock` snapshotted in `StBusy` is refused once `MsgStartBatch` moves the state to `StStreaming`. |
| `EngineAdmissionNoReserveBug.cfg` | Fails without the reservation: `readLoop` admits `MsgStartBatch` and two blocks ahead of `recvLoop`, the generation moves by two before the second block is admitted, and an honest block is refused. |

Each passing config checks that an honest peer is never refused and nothing
admitted is ever illegal when applied (`NoFalseViolation`), that at most one
admitted message waits at a time (`AtMostOneAdmitted`), that both sides agree
on the state whenever nothing is in flight (`ViewsAgreeWhenQuiet`), and that
nothing deadlocks.

### What slice 1 found

No bug. The two rules depend on each other: the reservation is what keeps the
drift between a snapshot and its admission to at most one generation, and the
allowance is what accepts exactly that drift. Remove either and an honest peer
is refused. Reading `sendLoop` for this slice also confirmed that gOuroboros
never batches a non-pipelined message out of turn: after a batch's first
message, a later one joins only if the state allows pipelining and lists its
type, and otherwise waits for the next agency window.

The existing gOuroboros tests (`protocol/message_scanner_test.go`) cover
refusal outside agency and many pipelined cases. A direct test of the two
rules above for a protocol that does not pipeline - drift of one accepted
after a peer-agency state, drift of one refused after a local-agency state,
drift of two refused - is not among them.

### Not in this slice

Pipelining: `PipelinedMessageTypes`, pipelined requests and their deferred
state changes, pipelined replies and their reservations, and
`pipelinedTypeGenerations`. Those are slices 2 and 3.
