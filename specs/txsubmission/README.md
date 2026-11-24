# tx-submission and its outstanding window

Tx-submission (node-to-node, version 2) moves transactions from a node that
has them to a node that wants them. Agency is the other way round from
chain-sync: the **server** (the inbound side, which wants transactions) asks,
and the **client** (the outbound side, which holds a mempool) answers.

The client keeps a FIFO of the transaction ids it has announced and the
server has not yet acknowledged. Each `MsgRequestTxIds(blocking, ack, req)`
first drops `ack` ids from the front of the FIFO, then asks for up to `req`
more. `MsgRequestTxs` asks for the bodies of some ids in the FIFO. The FIFO is
bounded by a window of 10 ids.

The blocking flag is not a free choice. The specification and the reference
make it a function of the FIFO:

- **Blocking** exactly when nothing is left unacknowledged after the
  acknowledgement. It must ask for at least one id, the reply must hold at
  least one, and it has no timeout. `MsgDone` is allowed only as its answer.
- **Non-blocking** exactly when something is left. It must acknowledge or ask
  for something, and the reply may be empty.

Read [Model `keepalive`](../keepalive/README.md) first for the receive-table idea.

## What the code does

gOuroboros (`protocol/txsubmission/`, at `61046085`):

- **`Client.handleRequestTxIds`** refuses a request that acknowledges more
  ids than it holds, or that would put the FIFO past the window. It then calls
  `RequestTxIdsFunc`, refuses a reply longer than the request or an empty
  reply to a blocking request for at least one id (`reconcileTxIds`), sends
  the reply, and records the new FIFO. If the callback asks to stop, it sends
  `MsgDone` for a blocking request and fails for a non-blocking one.
- **`Client.handleRequestTxs`** refuses duplicates and ids not in its FIFO.
- **`Server.RequestTxIds(blocking, n)`** lets the caller choose the flag. It
  always acknowledges `ackCount`, the length of the previous reply, so it
  **acknowledges everything it holds every time**. It refuses locally only an
  over-long acknowledgement or a request past the window. One request is
  pending at a time; the server never pipelines.
- **`Server.handleReplyTxIds` / `handleReplyTxs` / `handleDone`** check each
  reply against the pending request (`reconcileTxIds`,
  `validateAndOrderTxBodies`); `MsgDone` must answer a pending blocking
  request.

## The questions

`TxSubmission.tla` lets each side be the reference, gOuroboros today, a fixed
gOuroboros, or a rogue peer that sends anything:

1. **`ClientRefusesIllegal`**: does the client ever answer a request the
   reference client refuses?
2. **`ClientRefusesOnlyIllegal`**: does it ever refuse one the reference
   answers?
3. **`ServerSendsLegal`**: does an honest server ever send a request the
   reference client refuses?
4. **`ServerRefusesIllegal`** and **`ClientSendsLegal`**: the same two
   questions for replies.
5. **`BlockingRule`** / **`NonBlockingRule`**: is every blocking request
   answered with nothing left unacknowledged, and every non-blocking one with
   something left?
6. **`WindowBound`**: does the FIFO stay within the window?
7. **`ViewsAgree`**: do both sides hold the same FIFO between messages?
8. **`HonestNeverRefused`**: do two honest sides ever refuse each other?
9. **`ClampsOverWindow`**: from V16, does the client ever refuse a request
   only because it asks past its window, which the reference clamps?
10. Deadlock, which TLC checks by default.

`TxSubmissionTable.tla` asks the per-message question: for every role, state
and message kind, what does the receiver do?

## The answers

Window of 2, 4 fresh ids, 5 requests:

| Config | Server | Client | States | Result |
| --- | --- | --- | --- | --- |
| `TxSubmissionReference.cfg` | reference | reference | 375 | passes, every invariant |
| `TxSubmissionGouroboros.cfg` | gOuroboros | gOuroboros | 871 | passes the four invariants it lists |
| `TxSubmissionGouroborosBug.cfg` | gOuroboros | gOuroboros | | **fails** `NonBlockingRule` |
| `TxSubmissionEmptyReplyBug.cfg` | gOuroboros | gOuroboros | | **fails** `ClientSendsLegal` |
| `TxSubmissionServerBug.cfg` | gOuroboros | reference | | **fails** `ServerSendsLegal` |
| `TxSubmissionServerFixed.cfg` | fixed | reference | 186 | passes, every invariant |
| `TxSubmissionClientBug.cfg` | rogue | gOuroboros | | **fails** `ClientRefusesIllegal` |
| `TxSubmissionClientBlockingBug.cfg` | rogue | gOuroboros | | **fails** `BlockingRule` |
| `TxSubmissionClientFixed.cfg` | rogue | fixed | 2,342 | passes |
| `TxSubmissionRogueClientBug.cfg` | gOuroboros | rogue | | **fails** `ServerRefusesIllegal` |
| `TxSubmissionRogueClient.cfg` | fixed | rogue | 239 | passes |
| `TxSubmissionFixed.cfg` | fixed | fixed | 186 | passes, every invariant |
| `TxSubmissionV16.cfg` | reference, V16 | reference, V16 | 572 | passes, every invariant |
| `TxSubmissionV16Bug.cfg` | reference, V16 | fixed | | **fails** `ClientRefusesOnlyIllegal` |
| `TxSubmissionV16ClampBug.cfg` | reference, V16 | gOuroboros | | **fails** `ClampsOverWindow` |
| `TxSubmissionV16Clamp.cfg` | reference, V16 | gOuroboros, clamping | 572 | passes, every invariant |
| `TxSubmissionV16ClampRogue.cfg` | rogue, V16 | fixed, clamping | 2,716 | passes |

Three findings:

**The gOuroboros server sends requests the reference client refuses.**
Because it acknowledges everything it holds every time, nothing is ever left
unacknowledged after its acknowledgement. So every non-blocking request it
sends breaks the rule, and a reference client throws
`ProtocolErrorRequestNonBlocking` and closes the connection. The shortest
trace is three states: `MsgInit`, then `RequestTxIds(false, 1)`. It also lets
a caller send a blocking request for zero ids (`RequestedNothing`), which the
gOuroboros client then answers with an empty blocking reply
(`TxSubmissionEmptyReplyBug.cfg`) that the reference codec cannot decode. In
practice Dingo only sends blocking requests for at least one id, so it is not
affected; the exported API allows the rest.

**The gOuroboros client answers requests the reference client refuses.** It
checks the acknowledgement and the window, but not the blocking flag: a
blocking request with ids still outstanding, a blocking request for zero ids,
a non-blocking request with nothing outstanding, and a non-blocking request
that neither acknowledges nor asks. The first means the client may block
indefinitely (no timeout) while the server still holds ids it could fetch.

**gOuroboros on both sides hides both bugs.** `TxSubmissionGouroboros.cfg`
passes: the lax client accepts what the lax server sends. Each bug shows only
against the reference.

The two fixes together (`TxSubmissionFixed.cfg`) pass every invariant. With
the fixed server, `RequestTxIds(false, …)` is always refused, since that
server never leaves anything outstanding; it can only use blocking requests.

**Version 16.** From `NodeToNodeV_16` the window is a local setting of each
side, and the reference client clamps an oversized request instead of
refusing it (`TxOutboundV_2`): it replies with at most
`maxUnacked - (unacked - ack)` ids [R4]. gOuroboros negotiates V16 but its
client still refuses, as before V16. Against a reference server configured
with a window larger than 10 it would close the connection
(`TxSubmissionV16Bug.cfg`, and `TxSubmissionV16ClampBug.cfg`, which names
the fault on its own: `ClampsOverWindow`). The default window is 10 on both
sides, so default nodes do not meet it.

`ClientClamps` switches the gOuroboros client to the reference rule. Against
the reference server every invariant holds (`TxSubmissionV16Clamp.cfg`).
Against a rogue server, the fixed client with clamping still refuses every
request the reference refuses and its FIFO stays within the window
(`TxSubmissionV16ClampRogue.cfg`): clamping replaces only the window check,
not the acknowledgement or style checks. Before V16 the switch changes
nothing. Branch `fix/txsubmission-clamp-request-window` makes the change.

### The receive table

`TxSubmissionTable.cfg` prints 84 rows (2 roles × 6 states × 7 message
kinds). The receiver moves to the next state if its peer has agency and the
state has that transition, aborts otherwise, and does not read the message
yet if it holds agency itself ("Waits"). After `MsgDone` the server judges
the next message as the first of a new run, and the client leaves it unread.
gOuroboros judges a message on arrival, so its "Waits" is a refusal, except
that the client queues requests the server pipelines in `StTxIdsNonBlocking`
and `StTxs`.

## Checking the checks

Every invariant is shown to fail at least once: the `*Bug.cfg` configs above
for the first five and `BlockingRule`/`NonBlockingRule`, and two mutations:

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `TxSubmissionNoWindowBug.cfg` | the client's window check | `WindowBound` |
| `TxSubmissionKeepsAckedBug.cfg` | the server dropping acknowledged ids | `ViewsAgree` |

`HonestNeverRefused` fails in `TxSubmissionServerBug.cfg` as well.

The reachability probes at the bottom of `TxSubmission.tla` each claim that
something never happens. Each was run alone against
`TxSubmissionReference.cfg` and **each is violated**: the client reaches
`StTxIdsBlocking`, `StTxIdsNonBlocking`, `StTxs` and `StDone`; the FIFO fills
the window; and a non-blocking request acknowledges some ids while leaving
others (`ProbeNoPartialAck`). `TxSubmissionProbesBug.cfg` lists them all;
TLC stops at the first, so keep one `INVARIANT` line to see each.

## Modelling notes

- One step is one message, sent and judged at once. The gOuroboros server
  never pipelines, and the reference client reads pipelined requests in order
  after its reply, so this loses nothing for the window. The receive table
  covers messages that arrive early.
- The first draft of the probes config used TLC's `-continue` to report all
  probes in one run. It did not report `ProbeNoPartialAck`, although that
  probe is violated when run alone. Probes are therefore run one at a time.
- `RECURSIVE` (in `TxSubmissionTable.tla`) declares an operator that calls
  itself; here a server in `StDone` is judged as if in `StInit`.

## Go tests and fixes

Branches in the gOuroboros worktree, from `origin/main` `61046085`. None is
pushed.

**`test/txsubmission-state-model`**: `statemap_model_test.go` holds the 84
rows above. `TestStateMapMatchesModel` derives each within-run cell from
`StateMap` alone; `TestReceiveMatchesModel` drives a running client or
server into every cell and checks the outcome; `TestStatesThatCannotBeEntered`
pins that nothing re-enters `Init` and only `MsgDone` from `TxIdsBlocking`
enters `Done`; `TestClientSendsDoneOnlyForBlocking` checks the client never
sends `MsgDone` for a non-blocking request. Each was shown to fail under a
mutation:

| Mutation | Fails |
| --- | --- |
| drop `MsgDone` from `TxIdsBlocking` | `StateMap…/server/inTxIdsBlocking/MsgDone`, receive rows |
| drop `PipelinedMessageTypes` from `Txs` | the three client `inTxs` request rows, both tests |
| blocking `MatchFunc` always true | client `inIdle`/`inTxIdsNonBlocking` request rows |
| client sends `MsgDone` for a non-blocking stop | `TestClientSendsDoneOnlyForBlocking` |
| server does not restart after `MsgDone` | every `server/inDone` row |

Existing tests already pin the window and acknowledgement checks, `MsgRequestTxs`
membership, reply length, the empty blocking reply, size limits and pipelined
queueing; the new tests do not repeat them.

**`fix/txsubmission-client-request-rules`** (`fe65e481`): the client
refuses the four request shapes above (`checkRequestTxIdsStyle` in
`handleRequestTxIds`). `TestClientEnforcesRequestStyle` has nine cases, each
refused case next to an accepted one differing in one field; without the fix
the five refused cases fail and the four accepted pass.

**`fix/txsubmission-server-request-rules`** (`58ea57e9`): `RequestTxIds`
refuses, without sending, a non-blocking request or a blocking request for
nothing. `TestServerSendsOnlyRequestsOfTheRightStyle` has seven cases; without
the fix the four refused cases fail.

Both branches add the same helper, byte for byte, and change the same
existing tests the same way. Merged together with the test branch, the
package passes. Existing tests that sent the illegal shapes (non-blocking
from an empty FIFO, a zero request) now send the legal form. One of them,
`TestRequestTxIdsOverReturningCallbackNeverReachesThePeer`, had relied on the
10 s timeout of `TxIdsNonBlocking` to end the server's wait. A blocking
request has no timeout, so the test now stops the server itself.

## Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Blocking or not? | Blocking iff nothing remains after the ack [S3][S5] | Same; client throws `RequestBlocking`/`RequestNonBlocking` [R3]; server picks by its FIFO [R6] | Client does not check; server lets the caller choose, and never leaves anything | **Defect**, both sides |
| Request for nothing? | Blocking: req > 0; non-blocking: ack or req non-zero [S3] | `RequestedNothing` [R3] | Not checked by either side | **Defect**, both sides |
| Over the window | Error before V16, clamp from V16 [S4] | Same, by version [R4] | Always an error | **Differs** from V16; fixed on a branch |
| Empty blocking reply | Not allowed [S3] | Fails to decode [R2] | Client will not send one for req > 0; server refuses it for req > 0 | Agrees once req = 0 is refused |
| `MsgDone` | Only from `StTxIdsBlocking` [S2][S3] | Same [R1][R5] | Same (`StateMap`, `handleDone`) | Agrees |
| `MsgRequestTxs` ids | Announced, outstanding, no duplicates, not already asked for [S3] | Distinct and in the FIFO; "already asked for" not checked [R3] | Distinct and in the FIFO | Agrees with the reference |
| Duplicate ids in a reply | Not stated | Not checked | Refused | gOuroboros stricter; a reference peer never sends one |
| Messages that arrive early | Not stated | Read later [R7] | Refused, except pipelined requests in `TxIdsNonBlocking`/`Txs`, which are queued | Recorded difference |

## Sources

Pinned to [IntersectMBO/ouroboros-network `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c)
and gOuroboros `origin/main` at `61046085`. Reference paths are under
`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/`
unless shown.

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | [`docs/network-spec/miniprotocols.tex` 27-36](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36) | An unexpected message aborts the connection. |
| S2 | [same, 1285-1322, 1420-1432](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1285-L1432) | States, agency, transitions. |
| S3 | [same, 1323-1418](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1323-L1418) | "Either the numbers acknowledged or the number requested MUST be non-zero"; non-blocking "MUST be made ... if there are non-zero remaining unacknowledged transactions"; blocking: "This must be greater than zero", "MUST be made ... if there are zero remaining"; "In the blocking case, the reply MUST contain at least one"; `MsgRequestTxs` rules; `MsgDone` "when the server is making a blocking call". |
| S4 | [same, 1455-1475](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1455-L1475) | Window 10 before V16; from V16 a local setting and the client "replies with at most as many transaction ids as fit". |
| S5 | [same, 1527-1557](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1527-L1557) | Both sides agree on the FIFO; "If the FIFO is empty, the consumer must use a blocking request; otherwise, it must be a non-blocking request." |
| R1 | [`Type.hs` 196-317](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Type.hs#L196-L317) | Messages and agency; 214-241 the same rules as S3. |
| R2 | [`Codec.hs` 392-425](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Codec.hs#L392-L425) | Decoding per state; "MsgReplyTxIds: empty list not permitted" for blocking. |
| R3 | [`ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs` 131-260](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs#L131-L260) | The client's checks: `AckedTooManyTxids`, `RequestedTooManyTxids`, `RequestedNothing`, `RequestBlocking`, `RequestNonBlocking`; `MsgRequestTxs` duplicates and availability. |
| R4 | [`Outbound.hs` 95-104](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs#L95-L104), [`cardano-diffusion/lib/Cardano/Network/NodeToNode.hs` 389-391](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/cardano-diffusion/lib/Cardano/Network/NodeToNode.hs#L389-L391) | `TxOutboundV_2` from `NodeToNodeV_16`: clamp, not refuse. |
| R5 | [`Server.hs` 112-130](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Server.hs#L112-L130) | A blocking request awaits `MsgDone` or a non-empty reply; only non-blocking requests are pipelined. |
| R6 | [`ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/V2.hs` 334-358, 386-425](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/V2.hs#L334-L425) | The reference server sends blocking iff its FIFO is empty; reply checks `TxIdsNotRequested`, `TxNotRequested`. |
| R7 | typed-protocols `Driver.hs` (as cited in Model `keepalive`, `[S8]`) | A side reads only when its peer has agency. |
| G1-G4 | gOuroboros `protocol/txsubmission/` `txsubmission.go`, `client.go`, `server.go`, `validation.go` | `StateMap`; `handleRequestTxIds`, `handleRequestTxs`; `RequestTxIds`, `RequestTxs`, `handleReplyTxIds`, `handleReplyTxs`, `handleDone`; `reconcileTxIds`, `requestedTxIdsAreOutstanding`. |

## Not modelled

Transaction sizes and the size checks, byte limits, timeouts, the server's
restart race after `MsgDone`, client `Stop`/`Start`, the reference server's
pipelining depth, and duplicate ids within one reply.

## Running it

```sh
cd specs/txsubmission
# passing
../../bin/tlc -config TxSubmissionReference.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionGouroboros.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionServerFixed.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionClientFixed.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionRogueClient.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionFixed.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionV16.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionV16Clamp.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionV16ClampRogue.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionTable.cfg TxSubmissionTable.tla | grep '^<<'
# expected to fail
for c in GouroborosBug EmptyReplyBug ServerBug ClientBug ClientBlockingBug \
         RogueClientBug V16Bug V16ClampBug NoWindowBug KeepsAckedBug ProbesBug; do
  ../../bin/tlc -config TxSubmission$c.cfg TxSubmission.tla || true
done
```
