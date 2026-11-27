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
| `TxSubmissionV16ClampBlockingBug.cfg` | rogue, V16 | gOuroboros, clamping, first draft | | **fails** `ClientSendsLegal` |
| `TxSubmissionV16ClampBlocking.cfg` | rogue, V16 | gOuroboros, clamping | 5,634 | passes the four invariants it lists |
| `TxSubmissionZeroClampProbeBug.cfg` | reference, V16 | gOuroboros, clamping | | **fails** `ProbeNoZeroClamp` (reachable) |
| `TxSubmissionV16RefuseAckedBlockingBug.cfg` | reference, V16 | gOuroboros, clamping, refuses an acknowledged window | | **fails** `ClientRefusesOnlyIllegal` |

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

**The clamp's first draft sent an empty blocking reply (PR #3195 review).**
The first draft (`4b7d5262`) clamped every request, blocking or not, and
checked the callback's reply against the clamped count. A blocking request
that leaves ids unacknowledged on a full window was clamped to zero and
answered with an empty `MsgReplyTxIds`, which [S3] forbids and [R2] cannot
decode. The reference never gets there: [R3] throws `RequestBlocking` (and
`RequestedNothing`) before it uses the clamped count, so with nothing left
the clamp is `min(req, maxUnacked)`, which is at least one. A reference or
reference-following server never sends such a request, so only a server that
breaks [S3] reaches it.

The model shared the gap. `ClientReplyIds` made an honest client send at
least one id whenever `b` and `n > 0`, so the clamped bound `hi = 0` left no
reply step and the client could only send `MsgDone`; the empty reply was
never generated. `lo` now follows the code: at least one id only when the
bound the client checks, `hi`, is at least one. With that, mutation
`clampBlocking` (the first draft) fails `ClientSendsLegal` in three steps:
fill the window, then a blocking request for one id
(`TxSubmissionV16ClampBlockingBug.cfg`). The fix (`b2a2f787`): a clamping
client refuses a blocking request for no ids or one that leaves ids
unacknowledged, in every version, before it clamps (`blockOK` in
`ClientAcceptsIds`); `TxSubmissionV16ClampBlocking.cfg` passes against a
rogue server. This is the blocking half of the style rules the
`fix/txsubmission-client-request-rules` branch (PR #3128) adds; the two use
the same refusal messages.

The permissive side of that refusal (second review of PR #3195): a blocking
request that acknowledges the whole window and asks for ids is legal and must
be served. The model already covered it: `ClientRefusesOnlyIllegal` in
`TxSubmissionV16Clamp.cfg` flags any legal request the client refuses. The
mutation `refuseAckedBlocking` (counting the ids left before the
acknowledgement, the reviewer's Go mutant) now shows it:
`TxSubmissionV16RefuseAckedBlockingBug.cfg` fails in four steps (fill the
window, then a blocking request acknowledging both ids). The Go test gained
the served case at `8ece4753`; no behaviour changed, so the model's rules are
unchanged.

A non-blocking request on a full window is clamped to zero and answered with
an empty reply, as [R4] says ("can be none for a non-blocking request").
`ProbeNoZeroClamp` shows the model reaches it against a reference server with
a larger window. The code still calls `RequestTxIdsFunc` with a count of
zero there: the callback is how a gOuroboros caller learns the
acknowledgement (Dingo's `AcknowledgeOffered`), which [R3] applies itself
(`Seq.drop ackNo`) even when the count is zero. Not modelled; the model has
no callback.

### The receive table

`TxSubmissionTable.cfg` prints 84 rows (2 roles × 6 states × 7 message
kinds). The receiver moves to the next state if its peer has agency and the
state has that transition, aborts otherwise, and does not read the message
yet if it holds agency itself ("Waits"). After `MsgDone` the server judges
the next message as the first of a new run, and the client leaves it unread.
gOuroboros judges a message on arrival, so its "Waits" is a refusal, except
that the client queues requests the server pipelines in `StTxIdsNonBlocking`
and `StTxs`.

## A local stop during a blocking request

What a client application answers when its own node stops during a blocking
`MsgRequestTxIds` is the application's behaviour, not gOuroboros's. Dingo's
answer is modelled in the Dingo models repository, `specs/txsubmission-client`.
The gOuroboros side is unchanged: `ErrStopServerProcess` from
`RequestTxIdsFunc` sends `MsgDone`, and an empty reply to a blocking request
is refused as a protocol violation, as the reference requires.

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
| Over the window | Error before V16, clamp from V16 [S4] | Same, by version [R4] | PR #3195 head `8ece4753`: error before V16, clamp from V16; a blocking request is refused before clamping when it asks for nothing or leaves ids | Agrees once PR #3195 merges |
| Blocking request on a full window | Must not be sent; reply non-empty [S3] | `RequestBlocking` before the clamp [R3] | PR #3195 first draft `4b7d5262`: clamped to zero, empty reply; head `8f6c6d5b`: refused | **Defect** in the first draft; fixed at `8f6c6d5b` |
| Non-blocking request on a full window, from V16 | Reply "with at most as many as fit" [S4] | Clamped to zero, empty reply [R4] | Same; the callback is called with zero to deliver the acknowledgement | Agrees |
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
| R8 | [`ouroboros-network/api/lib/Ouroboros/Network/ControlMessage.hs` 43-55](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/api/lib/Ouroboros/Network/ControlMessage.hs#L43-L55) | `timeoutWithControlMessage`: `Terminate` returns `Nothing`, which `Outbound.hs` 201 answers with `MsgDone`. |
| G1-G4 | gOuroboros `protocol/txsubmission/` `txsubmission.go`, `client.go`, `server.go`, `validation.go` | `StateMap`; `handleRequestTxIds`, `handleRequestTxs`; `RequestTxIds`, `RequestTxs`, `handleReplyTxIds`, `handleReplyTxs`, `handleDone`; `reconcileTxIds`, `requestedTxIdsAreOutstanding`. |

## The server's locks and restart (`TxSubmissionServerLocks.tla`)

`TxSubmission.tla` answers which messages are legal. This module asks how
the gOuroboros server (`protocol/txsubmission/server.go`, at `7cd17437`)
moves a reply from its receive loop to the goroutine that asked for it,
and how it restarts after `MsgDone` while `Stop` may run. It models:

- **Callers** of `RequestTxIds`: `requestMu`, then `protocolMu` for reading,
  then `stateMu`; record the pending request; unlock; send; wait on the
  instance's one-slot result channel or its `DoneChan`. A caller that gets
  `ErrStopServerProcess` may call again, on the restarted instance.
- **The handler**, the current instance's receive loop: `handleInit`,
  `handleReplyTxIds`, and `handleDone` with its restart
  (`StopForRestart`, `initProtocol` under `protocolMu` then `stateMu`,
  `Start`).
- **The stopper**, `Server.Stop`: `protocolMu` for writing, set `stopped`,
  read the instance, stop it, wait for its loops.

`sync.RWMutex` gives a waiting writer preference: once `Stop` waits in
`Lock`, a new `RLock` blocks. The model encodes that (`CanRLock`), and it
is what turns the inversion below into a deadlock. Restart-vs-`Stop` muxer
slot handling is `specs/keepalive/KeepAliveLifecycle.tla`, which stands
for this server too, and is not repeated.

Invariants: `OnePending`, `ResultSlotNeverFull` (the receive loop never
finds the one slot taken), `NoInstallAfterStop`, `StopIsEffective`,
`NoResultLost` (a caller woken by `DoneChan` still takes a result already
delivered), `LockOrderRespected` (nobody waits for `protocolMu` while
holding `stateMu`), TLC's deadlock check, and the liveness properties
`CallerAlwaysReleased` and `StopTerminates` under weak fairness.

| Config | What it is | Result |
| --- | --- | --- |
| `TxSubmissionServerLocks.cfg` | fixed server; 2 callers, 2 calls each, 1 restart, `Stop` | passes, 5,159 states, both liveness properties |
| `TxSubmissionServerLocksRestarts.cfg` | fixed server; 2 restarts, no `Stop` | passes, 4,061 states |
| `TxSubmissionServerLocksReadUnderStateBug.cfg` | gOuroboros at `7cd17437` | **fails** `LockOrderRespected` |
| `TxSubmissionServerLocksDeadlockBug.cfg` | gOuroboros at `7cd17437`, deadlock check only | **deadlocks** in 7 steps |
| `TxSubmissionServerLocksStopGuardBug.cfg` | mutation: `initProtocol` without the `stopped` check | **fails** `NoInstallAfterStop` |
| `TxSubmissionServerLocksDrainBug.cfg` | mutation: no nested select after `DoneChan` | **fails** `NoResultLost` |

**The defect.** `handleInit` and `handleDone` called `ProtocolInstance()`
(read lock on `protocolMu`) while holding `stateMu`, the reverse of the
order every other path uses. The deadlock trace: a caller takes
`protocolMu` for reading; the handler, running `MsgInit`, takes
`stateMu`; `Stop` starts waiting for `protocolMu`; the caller now waits
for `stateMu`, the handler's read lock waits behind `Stop`, and `Stop`
waits for the caller. `handleDone`'s copy of the inversion is not
reachable alone in the code (the caller it answers holds `requestMu`, so
no second caller holds the read lock), but it is the same order and was
fixed with it. Bound in gOuroboros by
`TestServerInitDoesNotInvertLockOrder`
(`protocol/txsubmission/server_lock_order_internal_test.go`), which
fails 10 of 10 before the fix and passes after.

**What holds.** The one-slot handoff is safe: one result per pending
request, cleared under `stateMu` before the send, and `DoneChan` closes
only after the receive loop returns, so the nested select always finds a
result that was delivered. `Stop` racing a restart installs nothing
after `stopped` is set.

The client lifecycle (`Start`/`Stop`/`Init`) is not in this model. Its
restart after `MsgDone` and concurrent `Start`/`Stop` are covered by Go
tests only (`TestClientRestartsAfterDone`,
`TestClientStartStopConcurrent` in `client_restart_test.go`).

## A pipelining inbound (`TxSubmissionPipelined.tla`)

`TxSubmission.tla` sends one request at a time because the gOuroboros Server
never pipelines. The reference inbound does: it sends further requests for
ids and bodies before earlier replies arrive, and computes each
acknowledgement and count from a view that lacks the replies in flight. The
outbound answers in order. This module puts that inbound (ouroboros-network
`4646039f05eb` `Inbound/V2/State.hs` 480-561 `pickRequestTxIdsAction`, and
dmq-node `a267003c` `SigSubmissionV2/Inbound.hs`, which uses it) against the
gOuroboros outbound, the tx-submission and DMQ Client, whose checks are the
reference outbound's. The pipelining depth is bounded the reference's way:
ids requested and not received (`MaxReq`, dmq-node 33) and body requests
outstanding (`MaxBatches`, 4). The inbound's back-off and peer scheduling are
left out; they only suppress requests, so the model's inbound is a superset.

The engine hands the Client a pipelined request only after it has sent the
reply to the one before (`protocol.go` `recvLoop`), which `Handle` models.

| Config | States | Result |
| --- | --- | --- |
| `TxSubmissionPipelined.cfg`: tx-submission, both windows equal (10, here 3), V1 | 12,506 | passes |
| `TxSubmissionPipelinedDmq.cfg`: DMQ V2, both windows dmq-node's 132 (here 4) | 49,865 | passes |
| `TxSubmissionPipelinedDmqV1.cfg`: DMQ V1, the same | 48,893 | passes |
| `TxSubmissionPipelinedGouroboros.cfg`: the gOuroboros Server as the inbound | 2,150 | passes, with `DoneOnlyWhenIdle` |
| `TxSubmissionPipelinedDmqWindowBug.cfg`: DMQ on `7cd17437`: inbound window 132 (4), Client 100 (3) | | **fails** `HonestNeverRefused` (`requestedTooMany`) |
| `TxSubmissionPipelinedAckAllBug.cfg`: mutation, the inbound acknowledges everything while pipelining | | fails `HonestNeverRefused` (`requestNonBlocking`) |
| `TxSubmissionPipelinedNoDeferBug.cfg`: mutation, the engine hands over a pipelined request early | | fails `HonestNeverRefused` (`alreadyPending`) |
| `TxSubmissionPipelinedDoneAnyTimeBug.cfg`: mutation, `MsgDone` with requests outstanding | | fails `DoneOnlyWhenIdle` |
| `TxSubmissionPipelinedProbesBug.cfg`: depth 3, a full outbound window, a body request behind an id request | | each probe violated (run one at a time) |

Tx-submission is consistent: both windows are 10 (`txSubmissionMaxUnacked`,
the inbound policy's `maxUnacknowledgedTxIds`). DMQ was not: dmq-node's
requester fills a window of 132 that is not negotiated, and the gOuroboros
Client defaulted to 100, so dmq-node's fourth 33-id request was refused
(DRIFT N68). The trace at the model's scale: a blocking request for 2, then
a non-blocking one for 2 more with 2 outstanding, over a window of 3.
`ViewIsPrefix`, `NothingBehindBlocking` and `AckedAtMostOnce` hold in every
passing config.

## A transaction re-announced, and the byte limits (`TxSubmissionReannounce.tla`)

The reference outbound announces the mempool entries after the last index
it sent (`Outbound.hs` 116-175, freshness by index). A transaction removed
and added back (a fork switch) gets a new index, so it is announced again,
possibly while its first announcement is still unacknowledged; both
reference inbounds keep the duplicate and acknowledge by count (`Inbound/V1.hs`
300-306, `Inbound/V2/State.hs` 370-374). One reply is read from one mempool
snapshot, so it never names a transaction twice.

| Config | States | Result |
| --- | --- | --- |
| `TxSubmissionReannounceBug.cfg`: `7cd17437`, a reference inbound, the Client's mempool re-adding | | **fails** `HonestNeverRefused` (`repeatsOutstanding`) |
| `TxSubmissionReannounce.cfg`: `reconcileTxIds` refusing only an id twice within one reply | 1,967 | passes, with `NoDuplicateWithinReply` and `ViewsAgree` |
| `TxSubmissionReannounceProbeBug.cfg`: the window holds a transaction twice | | probe violated: reachable |
| `TxSubmissionReannounceBytes.cfg`: the gOuroboros Server's byte limits at their formulas, scaled | 1,243 | passes |
| `TxSubmissionReannounceBytesTightBug.cfg`: mutation, a retained-byte limit below a full window | | fails `HonestNeverRefused` (`bytes`) |

So DRIFT N22 (an id twice within one reply, refused) stays harmless, but
`reconcileTxIds` also refused a reply naming an id still in the window,
which a reference outbound sends (DRIFT N70). The Client applies the check
to its own application's reply and failed the connection. The Server cannot
meet it: every Server request acknowledges its whole window.

### Sources for the two models above

| Ref | Where | What |
| --- | --- | --- |
| P1 | ouroboros-network `4646039f05eb` `ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/V2/State.hs` 480-561 | the inbound's acknowledgement and request counts while pipelining |
| P2 | dmq-node `a267003c14e9` `dmq-node/src/DMQ/SigSubmissionV2/Inbound.hs` 103-363 | blocking only at depth zero, `MsgDone` only from `serverIdle`, replies collected in order |
| P3 | dmq-node `a267003c14e9` `dmq-node/src/DMQ/Policy.hs` 83-102; `src/DMQ/NodeToNode.hs` 229, 305, 326 | window 132, 33 per request, 4 body batches; the same window for both outbounds |
| P4 | ouroboros-network `4646039f05eb` `.../TxSubmission/Outbound.hs` 116-175 | announcements by mempool index; one snapshot per reply |
| P5 | ouroboros-network `4646039f05eb` `.../TxSubmission/Inbound/V1.hs` 300-306; `.../Inbound/V2/State.hs` 370-374 | duplicate ids within the window are expected |
| P6 | ouroboros-network `4646039f05eb` `.../TxSubmission/Inbound/V2/Policy.hs` | `max_TX_SIZE` and the ingress limit with a 10% margin |

## Not modelled

Advertised-size discrepancy (the 32-byte tolerance) and the decoder's
per-body work, timeouts (no tx-submission state in gOuroboros is timed
except the non-blocking and body replies, as in the reference), and the
client's `Start`/`Stop`/`Init` state machine (Go tests only). Byte limits
are modelled only as `TxSubmissionReannounce.tla`'s scaled sums.

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
../../bin/tlc -config TxSubmissionV16ClampBlocking.cfg TxSubmission.tla
../../bin/tlc -config TxSubmissionTable.cfg TxSubmissionTable.tla | grep '^<<'
../../bin/tlc -config TxSubmissionServerLocks.cfg TxSubmissionServerLocks.tla
../../bin/tlc -config TxSubmissionServerLocksRestarts.cfg TxSubmissionServerLocks.tla
# expected to fail
for c in GouroborosBug EmptyReplyBug ServerBug ClientBug ClientBlockingBug \
         RogueClientBug V16Bug V16ClampBug V16ClampBlockingBug NoWindowBug \
         KeepsAckedBug ProbesBug ZeroClampProbeBug V16RefuseAckedBlockingBug; do
  ../../bin/tlc -config TxSubmission$c.cfg TxSubmission.tla || true
done
for c in ReadUnderStateBug DeadlockBug StopGuardBug DrainBug; do
  ../../bin/tlc -config TxSubmissionServerLocks$c.cfg TxSubmissionServerLocks.tla || true
done
# pipelining and re-announcement: every config, Bug ones expected to fail
for c in TxSubmissionPipelined*.cfg; do ../../bin/tlc -config $c TxSubmissionPipelined.tla || true; done
for c in TxSubmissionReannounce*.cfg; do ../../bin/tlc -config $c TxSubmissionReannounce.tla || true; done
```
