# Model 11: the DMQ message protocols

CIP-0137, the Decentralized Message Queue (DMQ), adds three mini-protocols
that carry signed messages (Mithril signatures, for a start) between nodes and
to local clients:

| Protocol | Number | gOuroboros package | Model |
| --- | --- | --- | --- |
| Message submission (node-to-node) | 11 | `protocol/messagesubmission` | `MessageSubmission.tla` |
| Local message submission (node-to-client) | 14 | `protocol/localmessagesubmission` | `LocalMessageSubmission.tla` |
| Local message notification (node-to-client) | 15 | `protocol/localmessagenotification` | `LocalMessageNotification.tla` |

Read [Model 04](../04-chainsync/README.md) first; the "does each answer reach
the call that asked" and "does Stop abandon a request" questions come from
there.

## Where the rules come from, and how much to trust them

None of the three is in the network specification pinned for the other
models (`docs/network-spec/*.tex` at ouroboros-network `5f356486ab3e`, which
is also the current `main`): it has no DMQ, message-submission or
local-message section. The sources, in order of authority:

1. **CIP-0137** (cardano-foundation/CIPs `03387471`, status *Proposed*). It
   gives states, agency, transition tables and CDDL for all three protocols
   and both message-submission versions. It is a proposal, not a ratified
   standard, and it disagrees with the reference implementation on the wire
   (below).
2. **dmq-node** (IntersectMBO/dmq-node `a267003c`, current `main`), the
   reference implementation, in Haskell, by the ouroboros-network team.
   Message submission V1 *is* tx-submission (`TxSubmission2` types, codec and
   `txSubmissionOutbound` from ouroboros-network 2.0.0.0, tag `4646039f`, the
   version dmq-node builds against); V2 is its own protocol based on
   ouroboros-network's `ObjectDiffusion`. Local message submission is
   `LocalTxSubmission`. Following the brief, where the CIP and the reference
   differ, the model follows the reference.
3. Where both are silent, the tx-submission rules of the pinned network
   specification apply, because DMQ V1 is tx-submission.

## Part 1: message submission (`MessageSubmission.tla`)

### What the code does

The inbound side wants messages; the outbound side has them. The inbound asks
for message ids, acknowledging old ones in the same request, then asks for
the bodies it wants. Both sides keep the same FIFO of ids announced but not
yet acknowledged: the window. In gOuroboros the **Client is the outbound**
side and the **Server is the inbound** side in both versions. Both check the
window rules with the same functions (`validateMessageIDRequest`,
`reconcileMessageIDs`, `requestedMessagesAreOutstanding` in `validation.go`):
the Server before it sends a request, the Client when it receives one.

V1 starts in `StInit` (the outbound sends `MsgInit`) and the outbound may end
the run with `MsgDone` instead of answering a blocking request. V2 has no
`StInit`, and the inbound ends the run with `MsgDone` from `StIdle`.

### The questions

1. **`WindowBound`**: does either window ever exceed `MaxUnacked`?
2. **`ViewsAgree`**: do the two sides always hold the same window?
3. **`BlockingRule`**: is a blocking request open only when it acknowledges
   the whole window, a non-blocking one only when it leaves ids?
4. **`NoRepeatServe`**: does the outbound ever serve the body of one id
   twice while the id is unacknowledged? The specification says "it is an
   error to ask for transaction identifiers that ... were already asked for",
   and dmq-node's V2 outbound refuses such a request
   (`ProtocolErrorDuplicateRequest`).
5. **`HonestNeverRefused`**: does the outbound ever refuse a gOuroboros
   Server that used only its public API?
6. Deadlock: a blocking request with no ids left to give is the only
   legitimate wait (`Quiet`).

The inbound is either the gOuroboros Server (`Rogue = FALSE`) or a peer that
may send any request (`Rogue = TRUE`), including bad acknowledgements, counts
over the window, wrong blocking flags, unannounced ids, and repeated ids.

### The answer

| Config | States | Result |
| --- | --- | --- |
| `MessageSubmissionV1.cfg`: V1, the gOuroboros Server, with the repeat fix | 159 | passes |
| `MessageSubmissionV2.cfg`: V2, the same | 137 | passes |
| `MessageSubmissionRogue.cfg`: V2, any request, with the repeat fix | 217 | passes |
| `MessageSubmissionRepeatBug.cfg`: any request, gOuroboros today | | **fails** `NoRepeatServe` |
| `MessageSubmissionServerRepeatBug.cfg`: the gOuroboros Server today, a refusing outbound | | **fails** `HonestNeverRefused` |

The window rules hold, on both sides, against any peer: each side's checks are
the reference's checks. The repeat rule does not: **the gOuroboros Client
serves the same body again** when a peer asks for an id it already asked for,
and **the gOuroboros Server's `RequestMessages` sends such a request** if its
application asks, which dmq-node's V2 outbound answers by closing the
connection. The trace for the first is three steps: a blocking request, a
reply with one id, then two `MsgRequestMessages` for that id.

### Checking the checks

| Config (expected to fail) | Safeguard removed from the outbound | Invariant broken |
| --- | --- | --- |
| `MessageSubmissionNoWindowBug.cfg` | the `MaxUnacked` check | `WindowBound` |
| `MessageSubmissionNoBlockRuleBug.cfg` | blocking iff nothing is left | `BlockingRule` |

Probes, each claiming something never happens; TLC finds each one:
`ProbeWindowNeverFull`, `ProbeNeverNonBlocking`, `ProbeNeverDone` (in V1 and
Rogue), and `ProbeNeverRefused` (Rogue only; with the gOuroboros Server and
the fix nothing is ever refused, which is `HonestNeverRefused` again).

## Part 2: local message submission (`LocalMessageSubmission.tla`)

### What the code does

The client submits one message; the node accepts or rejects it; `MsgDone`
from `StIdle` ends the run. gOuroboros' `SubmitMessage` only queues the
message (`Protocol.SendMessage`) and returns. The send loop sends queued
messages in order, each once the client has agency again, so concurrent
calls are serialised on the wire. Answers go to `AcceptMessageFunc(ctx)` or
`RejectMessageFunc(ctx, reason)`, which are given **no message and no id**.
In the reference, `SendMsgSubmitTx tx k` hands the answer to `k`, the
continuation of that submission.

### The questions

1. **`NoViolation`**: does a side ever receive a message its state forbids?
2. **`AnswerReachesAsker`**: does the answer the application pairs with a call
   answer that call's message? An application that pairs answers with calls
   can only do it by order; the model uses the order in which its
   `SubmitMessage` calls returned.
3. Does `Stop` abandon a submission? (Deadlock: `Quiet` needs every call
   answered.)

### The answer

| Config | States | Result |
| --- | --- | --- |
| `LocalMessageSubmissionSerialised.cfg`: two calls, one at a time, then `Stop` | 30 | passes |
| `LocalMessageSubmissionTagged.cfg`: two concurrent calls, answers tied to calls (the reference) | 141 | passes |
| `LocalMessageSubmissionConcurrentBug.cfg`: two concurrent calls, gOuroboros callbacks | | **fails** `AnswerReachesAsker` |
| `LocalMessageSubmissionNoAgencyBug.cfg` (mutation: the send loop ignores agency) | | **fails** `NoViolation` |

`Stop` never abandons a submission: `MsgDone` is queued behind the
submissions and goes out from `StIdle` after their answers. `Start` runs once
(`onceStart`), so there is no restart to break. The protocol itself is sound.

The failing case is the API. Call A queues its message, call B queues its
message, B returns, A returns. The application now waits for B then A; the
node answers A then B. A rejection for A is reported for B. Nothing in the
callback can tell them apart. The trace is six steps.

This is a design limitation, not a wire defect, and fixing it changes the
callback signatures, so it is written up rather than fixed: an application
must make one `SubmitMessage` at a time and wait for its answer before the
next.

## Part 3: local message notification (`LocalMessageNotification.tla`)

### What the code does

The client asks for new messages, blocking or not. A non-blocking request is
answered at once, possibly with nothing; a blocking one only when there is at
least one message, and its answer is never empty (CIP-0137 CDDL
`[2, [+ message]]`; dmq-node's codec fails on an empty one).

The gOuroboros server answers a blocking request inside its message handler
(`handleBlockingRequest`): it drains the queue under the lock; if that gave
nothing, it releases the lock and calls `WaitForMessage`, which waits on
`newMessageSignal`, a channel with **one** slot. `AddMessage` puts a signal in
the slot if it is empty. `WaitForMessage` is exported, so the application can
wait on the same channel. One signal wakes one waiter.

### The questions

1. **`WakeupNotLost`**: while the handler waits and messages are queued, is
   there always a signal coming for it? If not, the client's blocking request
   is not answered until some later `AddMessage`, however long that is.
2. **`NoEmptyBlocking`**: does the client ever accept an empty blocking reply?

### The answer

| Config | States | Result |
| --- | --- | --- |
| `LocalMessageNotification.cfg`: gOuroboros, only the handler waits | 117 | passes |
| `LocalMessageNotificationAppWaitBug.cfg`: the application also calls `WaitForMessage` | | **fails** `WakeupNotLost` |
| `LocalMessageNotificationBroadcast.cfg`: the same, `AddMessage` wakes every waiter (the fix) | 221 | passes |
| `LocalMessageNotificationEmptyBlockingBug.cfg`: a server answers a blocking request with nothing; gOuroboros client | | **fails** `NoEmptyBlocking` |
| `LocalMessageNotificationRogue.cfg`: the same, the client refuses it (the fix) | 89 | passes |
| `LocalMessageNotificationUnbufferedBug.cfg` (mutation: the channel has no slot) | | **fails** `WakeupNotLost` |

With only the handler waiting, the one-slot channel is enough: a message
added between the drain and the wait leaves its signal in the slot (the
unbuffered mutation shows the slot is what makes that work). With a second
waiter, the signal goes to one of them. If the application gets it, the
blocking request stays unanswered with the message sitting in the queue.

This is the notification form of "an answer reaches a call other than the
one that asked". The reference has no such channel: its server blocks in STM
on the mempool, and an STM retry wakes on every change it read.

### The modelling mistake

The first version of the handler went from "found nothing" straight to
"waiting" in one step, so `AddMessage` could never land in between. The
unbuffered mutation then passed, which meant the model could not see the gap
the slot exists for. Splitting out the `unlocked` step exposed it. The same
split then failed the first broadcast design: a waiter that takes the
broadcast channel *after* releasing the lock misses an add in the gap. The
fix that passes takes the channel under the lock, which the Go fix does.

## Go tests and fixes

All on gOuroboros `61046085`, local branches only.

### State-table tests (one branch per protocol)

Each adds `statemap_model_test.go`, modelled on keep-alive's: the model's
agency and transitions, and every role x state x message cell derived from
`StateMap` the way `protocol.Protocol` judges an arriving message, plus a test
that `Done` is entered only by `MsgDone` from the modelled state and never
left. Cells the reference would leave waiting (a message sent while the
receiver holds agency) are refused on arrival by gOuroboros, as for every
protocol (see Model 01).

| Branch | Cells | Mutation in the state map | Fails |
| --- | --- | --- | --- |
| `test/messagesubmission-state-model` | 154 (V1 84, V2 70) | V2 allows `MsgDone` from `StMessageIdsBlocking`; the V1 blocking match inverted; V2 `StIdle` agency flipped | each fails `TestStateMapMatchesModel` (the first also `TestDoneIsEnteredOnlyAsModelled`) |
| `test/localmessagesubmission-state-model` | 24 | `MsgDone` from `StBusy`; `MsgRejectMessage` stays in `StBusy` | each fails |
| `test/localmessagenotification-state-model` | 40 | the blocking match inverted; a non-blocking reply accepted in `StBusyBlocking` | each fails |

Existing tests already pin the window rules of message submission
(`TestMessageIDRequestCountRules`, `TestReconcileMessageIDs*`,
`TestRequestedMessagesMustBeOutstandingAndUnique`, the direction-flow tests)
and the request/reply correlation and enqueue-failure rollback
(`TestClientEnqueueFailureDoesNotOverwriteNewerRequest`); the state-table
tests do not repeat them.

### Fixes

| Branch | Defect | Test, and proof it fails without the fix |
| --- | --- | --- |
| `fix/messagesubmission-repeat-request` | The Client serves a body again for an id already asked for; the Server's `RequestMessages` sends such a request | `TestClientRefusesRepeatedMessageRequest` (V1 and V2) and `TestServerRefusesToRepeatMessageRequest` fail on `main`. Guards: `TestServerMayRequestReannouncedID` fails if acknowledgement does not release the record; `TestServerUnsentRequestReleasesItsIDs` fails if the record is updated in place |
| `fix/localmessagenotification-empty-blocking-reply` | The client accepts an empty blocking reply | `TestClientRefusesEmptyBlockingReply` fails on `main`. `TestClientPreservesGenuineEmptyReplyCallback` asserted the old behaviour for the blocking case; it now covers only the non-blocking case |
| `fix/localmessagenotification-lost-wakeup` | An application `WaitForMessage` takes the wakeup meant for a blocking request | `TestAddMessageWakesBlockingRequestAndWaiter` (deterministic, `synctest`) fails 6 runs of 6 on `main`, either way round |

The repeat fix records the ids asked for, per side, until they are
acknowledged. dmq-node enforces it only in V2; the fix applies it to V1 as
well, because the tx-submission specification forbids the repeat in both
(V1's reference outbound tolerates it).

## Spec, reference, and gOuroboros

| Question | CIP-0137 | Reference (dmq-node) | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| V1 wire tags | `MsgInit` 0, request ids 1, reply ids 2, request 3, reply 4, done 5 [C2] | tx-submission's: request ids 0, reply ids 1, request 2, reply 3, done 4, `MsgInit` 6 [R4] | the CIP's | **incompatible with dmq-node V1**; a large change, written up |
| V2 wire tags | request ids 1, reply ids 2, request 3, reply 4, done 5 [C1] | request ids 1, reply ids 2, **`MsgReplyNoSigIds` 3**, request 4, reply 5, done 6 [R5] | the CIP's | **incompatible with dmq-node V2**; written up |
| V2: who starts it? | the inbound has agency in `StIdle`; `StInit` existed so the outbound could start on the initiator, and V2 "reverses the agency model" [C1] | the **initiator runs the inbound**, the responder the outbound [R6] | the Client (initiator) is the outbound in V2 too | **incompatible**: both sides wait in `StIdle`; written up |
| V2 blocking request with nothing to give | must wait | answers `MsgReplyNoSigIds` after 17 s [R1][R2] | no such message; waits | deviation, part of the tag rework |
| Window rules (ack, `MaxUnacked`, blocking iff empty, request 0) | "one cannot request 0 ids" either way [C3] | non-blocking may request 0 if it acknowledges [R2][R3]; same as tx-submission [S2] | as the reference | agree with the reference |
| A body asked for twice | silent | V2 refuses; V1 tolerates [R2][R3]; the type says "at most once" [R1] | served twice | **defect**, fixed |
| Empty `MsgRequestMessages` | silent | accepted [R2][R3] (the spec says "non-empty" [S3]) | accepted | agree with the reference |
| Message-submission time limits | none | V2: `StIdle` none, blocking 20 s, non-blocking and bodies 10 s [R5]; V1: blocking none, non-blocking and bodies 10 s [R7] | `StIdle` 300 s, blocking 30 s, non-blocking none, bodies 30 s | deviation; not a safety question, written up |
| Local submission answers | one per submission [C4] | handed to the submission's continuation | callbacks with no message | design limitation, written up |
| Local submission time limits | none | none: the server runs without limits [R8] | server times out a client idle 300 s in `StIdle`; client waits 30 s in `StBusy` | deviation: a local client quiet for five minutes is disconnected; written up |
| Empty blocking notification reply | forbidden: `[+ message]` [C5] | the codec refuses it [R9] | accepted | **defect**, fixed |
| Notification `hasMore` | in the non-blocking reply | per reply, from a `maxMsgs` cap [R10] | always `false`; the server sends its whole queue | deviation, harmless at the default sizes |
| Blocking vs non-blocking notification request | "blocking only after the server said it has no more" (`Type.hs`) | the server's check is commented out [R10] | not checked | agree with the reference |
| Server restart after `MsgDone` | silent | responders are restarted by the inbound governor | none of the three servers restarts | not modelled; as for other protocols |

## Sources

Pinned commits: CIP-0137 at cardano-foundation/CIPs `03387471`;
IntersectMBO/dmq-node `a267003c`; IntersectMBO/ouroboros-network `5f356486ab3e`
(specification) and `4646039f` (ouroboros-network 2.0.0.0, used by dmq-node);
gOuroboros `61046085`.

| Ref | Where | What it says |
| --- | --- | --- |
| C1 | [`CIP-0137/README.md` lines 75-185](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0137/README.md#L75-L185) | V2: differences from V1, states, agency, transitions, CDDL tags 1-5 |
| C2 | [lines 187-290](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0137/README.md#L187-L290) | V1: `StInit`, `MsgDone` from `StMessageIdsBlocking`, CDDL tags 0-5 |
| C3 | [lines 313-328](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0137/README.md#L313-L328) | blocking iff the window is empty; never request 0 ids |
| C4 | [lines 552-650](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0137/README.md#L552-L650) | local message submission |
| C5 | [lines 652-750](https://github.com/cardano-foundation/CIPs/blob/03387471681166e746518d58a33e25f2ccea3d29/CIP-0137/README.md#L652-L750) | local message notification; blocking reply `[2, [+ message]]` |
| S1 | [`docs/network-spec/miniprotocols.tex` lines 27-36](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36) | an unexpected message aborts the connection |
| S2 | [lines 1326-1377](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1326-L1377) | tx-submission id requests: ack, req, window, blocking rules |
| S3 | [lines 1386-1400](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1386-L1400) | bodies only for outstanding ids not "already asked for" |
| R1 | [`dmq-node/src/DMQ/Protocol/SigSubmissionV2/Type.hs` lines 147-280](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/SigSubmissionV2/Type.hs#L147-L280) | V2 messages, rules, "at most once", `MsgReplyNoSigIds`, agency |
| R2 | [`dmq-node/src/DMQ/SigSubmissionV2/Outbound.hs` lines 85-233](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/SigSubmissionV2/Outbound.hs#L85-L233) | V2 outbound checks; 17 s blocking timeout; `ProtocolErrorDuplicateRequest` |
| R3 | [`ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs` lines 100-220](https://github.com/IntersectMBO/ouroboros-network/blob/4646039f05eb809bd5252af17121644ec1dc0c2c/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs#L100-L220) | V1 outbound checks; no repeat check |
| R4 | [`TxSubmission2/Codec.hs` lines 310-362](https://github.com/IntersectMBO/ouroboros-network/blob/4646039f05eb809bd5252af17121644ec1dc0c2c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Codec.hs#L310-L362) | V1 tags; dmq-node's V1 codec wraps it (`DMQ/Protocol/SigSubmission/Codec.hs` 145-152) |
| R5 | [`dmq-node/src/DMQ/Protocol/SigSubmissionV2/Codec.hs` lines 81-95, 136-180](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/SigSubmissionV2/Codec.hs#L81-L180); `dmq-node/cddl/specs/sig-submission-v2.cddl` | V2 time limits and tags 1-6 |
| R6 | [`dmq-node/src/DMQ/NodeToNode.hs` lines 242-352, 536-600](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/NodeToNode.hs#L242-L352) | V2 initiator runs the inbound, responder the outbound; V1 the reverse; version selection |
| R7 | [`dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs` lines 68-78](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs#L68-L78) | V1 time limits |
| R8 | [`dmq-node/src/DMQ/NodeToClient.hs` lines 155-185](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/NodeToClient.hs#L155-L185); `DMQ/Protocol/LocalMsgSubmission/Type.hs` 20-22 | local servers run with `runAnnotatedPeer`, no limits; local submission is `LocalTxSubmission` |
| R9 | [`dmq-node/src/DMQ/Protocol/LocalMsgNotification/Codec.hs` lines 119-166](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/LocalMsgNotification/Codec.hs#L119-L166); `Type.hs` 45-77 | notification tags; an empty blocking reply fails to decode |
| R10 | [`dmq-node/src/DMQ/NodeToClient/LocalMsgNotification.hs` lines 45-95](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/NodeToClient/LocalMsgNotification.hs#L45-L95) | the notification server: STM wait, `maxMsgs`, `hasMore`, the blocking-rule check commented out |
| G1 | gOuroboros `protocol/messagesubmission/` | `messagesubmission.go` (state maps, timeouts), `validation.go`, `client.go`, `server.go`, `messages.go` (tags) |
| G2 | gOuroboros `protocol/localmessagesubmission/` | `localmessagesubmission.go` (state map, 300 s / 30 s), `client.go`, `server.go` |
| G3 | gOuroboros `protocol/localmessagenotification/` | `server.go` (`AddMessage`, `WaitForMessage`, `handleBlockingRequest`), `client.go` |
| G4 | gOuroboros `protocol/protocol.go` | `enqueueMessage`; role to muxer direction in `ensureRegistered`; timeouts only while the peer has agency |

## Not modelled

Message bodies, sizes, authentication, TTLs and the replay caches; the
pipelined inbound of dmq-node V2 (`runPipelinedAnnotatedPeerWithLimits`);
time limits; the role and tag incompatibilities above, which are not state
questions; restarting a server after `MsgDone`.

## Running it

```sh
cd specs/11-dmq
# passing configs
../../bin/tlc -config MessageSubmissionV1.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionV2.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionRogue.cfg MessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionSerialised.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionTagged.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageNotification.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationBroadcast.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationRogue.cfg LocalMessageNotification.tla
# expected to fail
../../bin/tlc -config MessageSubmissionRepeatBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionServerRepeatBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionNoWindowBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionNoBlockRuleBug.cfg MessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionConcurrentBug.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionNoAgencyBug.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageNotificationAppWaitBug.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationEmptyBlockingBug.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationUnbufferedBug.cfg LocalMessageNotification.tla
```

To run a probe, copy a passing config and replace its `INVARIANT` lines with
the probe's name.
