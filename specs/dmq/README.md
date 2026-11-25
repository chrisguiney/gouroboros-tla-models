# the DMQ message protocols

CIP-0137, the Decentralized Message Queue (DMQ), adds three mini-protocols
that carry signed messages (Mithril signatures, for a start) between nodes and
to local clients:

| Protocol | Number | gOuroboros package | Model |
| --- | --- | --- | --- |
| Message submission (node-to-node) | 11 | `protocol/messagesubmission` | `MessageSubmission.tla` |
| Local message submission (node-to-client) | 14 | `protocol/localmessagesubmission` | `LocalMessageSubmission.tla` |
| Local message notification (node-to-client) | 15 | `protocol/localmessagenotification` | `LocalMessageNotification.tla` |
| All three, after `MsgDone` | | the three `server.go` files | `DmqRestart.tla` |
| Message validity (all three) | | `protocol/common/authentication.go` | `MessageValidity.tla` |
| Receiving messages (node-to-node) | 11 | `protocol/messagesubmission/server.go`, `authentication.go` | `MessageIngress.tla` |

Read [Model `chainsync`](../chainsync/README.md) first; the "does each answer reach
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

Which side is the connection's initiator depends on the version. In dmq-node
the initiator runs the V1 outbound and the V2 inbound [R6]. Before the wire
fix, gOuroboros put its Client (the outbound) on the initiator in both
versions, so in V2 against dmq-node both ends ran the outbound and each
waited in `StIdle` for the other. In V2 the outbound may also answer a
blocking request with `MsgReplyNoSigIds`, which applies the acknowledgement
and announces nothing; dmq-node's outbound sends it after 17 s, and its
inbound gives up on a blocking request after 20 s [R5]. gOuroboros had no
such message before the fix, so a gOuroboros Client with nothing new could
not keep a dmq-node requester's connection open.

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
6. Deadlock: in V1 a blocking request with no ids left to give is the only
   legitimate wait (`Quiet`). In V2 it is not, because the requester gives up
   after 20 s; nor is an `StIdle` that no side may leave.

The inbound is either the gOuroboros Server (`Rogue = FALSE`) or a peer that
may send any request (`Rogue = TRUE`), including bad acknowledgements, counts
over the window, wrong blocking flags, unannounced ids, and repeated ids.
`RolesMatch` says whether the two ends agree which of them runs the inbound
in V2, and `NoIdsReply` whether the V2 outbound can send `MsgReplyNoSigIds`;
both are `TRUE` after the wire fix.

### The answer

| Config | States | Result |
| --- | --- | --- |
| `MessageSubmissionV1.cfg`: V1, the gOuroboros Server, with the repeat and wire fixes | 159 | passes |
| `MessageSubmissionV2.cfg`: V2, the same | 157 | passes |
| `MessageSubmissionRogue.cfg`: V2, any request, with the repeat and wire fixes | 245 | passes |
| `MessageSubmissionV2RolesBug.cfg`: V2, gOuroboros before the wire fix against dmq-node: both ends run the outbound | | **fails**: deadlock in the initial `StIdle` |
| `MessageSubmissionV2NoIdsReplyBug.cfg`: V2, a gOuroboros Client before the wire fix: no `MsgReplyNoSigIds` | | **fails**: deadlock, a blocking request with nothing left to give |
| `MessageSubmissionRepeatBug.cfg`: any request, gOuroboros today | | **fails** `NoRepeatServe` |
| `MessageSubmissionServerRepeatBug.cfg`: the gOuroboros Server today, a refusing outbound | | **fails** `HonestNeverRefused` |
| `MessageSubmissionV1Restart.cfg`: V1, two runs, the Server restarting after `MsgDone` and forgetting the ids it asked for | 318 | passes, with `AskedInWindow` |
| `MessageSubmissionV1RestartAskedBug.cfg`: the same, the restart keeping them | | **fails** `AskedInWindow` |

The window rules hold, on both sides, against any peer: each side's checks are
the reference's checks. The repeat rule does not: **the gOuroboros Client
serves the same body again** when a peer asks for an id it already asked for,
and **the gOuroboros Server's `RequestMessages` sends such a request** if its
application asks, which dmq-node's V2 outbound answers by closing the
connection. The trace for the first is three steps: a blocking request, a
reply with one id, then two `MsgRequestMessages` for that id.

### The repeat check across a restart (#3130 after merging main)

Main's #3197 restarts the Server after a V1 client's `MsgDone`, dropping the
run's outstanding IDs and requests. #3130's repeat check keeps a record of
the IDs the Server asked bodies for (`requestedIDs`), which a reply to the
next ID request releases with its acknowledgement. `MsgDone` is the answer to
a blocking request, so that acknowledgement is never applied, and the merged
code kept the record across the restart: a client announcing the same ID in
the next run could never have its body asked for. `Restart` (V1 only, as V2's
`MsgDone` comes from the Server) and `AskedInWindow` (the Server has asked only
for ids in its current window) show it; the fix, #3130 `50ef28f8` on merge
`867599d8`, resets the record with the window, and
`TestServerRestartForgetsRequestedIDs` fails without it. Every earlier config
runs one run (`MaxRuns = 1`) and is unchanged.

`4f710823` (test only, cannot affect the model): with the restart,
`TestV1InboundMatchesReferenceOutbound` polled the Server's current
instance for `IsDone` after `MsgDone`, which the restart replaces with a
fresh one (81 of 200 failures on 386); it now watches the run's own
instance, and its harness stops the Server with `Server.Stop`.

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
| `LocalMessageSubmissionOwnAnswer.cfg`: two concurrent calls, `SubmitMessage` returns its own answer under the submit lock (the fix) | 43 | passes |
| `LocalMessageSubmissionOwnAnswerNoLockBug.cfg` (mutation: own answer, no submit lock) | | **fails** `AnswerReachesAsker` |
| `LocalMessageSubmissionOwnAnswerProbeDoneBug.cfg` (probe: `ProbeNeverDone` with the fix) | | **fails** (Stop completes) |

`Stop` never abandons a submission: `MsgDone` is queued behind the
submissions and goes out from `StIdle` after their answers. `Start` runs once
(`onceStart`), so there is no restart to break. The protocol itself is sound.

The failing case is the API. Call A queues its message, call B queues its
message, B returns, A returns. The application now waits for B then A; the
node answers A then B. A rejection for A is reported for B. Nothing in the
callback can tell them apart. The trace is six steps.

This is a design limitation, not a wire defect. The fix follows the
reference, where `SendMsgSubmitTx tx k` hands the answer to that
submission's continuation (`protocols/lib/.../LocalTxSubmission/Client.hs` 46-56 at
ouroboros-network `5f356486ab3e`): `SubmitMessage` takes the client's submit
lock, registers as the waiter, queues its message, and returns its own
answer (nil, or the rejection) once it arrives (`OwnAnswer`). The lock is
what keeps registration order equal to queue order; without it
(`OwnAnswerNoLockBug`) two calls can register in one order and queue in the
other. `ConcurrentBug` is gOuroboros `origin/main` `5c4f31c1`. Go side:
`fix/localmessagesubmission-own-answer`.

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
| `LocalMessageNotificationRestart.cfg` / `...RestartWaitBug.cfg`: see Part 4 | | |

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

## Part 4: the servers after `MsgDone` (`DmqRestart.tla`)

### What the code does

When the client ends a run (`MsgDone`; `MsgClientDone` in local message
notification), the connection stays open and the client may start the same
protocol again. The specification says the server side "should be restarted
in its initial state in case the client wishes to use the protocol again
later" [S5], and the reference does: dmq-node runs
`Ouroboros.Network.Diffusion.run` [R12], whose inbound governor runs a
responder that ended cleanly again (`TrResponderRestarted`) [R11], for the
node-to-node and the node-to-client servers alike. In V1 message submission
the responder is the inbound side, which receives `MsgDone` [R6].

On gOuroboros `main` (`d8f5bc2a`) none of the three servers restarts. Local
message submission and message submission only log `MsgDone` and stay in
`StDone`; local message notification also shuts its queue and expiry cleaner
down. The new run's first message is then refused or never read.

One module covers all three. `Proto` picks the protocol's state table
([C2][C4][C5], the same as the gOuroboros state maps); both peers send any
message their table allows while they hold agency, and read the other's in
order. `ServerRestarts` lets the server read in `StDone` as the first state of
a new run. `MaxRuns = 2`; `MaxMsgs` bounds the messages.

### The questions

- **NewRunServed**: a message waiting for the server can be read
  (`inbox nonempty => ENABLED Recv("Server")`).
- **NoViolation**: no side receives a message its state forbids.

### The answer

| Config | States | Result |
| --- | --- | --- |
| `DmqRestartLocalSubmission.cfg`: reference, two runs | 56 | passes |
| `DmqRestartLocalNotification.cfg` | 73 | passes |
| `DmqRestartSubmissionV1.cfg` | 68 | passes |
| `DmqRestart*NoRestartBug.cfg` (three): gOuroboros `main` | 38-52 | **fails** `NewRunServed` |
| `DmqRestart*ProbeNoSecondRunBug.cfg` (three): probe, a second run starts | 28-45 | violated, as expected |

The deviation is real for all three. The fixes are below.

### Restart and an application wait (review of PR #3197)

The restart fix's first draft (PR #3197 `656bbcea`) closed the ended run's
protocol instance, as the restart must, but `WaitForMessage` selected on that
instance's stop channel. So an application waiting in `WaitForMessage` got
`ErrProtocolShuttingDown` on every `MsgClientDone`, although the server
restarts and keeps the queue it waits on. In dmq-node nothing like that
happens: `MsgClientDone` runs only the run's `mdone`
(`DMQ/NodeToClient/LocalMsgNotification.hs` 93-94), and the mempool a reader
waits on belongs to the node.

`DmqRestart.tla` has no application, and `LocalMessageNotification.tla` had
no restart, so neither could see it. `LocalMessageNotification.tla` now has
`ServerRestarts` (MsgClientDone returns to StIdle for a new run) and
`RestartReleasesWaiters` (the first draft), and the invariant
`AppWaitOutlivesRun`:

| Config | States | Result |
| --- | --- | --- |
| `LocalMessageNotificationRestartWaitBug.cfg`: restart, first draft | | **fails** `AppWaitOutlivesRun` in three states (wait, then MsgClientDone) |
| `LocalMessageNotificationRestart.cfg`: restart, the fix, broadcast wakeup | 179 | passes `WakeupNotLost`, `NoEmptyBlocking`, `AppWaitOutlivesRun` |

The fix (`c107bb53`): `WaitForMessage` watches only the server's `Stop` and
the connection; the blocking request handler still watches its own run's
stop channel, since it belongs to that run (and the client cannot send
`MsgClientDone` while that request holds agency). Go:
`TestWaitForMessageOutlivesRestart` (fails 4 runs of 5 before the fix,
"MsgClientDone ended a WaitForMessage"; the other run starts waiting after
the restart). The other five restarting servers have no exported wait; the
Peras await is per request and answers on its own run's instance, which is
right.

## Part 5: when a message is valid (`MessageValidity.tla`)

### What the code does

Every DMQ protocol hands a message to `protocol/common` before using it:
`TTLValidator.ValidateMessageTTLAt` checks its expiry, and
`MessageAuthenticator` (`VerifyMessage`, or `PrepareMessages` and its commit
function) checks the body, the message id, the issuing pool's stake, the
operational certificate (opcert), the KES signature, and that the pool's
opcert counter has not gone backwards. The authenticator remembers the highest
counter seen per pool. `PrepareMessages` checks a batch against a private copy
of those counters and returns a commit function, which re-checks against the
counters recorded meanwhile and then records the batch's.

The reference is dmq-node's `validateSig` (`Validate.hs`), run in one STM
transaction per batch: each message is checked against the counters the
earlier ones recorded, and a refused message records nothing. The body size
is checked earlier, when the message is decoded (`Codec.hs` `decodeBody`).

Three of the checks depend on state that changes over time, so the model keeps
it: the clock (in half-second ticks, because the reference's clock has
sub-second precision while expiry times are whole seconds), the node's current
KES period, and the counters. A message is a record of pool, counter, opcert
start, claimed KES period, the evolution its signature was really made at,
expiry and body size. Two workers may each hold a prepared batch and commit in
either order.

### The questions

- `NoAcceptBeyondReference`: gOuroboros never accepts what the reference would
  refuse at the same moment with the same counters.
- `AcceptAsReference`: gOuroboros accepts what the reference accepts, unless
  one of its own stricter checks (`GoExtras`) refuses it.
- `SeenMonotone` (action property): a pool's counter never goes down.
- `RejectKeepsSeen` (action property): a refused batch records nothing.

### The answer

`main` fails four ways, each a `*Bug.cfg` that sets `Mutation` to the current
behaviour:

| Config | What `main` does | The reference |
| --- | --- | --- |
| `MessageValidityKesAtCurrentBug.cfg` | verifies the KES signature at the evolution of the node's **current** period | at the **claimed** period minus the opcert start (`Validate.hs` 207-212); the current slot is not used |
| `MessageValidityLaxUpperBug.cfg` | accepts `expiresAt = now + maxTTL` | refuses it: `expiresAt < now + 1800` (122) |
| `MessageValidityTruncateNowBug.cfg` | truncates now to whole seconds, so half a second past expiry is accepted | `posixNow <= expiresAt` at full precision (118) |
| `MessageValidityNoBodySizeBug.cfg` | no body-size check | 90 to 2000 bytes (`Codec.hs` 193-202; CIP-0137 line 155) |
| `MessageValidityBatchFinalOnlyRecheckBug.cfg` | commit re-checks only the batch's **last** counter per pool, so a batch `[p:1, p:2]` commits after `p:2` was recorded meanwhile, accepting the stale `p:1` | each message against the counters at validation (183-197) |

The KES finding has two halves: a message signed late in one period is refused
once the period turns (about 30 minutes in every 36 hours, given the 1800 s
expiry bound), and a message signed at the current period but claiming an
earlier one is accepted, which dmq-node refuses as `InvalidKESSignature` and
disconnects the peer that sent it.

`MessageValidityExtrasBug.cfg` is main's two checks dmq-node does not make:
the counter must not be below the one in the node's chain state
(`PoolOpCertIssueNumber`; dmq-node compares only with counters seen in
messages), and the opcert's window must contain the node's own current KES
period (dmq-node never looks at the slot). Both refuse messages dmq-node
accepts and relays, and CIP-0137 requires neither (its required steps,
README lines 397-402, name no such check; the note at 405-411 offers the
chain as one possible counter source). The fixes drop both.

With the fixes (`Mutation = "none"`) `MessageValidity.cfg` (89,295 states)
and `MessageValidityBatch.cfg` (86,457 states) pass every question.
`MessageValidityNoCounterCheckBug`, `BatchNoCommitRecheckBug`,
`BatchCommitOverwritesBug` and `BatchRecordOnRejectBug` are mutations showing
each question can fail. Probes: `ProbeCrossPeriodBug` (after the fix a
message signed in an earlier period is accepted after the period moves on),
`BatchProbeAcceptBug` (batches commit).

## Part 6: what a node does with received messages (`MessageIngress.tla`)

### What the code does

The node-to-node inbound side (gOuroboros's `messagesubmission.Server`)
receives a reply to its body request and validates the messages in it. In
dmq-node the reply goes to the mempool writer (ouroboros-network
`Mempool/Simple.hs` 183-245): it reads the clock once, drops messages already
in the mempool as duplicates without validating them, validates the rest one
at a time with `validateSig`, adds the valid ones, and only then handles the
invalid ones (`app/Main.hs` 199-221): `SigExpired`, `PoolNotEligible`,
`UnrecognizedPool`, `NotInitialized` and `SigDuplicate` are traced; any other
error is thrown and closes the connection. `validateSig` also refuses, as
`SigTooFrequent`, a message less than `vcMinSigDelay` (60 s) after the last
one it accepted from the same pool, checked right after expiry; the time is
recorded only when a message is accepted.

gOuroboros also re-verifies messages it already accepted (relaying with
`AddMessage`, a local notification replay) and runs local submissions from
several connections at once through `PrepareMessages` and its commit.

The model keeps the clock, the set of accepted ids (dmq-node's mempool), the
pool's last-accepted time and the history of acceptances. Each message
carries a fixed set of failures; its outcome is the first failure in the
check order, with "too frequent" computed from the state. A reply's outcome
under gOuroboros and under the reference are computed from the same state
and compared.

### The questions

- `OutcomeAsReference`: a reply ends as the reference's would: the same
  messages accepted, the same last-accepted time, and a disconnect exactly
  when the reference disconnects.
- `ReverifyAccepted`: re-verifying an accepted message never fails.
- `DelayHeld`: no two acceptances are closer than the delay.
- `DuplicateNotFatal`: a local submission that lost a race to the same
  message is not refused.

### The answer

`main` and the first body-size fix fail four ways:

| Config | What `main` does | The reference |
| --- | --- | --- |
| `MessageIngressAllOrNothingBug.cfg` | any failing message, even an expired one or one from a pool without stake, refuses the whole reply and closes the connection | judges each message; drops expired and unregistered ones quietly; keeps the valid ones even when another is fatal |
| `MessageIngressMainOrderBug.cfg` | checks the pool before the KES window and the signatures before the counter, so a message failing both is dropped where the reference disconnects | `Validate.hs` order: expiry, rate, id, window, pool, counter, signatures |
| `MessageIngressNoRateLimitBug.cfg` | no rate limit | `SigTooFrequent`, fatal for node-to-node |
| `MessageIngressSizeAfterExpiryBug.cfg` | (the first body-size fix) checks the body in the authenticator, after expiry, so an expired message with a bad body is dropped | the decoder refuses the body first (`Codec.hs` 193-202): the whole reply fails and the connection closes |

With the fixes `MessageIngress.cfg` (148,820 states) passes every question.
Mutations: `RateOnDuplicateBug` (the limit applied to an accepted message, so
relaying it fails), `NoRateRecheckBug` (commit without re-checking the limit
accepts two concurrent submissions), `DupRaceFatalBug` (a submission that lost
a race to the same message is refused). Probes: `ProbeKeepValidBug` (a reply
both accepts a message and disconnects, as in the reference),
`ProbeTooFrequentBug` (a message with no other failure is refused as too
frequent).

## Go tests and fixes

All on gOuroboros `61046085`, local branches only.

### State-table tests (one branch per protocol)

Each adds `statemap_model_test.go`, modelled on keep-alive's: the model's
agency and transitions, and every role x state x message cell derived from
`StateMap` the way `protocol.Protocol` judges an arriving message, plus a test
that `Done` is entered only by `MsgDone` from the modelled state and never
left. Cells the reference would leave waiting (a message sent while the
receiver holds agency) are refused on arrival by gOuroboros, as for every
protocol (see Model `keepalive`).

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
| `fix/messagesubmission-reference-wire` | V1 used the CIP's tags, not tx-submission's; V2 lacked `MsgReplyNoSigIds` and used the CIP's tags; V2 put the outbound on the initiator; collections were definite-length lists, which the reference decoders refuse | `TestV1OutboundMatchesReferenceInbound`, `TestV1InboundMatchesReferenceOutbound`, `TestV2InboundIsInitiatorAndMatchesReferenceOutbound`, `TestV2OutboundIsResponderAndMatchesReferenceInbound` play dmq-node's side byte for byte and fail on `main` (wrong tag, no reply, wrong side, no request reaching the Client). `TestV2OutboundAnswersBlockingRequestWithNoIds`, `TestReplyNoMessageIdsRefusals` and `TestConnectionRolesFollowReference` cover the new method and the role mapping |
| `fix/localmessagesubmission-server-restart` (from `d8f5bc2a`) | The server stays in `StDone` after `MsgDone` | `TestServerAnswersSubmitSentDuringRestart` and `TestServerAnswersBackToBackRestarts` time out on `main` ("no reply from restarted server"). The server is added to the connection's restarting servers and to `TestServerStopDuringRestartStopsServer` |
| `fix/localmessagenotification-server-restart` (from `d8f5bc2a`) | `MsgClientDone` shuts the server down for good | `TestServerAnswersRequestSentDuringRestart` and `TestServerAnswersBackToBackRestarts` time out on `main`. The queue, acknowledged ids and expiry cleaner now outlast a run (the cleaner no longer watches the run's channels) and only `Stop` ends them; `TestServerStopDuringRestartStopsServer` covers Stop during a restart |
| `fix/messagesubmission-server-restart` (from `d8f5bc2a`) | The server stays in `StDone` after the client's `MsgDone`, with the run's request still recorded | `TestServerRequestsAfterRestart` and `TestServerHandlesInitSentDuringRestart` fail on `main` ("the server never accepted a request for the next run"). The run's outstanding ids and requests are dropped once the new instance has started; the queue and delivered ids are kept. V1 only: in V2 `MsgDone` comes from the server |
| `fix/localmessagenotification-lost-wakeup` | An application `WaitForMessage` takes the wakeup meant for a blocking request | `TestAddMessageWakesBlockingRequestAndWaiter` (deterministic, `synctest`) fails 6 runs of 6 on `main`, either way round |

The repeat fix records the ids asked for, per side, until they are
acknowledged. dmq-node enforces it only in V2; the fix applies it to V1 as
well, because the tx-submission specification forbids the repeat in both
(V1's reference outbound tolerates it).

### Message validity and receipt

Branches from gOuroboros `62fa36d1` (the first five) or `ebc63eab` (the rest).

| Branch | Commits | What it shows |
| --- | --- | --- |
| `fix/dmq-kes-claimed-period` | `7e1a0820`, `db6103a6` | `TestVerifyMessageKESPeriodAsReference` (11 cells). On `main` 3 fail (cross-period both ways; a signature at the current period claiming an earlier one is accepted). The second commit drops the opcert window at the current slot: its two cells failed before it. `CurrentSlot`, `SlotsPerKESPeriod` and `VerifyMessageWithSlot`'s slot become unused (deprecated) |
| `fix/dmq-ttl-reference-bounds` | `1f492baf`, `5d48a376` | `TestValidateMessageTTLAtAsReference` (8 cells; 2 fail on `main`); `TestIsValidAtAsReferenceMempool` (4 cells; "at expiresAt" fails on `main`): `IsValidAt` now drops a message once `expiresAt <= now`, as the mempool does |
| `fix/dmq-message-body-size` | `9804e9d9`, `52c1b032` | `TestVerifyMessageBodySizeAsReference`; a 0-byte body is accepted on `main`. The second commit refuses the body when decoding, before expiry (`TestDmqMessageDecodeRefusesBodySize`, expired messages in both shapes; on the first commit a 0-byte body decodes) |
| `fix/dmq-commit-recheck-every-counter` | `aa2673b6` | `TestPrepareMessagesCommitRechecksEveryCounter`; the stale commit returns nil on `main` |
| `test/dmq-validity-reference` | `2a86f5ad` | `TestVerifyMessageCounterAndPoolAsReference` (48 cells); 3 mutations killed |
| `fix/dmq-payload-preserved-bytes` | `d21d3969` | `TestVerifyMessageHashesPayloadBytesAsReceived`: a payload with a non-minimal KES period, signed and hashed as received, fails on `main` with an ID mismatch; the decoded payload now keeps its bytes (`DecodeStoreCbor`) and re-encodes to them |
| `fix/dmq-drop-chain-counter-check` | `aa7c8605` | `TestVerifyMessageIgnoresChainCounter`: on `main` "issue number is stale: chain=5, message=1". `PoolOpCertIssueNumber` becomes unused (deprecated) |
| `fix/dmq-sig-rate-limit` | `d4c8c2f1` | `TestVerifyMessageRateLimitAsReference` (7 cases; 4 fail on `main`). Mutations killed: no duplicate exemption, no commit re-check, a refused duplicate race, an inclusive bound |
| `fix/messagesubmission-reference-receipt` | `a12edd17` | `TestServerReceivesRepliesAsReference` (7 cells; 5 fail on `main`) and `TestServerReplyKeepsValidMessagesBesideAFatalOne`, which replaces a test of the all-or-nothing behaviour. Mutations killed: main's check order, an expired message fatal, a dropped authentication error fatal, stopping at the first failure |

All nine merge onto current `main` (`scratch/dmq-validation-combined`,
`7274cb47` after the decode-time size check, local only) with two hand resolutions in `authentication.go` (the
window and chain-counter drops both remove adjacent config checks; the rate
limit and the receipt branch both rework `PrepareMessages`) and one
cross-branch test fix: `TestPrepareMessagesCommitRechecksEveryCounter` needs
`MinSigDelay: -1` once the rate limit is in. Merged further with PR #3130's
head (`4f710823`), its new `NewMsgReplyMessages(version, ...)` signature needs
the two receipt tests updated; then the four DMQ packages and `protocol` pass
with `-race`.

## Spec, reference, and gOuroboros

| Question | CIP-0137 | Reference (dmq-node) | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| V1 wire tags | `MsgInit` 0, request ids 1, reply ids 2, request 3, reply 4, done 5 [C2] | tx-submission's: request ids 0, reply ids 1, request 2, reply 3, done 4, `MsgInit` 6 [R4] | the CIP's on `main` | **incompatible with dmq-node V1**; fixed on `fix/messagesubmission-reference-wire` |
| V2 wire tags | request ids 1, reply ids 2, request 3, reply 4, done 5 [C1] | request ids 1, reply ids 2, **`MsgReplyNoSigIds` 3**, request 4, reply 5, done 6 [R5] | the CIP's on `main` | **incompatible with dmq-node V2**; fixed on the same branch |
| Collection encoding | silent | indefinite-length lists only: every decoder calls `decodeListLenIndef` [R4][R5] | definite-length on `main` | **incompatible**; fixed on the same branch |
| V2: who starts it? | the inbound has agency in `StIdle`; `StInit` existed so the outbound could start on the initiator, and V2 "reverses the agency model" [C1] | the **initiator runs the inbound**, the responder the outbound [R6] | on `main` the Client (initiator) is the outbound in V2 too | **incompatible**: both sides wait in `StIdle` (`MessageSubmissionV2RolesBug.cfg`); fixed on the same branch |
| V2 blocking request with nothing to give | must wait | answers `MsgReplyNoSigIds` after 17 s [R1][R2]; the requester gives up after 20 s [R5] | no such message on `main`; waits | **incompatible** (`MessageSubmissionV2NoIdsReplyBug.cfg`); the branch adds `Client.ReplyNoMessageIds`, which the application must call |
| Window rules (ack, `MaxUnacked`, blocking iff empty, request 0) | "one cannot request 0 ids" either way [C3] | non-blocking may request 0 if it acknowledges [R2][R3]; same as tx-submission [S2] | as the reference | agree with the reference |
| A body asked for twice | silent | V2 refuses; V1 tolerates [R2][R3]; the type says "at most once" [R1] | served twice | **defect**, fixed |
| Empty `MsgRequestMessages` | silent | accepted [R2][R3] (the spec says "non-empty" [S3]) | accepted | agree with the reference |
| Message-submission time limits | none | V2: `StIdle` none, blocking 20 s, non-blocking and bodies 10 s [R5]; V1: blocking none, non-blocking and bodies 10 s [R7] | `StIdle` 300 s, blocking 30 s, non-blocking none, bodies 30 s | deviation; not a safety question, written up |
| Local submission answers | one per submission [C4] | handed to the submission's continuation | callbacks with no message | design limitation, written up |
| Local submission time limits | none | none: the server runs without limits [R8] | server times out a client idle 300 s in `StIdle`; client waits 30 s in `StBusy` | deviation: a local client quiet for five minutes is disconnected; written up |
| Empty blocking notification reply | forbidden: `[+ message]` [C5] | the codec refuses it [R9] | accepted | **defect**, fixed |
| Notification `hasMore` | in the non-blocking reply | per reply, from a `maxMsgs` cap [R10] | always `false`; the server sends its whole queue | deviation, harmless at the default sizes |
| Blocking vs non-blocking notification request | "blocking only after the server said it has no more" (`Type.hs`) | the server's check is commented out [R10] | not checked | agree with the reference |
| Server restart after `MsgDone` | silent; the network specification: "should be restarted in its initial state" [S5] | responders are restarted by the inbound governor [R11][R12] | none of the three servers restarts on `main` | **does not conform** (`DmqRestart*NoRestartBug.cfg`); fixed on the three `*-server-restart` branches |

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
| R4 | [`TxSubmission2/Codec.hs` lines 310-440](https://github.com/IntersectMBO/ouroboros-network/blob/4646039f05eb809bd5252af17121644ec1dc0c2c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Codec.hs#L310-L440) | V1 tags and indefinite lists; dmq-node's V1 codec wraps it (`DMQ/Protocol/SigSubmission/Codec.hs` 145-152) |
| R5 | [`dmq-node/src/DMQ/Protocol/SigSubmissionV2/Codec.hs` lines 81-95, 136-264](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/SigSubmissionV2/Codec.hs#L81-L264); `dmq-node/cddl/specs/sig-submission-v2.cddl` 23-28; `DMQ/Protocol/SigSubmissionV2/Inbound.hs` 99-100 | V2 time limits (blocking 20 s), tags 1-6, indefinite lists; the inbound treats `MsgReplyNoSigIds` as an empty reply |
| R6 | [`dmq-node/src/DMQ/NodeToNode.hs` lines 242-352, 536-600](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/NodeToNode.hs#L242-L352) | V2 initiator runs the inbound, responder the outbound; V1 the reverse; version selection |
| R7 | [`dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs` lines 68-78](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs#L68-L78) | V1 time limits |
| R8 | [`dmq-node/src/DMQ/NodeToClient.hs` lines 155-185](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/NodeToClient.hs#L155-L185); `DMQ/Protocol/LocalMsgSubmission/Type.hs` 20-22 | local servers run with `runAnnotatedPeer`, no limits; local submission is `LocalTxSubmission` |
| R9 | [`dmq-node/src/DMQ/Protocol/LocalMsgNotification/Codec.hs` lines 119-166](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/Protocol/LocalMsgNotification/Codec.hs#L119-L166); `Type.hs` 45-77 | notification tags; an empty blocking reply fails to decode |
| R11 | [`ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs` lines 455-470](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L455-L470); [`ouroboros-network/lib/Ouroboros/Network/Diffusion.hs` lines 402-418](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L402-L418) | a responder that ended cleanly is run again; the node-to-client server runs under an inbound governor too |
| R12 | [`dmq-node/app/Main.hs` line 270](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/app/Main.hs#L270) | dmq-node runs `Ouroboros.Network.Diffusion.run` |
| S5 | [`docs/network-spec/connection-manager.tex` lines 492-496](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/connection-manager.tex#L492-L496) | the server side "should be restarted in its initial state" |
| R10 | [`dmq-node/src/DMQ/NodeToClient/LocalMsgNotification.hs` lines 45-95](https://github.com/IntersectMBO/dmq-node/blob/a267003c14e95b3c9086319e5775a1f618456765/dmq-node/src/DMQ/NodeToClient/LocalMsgNotification.hs#L45-L95) | the notification server: STM wait, `maxMsgs`, `hasMore`, the blocking-rule check commented out |
| G1 | gOuroboros `protocol/messagesubmission/` | `messagesubmission.go` (state maps, timeouts), `validation.go`, `client.go`, `server.go`, `messages.go` (tags) |
| G2 | gOuroboros `protocol/localmessagesubmission/` | `localmessagesubmission.go` (state map, 300 s / 30 s), `client.go`, `server.go` |
| G3 | gOuroboros `protocol/localmessagenotification/` | `server.go` (`AddMessage`, `WaitForMessage`, `handleBlockingRequest`), `client.go` |
| G4 | gOuroboros `protocol/protocol.go` | `enqueueMessage`; role to muxer direction in `ensureRegistered`; timeouts only while the peer has agency |

## Not modelled

The per-connection replay caches beyond what `MessageIngress.tla` keeps as
the set of accepted ids; the opcert cold signature, message id and payload
bytes (pure checks, covered by Go tests); the
pipelined inbound of dmq-node V2 (`runPipelinedAnnotatedPeerWithLimits`);
time limits as durations (the 20 s V2 limit appears only as "an unanswered
blocking request is a deadlock"); wire tags and list encodings, which the Go
tests check byte for byte. Restarts are modelled only in `DmqRestart.tla`,
and not for V2, whose `MsgDone` comes from the server.

## Running it

```sh
cd specs/dmq
# passing configs
../../bin/tlc -config MessageSubmissionV1.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionV2.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionRogue.cfg MessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionSerialised.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionTagged.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageNotification.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationBroadcast.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationRogue.cfg LocalMessageNotification.tla
../../bin/tlc -config MessageValidity.cfg MessageValidity.tla
../../bin/tlc -config MessageValidityBatch.cfg MessageValidity.tla
../../bin/tlc -config MessageIngress.cfg MessageIngress.tla
# expected to fail
../../bin/tlc -config MessageSubmissionRepeatBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionServerRepeatBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionV2RolesBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionV2NoIdsReplyBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionNoWindowBug.cfg MessageSubmission.tla
../../bin/tlc -config MessageSubmissionNoBlockRuleBug.cfg MessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionConcurrentBug.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageSubmissionNoAgencyBug.cfg LocalMessageSubmission.tla
../../bin/tlc -config LocalMessageNotificationAppWaitBug.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationEmptyBlockingBug.cfg LocalMessageNotification.tla
../../bin/tlc -config LocalMessageNotificationUnbufferedBug.cfg LocalMessageNotification.tla
../../bin/tlc -config MessageValidityKesAtCurrentBug.cfg MessageValidity.tla
../../bin/tlc -config MessageValidityBatchFinalOnlyRecheckBug.cfg MessageValidity.tla
../../bin/tlc -config MessageIngressAllOrNothingBug.cfg MessageIngress.tla
```

To run a probe, copy a passing config and replace its `INVARIANT` lines with
the probe's name.
