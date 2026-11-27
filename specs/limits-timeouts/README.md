# Per-state timeouts and byte limits

Which side of a mini-protocol a state's timer runs on, what it is set to, and
what happens to a message larger than the state allows, for the Leios and
Peras mini-protocols and message submission (DMQ). The engine's rule is
modelled once (`StateLimits.tla`); each protocol side is a table
(`LimitsTables.tla`) as gOuroboros `7cd17437` builds it, beside the
reference's.

Read [Model `engine`](../engine/README.md), slice 3 (`EngineTimer.tla`),
first: this model applies its "afterHandler" rule to each protocol's table.

## What the code does

`stateLoop` arms the entered state's `Timeout` only where the peer holds
agency, never in the initial state (`InitialStateTimeout` is unset for every
protocol here), and not while `MessageHandlerFunc` runs; when the handler
returns it arms the current state's timer if the peer holds agency. The read
loop refuses a message whose declared size exceeds the active state's
`PendingMessageByteLimit` (`ErrProtocolViolationQueueExceeded`, "oversized
message"), which ends the protocol, before the rest arrives.

Each side installs its own copy of `StateMap`:

| Side | Timed waits (this side waits) | Byte limits |
| --- | --- | --- |
| LeiosFetch client | Votes, BlockRange: `Config.Timeout` (5 s). Block, BlockTxs: none; the caller's context bounds each request | Idle 65,535; Block 660,000; BlockTxs 550,000; BlockRange 64 MiB |
| LeiosFetch server | Idle: none | Idle 65,535 |
| LeiosNotify client | Quit: `Config.Timeout` (60 s); Idle and Busy none | every state: the budget, 655,350 by default |
| LeiosVotes client | Busy: `Config.Timeout` (60 s) | Busy 1,111 |
| Peras client | Blocking 10 s, MustReply 60 s, NonBlocking and Objects `Config.Timeout` (10 s) | every active state 50 x 1,100 + 256 |
| Peras server (same map) | Init, Idle: none | as the client |
| Message submission Server | V1: blocking 30 s, non-blocking none, messages 30 s; V2: the same. The package constants: the Config's timeouts are not applied | none |
| Message submission Client | Idle: `IdleTimeout` (300 s); a V2 Client's first Idle is the initial state, untimed | none |

## The answers

| Config | States | Result |
| --- | --- | --- |
| `StateLimitsLeiosFetchClientBlockLimitBug.cfg`: today | 81 | **fails** `NoLooserThanReference` |
| `StateLimitsLeiosFetchClient.cfg`: the fix (Block limit 600,010) | 1,662 | passes |
| `StateLimitsLeiosFetchServer.cfg`: today | 198 | passes |
| `StateLimitsLeiosNotifyClient.cfg`: today (byte budget recorded, DRIFT N45) | 666 | passes |
| `StateLimitsLeiosVotesClient.cfg`: today | 186 | passes |
| `StateLimitsPerasVotesClient.cfg`: today | 2,360 | passes |
| `StateLimitsPerasVotesServer.cfg`: today | 218 | passes |
| `StateLimitsMsgSubV1ServerBlockingBug.cfg`: today's V1 blocking timer | 37 | **fails** `TimedAsReference` |
| `StateLimitsMsgSubV1ServerNonBlockingBug.cfg`: today's non-blocking wait | 37 | **fails** `WaitIsBounded` |
| `StateLimitsMsgSubV2ServerNonBlockingBug.cfg`: the same in V2 | 40 | **fails** `WaitIsBounded` |
| `StateLimitsMsgSubV1Server.cfg`, `StateLimitsMsgSubV2Server.cfg`: the fixes | 212, 370 | pass |
| `StateLimitsMsgSubV1Client.cfg`, `StateLimitsMsgSubV2Client.cfg`: today (Idle 300 s recorded) | 88, 76 | pass |
| `StateLimitsMsgSubV2ServerOptionsBug.cfg`: today, every option 1 s | 3 | **fails** `OptionsTakeEffect` |
| `StateLimitsMsgSubV1ServerOptionsBug.cfg`: the same in V1 | 25 | **fails** `OptionsTakeEffect` |
| `StateLimitsMsgSubV2ServerOptions.cfg`, `StateLimitsMsgSubV1ServerOptions.cfg`: the fix | 370, 212 | pass |
| `StateLimitsMsgSubV1ClientOptions.cfg`: today | 88 | passes |
| `StateLimitsMsgSubV1ClientEveryStateBug.cfg`: mutation, every state's timer armed | 10 | **fails** `TimerOnlyWhileWaiting` |
| `StateLimitsLeiosNotifyClientWaitBug.cfg`: mutation, an over-limit message held | 120 | **fails**: deadlock |
| `StateLimitsPerasVotesClientAcceptBug.cfg`: mutation, the limit not checked | 61 | **fails** `NeverAcceptsOverLimit` |
| `StateLimitsPerasVotesClientProbesBug.cfg`: probe | 31 | violated, as expected (`ProbeTimerNeverFires`; `ProbeNeverRefused` too) |

**Defect 1: LeiosFetch accepts a block reply the reference refuses.**
`MaxBlockMessageBytes` is the 600,000-byte endorser block plus a tenth,
660,000 bytes. The reference's limit for `MsgLeiosBlock` is the block plus
ten bytes of framing, 600,010 [R1]. The constant and `PROTOCOL_LIMITS.md`
call 660,000 the reference's limit. Fixed on local branch
`fix/leiosfetch-block-limit` (DRIFT N73); Go: `TestBlockReplyOverReferenceLimitIsRefused`
(declares a 600,011-byte reply; today the client waits for the rest instead
of refusing it).

**Defect 2: the message-submission timeout options do not reach the side
that waits.** The Server sends the requests and waits for the replies, but
installs the package's state maps unchanged, so
`WithMessageIdsBlockingTimeout`, `WithMessageIdsNonblockingTimeout` and
`WithMessagesTimeout` never bound its waits. The Client applies them, but to
states where it holds agency, which the engine never times. Fixed on local
branch `fix/messagesubmission-blocking-timeout-option`: both sides install
one map with the Config's timeouts. The blocking option applies only to V2:
a V1 blocking request is untimed in the reference [R4] (local branch
`fix/messagesubmission-v1-blocking-untimed`, `StateLimitsMsgSubV1ServerBlockingBug.cfg`),
so a bound meant for V2 must not drop a V1 peer with nothing new.
`WithInitTimeout` bounds nothing either: Init is the initial state, never
timed, and the reference waits forever there; `WithDoneTimeout` names a state
with no agency. Both are documented as having no effect. Go:
`TestServerTimesItsWaitsWithTheOptions`, `TestV1BlockingIDRequestIgnoresTheOption`.

**Defect 3: a non-blocking request for message IDs is untimed.** The reference
times it with shortWait, 10 s, in V1 and V2 [R4]; gOuroboros sets 0, so a
peer that never answers holds the requester forever. Fixed on local branch
`fix/messagesubmission-nonblocking-timeout` (DRIFT N74); Go:
`TestWaitsTheReferenceTimesAreTimed`.

Recorded differences, not defects (`TimeoutDeviations`, `LimitDeviations`
in the configs): LeiosNotify's byte budget (DRIFT N45); message submission's
Messages 30 s against 10 s, V2 blocking 30 s against 20 s, Idle 300 s against
waitForever, and no per-state byte limits (DRIFT N74).

Peras certificates (COVERAGE gap 157): gOuroboros implements no Peras
certificate diffusion mini-protocol, only vote diffusion, so there is no
timer or limit table to check.

## Go tests bound to the model

On local branch `test/limits-and-timeouts`:

| Test | Binds |
| --- | --- |
| `perasvotes.TestStateTimersAndLimitsMatchModel` | `PerasClient`, `PerasServer`; `TimerOnlyWhileWaiting`, `TimedAsReference` |
| `perasvotes.TestClientRefusesOverLimitReplyWithoutWedging` | `NeverAcceptsOverLimit`, no deadlock |
| `leiosvotes.TestStateTimersAndLimitsMatchModel` | `VotesClient`; `TimerOnlyWhileWaiting` |
| `leiosnotify.TestStateTimersAndLimitsMatchModel` | `NotifyClient`; `TimedAsReference` |
| `leiosfetch.TestServerStateMapMatchesModel` | `FetchServer`; `WaitIsBounded` |
| `messagesubmission.TestV1ClientTimesItsIdleWait` | `OptionsTakeEffect` (Client) |
| `messagesubmission.TestV2ClientDoesNotTimeItsFirstIdle` | `Arm`'s initial-state rule, `OnlyThePeerIsTimed` |

## Sources

- [S1] ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`: time limits bound the receiver's wait.
- [R0] typed-protocols `8fa4ed2f5bfe` `Network/TypedProtocol/Driver.hs`; ouroboros-network `runPeerWithLimits`.
- [R1] ouroboros-consensus `ec239d57f618` (unchanged at `136122cc666c`) `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LeiosFetch/Type.hs` 218-245 (`byteLimitsLeiosFetch`, `timeLimitsLeiosFetch`); `.../Consensus/Leios/Types.hs` 479-480 (`maxEndorserBlockBytesSize = 600 * 1000`).
- [R2] same commit, `.../MiniProtocol/LeiosNotify/Type.hs` 186-227 (`maxLeiosVotesPerMessage`, `maxLeiosNotifyReplyBytes`, `byteLimitsLeiosNotify`, `timeLimitsLeiosNotify`).
- [R3] ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ObjectDiffusion/Codec.hs` 38-90 (`byteLimitsObjectDiffusion`, `timeLimitsObjectDiffusion`); `d5fc44653f8b` (the release ouroboros-consensus `136122cc666c` builds against; its `NodeToNode.hs` 946-968 passes `byteLimitsObjectDiffusion size`) same file 33-80; `ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs` 108-120 (`largeByteLimit`, `smallByteLimit`, `shortWait`, `longWait`, `waitForever`).
- [R4] dmq-node `67a1a1e5a579` `dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs` 57-100 (`timeLimitsSigSubmission`, `byteLimitsSigSubmission`); `.../SigSubmissionV2/Codec.hs` 45-95.
- [C1] CIP-0164: no LeiosVotes limits (UNSOURCED rows: LeiosVotes; LeiosFetch Votes and BlockRange, gOuroboros additions).
- [G] gOuroboros `7cd17437`: `protocol/protocol.go` `stateLoop`; `protocol/leiosfetch/leiosfetch.go`, `client.go` `NewClient`; `protocol/leiosnotify/leiosnotify.go` `protocolConfig`; `protocol/leiosvotes/client.go` `clientStateMap`; `protocol/perasvotes/client.go` `clientStateMap`, `server.go` `initProtocol`; `protocol/messagesubmission/messagesubmission.go` `stateMapV1`, `stateMapV2`, `client.go` `NewClient`, `server.go` `initProtocol`.

Run with `make limits-timeouts`.
