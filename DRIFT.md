# Drift: where gOuroboros differs from the Cardano reference

This document lists every place where gOuroboros, the Go library this repository models, behaves differently from the *reference implementation* (the Haskell code the Cardano node runs). For each difference it cites the *specification* (the written rules) to say whether gOuroboros still follows them. It collects the three-way comparisons in the model READMEs under `specs/`, and the fixes recorded since, in one place. Every citation below was fetched and read at the revision named here; a README was not taken on trust.

## Pinned revisions

| Source | Revision | What it is |
| --- | --- | --- |
| gOuroboros `main` | `d0b958459c12` | the code being judged; open pull requests are cited at their head commit |
| IntersectMBO/ouroboros-network | `5f356486ab3e` | network specification (`docs/network-spec`), CDDL (`cardano-diffusion/protocols/cddl/specs`), reference network code |
| IntersectMBO/typed-protocols | `8fa4ed2f5bfe` | the driver every reference mini-protocol runs on |
| IntersectMBO/ouroboros-consensus | `ec239d57f618` | reference consensus, Leios protocols, ChainDB; the consensus report (`docs/tech-reports/report`) |
| IntersectMBO/cardano-ledger | `1210d37fe6bd` | formal ledger specs (`eras/*/formal-spec`) and reference ledger rules |
| IntersectMBO/formal-ledger-specifications | `60b68036c8b4` | Conway rules (used for the library contracts below) |
| cardano-foundation/CIPs | `db48da14bff1` | CIP-0137 (message queue), CIP-0164 (Leios), CIP-0140 (Peras), CIP-0177 (Tachys); all Proposed |
| IntersectMBO/dmq-node | `a267003c14e9` | reference for CIP-0137 |

plutus `bdc12f105a98` was in scope, but no difference was found there, so it is not cited. The Ouroboros Genesis paper (IACR ePrint 2018/378) could not be fetched (the server refused); where it matters, the consensus report's restatement of its rule is cited instead and the paper is marked unverified.

Line numbers are at those revisions. "PR #n head `abc1234`" means the file at the head commit of that open gOuroboros pull request.

## Terms used here

- **Mini-protocol**: one conversation type between two nodes, such as chain-sync (following a chain's headers) or block-fetch (downloading blocks). Each is a state machine; in each state exactly one side has **agency**, the right to send next.
- **Node-to-node (N2N)** protocols run between nodes over the internet; **node-to-client (N2C)** protocols run between a node and a local program, such as a wallet.
- **Timeout** and **size limit**: the spec gives, per state, the longest the receiver waits for the next message and the largest message it accepts.
- **k**: the security parameter, the deepest rollback Praos allows.
- **Caller**: the program that uses gOuroboros. Here that is usually Dingo, Blink Labs' node, which keeps the ledger state that gOuroboros only reads.

## How to read a verdict

The verdict says whether gOuroboros on `main` follows the specification.

- **conforms**: it does.
- **conforms (stricter)**: it refuses something the spec allows, or waits less than the spec's bound. Every timeout table says the limits "bound how much time the receiver side can wait", so a shorter wait is inside the bound, but it can drop a peer the spec calls on time.
- **conforms (implementation choice)**: the spec is silent, or leaves the choice open, and gOuroboros chose differently from the reference.
- **does not conform**: it breaks a rule the spec states, or lacks something the spec requires. A larger size limit than the spec's counts here, since the spec says an oversized message should end the connection.
- **n/a (library contract)**: gOuroboros leaves the rule to its caller.

Where an open pull request changes the behaviour, the verdict reads "main → PR", for example "does not conform → conforms". The counts below use the `main` side. **spec silent** means no rule could be found; no section is invented for it.

The entries fall into five kinds:

1. Open PR moves to the reference.
2. Differs; both within the spec.
3. gOuroboros follows the spec, the reference does not.
4. gOuroboros outside the spec.
5. gOuroboros-only addition.

A sixth kind, state gOuroboros leaves to its caller, is listed at the end as contracts, not drift.

## Summary

82 entries. On `main`: does not conform 36; conforms 24; conforms (implementation choice) 14; conforms (stricter) 8.

| # | Area | Behaviour | Reference | gOuroboros | Spec says | Verdict | Status / PR |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [N1](#n1) | network | A message from a peer that does not have agency | Not read until the peer has agency, then judged against that state | Judged on arrival and refused | Silent on when the judgement happens | conforms (stricter) | Recorded, no change planned (models `keepalive`, `txsubmission`, `peersharing`, `localtx`, `localstatequery`) |
| [N2](#n2) | network | Which side a state's timeout applies to | Only the side waiting to receive is timed | main: the side holding agency is timed too, so a slow local callback times itself out; PR: receiver only, timed from when its handler for the previous message returns | Timeouts bound how long the receiver waits | conforms (implementation choice) → conforms | Open PR #3159 at `18e0418a` |
| [N3](#n3) | network | Bytes that arrive after a client's `MsgDone` | Kept on the mini-protocol's queue for a later run | Refused (no agency in `Done`); never replayed into a new run | Silent | conforms | Recorded (model `keepalive`); no visible effect while gOuroboros clients never restart a finished run |
| [N4](#n4) | network | Keep-alive client wait for the server's reply | 60 s, with a `TODO` asking for 10 s | 10 s by default (`WithTimeout` changes it) | 60 s in `StServer` | conforms (stricter) | Recorded; deliberate |
| [N5](#n5) | network | Clients that never send `MsgDone` | Keep-alive, peer-sharing and local-state-query clients send `MsgDone` when told to terminate | No API sends it; `Stop` unregisters and the connection closes later | The client may terminate; it is not required to | conforms | Recorded (models `keepalive`, `peersharing`, `localstatequery`). A node holds an acquired local state until the connection closes |
| [N6](#n6) | network | Chain-sync `StMustReply` timeout | Random 601-911 s | main: random 135-269 s; PR: 601-911 s | Random 601-911 s | conforms (stricter) → conforms | Open PR #3112 |
| [N7](#n7) | network | Chain-sync node-to-node message size limit | 65,535 bytes in every state | main: 462,000 bytes (the ingress queue size); PR: 65,535, with 462,000 kept as the pending-receive budget | 65,535 bytes in every state | does not conform → conforms | Open PR #3112 |
| [N8](#n8) | network | Chain-sync `StMustReply` timeout for a trusted peer | Never times out a trustable peer | Always applies the timeout; has no notion of a trusted peer | Timeout only for peers that are not trustable | conforms (stricter) | Recorded, not changed; whether a peer is trusted is the caller's knowledge |
| [N9](#n9) | network | Chain-sync `GetCurrentTip` answer routing | Each request's continuation receives its own answer | main: whichever caller is registered on a shared channel, so a roll's older tip can answer the call; PR: only the call's own answer | Answers come back in request order to the requester | conforms | Open PR #3094. A library defect: the wire is unaffected |
| [N10](#n10) | network | Handshake query answered before negotiation | Query reply only when the proposal is acceptable and the agreed data asks for it | main: any decodable proposed version that asks for a query gets one, even with no common version or the wrong network magic; PR: after negotiation | Query sends back the supported versions; negotiation fails on a magic mismatch | conforms (implementation choice) → conforms | Open PR #3127 |
| [N11](#n11) | network | Handshake simultaneous open | Supported: a `MsgProposeVersions` received in `Confirm` is read as `MsgReplyVersions` | main: not supported (a proposal in `Confirm` is an error); PR: supported | Supported | does not conform → conforms | Open PR #3127 |
| [N12](#n12) | network | Handshake `MsgQueryReply` without a query | Taken as a query result | Error | Silent | conforms (stricter) | Recorded (model `handshake`) |
| [N13](#n13) | network | Handshake `MsgAcceptVersion` carries the server's own data | Sends the negotiated (agreed) data | Sends its own version data for the chosen version; each side combines the flags itself | The negotiated data is sent back | does not conform | Fixed on local branch `fix/handshake-accept-negotiated-data` (model `handshake` `AcceptCarriesNegotiatedData`). No wrong outcome: the reference client recomputes the agreement |
| [N14](#n14) | network | Handshake version keys out of order | Recognised keys must ascend, else a decode failure; unrecognised keys skipped | Accepts any order; rejects duplicates | Keys must be unique and ascending | does not conform | Fixed on local branch `fix/handshake-version-key-order` (model `handshake` `UnorderedMapsRejected`, `UnknownKeysTolerated`); checks recognised keys only, as the reference does |
| [N15](#n15) | network | Block-fetch `Stop` with ranges outstanding | Collects every answer, then sends `MsgClientDone`; a demotion that times out closes the connection | main: gives up after 250 ms without `MsgClientDone` and allows `Start`, so a late reply reaches the new run; PR: abandons only when owed, latches, stops the muxer | `MsgClientDone` only from `StIdle` | does not conform → conforms | Open PR #3114 (chain-sync's identical defect was fixed by merged #3092) |
| [N16](#n16) | network | Block-fetch `RangeDoneFunc` for a request that was never sent | A request's receiver exists only once the request is sent | main: the shutdown drain calls `RangeDoneFunc` for a request whose `RequestRange` returned an error; PR: not | Silent (library API) | conforms | Open PR #3114. Library defect; Dingo works around it |
| [N17](#n17) | network | Block-fetch `StBusy` timeout default | 60 s | main: `NewConfig` sets `BatchStartTimeout` 5 s; PR: 60 s | 60 s | conforms (stricter) → conforms | Open PR #3114 (Dingo already sets 60 s) |
| [N18](#n18) | network | Block-fetch size limit in `StBusy` (and `StIdle` for a pipelining client) | 65,535 bytes | 2,500,000 bytes, because a `MsgBlock` that arrives early is judged against `StBusy` | 65,535 bytes | does not conform | Not fixed; needed by gOuroboros' engine, which judges a message against the state current when it arrives |
| [N19](#n19) | network | Block-fetch `RangeTimeout` | None | A whole range must finish within about 36 hours by default | Silent | conforms (implementation choice) | gOuroboros addition. Local only: it ends the caller's wait and sends nothing |
| [N20](#n20) | network | Tx-submission blocking and non-blocking request rules | Client throws `ProtocolErrorRequestBlocking`, `RequestNonBlocking`, `RequestedNothing`; server picks the style from its FIFO | main: the client does not check; `Server.RequestTxIds` lets the caller pick either style; PR: both enforced | Blocking iff nothing stays unacknowledged; ack or request non-zero | does not conform → conforms | Open PR #3128 (Dingo always sends blocking requests for at least one id) |
| [N21](#n21) | network | Tx-submission request over the window from `NodeToNodeV_16` | From V16 the client clamps the reply to its own window | Always a protocol error | From V16 not an error; reply with as many as fit | does not conform | Fixed in PR #3195 head `8f6c6d5b` (model `txsubmission` `ClampsOverWindow`; the first draft `4b7d5262` clamped a blocking request to an empty reply, `TxSubmissionV16ClampBlockingBug.cfg`) |
| [N22](#n22) | network | Tx-submission duplicate ids in one reply | Not checked | Refused | Silent | conforms (stricter) | Recorded; a reference peer never sends duplicates |
| [N23](#n23) | network | Peer-sharing: how many peers the server sends | `min(10, amount)` | `min(amount, 230)` | At most the amount requested, bounded by the message size | conforms (implementation choice) | Policy choice |
| [N24](#n24) | network | Peer-sharing request when peer sharing was negotiated off | Mini-protocol not registered; a segment for it is `UnknownMiniProtocol` and tears the connection down | Answers an empty list | Such a node does not run the server | conforms (implementation choice) | Deliberate (documented in the package) |
| [N25](#n25) | network | Peer-sharing address forms | An IPv4-mapped IPv6 address is sent as IPv6; the old eight-field IPv6 form is not decoded; declared list length ignored | IPv4-mapped sent as IPv4 (`net.IP.To4`); old form accepted on decode; list length checked | CDDL `peer-sharing-v14.cddl` | conforms | Recorded (model `peersharing`); same endpoint on a dual-stack host |
| [N26](#n26) | network | Local-tx-monitor: re-acquire (`MsgAwaitAcquire`) is timed | The node holds the answer until the mempool changes | main: the client times it at 5 s, so it dies against a real node; PR: not timed (acquire from `Idle` still is) | Await a new snapshot; no timeouts | does not conform → conforms | Open PR #3154 |
| [N27](#n27) | network | Local-tx-monitor server answers `MsgAwaitAcquire` at once | Waits until the snapshot differs | Answers immediately with the current snapshot | Await a new snapshot | does not conform | Opt-in fix in PR #3196 (`AwaitMempoolFunc`); merge after PR #3154, which stops the client timing the await |
| [N28](#n28) | network | Local-tx-monitor `MsgGetMeasures` | Always decoded and answered | Not implemented; decoding fails and the connection is torn down | Part of the protocol | does not conform | Not fixed; a missing feature |
| [N29](#n29) | network | Local-tx-monitor `Stop` while a snapshot is acquired | `MsgDone` only from `StIdle` (typed) | main: sends `MsgDone` from `Acquired`, an illegal message; PR: sends `MsgRelease` first | `MsgDone` only from `StIdle` | does not conform → conforms | Open PR #3088 (by another contributor) |
| [N30](#n30) | network | Node-to-client default timeouts | No time limits in the node-to-client codecs | main: local-state-query 5 s / 180 s, local-tx-monitor 5 s / 30 s, local-tx-submission 30 s; PRs: none by default | No timeouts | does not conform → conforms | Open PRs #3159 and #3140 |
| [N31](#n31) | network | Local-state-query server after `MsgDone` | Restarted by the inbound governor | main: stays `Done`; a new run's `MsgAcquire` is never answered; PR: restarts | A cleanly terminated server-side mini-protocol is restarted | does not conform → conforms | Open PR #3113 |
| [N32](#n32) | network | Other servers that do not restart after `MsgDone` | Every responder is restarted | Local-tx-monitor, local-tx-submission, message submission, local message submission, local message notification and Peras votes stay done | Restart | does not conform | Fixed in PR #3197 (head `c107bb53`). Keep-alive, chain-sync, block-fetch, tx-submission, peer-sharing and the three Leios servers do restart on main |
| [N33](#n33) | network | Local-state-query `Release` with nothing acquired | Impossible by types | main: sends `MsgRelease` from `Idle`, which tears the connection down; PR: returns `ErrNotAcquired` | `MsgRelease` only from `StAcquired` | does not conform → conforms | Open PR #3113 |
| [N34](#n34) | network | Local-state-query immutable-tip acquire below version 16 | Refuses to encode it | main: sends it; PR: `ErrAcquireImmutableTipUnsupportedVersion` | Silent | conforms | Open PR #3113 (interoperability defect against old nodes) |
| [N35](#n35) | network | Local-state-query implicit acquire | No implicit acquire | main: a query on an idle client acquires the volatile tip and never releases it, so later queries answer from a stale state; PR: released when the call returns | Silent (the wire sequence is legal either way) | conforms | Open PR #3113. Library defect (stale answers) |
| [N36](#n36) | network | Local-state-query server: `MsgRelease` without a `ReleaseFunc` | Accepted | main: an error that tears down a client that released; PR: accepted | `MsgRelease` is legal from `StAcquired` | does not conform → conforms | Open PR #3113 |
| [N37](#n37) | network | DMQ message submission wire format | dmq-node: V1 uses tx-submission's tags (Init = 6); V2 tags 1-6 with `MsgReplyNoSigIds` = 3; indefinite-length lists; in V2 the initiator runs the inbound side | main: the CIP's tags, no `MsgReplyNoSigIds`, definite lists, V2 initiator is the outbound side (both sides wait); PR: dmq-node's | CIP-0137 (Proposed): V1 tags 0-5, V2 tags 1-5, inbound has agency in V2 `StIdle` | conforms → does not conform (to the CIP text) | Open PR #3130 moves from the CIP to dmq-node, the only implementation; main cannot talk to dmq-node at all |
| [N38](#n38) | network | DMQ: the same message body requested twice | V2 refuses a repeat across requests; V1 only within one request | main: served twice; PR: refused as the reference does per version | Silent | conforms | Open PR #3130 |
| [N39](#n39) | network | DMQ time limits | V1: blocking none, non-blocking and bodies 10 s; V2: blocking 20 s; local servers run without limits | Message submission: `StIdle` 300 s, blocking 30 s, non-blocking none, bodies 30 s; local submission: server drops a client idle 300 s | Silent | conforms (implementation choice) | Recorded (model `dmq`) |
| [N40](#n40) | network | DMQ local notification: empty reply to a blocking request | The codec refuses it | main: accepted; PR: refused | A blocking reply holds at least one message | does not conform → conforms | Open PR #3142 |
| [N41](#n41) | network | DMQ local notification: lost wake-up | STM wait; every waiter sees a new message | main: `AddMessage` wakes one waiter, so a blocking request can stay unanswered; PR: wakes every waiter | Silent on implementation; a blocking request is answered once a message exists | conforms | Open PR #3142. Liveness defect, wire unaffected |
| [N42](#n42) | network | DMQ local protocols: `hasMore` and submission answers | `hasMore` set per reply from a cap; each submission's answer goes to its own continuation | `hasMore` always false (sends the whole queue); local-submission callbacks carry no message id | `hasMore` in the non-blocking reply; one answer per submission | conforms | Recorded; harmless at default sizes; API limitation |
| [N43](#n43) | network | LeiosNotify: request after `MsgQuit`, and `MsgCanceled` before `MsgQuit` | Never requests after quit (`drainThePipe`); an early `MsgCanceled` throws | main: `Stop` racing a refill can send a request after `MsgQuit`; an early `MsgCanceled` is ignored and the loop stalls; PR: both fixed | Silent (CIP-0164 describes a different LeiosNotify) | conforms | Open PR #3160 |
| [N44](#n44) | network | LeiosVotes: next request pipelined while `Busy` | No reference implementation | main: the server refuses it; PR: accepted | Requests should be pipelined | does not conform → conforms | Open PR #3160 |
| [N45](#n45) | network | Leios limits and timeouts | LeiosNotify reply 1,536 bytes / 16 votes; LeiosFetch `Block` and `BlockTxs` 60 s | LeiosNotify 65,535 bytes / 1,000 votes; LeiosFetch block states untimed (the caller's context bounds them); LeiosVotes count 1-1,000 | Silent on limits; CIP's request count unbounded | conforms (implementation choice) | Recorded (model `leios-peras`) |
| [N46](#n46) | network | LeiosFetch extra messages (tags 10-14) | Only `Block` and `BlockTxs` (tags 0-4) | Adds votes and block-range requests | CIP-0164 has its own message set | conforms (implementation choice) | gOuroboros extension. A reference peer never sends them; sent to a reference server they fail to decode, so only use them with peers that know them |
| [N47](#n47) | network | Peras votes (ObjectDiffusion): await, server idle, timeouts | `MsgServerIdle` [6], `MsgAwaitReply` [7], a `MustReply` state; client waits 10 s, then 60 s after await | main: no await messages, no `MustReply`, one 5 s timeout; PR: as the reference, server awaits then replies or idles | CDDL defines tags 6 and 7 | does not conform → conforms | Open PR #3165. The network spec itself only lists `NodeToNodeV_17` as "Experimental, support Peras mini-protocols" (line 2231) |
| [C1](#c1) | consensus | Which VRF tie-break applies across eras | Taken from the newer tip's era | Taken from the caller's `ProtocolMajor` (restricted from 9) | Silent (the Praos papers do not define a VRF tie-break) | conforms (implementation choice) | Recorded (model `consensus`); same answer within one era |
| [C2](#c2) | consensus | Adopting a fork deeper than k by density | Never rolls back more than k: Genesis is implemented with the Limit on Eagerness (LoE) and the density disconnection governor (GDD) | `IsDeepFork` routes a fork deeper than k to `CompareWithDensity`, which can prefer it; no LoE or GDD | The Genesis density rule imposes no maximum rollback | conforms | Documented design. Follows the paper's rule; differs from the reference, which keeps Praos' k bound. A caller that adopts the result whole can roll back more than k |
| [C3](#c3) | consensus | A tip with no VRF output | Cannot happen | Ranks below any tip with one | Silent | conforms | Unreachable from a valid header |
| [C4](#c4) | consensus | Shelley header after Origin (the first block) | Block 0, any slot, predecessor `GenesisHash` | main: `ValidateHeaderInput` cannot say "no previous header", so block 0 always fails; PR: `PrevIsOrigin`, with the predecessor absent or the zero hash | No sequence check without a previous block | does not conform → conforms | Open PR #3111 at `64573df5` (model `consensus` `ShelleyEnvelope.tla`) |
| [C5](#c5) | consensus | Byron header envelope: slot and block number | Slot strictly later except a main block after an EBB; an EBB after a main block shares its number; first block number 0 | main: any main block or EBB may share its predecessor's slot; an EBB may take either number; the first block must be 1; PR: as the reference | Slot strictly increases | does not conform → conforms | Open PR #3111 (reverses an earlier deliberate relaxation; Dingo does not call this validator). An EBB is an epoch boundary block, a Byron block with no transactions that opens each epoch |
| [C6](#c6) | consensus | Genesis window anchor | One anchor, the LoE tip, shared by every candidate | Each fragment counts from its own intersection with our selection | Window anchored at the intersection of the two chains compared | does not conform | Not fixed; correct only if the caller anchors every fragment at one point (model `consensus-genesis`, `OwnAnchorBug`) |
| [C7](#c7) | consensus | Genesis: exact tie, and deciding before the window is complete | Both tied peers are dropped; a peer still sending is kept until it cannot win, and only when it offers more than k blocks | A tie goes to the longer fragment, then the first; decides on the blocks received so far; no `offersMoreThanK` guard | Silent on ties and partial windows | conforms (implementation choice) | Recorded (model `consensus-genesis`). Safe only if the caller waits for the window to fill |
| [C8](#c8) | consensus | Genesis window count from `SimpleChainFragment` | Exact header count | Estimated from the fragment's span (`float64`), with rounding errors | Count the blocks in the window | does not conform | The float rounding is fixed on local branch `fix/genesis-window-estimate-rounding` (`74699bf6`, no PR); the estimate itself remains. Callers with real headers should implement `ChainFragment` with a count |
| [C9](#c9) | consensus | Genesis window size in Byron | 2k | 3k/f, which is 3k with f = 1 | s = 3k/f | conforms | Recorded; nothing calls it for Byron |
| [C10](#c10) | consensus | Byron re-delegation to the delegate already active | No change | main: rewrites the activation slot; the delegation map is the same; PR: no change | A delegate already in the map leaves the state unchanged | conforms | Open PR #3174 (model `ledger-byron`, `SlotsAgree`, `ByronDelegationOwnEntryBug.cfg`). Benign on main: the slot is read only by a check every later schedule passes |
| [C11](#c11) | consensus | Tachys leader schedule | None | Optional public leader schedule that replaces the private VRF lottery for issuer authorization (`NewTachysLeaderSelector`, `NewTachysHeaderValidator`) | CIP-0177 (Proposed) | conforms (implementation choice) | Opt-in, for partner chains. Not Praos: a Tachys header is not valid on a Praos network, and nothing selects it by default |
| [C12](#c12) | consensus | Rolling nonce from a raw 64-byte VRF output | The VRF output is hashed to a 32-byte nonce first (`mkNonceFromOutputVRF`), then combined | main before `756a9a89`: `CalculateRollingNonce` accepted the 64-byte output and hashed `prev ‖ output` (96 bytes). Now `NonceFromTPraosVRF`/`NonceFromPraosVRF` derive the contribution and a 64-byte operand is rejected | Combine two seeds; the block's seed is the nonce from its header | does not conform → conforms | Fixed by #3053 (merged, `756a9a89`) |
| [C13](#c13) | consensus | The neutral nonce as an identity | `x ⭒ NeutralNonce = x` and `NeutralNonce ⭒ x = x` | Rolling: `CombineNonces` has `NonceTypeNeutral` as identity on both sides since `756a9a89`. Epoch: main's `CalculateEpochNonce` hashes a zero (or rejects an empty) candidate or lab nonce; branch: `EpochNonceFromNonces` takes `common.Nonce` and composes with `CombineNonces`, and `CalculateEpochNonce` is deprecated | `0_seed` is the neutral element of ⭒ | does not conform (epoch nonce only) → conforms | Rolling part fixed by #3053 (`756a9a89`). Epoch part fixed additively on local branch `fix/nonce-neutral-epoch-and-vrf-input` (`da43d778`), no PR yet; model `consensus-nonce` `EpochNonceNewByron` passes, `EpochNonceDirectLabBug` still reproduces the deprecated function. Dingo applies the identity by hand and can move to the new function |
| [C14](#c14) | consensus | A neutral epoch nonce in the VRF input | Appends nothing for a neutral η0 | main: `MkInputVrf` and `MkSeedTPraos` need 32 bytes, so a neutral η0 is passed as 32 zero bytes; branch: `MkInputVrfFromNonce`, `MkSeedTPraosFromNonce` and `ComputeVRFInputFromNonce` take `common.Nonce` and append nothing for `NonceTypeNeutral`, and the `[]byte` builders are deprecated | `slotToSeed slot ⭒ η0`, with `0_seed` neutral | does not conform → conforms | Fixed additively on local branch `fix/nonce-neutral-epoch-and-vrf-input` (`da43d778`), no PR yet; model `consensus-nonce` `EpochNonceNewNeutral` passes, `EpochNonceVrfInputBug` still reproduces the deprecated builders. gOuroboros' exported `[]byte` callers (leader election, header validation, `VerifyBlock`) still cannot express a neutral η0. Only a chain with a neutral initial nonce reaches it, in its first epoch |
| [C15](#c15) | consensus | TPraos overlay schedule (d > 0) | A non-active overlay slot is rejected; an active one belongs to a genesis delegate, checked against its delegation with no stake | main: `ValidateHeaderInput` cannot carry d or the genesis delegations, so a valid genesis-delegate header is rejected (no stake, no pool VRF key) and a pool header in a non-active slot is accepted; branch: required `Overlay`, `ErrNotActiveSlot`, `ErrWrongGenesisColdKey`, `ErrWrongGenesisVRFKey` | OVERLAY rule: Active-OBFT and Decentralized | does not conform → conforms | Fixed on local branch `fix/consensus-tpraos-overlay` (`78f2f391`), no PR yet (model `consensus-eras`, `OverlayGenesisBug`, `OverlayNonActiveBug`). No production caller: Dingo validates with `VerifyBlock` and its own overlay check |
| [C16](#c16) | consensus | Header envelope: ObsoleteNode, header size, body size | Checked before the protocol rules | main: not in `ValidateHeader`; branch: required `Envelope`, `ErrObsoleteNode`, `ErrHeaderSizeTooLarge`, `ErrBlockSizeTooLarge`; a missing input is the only error (`ErrMissingHeaderInput`) | `chainChecks` | does not conform → conforms | Fixed on the same branch (model `consensus-eras`, `ExtrasBug`, `MissingInputBug`) |
| [C17](#c17) | consensus | Byron slot to epoch past Byron | The era history (`Summary`) converts every slot | main: `ByronConfig.SlotToEpoch` divides any slot by the Byron epoch length (mainnet slot 4514400 gives 209, not 208); branch: `EndSlot` and `SlotToEpochChecked` (`ErrSlotAfterByron`) | Conversions use each era's own epoch size | does not conform → conforms | Fixed on local branch `fix/consensus-byron-slot-epoch` (`70d83369`), no PR yet (model `consensus-eras`, `GoByronSoundBug`). Only tests call it |
| [L1](#l1) | ledger | Pool registration when the caller's view is stale | Registered means present in `psStakePools`, which POOLREAP clears at the epoch boundary | main: trusts the caller's `IsPoolRegistered`, so a stale view lets a delegation to (or retirement of) a reaped pool through, and treats re-registering a reaped pool as a re-registration; PR: one epoch-aware predicate | Delegation needs a registered pool; a reaped pool is gone | does not conform → conforms | Open PR #3129. Dingo's view already satisfies the contract |
| [L2](#l2) | ledger | Transaction id of a body without stored CBOR | A body always carries its serialization; the encoder omits an empty CIP-159 map | main: hashes empty input, the same id for every such body; PR: hashes the body's encoding, omitting empty Dijkstra maps, and gives a body with no valid encoding the zero id | The id is the hash of the body's CBOR | does not conform → conforms | Open PR #3141. Decoded bodies were always right; bodies built in code were wrong. No TLA+ model: a pure function, covered by Go tests |
| [L3](#l3) | ledger | Conway CC vote with a nil voter key | Not representable | main: `UtxoValidateCCVotingRestrictions` panics; PR: skips it as the sibling rules do | n/a (unreachable from decoded CBOR) | conforms | Open PR #3155. Library defect, hand-built transactions only |
| [L4](#l4) | ledger | BadInputs covers only spent inputs | Alonzo: spent and collateral inputs; Babbage: reference inputs too | main: spent inputs only; missing collateral and reference inputs are caught by the witness rules instead; PR: the reference's set, with BadInputs first in each rule list | All of them must exist | conforms | Open PR #3193 at `efd0b081` (model `ledger-utxo` `GoBadInputsComplete`, `GoMissingInputIsBadInputs`) |
| [L5](#l5) | ledger | Byron transaction with no inputs or no outputs | Cannot be decoded (`NonEmpty`) | main: accepted; a no-input, zero-output transaction pays no fee (it counts as redeem-only) | Inputs and outputs non-empty | does not conform | Fixed on a local branch, no PR yet |
| [L6](#l6) | ledger | Byron `maxTxSize` | `TxValidationTxTooLarge` | No check anywhere | `txSize tx ≤ maxTxSize` | does not conform | Open, no branch. Adding it changes the API (`VerifyConfig` or `ValidateAgainstUtxo`) |
| [L7](#l7) | ledger | Byron minimum fee rounding | Summand rounded to a whole lovelace when decoded, then the per-byte part rounded up | The whole sum rounded up | `a + b·txSize ≤ fee`, exact | conforms | Since the fee is a whole number, rounding the sum up is exactly the spec's check; the reference can accept a fee half a lovelace short. Differs only for a fractional summand, which no network has |
| [L8](#l8) | ledger | Byron repeated inputs and witness counts | A repeated input is counted once; witnesses are zipped with inputs, so a short list leaves inputs unchecked | Repeated input rejected; witness count must equal input count | Inputs are a set; every input needs a valid witness | conforms (stricter) | Deliberate. Stricter than the spec only for extra witnesses, which the spec allows |
| [L9](#l9) | ledger | Leios committee with fewer pools than `Nc` | `min(Nc, pools)` seats; the bitfield is sized by the seated committee | Requires exactly `Nc` seats, so every valid certificate from a small committee is refused | Take all pools if fewer than `Nc` | does not conform | Fixed on local branch `fix/leios-committee-size` (`fec72765`), no PR yet. Hits the prototype testnet (committee size 900) |
| [L10](#l10) | ledger | Leios certificate in a later epoch than its announcement | cardano-ledger refuses it (`LeiosCertAnnouncedInPreviousEpoch`); the consensus prototype does not check | Not checked | Not required | conforms | Recorded (model `ledger-leios`) |
| [L11](#l11) | ledger | Node-to-client CertRB with inlined EB transactions | none | Accepts a certifying block whose endorser-block transactions are inlined, over node-to-client only | CertRB carries no transactions on chain | conforms | Local delivery only; the on-chain body is unchanged |
| [L13](#l13) | ledger | Conway vote naming an enacted purpose root | Refused, `GovActionsDoNotExist`: votes resolve against the live proposals only | main: accepted when the caller's `GovActionById` returns the root, which the contract allowed and Dingo does; PR: the contract excludes roots | A vote names a proposal in the governance state | does not conform → conforms | Open PR #3155. Dingo's `GovActionById` must stop returning the current root |
| [L12](#l12) | ledger | CBOR nesting limit | No nesting limit | 16,384 levels for blocks and ledger data; 1,024 for peer messages | RFC 8949 sets none | conforms | Just above what a 16,384-byte transaction can nest; raising `maxTxSize` would let a valid transaction nest deeper than gOuroboros accepts |
| [P1](#p1) | pipeline | An invalid block in the pipeline | ChainDB records it, ignores it and its successors, and carries on | The pipeline stops (fatal) | Silent | conforms (implementation choice) | Documented in chain-sync's `Config.Pipeline` |
| [P2](#p2) | pipeline | Closing with blocks queued | Every queued block is answered `FailedToAddBlock` | Dropped; a waiting `Fence` gets `ErrPipelineStopped` | Silent | conforms (implementation choice) | Recorded (model `pipeline-cbor`) |
| [P3](#p3) | pipeline | `WaitForDrain` during `Stop` | Rollback is part of chain selection, serialised with adds | main: returns once `Stop` begins while a block may still commit after the caller's rollback; PR: waits for the apply runner | Silent | conforms | Open PR #3161. Library defect; not reached through chain-sync or Dingo today |
| [P4](#p4) | pipeline | An unread `Results` channel | Chain selection never waits on a follower | main: stalls the apply runner; PR: never blocks commits, drops the oldest result for a reader that falls behind (counted in `ResultsDropped`) | Silent | conforms | Open PR #3161 |
| [P5](#p5) | pipeline | `WithLosslessResults` | none | Opt-in with an `ApplyFunc`; always on in header-only and trusted decode-only modes: `Results` delivers every committed block and commits wait for the reader | Silent | conforms (implementation choice) | On PR #3161 at `0dbc3775` (decode-only modes are lossless by default; Dingo's opt-in is now redundant). Wire: a slower commit only delays chain-sync's next request, which the protocol allows; ledger: unchanged |

## Network

### N1

**A message from a peer that does not have agency** (kind 2: differs; both within the spec)

- **What differs.** Reference: not read until the peer has agency, then judged against that state. gOuroboros: judged on arrival and refused.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Protocols as State Machines", lines 32-36: "If either side receives a message that is not expected according to the mini-protocol the communication is aborted"; spec silent on when an early message is judged
- **Reference.** typed-protocols `8fa4ed2f5bfe` `typed-protocols/src/Network/TypedProtocol/Driver.hs` 161-163 (`go dstate (Await ...)`: a peer reads only while awaiting)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/protocol.go` 1608-1624 (`reserveInboundAdmission`: a message that is not pipelined is denied while this side holds agency, or in `Done`)
- **Verdict.** conforms (stricter)
- **Status.** Recorded, no change planned (models `keepalive`, `txsubmission`, `peersharing`, `localtx`, `localstatequery`)

Only a misbehaving peer sends early. The reference sometimes answers such a peer (two `MsgKeepAlive` in a row both get answered); gOuroboros closes the connection at once.

### N2

**Which side a state's timeout applies to** (kind 1: open PR moves to the reference)

- **What differs.** Reference: only the side waiting to receive is timed. gOuroboros: main: the side holding agency is timed too, so a slow local callback times itself out; PR: receiver only, and its timer starts once the handler for the previous message returns (at `c0a5ca9c3` a slow inbound handler still counted against the peer: review finding, model `engine` `EngineTimerAtTransitionBug.cfg`).
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, block-fetch "Timeouts per state", lines 1227-1228 (same sentence in every N2N protocol): "These limits bound how much time the receiver side can wait for the arrival of a message."
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/framework/lib/Ouroboros/Network/Driver/Limits.hs` 109-131 (`sendMessage` untimed, `recvMessage` wrapped in `timeoutFn`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/protocol.go` 2322-2362 (timer armed for `agencyLocal` too); PR #3159 head `18e0418a` `protocol/protocol.go` (`stateLoop`: `skipTimeout` for `agencyLocal`, `handling` and `handlerDoneChan`; `recvLoop` reports the handler's return)
- **Verdict.** conforms (implementation choice) → conforms
- **Status.** Open PR #3159 at `18e0418a` (model `engine` slice 3, `EngineTimer.tla`)

The spec only describes the receiver's wait; timing the sender is extra. Its visible effect on main is a server that drops a healthy connection because its own callback was slow (seen with block-fetch and peer-sharing servers).

### N3

**Bytes that arrive after a client's `MsgDone`** (kind 2: differs; both within the spec)

- **What differs.** Reference: kept on the mini-protocol's queue for a later run. gOuroboros: refused (no agency in `Done`); never replayed into a new run.
- **Spec.** spec silent: The state machine ends in `StDone` where nobody has agency; nothing says what happens to later bytes on the client side
- **Reference.** typed-protocols `8fa4ed2f5bfe` `Driver.hs` 173-176 ("we want to allow for one protocols to be run after another on the same channel")
- **gOuroboros.** gOuroboros `d0b95845` `protocol/protocol.go` 1623-1624 (`agencyNeither`: denied)
- **Verdict.** conforms
- **Status.** Recorded (model `keepalive`); no visible effect while gOuroboros clients never restart a finished run

The handshake is the same case: the reference tears the connection down on a message after `Done`, gOuroboros drops it.

### N4

**Keep-alive client wait for the server's reply** (kind 2: differs; both within the spec)

- **What differs.** Reference: 60 s, with a `TODO` asking for 10 s. gOuroboros: 10 s by default (`WithTimeout` changes it).
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, keep-alive "Timeouts per state", lines 1633-1648: table: `StServer` 60s
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Codec.hs` 115 (`timeLimitForState SingServer = Just 60 -- TODO: #2505 should be 10s.`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/keepalive/keepalive.go` 33 (`DefaultKeepAliveTimeout = 10`), 170
- **Verdict.** conforms (stricter)
- **Status.** Recorded; deliberate

A shorter wait stays inside the spec's bound, but a server that answers between 10 s and 60 s loses the connection although the spec says it is on time.

### N5

**Clients that never send `MsgDone`** (kind 2: differs; both within the spec)

- **What differs.** Reference: keep-alive, peer-sharing and local-state-query clients send `MsgDone` when told to terminate. gOuroboros: no API sends it; `Stop` unregisters and the connection closes later.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, local-state-query messages, lines 1993-1994: "[MsgDone] The client can terminate the protocol."
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/lib/Ouroboros/Network/PeerSharing.hs` 125 (`SendMsgDone` on `Terminate`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/keepalive/client.go` 149 (`Stop`, no `MsgDone`)
- **Verdict.** conforms
- **Status.** Recorded (models `keepalive`, `peersharing`, `localstatequery`). A node holds an acquired local state until the connection closes

### N6

**Chain-sync `StMustReply` timeout** (kind 1: open PR moves to the reference)

- **What differs.** Reference: random 601-911 s. gOuroboros: main: random 135-269 s; PR: 601-911 s.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Node-to-node timeouts per state" (chain-sync), line 944: "`StMustReply` & random between 601s and 911s"
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ChainSync/Codec.hs` 57, 63 (`minChainSyncTimeout = 601`, `maxChainSyncTimeout = 911`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/chainsync/chainsync.go` 251-252; PR #3112 head `4032512e4` same file 267-268
- **Verdict.** conforms (stricter) → conforms
- **Status.** Open PR #3112

`StMustReply` is where a client waits for the next block. On main a quiet but honest server is dropped after as little as 135 s.

### N7

**Chain-sync node-to-node message size limit** (kind 1: open PR moves to the reference)

- **What differs.** Reference: 65,535 bytes in every state. gOuroboros: main: 462,000 bytes (the ingress queue size); PR: 65,535, with 462,000 kept as the pending-receive budget.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Node-to-node size limits per state" (chain-sync), lines 910-924: table: `StIdle`, `StCanAwait`, `StMustReply`, `StIntersect` all 65535
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/ChainSync/Codec.hs` 43-49 (`smallByteLimit` per state); `ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs` 110-111
- **gOuroboros.** gOuroboros `d0b95845` `protocol/chainsync/chainsync.go` 233, 116-146; PR #3112 head `4032512e4` same file 245-247 (`SmallMaxPendingMessageBytes = 65535`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3112

Main accepts a message up to seven times larger than the spec allows instead of tearing the connection down.

### N8

**Chain-sync `StMustReply` timeout for a trusted peer** (kind 2: differs; both within the spec)

- **What differs.** Reference: never times out a trustable peer. gOuroboros: always applies the timeout; has no notion of a trusted peer.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Node-to-node timeouts per state" (chain-sync), line 936: "The timeout on state StMustReply only applies if the peer is not trustable."
- **Reference.** ouroboros-network `5f356486ab3e` `cardano-diffusion/protocols/lib/Cardano/Network/Protocol/ChainSync/Codec/TimeLimits.hs` 38, 67 (`IsTrustable -> (Nothing, rnd)`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/chainsync/chainsync.go` 134-137 (`TimeoutFunc: MustReplyTimeoutFunc` for every peer)
- **Verdict.** conforms (stricter)
- **Status.** Recorded, not changed; whether a peer is trusted is the caller's knowledge

### N9

**Chain-sync `GetCurrentTip` answer routing** (kind 1: open PR moves to the reference)

- **What differs.** Reference: each request's continuation receives its own answer. gOuroboros: main: whichever caller is registered on a shared channel, so a roll's older tip can answer the call; PR: only the call's own answer.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Pipelining of Mini Protocols", lines 2180-2208: replies are delivered in request order; spec silent on library API routing
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ChainSync/ClientPipelined.hs` 72 (`SendMsgFindIntersect`, a request and its own continuation)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/chainsync/client.go` 605, 658-665 (`waitingForCurrentTipChan`); PR #3094 head `5c0d22eb5` `client.go` 544
- **Verdict.** conforms
- **Status.** Open PR #3094. A library defect: the wire is unaffected

### N10

**Handshake query answered before negotiation** (kind 1: open PR moves to the reference)

- **What differs.** Reference: query reply only when the proposal is acceptable and the agreed data asks for it. gOuroboros: main: any decodable proposed version that asks for a query gets one, even with no common version or the wrong network magic; PR: after negotiation.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Node-to-node handshake", lines 556-557 and 564-573: "query ... True will send back all supported versions & version data and terminate the connection"; "if the network magic agrees ... otherwise the negotiation fails"
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/framework/lib/Ouroboros/Network/Protocol/Handshake/Server.hs` 38-39 (`Right (_, _, agreedData) | query agreedData -> Yield (MsgQueryReply ...)`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/server.go` 105-120; PR #3127 head `19c0debbf` same file 213-214
- **Verdict.** conforms (implementation choice) → conforms
- **Status.** Open PR #3127

The spec does not say whether a query must first pass negotiation; main tells a peer on another network which versions it supports.

### N11

**Handshake simultaneous open** (kind 1: open PR moves to the reference)

- **What differs.** Reference: supported: a `MsgProposeVersions` received in `Confirm` is read as `MsgReplyVersions`. gOuroboros: main: not supported (a proposal in `Confirm` is an error); PR: supported.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Handshake mini-protocol", lines 447 and 704-709: "The handshake mini protocol is designed to handle simultaneous TCP open."
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/Handshake/Client.hs` 120 (`MsgReplyVersions vMap -> ...`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/client.go` 113 (`default:` error); PR #3127 head `19c0debbf` `client.go` 125-126, 193. Review: at `78792c96` each side ended with the peer's raw data (reference: the agreed data, `Client.hs` 213-215); fixed at `5826fae1` (model `handshake` `SimAgreedData`, `HandshakeSimOpenRawPeerDataBug.cfg`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3127, head `5826fae1`

Simultaneous open happens when two nodes dial each other at the same moment and TCP joins the two attempts into one connection.

### N12

**Handshake `MsgQueryReply` without a query** (kind 2: differs; both within the spec)

- **What differs.** Reference: taken as a query result. gOuroboros: error.
- **Spec.** spec silent: The spec describes the query reply only as the answer to a query
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/Handshake/Client.hs` 132 (`MsgQueryReply vMap -> ...` in any proposal)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/client.go` 381-384 ("received handshake QueryReply message without proposing query mode")
- **Verdict.** conforms (stricter)
- **Status.** Recorded (model `handshake`)

### N13

**Handshake `MsgAcceptVersion` carries the server's own data** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: sends the negotiated (agreed) data. gOuroboros: sends its own version data for the chosen version; each side combines the flags itself.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Node-to-node handshake", lines 572-573: "If the negotiation is successful, the negotiated version data is sent back using MsgAcceptVersion"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/Handshake/Server.hs` 43 (`Yield (MsgAcceptVersion vNumber $ encodeData vNumber agreedData)`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/server.go` 161, 228
- **Verdict.** does not conform
- **Status.** Fixed on local branch `fix/handshake-accept-negotiated-data`; model `handshake` `HandshakeAcceptOwnDataBug.cfg` reproduces main. No wrong outcome found: the reference client recomputes the agreement, and every combining rule is idempotent and commutative
- **Review follow-up.** PR #3194 at `8ab16c0f`: the server's `FinishedFunc` also gets the agreed data (reference `Server.hs` 42-44); model `handshake` `AgreedDataBothSides`, `HandshakeServerRawPeerDataBug.cfg`
- **Review follow-up.** PR #3194 at `97039771` and PR #3127 at `8461ae3a`: a version table entry held as a pointer now agrees like a value; before, it came back unchanged as the side's own data. Verdict: conforms on both branches. Model `handshake` `AgreeHeld`, `HandshakePointerUnagreedBug.cfg`, `HandshakeSimOpenPointerUnagreedBug.cfg`

### N14

**Handshake version keys out of order** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: recognised keys must ascend, else the message fails to decode; unrecognised keys are skipped. gOuroboros: accepts any order; rejects duplicates.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Client and Server Implementation" (handshake), lines 655-656: "version numbers ... in the version table are unique and appear in ascending order"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/Handshake/Codec.hs` 101-102 ("encodes proposed map in ascending order and it expects to receive them in this order"), 228-241 (`decodeVersions`: an unrecognised key is skipped, a recognised key must exceed the previous recognised key)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/collection_decode.go` 85 (duplicate check only)
- **Verdict.** does not conform
- **Status.** Fixed on local branch `fix/handshake-version-key-order`; model `handshake` `HandshakeKeyOrderBug.cfg` reproduces main. The fix follows the reference: only recognised keys must ascend, and an unrecognised key out of order is accepted. A strict every-key check would refuse such a peer (`HandshakeKeyOrderEveryBug.cfg`)

### N15

**Block-fetch `Stop` with ranges outstanding** (kind 1: open PR moves to the reference)

- **What differs.** Reference: collects every answer, then sends `MsgClientDone`; a demotion that times out closes the connection. gOuroboros: main: gives up after 250 ms without `MsgClientDone` and allows `Start`, so a late reply reaches the new run; PR: abandons only when owed, latches, stops the muxer.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, block-fetch transition table, line 1194: "StIdle & MsgClientDone & & StDone"
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/lib/Ouroboros/Network/BlockFetch/Client.hs` 181-188 (`senderTerminate (Succ n) = Collect ...`, `Zero = Yield MsgClientDone`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/blockfetch/client.go` 473, 514-519; PR #3114 head `395b9c2e7` same file 507-547
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3114 (chain-sync's identical defect was fixed by merged #3092)

### N16

**Block-fetch `RangeDoneFunc` for a request that was never sent** (kind 1: open PR moves to the reference)

- **What differs.** Reference: a request's receiver exists only once the request is sent. gOuroboros: main: the shutdown drain calls `RangeDoneFunc` for a request whose `RequestRange` returned an error; PR: not.
- **Spec.** spec silent
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/BlockFetch/Client.hs` (a receiver per pipelined request)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/blockfetch/client.go` 1238; PR #3114 head `d10daf24` same file 140-147 (`sending`), 1116-1140 (a refused request leaves the queue before the send token is handed back; at `395b9c2e7` the token was released first, so a concurrent range's answers could reach the stale entry: review finding, model `blockfetch` `BlockFetchQueueSendFailsEarlyTokenBug.cfg`)
- **Verdict.** conforms
- **Status.** Open PR #3114 at `d10daf24`. Library defect; Dingo works around it

### N17

**Block-fetch `StBusy` timeout default** (kind 1: open PR moves to the reference)

- **What differs.** Reference: 60 s. gOuroboros: main: `NewConfig` sets `BatchStartTimeout` 5 s; PR: 60 s.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, block-fetch "Timeouts per state", line 1235: "`StBusy` & 60s"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/BlockFetch/Codec.hs` 54; `.../Protocol/Limits.hs` 116-117 (`longWait = Just 60`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/blockfetch/blockfetch.go` 282; PR #3114 head `395b9c2e7` same file 229, 287
- **Verdict.** conforms (stricter) → conforms
- **Status.** Open PR #3114 (Dingo already sets 60 s)

### N18

**Block-fetch size limit in `StBusy` (and `StIdle` for a pipelining client)** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: 65,535 bytes. gOuroboros: 2,500,000 bytes, because a `MsgBlock` that arrives early is judged against `StBusy`.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, block-fetch "Size limits per state", lines 1216-1217: table: `StIdle` 65535, `StBusy` 65535
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/BlockFetch/Codec.hs` 42-43 (`smallByteLimit`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/blockfetch/blockfetch.go` 73, 185 (`BusyMaxPendingMessageBytes = StreamingMaxPendingMessageBytes`)
- **Verdict.** does not conform
- **Status.** Not fixed; needed by gOuroboros' engine, which judges a message against the state current when it arrives

### N19

**Block-fetch `RangeTimeout`** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: none. gOuroboros: a whole range must finish within about 36 hours by default.
- **Spec.** spec silent
- **Reference.** none
- **gOuroboros.** gOuroboros `d0b95845` `protocol/blockfetch/blockfetch.go` 144-146, 210
- **Verdict.** conforms (implementation choice)
- **Status.** gOuroboros addition. Local only: it ends the caller's wait and sends nothing

### N20

**Tx-submission blocking and non-blocking request rules** (kind 1: open PR moves to the reference)

- **What differs.** Reference: client throws `ProtocolErrorRequestBlocking`, `RequestNonBlocking`, `RequestedNothing`; server picks the style from its FIFO. gOuroboros: main: the client does not check; `Server.RequestTxIds` lets the caller pick either style; PR: both enforced.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, tx-submission, lines 1336-1338 and 1554-1555: "Either the numbers acknowledged or the number requested MUST be non-zero." / "If the FIFO is empty, the consumer must use a blocking request; otherwise, it must be a non-blocking request."
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs` 178-185
- **gOuroboros.** gOuroboros `d0b95845` `protocol/txsubmission/client.go` 293, `server.go` 148; PR #3128 head `7e0a7d1c3` `validation.go` 71-102
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3128 (Dingo always sends blocking requests for at least one id)

### N21

**Tx-submission request over the window from `NodeToNodeV_16`** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: from V16 the client clamps the reply to its own window. gOuroboros: always a protocol error.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Maximum number of unacknowledged transaction identifiers", lines 1464-1470: "Requesting more transaction ids than the client's limit allows is not a protocol error: the client replies with at most as many transaction ids as fit within its limit."
- **Reference.** ouroboros-network `5f356486ab3e` `.../TxSubmission/Outbound.hs` 95-104 (`TxOutboundV_2`), 150 (`reqNo0 \`min\` maxReqNo`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/txsubmission/client.go` 331-339
- **Verdict.** does not conform
- **Status.** Fixed in PR #3195, head `8f6c6d5b`; model `txsubmission` `TxSubmissionV16ClampBug.cfg` reproduces main. Default windows (10 each side) never trigger it. Review: the first draft `4b7d5262` clamped a blocking request on a full window to zero and sent an empty blocking reply (`TxSubmissionV16ClampBlockingBug.cfg`); `8f6c6d5b` refuses a blocking request for nothing or with ids left before clamping, as `Outbound.hs` 182-185 does. A non-blocking request clamped to zero gets an empty reply, as the reference does (`ProbeNoZeroClamp`)

### N22

**Tx-submission duplicate ids in one reply** (kind 2: differs; both within the spec)

- **What differs.** Reference: not checked. gOuroboros: refused.
- **Spec.** spec silent
- **Reference.** ouroboros-network `5f356486ab3e` `.../TxSubmission/Outbound.hs` (no duplicate check)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/txsubmission/validation.go` 248
- **Verdict.** conforms (stricter)
- **Status.** Recorded; a reference peer never sends duplicates

### N23

**Peer-sharing: how many peers the server sends** (kind 2: differs; both within the spec)

- **What differs.** Reference: `min(10, amount)`. gOuroboros: `min(amount, 230)`.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, peer-sharing messages, lines 1699-1702: "It is a protocol error to send more peers than it was requested."
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/lib/Ouroboros/Network/PeerSharing.hs` 173-174 (`ps_POLICY_PEER_SHARE_MAX_PEERS = 10`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/peersharing/peersharing.go` 87 (`MaxSharedPeers = 230`)
- **Verdict.** conforms (implementation choice)
- **Status.** Policy choice

### N24

**Peer-sharing request when peer sharing was negotiated off** (kind 2: differs; both within the spec)

- **What differs.** Reference: mini-protocol not registered; a segment for it is `UnknownMiniProtocol` and tears the connection down. gOuroboros: answers an empty list.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Client Implementation Details" (peer-sharing), lines 1770-1771: "This peer won't even have the Peer-Sharing miniprotocol server running."
- **Reference.** ouroboros-network `5f356486ab3e` `network-mux/src/Network/Mux/Ingress.hs` 126
- **gOuroboros.** gOuroboros `d0b95845` `protocol/peersharing/server.go` 122-134
- **Verdict.** conforms (implementation choice)
- **Status.** Deliberate (documented in the package)

### N25

**Peer-sharing address forms** (kind 2: differs; both within the spec)

- **What differs.** Reference: an IPv4-mapped IPv6 address is sent as IPv6; the old eight-field IPv6 form is not decoded; declared list length ignored. gOuroboros: IPv4-mapped sent as IPv4 (`net.IP.To4`); old form accepted on decode; list length checked.
- **Spec.** ouroboros-network `5f356486ab3e` `cardano-diffusion/protocols/cddl/specs/peer-sharing-v14.cddl`: IPv4 `[0, word32, port]`, IPv6 `[1, word32, word32, word32, word32, port]`
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/api/lib/Ouroboros/Network/PeerSelection/PeerSharing/Codec.hs` (`encodeRemoteAddress`, `decodeRemoteAddress`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/peersharing/messages.go` 122
- **Verdict.** conforms
- **Status.** Recorded (model `peersharing`); same endpoint on a dual-stack host

### N26

**Local-tx-monitor: re-acquire (`MsgAwaitAcquire`) is timed** (kind 1: open PR moves to the reference)

- **What differs.** Reference: the node holds the answer until the mempool changes. gOuroboros: main: the client times it at 5 s, so it dies against a real node; PR: not timed (acquire from `Idle` still is).
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, local tx-monitor, lines 2112-2113 and 2172-2174: "[MsgAwaitAcquire] Like 'MsgAcquire' but await a new snapshot different from the one currently acquired." / "No timeouts."
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/LocalTxMonitor/Server.hs` 85 (`recvMsgAwaitAcquire`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localtxmonitor/localtxmonitor.go` 205; PR #3154 head `615e2a84` same file 69-73, 147-149, and `client.go` `Stop`, which ends a call waiting for the server rather than waiting for its answer under `busyMutex` (at `e9996ade` a `Stop` during an await waited forever)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3154 (head `615e2a84`). Model: `specs/localtx/LocalTxMonitorStopWaitBug.cfg` (`StopNeverWaitsOnPeer`)

### N27

**Local-tx-monitor server answers `MsgAwaitAcquire` at once** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: waits until the snapshot differs. gOuroboros: answers immediately with the current snapshot.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, local tx-monitor messages, lines 2112-2113: "await a new snapshot different from the one currently acquired"
- **Reference.** ouroboros-consensus `ec239d57f618` `.../MiniProtocol/LocalTxMonitor/Server.hs` 85
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localtxmonitor/server.go` 83, 105-125
- **Verdict.** does not conform
- **Status.** Fixed opt-in on local branch `fix/localtxmonitor-await-acquire` (`c0ec388e`): `Config.AwaitMempoolFunc` gets the held snapshot and blocks until the mempool differs; unset, the server answers at once as before. The default should not change until the client stops timing an await (PR #3154), and only an application with a mempool-change signal can supply the function. Model: `specs/localtx/LocalTxMonitorFixed.cfg`. Published as PR #3196 (head `26f0e50a`); review found the awaited acquire times out against a default gOuroboros client, which `LocalTxMonitorTimeoutBug.cfg` already shows and PR #3154 fixes: merge PR #3154 first, then remove the zeroed `AcquireTimeout` from PR #3196's test helper

### N28

**Local-tx-monitor `MsgGetMeasures`** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: always decoded and answered. gOuroboros: not implemented; decoding fails and the connection is torn down.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, local tx-monitor, lines 2137-2138, 2160-2161: "[MsgGetMeasures] The client asks the server for information on the mempool's measures."
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/LocalTxMonitor/Codec.hs` 78
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localtxmonitor/messages.go` 28-39 (tags 0-10 only)
- **Verdict.** does not conform
- **Status.** Fixed on local branch `fix/localtxmonitor-get-measures` (`923a32dc`): both messages, `Client.GetMeasures`, and the server's answer, gated on `NodeToClientV_20` as the reference encoder is (`Codec.hs` 57, 78-86, 102-113). Model: `LocalTxMonitorOldNode.cfg`, `LocalTxMonitorOldNodeBug.cfg`

### N29

**Local-tx-monitor `Stop` while a snapshot is acquired** (kind 1: open PR moves to the reference)

- **What differs.** Reference: `MsgDone` only from `StIdle` (typed). gOuroboros: main: sends `MsgDone` from `Acquired`, an illegal message; PR: sends `MsgRelease` first.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, local tx-monitor transition table, line 2162: "StIdle & MsgDone & & StDone"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/LocalTxMonitor/Type.hs` (agency typing)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localtxmonitor/client.go` 99-110; PR #3088 head `0fcda55b0` same file 104-121
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3088 (by another contributor)

### N30

**Node-to-client default timeouts** (kind 1: open PR moves to the reference)

- **What differs.** Reference: no time limits in the node-to-client codecs. gOuroboros: main: local-state-query 5 s / 180 s, local-tx-monitor 5 s / 30 s, local-tx-submission 30 s; PRs: none by default.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Timeouts per state" for local tx-submission (1884-1886), local-state-query (2018-2020), local tx-monitor (2172-2174): "No timeouts."
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/LocalStateQuery/Type.hs` 55 (a comment, "There is a timeout in this state", that no codec enforces)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localstatequery/localstatequery.go` 185-186, `protocol/localtxmonitor/localtxmonitor.go` 205-206, `protocol/localtxsubmission/localtxsubmission.go` 114; PR #3159 head `c0a5ca9c3` (LSQ, monitor), PR #3140 head `641eff0a` `localtxsubmission.go` 113, with `client.go` `Stop` ending a held `SubmitTx` (at `18f07468` a `Stop` during a held submission waited under `busyMutex` for the node) and `TestClientBusyTimeout` checking the Busy timer a running client gets, by default and with `WithTimeout`
- **Verdict.** does not conform → conforms
- **Status.** Open PRs #3159 and #3140 (head `641eff0a`). Model: `specs/localtx/LocalTxSubmissionStopWaitBug.cfg` (`StopNeverWaitsOnPeer`)

A node holds `MsgSubmitTx` while its mempool is full, and a state query can be slow; a 30 s client timeout tears down a correct exchange.

### N31

**Local-state-query server after `MsgDone`** (kind 1: open PR moves to the reference)

- **What differs.** Reference: restarted by the inbound governor. gOuroboros: main: stays `Done`; a new run's `MsgAcquire` is never answered; PR: restarts.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/connection-manager.tex`, "Inbound side: the inbound governor", lines 492-496: "the server side of the mini-protocol should be restarted in its initial state in case the client wishes to use the protocol again later"
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs` 455-470 (`TrResponderRestarted`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localstatequery/server.go` 403-411; PR #3113 head `566b18c0e` same file 445-458 (`StopForRestart`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3113

### N32

**Other servers that do not restart after `MsgDone`** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: every responder is restarted. gOuroboros: local-tx-monitor, local-tx-submission, message submission, local message submission, local message notification and Peras votes stay done.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/connection-manager.tex`, lines 492-496: "should be restarted in its initial state"
- **Reference.** ouroboros-network `5f356486ab3e` `.../InboundGovernor.hs` 455-470
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localtxmonitor/server.go` 164-172, `protocol/localtxsubmission/server.go` 112-120, `protocol/messagesubmission/server.go` 511-520, `protocol/localmessagesubmission/server.go` 315-324 (log only); Peras `protocol/perasvotes/server.go` 59
- **Verdict.** does not conform
- **Status.** Fixed on local branches `fix/<protocol>-server-restart`, one per server (local-tx-monitor `885a5991`, local-tx-submission `1086fdb1`; the DMQ and Peras servers on their own branches). Keep-alive, chain-sync, block-fetch, tx-submission, peer-sharing and the three Leios servers do restart on main. Model invariant `NewRunServed` in `specs/localtx` Published together as PR #3197 (head `c107bb53`). Review: the first draft (`656bbcea`) let `WaitForMessage` in local message notification select on the run's stop channel, so every `MsgClientDone` ended an application wait with a shutdown error; `c107bb53` watches only `Stop` and the connection there (the in-run blocking request still watches its run). Model `specs/dmq` `LocalMessageNotificationRestartWaitBug.cfg` / `AppWaitOutlivesRun`

### N33

**Local-state-query `Release` with nothing acquired** (kind 1: open PR moves to the reference)

- **What differs.** Reference: impossible by types. gOuroboros: main: sends `MsgRelease` from `Idle`, which tears the connection down; PR: returns `ErrNotAcquired`.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, local-state-query transition table, line 2007: "StAcquired & MsgRelease & & StIdle"
- **Reference.** ouroboros-network `5f356486ab3e` `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/LocalStateQuery/Client.hs`
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localstatequery/client.go` 210; PR #3113 head `566b18c0e` same file 219-220, 2152
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3113

### N34

**Local-state-query immutable-tip acquire below version 16** (kind 1: open PR moves to the reference)

- **What differs.** Reference: refuses to encode it. gOuroboros: main: sends it; PR: `ErrAcquireImmutableTipUnsupportedVersion`.
- **Spec.** spec silent: The protocol section lists acquire targets without version gating
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/LocalStateQuery/Codec.hs` 47, 89 (`MsgAcquire ImmutableTip` gated)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localstatequery/client.go` 194-205; PR #3113 head `566b18c0e` same file 201, 2112
- **Verdict.** conforms
- **Status.** Open PR #3113 (interoperability defect against old nodes)

### N35

**Local-state-query implicit acquire** (kind 1: open PR moves to the reference)

- **What differs.** Reference: no implicit acquire. gOuroboros: main: a query on an idle client acquires the volatile tip and never releases it, so later queries answer from a stale state; PR: released when the call returns.
- **Spec.** spec silent
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/LocalStateQuery/Client.hs` (one continuation per state)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localstatequery/client.go` 2157; PR #3113 head `566b18c0e` same file 2151-2171
- **Verdict.** conforms
- **Status.** Open PR #3113. Library defect (stale answers)

### N36

**Local-state-query server: `MsgRelease` without a `ReleaseFunc`** (kind 1: open PR moves to the reference)

- **What differs.** Reference: accepted. gOuroboros: main: an error that tears down a client that released; PR: accepted.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, line 2007: "StAcquired & MsgRelease & & StIdle"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/LocalStateQuery/Type.hs` (messages)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localstatequery/server.go` 345-351; PR #3113 head `566b18c0e` same file 388-392
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3113

### N37

**DMQ message submission wire format** (kind 1: open PR moves to the reference)

- **What differs.** Reference: dmq-node: V1 uses tx-submission's tags (Init = 6); V2 tags 1-6 with `MsgReplyNoSigIds` = 3; indefinite-length lists; in V2 the initiator runs the inbound side. gOuroboros: main: the CIP's tags, no `MsgReplyNoSigIds`, definite lists, V2 initiator is the outbound side (both sides wait); PR: dmq-node's.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` CDDL lines 146-150 (V2), 253-258 (V1); "Version differences" line 81: "msgRequestMessageIds = [1, ...] ... msgDone = [5, ]"; "In V2, the inbound side has agency in the StIdle state"
- **Reference.** dmq-node `a267003c14e9` `dmq-node/cddl/specs/sig-submission-v2.cddl` 23-28; `src/DMQ/Protocol/SigSubmissionV2/Codec.hs` 153 (`encodeListLenIndef`); `src/DMQ/NodeToNode.hs` 242-273 (initiator runs `sigSubmissionV2InboundPeerPipelined`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/messagesubmission/messages.go` 27-32; PR #3130 head `ffea36819` same file 29-46, 176; `messagesubmission.go` 182-184
- **Verdict.** conforms → does not conform (to the CIP text)
- **Status.** Open PR #3130 moves from the CIP to dmq-node, the only implementation; main cannot talk to dmq-node at all

The CIP is Proposed, not final, and dmq-node does not follow it. The PR chooses interoperability. Agency on V2 roles agrees with the CIP (the inbound side starts); the tags and list encoding do not. Decision recorded in the closing list.

### N38

**DMQ: the same message body requested twice** (kind 1: open PR moves to the reference)

- **What differs.** Reference: v2 refuses a repeat across requests; V1 only within one request. gOuroboros: main: served twice; PR: refused as the reference does per version.
- **Spec.** spec silent
- **Reference.** dmq-node `a267003c14e9` `src/DMQ/Protocol/SigSubmissionV2/Type.hs` 168 ("at most once"), `src/DMQ/SigSubmissionV2/Outbound.hs` 211 (`ProtocolErrorDuplicateRequest`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/messagesubmission/client.go`; PR #3130 head `ffea36819`
- **Verdict.** conforms
- **Status.** Open PR #3130

### N39

**DMQ time limits** (kind 2: differs; both within the spec)

- **What differs.** Reference: v1: blocking none, non-blocking and bodies 10 s; V2: blocking 20 s; local servers run without limits. gOuroboros: message submission: `StIdle` 300 s, blocking 30 s, non-blocking none, bodies 30 s; local submission: server drops a client idle 300 s.
- **Spec.** spec silent (CIP-0137 gives no time limits)
- **Reference.** dmq-node `a267003c14e9` `src/DMQ/Protocol/SigSubmission/Codec.hs` 73-77
- **gOuroboros.** gOuroboros `d0b95845` `protocol/messagesubmission/messagesubmission.go` 36-41; `protocol/localmessagesubmission/localmessagesubmission.go` 39-40
- **Verdict.** conforms (implementation choice)
- **Status.** Recorded (model `dmq`)

### N40

**DMQ local notification: empty reply to a blocking request** (kind 1: open PR moves to the reference)

- **What differs.** Reference: the codec refuses it. gOuroboros: main: accepted; PR: refused.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` local message notification CDDL, line 720: "msgReplyMessagesBlocking = [2, [+ message]]"
- **Reference.** dmq-node `a267003c14e9` `src/DMQ/Protocol/LocalMsgNotification/Codec.hs` 143 ("empty list" fails)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localmessagenotification/client.go` 222; PR #3142 head `07238ab8e` same file 238
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3142

### N41

**DMQ local notification: lost wake-up** (kind 1: open PR moves to the reference)

- **What differs.** Reference: STM wait; every waiter sees a new message. gOuroboros: main: `AddMessage` wakes one waiter, so a blocking request can stay unanswered; PR: wakes every waiter.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` line 693: "In the blocking case, the reply is guaranteed to contain at least one message."
- **Reference.** dmq-node `a267003c14e9` `src/DMQ/NodeToClient/LocalMsgNotification.hs` 45-55 (STM-based server)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localmessagenotification/server.go` 96
- **Verdict.** conforms
- **Status.** Open PR #3142. Liveness defect, wire unaffected

### N42

**DMQ local protocols: `hasMore` and submission answers** (kind 2: differs; both within the spec)

- **What differs.** Reference: `hasMore` set per reply from a cap; each submission's answer goes to its own continuation. gOuroboros: `hasMore` always false (sends the whole queue); local-submission callbacks carry no message id.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` notification CDDL (`msgReplyMessagesNonBlocking = [1, [* message], hasMore]`): "msgReplyMessagesNonBlocking = [1, [* message], hasMore]"
- **Reference.** dmq-node `a267003c14e9` `src/DMQ/NodeToClient/LocalMsgNotification.hs` 45-55 (`maxMsgs`, `hasMore`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/localmessagenotification/server.go`, `protocol/localmessagesubmission/client.go`
- **Verdict.** conforms
- **Status.** Recorded; harmless at default sizes; API limitation

### N43

**LeiosNotify: request after `MsgQuit`, and `MsgCanceled` before `MsgQuit`** (kind 1: open PR moves to the reference)

- **What differs.** Reference: never requests after quit (`drainThePipe`); an early `MsgCanceled` throws. gOuroboros: main: `Stop` racing a refill can send a request after `MsgQuit`; an early `MsgCanceled` is ignored and the loop stalls; PR: both fixed.
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../MiniProtocol/LeiosNotify/Client.hs` 105 (`MsgCanceled -> throwIO ExnLeiosNotifyUnexpectedCancel`), 228 (`drainThePipe`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/leiosnotify/client.go` 95-97, 168, 215; PR #3160 head `ad0d48de` same file 34-38, 188, 235, and `Sync`, which checks `quitting` before the running loop so that `Sync` after `Stop` returns `ErrProtocolShuttingDown` even while the loop is still parked (at `cfa1edeb` it returned "notification loop is already running")
- **Verdict.** conforms
- **Status.** Open PR #3160 (head `ad0d48de`). Model: `specs/leios-peras/LeiosNotifySyncOrderBug.cfg` (`SyncAfterStopReportsShutdown`)

### N44

**LeiosVotes: next request pipelined while `Busy`** (kind 1: open PR moves to the reference)

- **What differs.** Reference: no reference implementation. gOuroboros: main: the server refuses it; PR: accepted.
- **Spec.** CIPs `db48da14bff1` `CIP-0164/README.md` lines 1449-1452 (status Proposed): "the protocols above should be combined with pipelining, meaning that the request for the next batch of responses should be sent before the previous batch has been delivered"
- **Reference.** none (no LeiosVotes in ouroboros-consensus `ec239d57f618`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/leiosvotes/leiosvotes.go` 85-98; PR #3160 head `cfa1edeb0` same file 91
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3160

### N45

**Leios limits and timeouts** (kind 2: differs; both within the spec)

- **What differs.** Reference: leiosNotify reply 1,536 bytes / 16 votes; LeiosFetch `Block` and `BlockTxs` 60 s. gOuroboros: leiosNotify 65,535 bytes / 1,000 votes; LeiosFetch block states untimed (the caller's context bounds them); LeiosVotes count 1-1,000.
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../MiniProtocol/LeiosNotify/Type.hs` 191, 201; `.../LeiosFetch/Type.hs` 243-245
- **gOuroboros.** gOuroboros `d0b95845` `protocol/leiosnotify/messages.go` 41, 45; `protocol/leiosfetch/client.go` 485-505; `protocol/leiosvotes/leiosvotes.go` 32
- **Verdict.** conforms (implementation choice)
- **Status.** Recorded (model `leios-peras`)

### N46

**LeiosFetch extra messages (tags 10-14)** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: only `Block` and `BlockTxs` (tags 0-4). gOuroboros: adds votes and block-range requests.
- **Spec.** CIPs `db48da14bff1` `CIP-0164/README.md` lines 1539-1548 (message table): `MsgLeiosMultiBlockRequest`, `MsgLeiosBlock`, `MsgLeiosNoMoreBlocks`
- **Reference.** ouroboros-consensus `ec239d57f618` `.../MiniProtocol/LeiosFetch/Type.hs`
- **gOuroboros.** gOuroboros `d0b95845` `protocol/leiosfetch/messages.go` 44-48
- **Verdict.** conforms (implementation choice)
- **Status.** gOuroboros extension. A reference peer never sends them; sent to a reference server they fail to decode, so only use them with peers that know them

### N47

**Peras votes (ObjectDiffusion): await, server idle, timeouts** (kind 1: open PR moves to the reference)

- **What differs.** Reference: `MsgServerIdle` [6], `MsgAwaitReply` [7], a `MustReply` state; client waits 10 s, then 60 s after await. gOuroboros: main: no await messages, no `MustReply`, one 5 s timeout; PR: as the reference, server awaits then replies or idles.
- **Spec.** ouroboros-network `5f356486ab3e` `cardano-diffusion/protocols/cddl/specs/object-diffusion.cddl` 27-28: "msgServerIdle = [6]" / "msgAwaitReply = [7]"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/ObjectDiffusion/Type.hs` 109, 281-282; `.../ObjectDiffusion/Codec.hs` 65-88
- **gOuroboros.** gOuroboros `d0b95845` `protocol/perasvotes/messages.go` 26-38, `perasvotes.go` 38; PR #3165 head `55c7cdf95` `messages.go` 39-44, `perasvotes.go` 40-50
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3165. The network spec itself only lists `NodeToNodeV_17` as "Experimental, support Peras mini-protocols" (line 2231)

## Consensus

### C1

**Which VRF tie-break applies across eras** (kind 2: differs; both within the spec)

- **What differs.** Reference: taken from the newer tip's era. gOuroboros: taken from the caller's `ProtocolMajor` (restricted from 9).
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus-protocol/.../Protocol/Praos/Common.hs` 116-174; `.../HardFork/Combinator/Protocol/ChainSel.hs` 38-45
- **gOuroboros.** gOuroboros `d0b95845` `consensus/selection.go` 63-68
- **Verdict.** conforms (implementation choice)
- **Status.** Recorded (model `consensus`); same answer within one era

### C2

**Adopting a fork deeper than k by density** (kind 3: gOuroboros follows the spec, the reference does not)

- **What differs.** Reference: never rolls back more than k: Genesis is implemented with the Limit on Eagerness (LoE) and the density disconnection governor (GDD). gOuroboros: `IsDeepFork` routes a fork deeper than k to `CompareWithDensity`, which can prefer it; no LoE or GDD.
- **Spec.** ouroboros-consensus `ec239d57f618` `docs/tech-reports/report/chapters/future/genesis.tex` lines 169-171 (the consensus report restating the Genesis paper's `maxvalid-bg`); Genesis paper (IACR ePrint 2018/378) unverified: "Unlike the Longest Chain rule, the Density rule does not impose a maximum rollback."
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Storage/ChainDB/Impl/ChainSel.hs` 927 (`trimToLoE`); `docs/tech-reports/report/chapters/storage/chainselection.tex` 93-97
- **gOuroboros.** gOuroboros `d0b95845` `consensus/selection.go` 25-45, 251 (`IsDeepFork`), 409 (`CompareWithDensity`)
- **Verdict.** conforms
- **Status.** Documented design. Follows the paper's rule; differs from the reference, which keeps Praos' k bound. A caller that adopts the result whole can roll back more than k

The ledger calls this `PreferCandidateWithDensity`; at `d0b95845` the entry point is `PraosChainSelector.CompareWithDensity`.

### C3

**A tip with no VRF output** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: cannot happen. gOuroboros: ranks below any tip with one.
- **Spec.** spec silent
- **Reference.** n/a
- **gOuroboros.** gOuroboros `d0b95845` `consensus/selection.go` 208-216
- **Verdict.** conforms
- **Status.** Unreachable from a valid header

### C4

**Shelley header after Origin (the first block)** (kind 1: open PR moves to the reference)

- **What differs.** Reference: block 0, any slot, predecessor `GenesisHash`. gOuroboros: main: `ValidateHeaderInput` cannot say "no previous header", so block 0 always fails; PR: `PrevIsOrigin`, with the predecessor absent or the zero hash (at `1bc529c6` any predecessor passed).
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex`, `prtlSeqChecks`, lines 1700-1711: "prtlSeqChecks lab bh = True if lab = Nothing; s_l < slot ∧ b_l + 1 = bn ∧ ph = bprev bhb otherwise"
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HeaderValidation.hs` (`expectedFirstBlockNo`, `UnexpectedBlockNo`)
- **gOuroboros.** gOuroboros `d0b95845` `consensus/validate.go` 284-292; PR #3111 head `64573df5` same file 121-125, 279, 315-325
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3111 at `64573df5`; model `consensus` `ShelleyEnvelope.tla`

### C5

**Byron header envelope: slot and block number** (kind 1: open PR moves to the reference)

- **What differs.** Reference: slot strictly later except a main block after an EBB; an EBB after a main block shares its number; first block number 0. gOuroboros: main: any main block or EBB may share its predecessor's slot; an EBB may take either number; the first block must be 1; PR: as the reference.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/byron/chain/formal-spec/byron-blockchain.tex`, "Permissive BFT Header Processing", line 582: "s > s_last"
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus-cardano/src/byron/Ouroboros/Consensus/Byron/Ledger/HeaderValidation.hs` 39-52
- **gOuroboros.** gOuroboros `d0b95845` `consensus/byron/validate.go` 112-113, 249, 284; PR #3111 head `1bc529c64` same file 93-96, 260-300. Review: at `094aeac6` an EBB predecessor passed as a `*ByronEpochBoundaryBlock` counted as a main block (reference: kind from `byronHeaderIsEBB`, `HeaderValidation.hs` 30-32); fixed at `b137d455` (model `consensus` `ByronEnvelope.tla`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3111 at `b137d455` (reverses an earlier deliberate relaxation; Dingo does not call this validator). An EBB is an epoch boundary block, a Byron block with no transactions that opens each epoch

### C6

**Genesis window anchor** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: one anchor, the LoE tip, shared by every candidate. gOuroboros: each fragment counts from its own intersection with our selection.
- **Spec.** ouroboros-consensus `ec239d57f618` `docs/tech-reports/report/chapters/future/genesis.tex` lines 153-157: "preferred ... if it is denser (contains more blocks) in a window of s slots anchored at the intersection between the two chains"
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Genesis/Governor.hs` 294-319 (`sharedCandidatePrefix`)
- **gOuroboros.** gOuroboros `d0b95845` `consensus/genesis/genesis.go` 172-174 (`Compare` uses each fragment's `BlockCountInWindow`)
- **Verdict.** does not conform
- **Status.** Not fixed; correct only if the caller anchors every fragment at one point (model `consensus-genesis`, `OwnAnchorBug`)

### C7

**Genesis: exact tie, and deciding before the window is complete** (kind 2: differs; both within the spec)

- **What differs.** Reference: both tied peers are dropped; a peer still sending is kept until it cannot win, and only when it offers more than k blocks. gOuroboros: a tie goes to the longer fragment, then the first; decides on the blocks received so far; no `offersMoreThanK` guard.
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Genesis/Governor.hs` 470-486
- **gOuroboros.** gOuroboros `d0b95845` `consensus/genesis/genesis.go` 172-198
- **Verdict.** conforms (implementation choice)
- **Status.** Recorded (model `consensus-genesis`). Safe only if the caller waits for the window to fill

### C8

**Genesis window count from `SimpleChainFragment`** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: exact header count. gOuroboros: estimated from the fragment's span (`float64`), with rounding errors.
- **Spec.** ouroboros-consensus `ec239d57f618` `docs/tech-reports/report/chapters/future/genesis.tex` lines 153-157: "denser (contains more blocks) in a window of s slots"
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Genesis/Governor.hs` 387-447
- **gOuroboros.** gOuroboros `d0b95845` `consensus/genesis/genesis.go` 270-282
- **Verdict.** does not conform
- **Status.** The float rounding is fixed on local branch `fix/genesis-window-estimate-rounding` (`74699bf6`, no PR); the estimate itself remains. Callers with real headers should implement `ChainFragment` with a count

### C9

**Genesis window size in Byron** (kind 3: gOuroboros follows the spec, the reference does not)

- **What differs.** Reference: 2k. gOuroboros: 3k/f, which is 3k with f = 1.
- **Spec.** ouroboros-consensus `ec239d57f618` `docs/tech-reports/report/chapters/future/genesis.tex` line 167: "The genesis window size s will be set to s = 3k/f."
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus-cardano/src/byron/Ouroboros/Consensus/Byron/Ledger/Ledger.hs` 338
- **gOuroboros.** gOuroboros `d0b95845` `consensus/genesis/genesis.go` 65 (`ComputeGenesisWindow`)
- **Verdict.** conforms
- **Status.** Recorded; nothing calls it for Byron

### C10

**Byron re-delegation to the delegate already active** (kind 1: open PR moves to the reference)

- **What differs.** Reference: no change. gOuroboros: main: rewrites the activation slot; the delegation map is the same; PR: no change (`delegateIsActive` includes the delegator's own entry).
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/formal-spec/delegation.tex` line 305: "vk_d ∈ range dms ∨ ..." (the no-change activation rule)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/impl/src/Cardano/Chain/Delegation/Validation/Activation.hs` 65-67 (`notMemberR`)
- **gOuroboros.** gOuroboros `d0b95845` `consensus/byron/pbft_delegation.go` 128-158; PR #3174 head `faad03cd` same file 355-380 (`activate`, `delegateIsActive`)
- **Verdict.** conforms
- **Status.** Open PR #3174 (model `ledger-byron`, `SlotsAgree`, `ByronDelegationOwnEntryBug.cfg`). Benign on main: the slot is read only by a check every later schedule passes

### C11

**Tachys leader schedule** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: none. gOuroboros: optional public leader schedule that replaces the private VRF lottery for issuer authorization (`NewTachysLeaderSelector`, `NewTachysHeaderValidator`).
- **Spec.** CIPs `db48da14bff1` `CIP-0177/README.md` (title "Ouroboros Tachys - Faster Cardano partner chains", status Proposed); gOuroboros pins revision `86b89208`, not checked here
- **Reference.** none
- **gOuroboros.** gOuroboros `d0b95845` `consensus/README.md` 88-107; `consensus/block.go` 41-60
- **Verdict.** conforms (implementation choice)
- **Status.** Opt-in, for partner chains. Not Praos: a Tachys header is not valid on a Praos network, and nothing selects it by default

### C12

**Rolling nonce from a raw 64-byte VRF output** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: the VRF output is hashed to a 32-byte nonce first (`mkNonceFromOutputVRF`), then combined. gOuroboros: `CalculateRollingNonce` accepts the 64-byte output and hashes `prev ‖ output` (96 bytes).
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/crypto-details.tex` lines 71-72; `chain.tex` 615 (`η_v ⭒ η`): "The seed operation x ⭒ y ... is implemented as the BLAKE2b-256 hash of the concatenation of x and y."
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/BaseTypes.hs` 615-619 (`mkNonceFromOutputVRF` hashes the output), 607-610 (`⭒`)
- **gOuroboros.** gOuroboros `d0b95845` `ledger/common/nonce.go` 115 (before); `756a9a89` `ledger/common/nonce.go` 96-156 (`NonceFromTPraosVRF`, `NonceFromPraosVRF`, `CombineNonces`, `CalculateRollingNonce` rejecting 64 bytes)
- **Verdict.** does not conform → conforms
- **Status.** Fixed by #3053 (merged, `756a9a89`). It reproduces the 15 chained mainnet Shelley vectors the model's Go test uses. The local branch `fix/ledger-nonce-raw-vrf-operand` is superseded. Dingo passes the 32-byte nonce, so it is unaffected

### C13

**The neutral nonce as an identity** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: `x ⭒ NeutralNonce = x` and `NeutralNonce ⭒ x = x`. gOuroboros: from a zero evolving nonce `CalculateRollingNonce` returned `blake2b(x)` (fixed by `CombineNonces`); `CalculateEpochNonce` hashes a zero (or rejects an empty) candidate or lab nonce. The branch adds `EpochNonceFromNonces(candidate, lab, extraEntropy common.Nonce)`, which is `CombineNonces` twice.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/crypto-primitives.tex`, "VRF definitions", line 258: "0_seed ∈ Seed   neutral seed element"
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/BaseTypes.hs` 611-612
- **gOuroboros.** gOuroboros `756a9a89` `ledger/common/nonce.go` 128 (`CombineNonces`: neutral identity on both sides), 188 (`CalculateEpochNonce`: no neutral input); branch `da43d778` `ledger/common/nonce.go` 188-194 (`EpochNonceFromNonces`)
- **Verdict.** does not conform (epoch nonce only) → conforms
- **Status.** Rolling part fixed by #3053 (merged, `756a9a89`). `CalculateEpochNonce` cannot take a neutral candidate or lab nonce, reached at the second tick after a chain's start; it is kept unchanged and deprecated. Fixed additively on local branch `fix/nonce-neutral-epoch-and-vrf-input` (`da43d778`), no PR yet, which supersedes `fix/ledger-nonce-neutral-identity` (`3284a9cb`). `EpochNonceNewByron` passes on the new function; `EpochNonceDirectLabBug` and `EpochNonceNewLabBug` fail. Dingo applies the identity by hand on the public networks (`ledger/extra_entropy.go` `assembleEpochNonce`) and can call `EpochNonceFromNonces` instead

### C14

**A neutral epoch nonce in the VRF input** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: appends nothing for a neutral η0. gOuroboros: `MkInputVrf` and `MkSeedTPraos` need 32 bytes, so a neutral η0 is passed as 32 zero bytes. The branch adds `MkInputVrfFromNonce`, `MkSeedTPraosFromNonce` and `ComputeVRFInputFromNonce`, which take a `common.Nonce` epoch nonce and append nothing for `NonceTypeNeutral`.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex` line 1036; `crypto-primitives.tex` line 258: "ucNonce XOR (slotToSeed slot ⭒ η_0)"
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/BaseTypes.hs` 611
- **gOuroboros.** gOuroboros `d0b95845` `vrf/vrf.go` 245, 327; branch `da43d778` `vrf/vrf.go` 278-292 (`MkInputVrfFromNonce`), 385-403 (`MkSeedTPraosFromNonce`), `consensus/block.go` 557 (`ComputeVRFInputFromNonce`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed additively on local branch `fix/nonce-neutral-epoch-and-vrf-input` (`da43d778`), no PR yet; the `[]byte` builders are kept and deprecated. `EpochNonceNewNeutral` passes; `EpochNonceVrfInputBug` and `EpochNonceNewVrfInputBug` fail. gOuroboros' own exported APIs that take a `[]byte` η0 (`IsSlotLeader*`, header validation, `VerifyBlock`) now call the new builders but still cannot express a neutral η0. Only a chain with a neutral initial nonce reaches it, in its first epoch

### C15

**TPraos overlay schedule (d > 0)** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: the slot at offset s is an overlay slot when ceiling(s·d) < ceiling((s+1)·d), active when its position is a multiple of floor(1/f), and then belongs to genesis key (position / floor(1/f)) mod |keys|; a non-active slot fails, an active one checks the delegate's cold key, VRF key and both proofs, with no stake. gOuroboros: main has no overlay inputs, so it rejects valid genesis-delegate headers and accepts pool headers in non-active slots; the branch requires `Overlay` and checks the schedule.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex` 1170-1192 (`isOverlaySlot`, `classifyOverlaySlot`), 1198-1274 (Active-OBFT, Decentralized), 1280-1305 (predicate failures)
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/Rules/Overlay.hs` 219-282, 314-344; `libs/cardano-ledger-core/src/Cardano/Ledger/Slot.hs` 117-130
- **gOuroboros.** gOuroboros `f9ba2d3c` `consensus/validate.go` (`ValidateHeader`, `ValidateHeaderInput`); branch `78f2f391` `consensus/overlay.go` (`classifyOverlaySlot`, `checkRequiredInputs`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/consensus-tpraos-overlay` (`78f2f391`), no PR yet. Breaking: every caller must now pass `Overlay` for TPraos headers. No production caller in gOuroboros or Dingo

### C16

**Header envelope: ObsoleteNode, header size, body size** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: the protocol major (the header's own in TPraos, the ledger view's in Praos) is at most the node's maximum, the header size at most `maxBlockHeaderSize`, the declared body size at most `maxBlockBodySize`. gOuroboros: main does not check them in `ValidateHeader`; the branch requires `Envelope` in every mode and returns `ErrMissingHeaderInput` alone when an input is missing.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex` 1682-1687 (`chainChecks`)
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Protocol/EnvelopeChecks.hs` 77-91; `Protocol/TPraos.hs` 69-80; `Protocol/Praos.hs` 82-106; cardano-ledger `eras/shelley/impl/src/Cardano/Ledger/Chain.hs` 65-82
- **gOuroboros.** gOuroboros `f9ba2d3c` `consensus/validate.go`; branch `78f2f391` `consensus/overlay.go` (`validateEnvelopeLimits`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on the same branch, no PR yet. `VerifyBlock` already checks the sizes from protocol parameters

### C17

**Byron slot to epoch past Byron** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: slot-to-epoch goes through the era history, each era with its own epoch size. gOuroboros: `ByronConfig.SlotToEpoch` uses `slot / SlotsPerEpoch` for any slot; the branch adds `EndSlot` (from the era history) and `SlotToEpochChecked`, which refuses a slot at or past it.
- **Spec.** ouroboros-consensus `ec239d57f618` `docs/tech-reports/report/chapters/hfc/time.tex` 142-177
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/History/Qry.hs` 366-378, 496-523
- **gOuroboros.** gOuroboros `f9ba2d3c` `consensus/byron/byron.go` (`SlotToEpoch`); branch `70d83369` same file (`SlotToEpochChecked`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/consensus-byron-slot-epoch` (`70d83369`), no PR yet. Only tests call it

## Ledger

### L1

**Pool registration when the caller's view is stale** (kind 1: open PR moves to the reference)

- **What differs.** Reference: registered means present in `psStakePools`, which POOLREAP clears at the epoch boundary. gOuroboros: main: trusts the caller's `IsPoolRegistered`, so a stale view lets a delegation to (or retirement of) a reaped pool through, and treats re-registering a reaped pool as a re-registration; PR: one epoch-aware predicate.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/delegation.tex` line 1137; `epoch.tex` POOLREAP 564-572: "c ∈ DCertDeleg ⇒ dpool c ∈ dom poolParams"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Deleg.hs` 329-331; `.../Rules/Pool.hs` 299
- **gOuroboros.** gOuroboros `d0b95845` `ledger/shelley/rules.go` 791, 1652; `ledger/common/block_state.go` 747-752; PR #3129 head `11c562279` `ledger/common/pool_deposit.go` 43 (`PoolRegistered`), `block_state.go` 163
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3129. Dingo's view already satisfies the contract

### L2

**Transaction id of a body without stored CBOR** (kind 1: open PR moves to the reference)

- **What differs.** Reference: a body always carries its serialization. gOuroboros: main: hashes empty input, the same id for every such body; PR: hashes the body's encoding. Review follow-up: a Dijkstra body with an empty, non-nil CIP-159 map (keys 24 to 27) failed to encode and fell back to the empty-input hash, so `{TxFee:5}` and `{TxFee:6}` collided again. The encoder now omits an empty map as the reference does, and a body that still cannot be encoded gets the zero id rather than a hash that looks real.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/crypto-details.tex`, "Abstract functions", lines 64-69: "txid ... is implemented as the BLAKE2b-256 hash of the CBOR serialization of the transaction body"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/TxBody.hs` 518-552 (`encodeTxBodyRaw`: `Omit` on an empty map at keys 24 to 27; the decoder refuses one, 449-452). Otherwise n/a: the reference keeps a decoded or built body's bytes with it, so this state cannot arise
- **gOuroboros.** gOuroboros `d0b95845` `ledger/common/tx.go` 719-721; PR #3141 head `236fdccd` same file 734 (`TransactionBodyId`), `ledger/dijkstra/dijkstra.go` (`validateDijkstra*ForEncoding`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3141. Decoded bodies were always right; bodies built in code were wrong. No TLA+ model: the id is a pure function of the body, with no state or interleaving to model, so Go tests cover it (`TestTransactionBodyIdHashesBodyEncoding`, `TestDijkstraBodyIdOmitsEmptyMaps`, `TestDijkstraSubTransactionBodyIdOmitsEmptyMaps`, `TestTransactionBodyIdOfUnencodableBodyIsZero`). The `AGENTS.md` and `CLAUDE.md` wording fix in the same PR cannot affect any model

### L3

**Conway CC vote with a nil voter key** (kind 1: open PR moves to the reference)

- **What differs.** Reference: not representable. gOuroboros: main: `UtxoValidateCCVotingRestrictions` panics; PR: skips it as the sibling rules do.
- **Spec.** spec silent
- **Reference.** n/a
- **gOuroboros.** gOuroboros `d0b95845` `ledger/conway/rules.go` 4663-4666; PR #3155 head `b5294771` same file 4666
- **Verdict.** conforms
- **Status.** Open PR #3155. Library defect, hand-built transactions only

### L4

**BadInputs covers only spent inputs** (kind 2: differs; both within the spec)

- **What differs.** Reference: alonzo: spent and collateral inputs; Babbage: reference inputs too. gOuroboros: main: spent inputs only; missing collateral and reference inputs are caught by the witness rules instead; PR: the reference's set, and BadInputs runs first so a missing input is reported as BadInputs.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/alonzo/formal-spec/utxo.tex` line 644: "txins txb ∪ collateral txb ⊆ dom utxo"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxo.hs` 540
- **gOuroboros.** gOuroboros `d0b95845` `ledger/shelley/rules.go` 270, `ledger/alonzo/rules.go` 740, `ledger/babbage/rules.go` 724; PR #3193 head `efd0b081` `ledger/shelley/rules.go` `ValidateBadInputs`, and the rule lists in `ledger/{alonzo,babbage,conway,dijkstra}/rules.go`
- **Verdict.** conforms
- **Status.** Open PR #3193 at `efd0b081`. Same accept/reject on every modelled cell (model `ledger-utxo`); the failure is now BadInputs, as in the reference

### L5

**Byron transaction with no inputs or no outputs** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: cannot be decoded (`NonEmpty`). gOuroboros: main: accepted; a no-input, zero-output transaction pays no fee (it counts as redeem-only).
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/formal-spec/utxo.tex`, UTXO rule, lines 193-194: "txins tx ≠ ∅   txouts tx ≠ ∅"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/impl/src/Cardano/Chain/UTxO/Tx.hs` 56-58
- **gOuroboros.** gOuroboros `d0b95845` `ledger/byron/byron.go` 780; local branch `fix/ledger-byron-nonempty-tx` (`5eec6b76`) same file 792-797
- **Verdict.** does not conform
- **Status.** Fixed on a local branch, no PR yet

### L6

**Byron `maxTxSize`** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: `TxValidationTxTooLarge`. gOuroboros: no check anywhere.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/formal-spec/utxo.tex`, UTXOW rule, line 339: "maxTxSize ↦ t ∈ pps   txSize tx ≤ t"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/impl/src/Cardano/Chain/UTxO/Validation.hs` 193
- **gOuroboros.** gOuroboros `d0b95845` `ledger/byron/byron.go` 780-890 (`ValidateAgainstUtxo`, no size parameter)
- **Verdict.** does not conform
- **Status.** Open, no branch. Adding it changes the API (`VerifyConfig` or `ValidateAgainstUtxo`)

### L7

**Byron minimum fee rounding** (kind 3: gOuroboros follows the spec, the reference does not)

- **What differs.** Reference: summand rounded to a whole lovelace when decoded, then the per-byte part rounded up. gOuroboros: the whole sum rounded up.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/formal-spec/utxo.tex` lines 127-128, 192: "minfee pps tx = a pps + b pps * txSize tx"; "minfee pps tx ≤ fee"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/impl/src/Cardano/Chain/Common/TxSizeLinear.hs` 73 (`round`), 83-86 (`scaleLovelaceRationalUp` on b only)
- **gOuroboros.** gOuroboros `d0b95845` `ledger/common/verify_config.go` 197-207
- **Verdict.** conforms
- **Status.** Since the fee is a whole number, rounding the sum up is exactly the spec's check; the reference can accept a fee half a lovelace short. Differs only for a fractional summand, which no network has

### L8

**Byron repeated inputs and witness counts** (kind 3: gOuroboros follows the spec, the reference does not)

- **What differs.** Reference: a repeated input is counted once; witnesses are zipped with inputs, so a short list leaves inputs unchecked. gOuroboros: repeated input rejected; witness count must equal input count.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/formal-spec/utxo.tex` lines 107-109 (`txins ∈ Tx → ℙ TxIn`), 340-343 (UTXOW): "∀ i ∈ txins tx · ∃ (vk, σ) ∈ wits tx · V_vk⟦txbody tx⟧_σ ∧ addr_h utxo i = hash vk"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/byron/ledger/impl/src/Cardano/Chain/UTxO/Validation.hs` 389 (`zip addresses (V.toList witness)`)
- **gOuroboros.** gOuroboros `d0b95845` `ledger/byron/byron.go` 793 (count), 804 (duplicate)
- **Verdict.** conforms (stricter)
- **Status.** Deliberate. Stricter than the spec only for extra witnesses, which the spec allows

### L9

**Leios committee with fewer pools than `Nc`** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: `min(Nc, pools)` seats; the bitfield is sized by the seated committee. gOuroboros: requires exactly `Nc` seats, so every valid certificate from a small committee is refused.
- **Spec.** CIPs `db48da14bff1` `CIP-0164/README.md`, "Epoch Boundary", lines 1152-1153 (status Proposed): "Take the first N_c pools, or all of them if fewer than N_c are registered."
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/State/Leios.hs` 108 (`size = min ... committeeSize ... (V.length candidates)`)
- **gOuroboros.** gOuroboros `d0b95845` `ledger/leios/certificate.go` 121
- **Verdict.** does not conform
- **Status.** Fixed on local branch `fix/leios-committee-size` (`fec72765`), no PR yet. Hits the prototype testnet (committee size 900)

### L10

**Leios certificate in a later epoch than its announcement** (kind 2: differs; both within the spec)

- **What differs.** Reference: cardano-ledger refuses it (`LeiosCertAnnouncedInPreviousEpoch`); the consensus prototype does not check. gOuroboros: not checked.
- **Spec.** spec silent (CIP-0164 sizes the bitfield by the announcing epoch but states no rule)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/LeiosCert.hs` 59
- **gOuroboros.** gOuroboros `d0b95845` `ledger/dijkstra/leios_header.go` (`ValidateLeiosCertificateTiming`)
- **Verdict.** conforms
- **Status.** Recorded (model `ledger-leios`)

### L11

**Node-to-client CertRB with inlined EB transactions** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: none. gOuroboros: accepts a certifying block whose endorser-block transactions are inlined, over node-to-client only.
- **Spec.** spec silent on node-to-client delivery
- **Reference.** n/a
- **gOuroboros.** gOuroboros `d0b95845` `ledger/dijkstra/leios_header.go` 170-172; `ledger/dijkstra/dijkstra.go` 2571 (`OnChainBlockBodyCbor` strips them)
- **Verdict.** conforms
- **Status.** Local delivery only; the on-chain body is unchanged

### L12

**CBOR nesting limit** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: no nesting limit. gOuroboros: 16,384 levels for blocks and ledger data; 1,024 for peer messages.
- **Spec.** spec silent
- **Reference.** n/a
- **gOuroboros.** gOuroboros `d0b95845` `cbor/decode.go` 70, 72-74
- **Verdict.** conforms
- **Status.** Just above what a 16,384-byte transaction can nest; raising `maxTxSize` would let a valid transaction nest deeper than gOuroboros accepts

### L13

**Conway vote naming an enacted purpose root** (kind 1: open PR moves to the reference)

- **What differs.** Reference: refused (`GovActionsDoNotExist`). gOuroboros: main: `UtxoValidateUnknownGovActionIds` accepts any id `GovActionExists` finds, and the contract let a state answer for a purpose's current root; PR: the contract excludes the root, and the hard-fork check reads it from `GovPurposeRoots`.
- **Spec.** formal-ledger-specifications `60b68036c8b4` `src/Ledger/Conway/Specification/Gov.lagda.md` 503-509 (a vote names an action in the governance state)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/conway/impl/src/Cardano/Ledger/Conway/Rules/Gov.hs` 361-362 (`checkVotesAreValid` over `proposalsActionsMap`)
- **gOuroboros.** gOuroboros `d0b95845` `ledger/common/state.go` 519-520, `ledger/conway/rules.go` `UtxoValidateUnknownGovActionIds`; PR #3155 head `b5294771` `ledger/common/state.go` 525-533, `ledger/conway/rules.go` 1152, 4183
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3155. Model `ledger-governance` `VotesOnlyLive`, `GovLifecycleRootVoteBug.cfg`. Dingo 2fc7975d `ledger/view.go` 2680-2692 returns the root and must drop that exception

## Pipeline

### P1

**An invalid block in the pipeline** (kind 2: differs; both within the spec)

- **What differs.** Reference: chainDB records it, ignores it and its successors, and carries on. gOuroboros: the pipeline stops (fatal).
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Storage/ChainDB/Impl/ChainSel.hs` 1487-1495 (`addInvalidBlock`)
- **gOuroboros.** gOuroboros `d0b95845` `pipeline/apply_stage.go` 190
- **Verdict.** conforms (implementation choice)
- **Status.** Documented in chain-sync's `Config.Pipeline`

### P2

**Closing with blocks queued** (kind 2: differs; both within the spec)

- **What differs.** Reference: every queued block is answered `FailedToAddBlock`. gOuroboros: dropped; a waiting `Fence` gets `ErrPipelineStopped`.
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Storage/ChainDB/Impl/Types.hs` 786-798 (`closeChainSelQueue`)
- **gOuroboros.** gOuroboros `d0b95845` `pipeline/pipeline.go` 958 (`Stop`)
- **Verdict.** conforms (implementation choice)
- **Status.** Recorded (model `pipeline-cbor`)

### P3

**`WaitForDrain` during `Stop`** (kind 1: open PR moves to the reference)

- **What differs.** Reference: rollback is part of chain selection, serialised with adds. gOuroboros: main: returns once `Stop` begins while a block may still commit after the caller's rollback; PR: waits for the apply runner.
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Storage/ChainDB/Impl/Background.hs` 127 (`addBlockRunner`)
- **gOuroboros.** gOuroboros `d0b95845` `pipeline/pipeline.go` 1071; PR #3161 head `805d32abd` same file 1117
- **Verdict.** conforms
- **Status.** Open PR #3161. Library defect; not reached through chain-sync or Dingo today

### P4

**An unread `Results` channel** (kind 1: open PR moves to the reference)

- **What differs.** Reference: chain selection never waits on a follower. gOuroboros: main: stalls the apply runner; PR: never blocks commits, drops the oldest result for a reader that falls behind (counted in `ResultsDropped`).
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Storage/ChainDB/Impl/Background.hs` 127 (`addBlockRunner`; followers read the chain themselves)
- **gOuroboros.** gOuroboros `d0b95845` `pipeline/pipeline.go` 701; PR #3161 head `805d32abd` same file 1006-1010
- **Verdict.** conforms
- **Status.** Open PR #3161

### P5

**`WithLosslessResults`** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: none. gOuroboros: opt-in with an `ApplyFunc`; always on in header-only and trusted decode-only modes, whose only output is `Results`: every committed block is delivered and commits wait for the reader. At PR head `805d32abd` decode-only modes dropped results unless the caller opted in (review finding; model `pipeline-cbor` `BlockPipelineDecodeOnlyDropBug.cfg`).
- **Spec.** spec silent
- **Reference.** n/a
- **gOuroboros.** PR #3161 head `0dbc3775` `pipeline/pipeline.go` (`Start`, `losslessResults`), `pipeline/options.go` (`LosslessResults`, `WithLosslessResults`)
- **Verdict.** conforms (implementation choice)
- **Status.** On PR #3161 at `0dbc3775` (decode-only modes lossless by default; Dingo's trusted decode-only opt-in is now redundant). Wire: a slower commit only delays chain-sync's next request, which the protocol allows; ledger: unchanged

## Library boundary: contracts, not drift

gOuroboros keeps no ledger state. These rules exist in the spec and the reference, and gOuroboros leaves them to its caller. Each is a contract the caller must meet, not a difference in gOuroboros' own behaviour. Verdict for each: n/a (library contract).

- **Epoch boundary**: POOLREAP (retiring pools), SNAP (stake snapshots) and applying the reward update (`eras/shelley/formal-spec/epoch.tex`, POOLREAP at lines 564-572). gOuroboros computes rewards from a caller-supplied `RewardSnapshot` (`ledger/common/rewards.go`).
- **Pool registration view**: `LedgerState.PoolCurrentState` and `IsPoolRegistered` must reflect POOLREAP (L1).
- **Leader snapshot**: `LeaderPoolVrfKeyHash` must read the active ("set") snapshot, not current registration (`ledger/common/verify_config.go`).
- **Conway governance**: ratification, enactment, proposal removal, deposit refunds, DRep and committee expiry. The GOV rules rely on `GovActionById` returning the proposals in the governance state and on `GovActionState.ExpirySlot` (`ledger/common/state.go` 467, 520) being the last slot of epoch `expiresAfter`, matching the spec's `¬ expired` premise (formal-ledger-specifications `60b68036c8b4`, `src/Ledger/Conway/Specification/Gov.lagda.md` 503-507). PR #3155 documents this contract, including that the current purpose root is not returned (L13).
- **UTxO and fees**: the caller supplies the UTxO view and, for Byron, the fee policy; it keeps the fee and deposit pots (model `ledger-utxo`).
- **Byron update mechanism**: gOuroboros checks proposals and votes only statelessly (`ledger/byron/payload.go`); registration, vote tally, confirmation, endorsement and adoption are the caller's.
- **Byron heavyweight delegation**: `ApplyPayloadCbor` must be called once per main block, in slot order, keeping the result only if the block is adopted (`consensus/byron/pbft_delegation.go`).
- **Chain selection**: `PreferCandidate` does not enforce k; the caller must offer only candidates within k for Praos. For Genesis the caller must anchor fragments at one point, wait for windows to fill, and decide when to use the density rule (`ShouldUseGenesis` is a threshold it applies); see C2, C6, C7.
- **Leios**: applying an endorser block, checking it against the announced hash and size, applying it at most once, and rollback (model `ledger-leios`); the caller supplies the seated committee.
- **Peer trust**: whether a chain-sync peer is trusted (N8).
- **Epoch nonce**: holding the evolving, candidate and lab nonces, ticking and freezing (strict `<` with the era's window), deriving each block's 32-byte nonce, and restoring the state on rollback (model `consensus-nonce`). The spec takes the lab nonce from the previous epoch's last block's own hash (cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex` line 478: "seed generated from hash of previous epoch's last block header"); the reference and the network use that block's predecessor hash. `CalculateEpochNonce`'s `prevEpochFirstBlockHash` names neither, so the caller must pass the reference's value.
- **Mempool change signal** for a local-tx-monitor server that awaits (N27).

## Where the spec and the reference disagree and gOuroboros follows the reference

Not drift, since gOuroboros matches the reference, but worth knowing. Details and citations are in the model READMEs named.

- Chain-sync is pipelined by the reference and gOuroboros; the spec says "pipelining is used by the clients of all mini-protocols except Chain-Sync" (`miniprotocols.tex` line 2185). Models `engine` and `chainsync`.
- The local tx-monitor table lists `MsgReplyNextTx` for `StBusy HasTx` (`miniprotocols.tex` line 2157), a typo for `MsgReplyHasTx`. Model `localtx`.
- Byron zero-valued outputs and the redeem-only fee exemption, and Mary's token-exempt output minimum. Models `ledger-utxo` and `ledger-byron`.
- A deregistration refunds the deposit recorded at registration, not the current `keyDeposit`. Model `ledger-shelley`.
- Conway bootstrap rules: the return account is not checked in protocol version 9, and committee voters must be in the enacted committee only from version 11. Model `ledger-governance`.
- Endorser-block encoding: a bare map with `uint32` sizes (the node) instead of the CIP's array around an ordered map. Model `ledger-leios`.
- Message submission window rules (a non-blocking request may ask for 0 ids if it acknowledges some) and empty `MsgRequestMessages`. Model `dmq`.

## Resolved since the models were written

- Keep-alive server restart after `MsgDone` (merged #3080), and the shutdown race in every restarting server (merged #3087).
- Chain-sync `Stop` without `MsgDone` (merged #3092, now on `main`).

## Does not conform: needs a decision

Entries where gOuroboros on `main` breaks a stated rule, with what would close each one.

No pull request yet (decide whether and how to fix):

- **N13** Handshake `MsgAcceptVersion` carries the server's own data. Fixed on local branch `fix/handshake-accept-negotiated-data`.
- **N14** Handshake version keys out of order. Fixed on local branch `fix/handshake-version-key-order`.
- **N18** Block-fetch size limit in `StBusy` (and `StIdle` for a pipelining client). Not fixed; needed by gOuroboros' engine, which judges a message against the state current when it arrives.
- **N21** Tx-submission request over the window from `NodeToNodeV_16`. Fixed in PR #3195 (head `8f6c6d5b`).
- **N27** Local-tx-monitor server answers `MsgAwaitAcquire` at once. Opt-in fix in PR #3196 (head `26f0e50a`), which depends on PR #3154 for the client side.
- **N28** Local-tx-monitor `MsgGetMeasures`. Not fixed; a missing feature.
- **N32** Other servers that do not restart after `MsgDone`. Fixed in PR #3197 (head `c107bb53`). Keep-alive, chain-sync, block-fetch, tx-submission, peer-sharing and the three Leios servers do restart on main.
- **C6** Genesis window anchor. Not fixed; correct only if the caller anchors every fragment at one point (model `consensus-genesis`, `OwnAnchorBug`).
- **C8** Genesis window count from `SimpleChainFragment`. The float rounding is fixed on local branch `fix/genesis-window-estimate-rounding` (`74699bf6`, no PR); the estimate itself remains. Callers with real headers should implement `ChainFragment` with a count.
- **C13** The neutral nonce as an identity in the epoch nonce (the rolling part is fixed by #3053). Fixed additively on local branch `fix/nonce-neutral-epoch-and-vrf-input` (`da43d778`), no PR yet: `EpochNonceFromNonces`, `CalculateEpochNonce` deprecated.
- **C14** A neutral epoch nonce in the VRF input. Fixed additively on the same branch, no PR yet: `MkInputVrfFromNonce`, `MkSeedTPraosFromNonce`, `ComputeVRFInputFromNonce`, the `[]byte` builders deprecated. Only a chain with a neutral initial nonce reaches it, in its first epoch.
- **C15** TPraos overlay schedule. Fixed on local branch `fix/consensus-tpraos-overlay` (`78f2f391`), no PR yet; breaking for callers, which must now pass `Overlay`.
- **C16** Header envelope checks. Fixed on the same branch; callers must pass `Envelope`.
- **C17** Byron slot to epoch past Byron. Fixed on local branch `fix/consensus-byron-slot-epoch` (`70d83369`), no PR yet.
- **L5** Byron transaction with no inputs or no outputs. Fixed on a local branch, no PR yet.
- **L6** Byron `maxTxSize`. Open, no branch. Adding it changes the API (`VerifyConfig` or `ValidateAgainstUtxo`).
- **L9** Leios committee with fewer pools than `Nc`. Fixed on local branch `fix/leios-committee-size` (`fec72765`), no PR yet. Hits the prototype testnet (committee size 900).

Fixed by an open pull request (decide by reviewing and merging it):

- **N7** Chain-sync node-to-node message size limit. Open PR #3112.
- **N11** Handshake simultaneous open. Open PR #3127.
- **N15** Block-fetch `Stop` with ranges outstanding. Open PR #3114 (chain-sync's identical defect was fixed by merged #3092).
- **N20** Tx-submission blocking and non-blocking request rules. Open PR #3128 (Dingo always sends blocking requests for at least one id).
- **N26** Local-tx-monitor: re-acquire (`MsgAwaitAcquire`) is timed. Open PR #3154.
- **N29** Local-tx-monitor `Stop` while a snapshot is acquired. Open PR #3088 (by another contributor).
- **N30** Node-to-client default timeouts. Open PRs #3159 and #3140.
- **N31** Local-state-query server after `MsgDone`. Open PR #3113.
- **N33** Local-state-query `Release` with nothing acquired. Open PR #3113.
- **N36** Local-state-query server: `MsgRelease` without a `ReleaseFunc`. Open PR #3113.
- **N40** DMQ local notification: empty reply to a blocking request. Open PR #3142.
- **N44** LeiosVotes: next request pipelined while `Busy`. Open PR #3160.
- **N47** Peras votes (ObjectDiffusion): await, server idle, timeouts. Open PR #3165. The network spec itself only lists `NodeToNodeV_17` as "Experimental, support Peras mini-protocols" (line 2231).
- **C4** Shelley header after Origin (the first block). Open PR #3111 at `64573df5`.
- **C5** Byron header envelope: slot and block number. Open PR #3111 (reverses an earlier deliberate relaxation; Dingo does not call this validator). An EBB is an epoch boundary block, a Byron block with no transactions that opens each epoch.
- **L1** Pool registration when the caller's view is stale. Open PR #3129. Dingo's view already satisfies the contract.
- **L2** Transaction id of a body without stored CBOR. Open PR #3141. Decoded bodies were always right; bodies built in code were wrong.
- **L13** Conway vote naming an enacted purpose root. Open PR #3155; Dingo must stop returning the root.

Also needing a decision, though it conforms: **N37**, because PR #3130 follows dmq-node and so departs from the CIP-0137 text. **L4** is decided by PR #3193: BadInputs checks the reference's set and runs first.
