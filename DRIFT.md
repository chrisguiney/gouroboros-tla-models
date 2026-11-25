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

110 entries. On `main`: does not conform 63; conforms 24; conforms (implementation choice) 14; conforms (stricter) 9. A qualified verdict counts under its main word: "does not conform (decode)" and "(epoch nonce only)" as does not conform, "conforms for canonical encodings" as conforms, "conforms (stricter, and missing the rate limit)" as stricter.

| # | Area | Behaviour | Reference | gOuroboros | Spec says | Verdict | Status / PR |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [N1](#n1) | network | A message from a peer that does not have agency | Not read until the peer has agency, then judged against that state | Judged on arrival and refused | Silent on when the judgement happens | conforms (stricter) | Recorded, no change planned (models `keepalive`, `txsubmission`, `peersharing`, `localtx`, `localstatequery`) |
| [N2](#n2) | network | Which side a state's timeout applies to | Only the side waiting to receive is timed | main: the side holding agency is timed too, so a slow local callback times itself out; PR: receiver only, timed from when its handler for the previous message returns | Timeouts bound how long the receiver waits | conforms (implementation choice) → conforms | Open PR #3159 at `18e0418a` |
| [N3](#n3) | network | Bytes that arrive after a client's `MsgDone` | Kept on the mini-protocol's queue for a later run | Refused (no agency in `Done`); never replayed into a new run | Silent | conforms | Recorded (model `keepalive`); no visible effect while gOuroboros clients never restart a finished run |
| [N4](#n4) | network | Keep-alive client wait for the server's reply | 60 s, with a `TODO` asking for 10 s | 10 s by default (`WithTimeout` changes it) | 60 s in `StServer` | conforms (stricter) | Recorded; deliberate |
| [N5](#n5) | network | Clients that never send `MsgDone` | Keep-alive, peer-sharing and local-state-query clients send `MsgDone` when told to terminate | No API sends it; `Stop` unregisters and the connection closes later | The client may terminate; it is not required to | conforms | Recorded (models `keepalive`, `peersharing`, `localstatequery`). A node holds an acquired local state until the connection closes |
| [N6](#n6) | network | Chain-sync `StMustReply` timeout | Random 601-911 s | main: random 135-269 s; PR: 601-911 s | Random 601-911 s | conforms (stricter) → conforms | Open PR #3112 (model `chainsync` `ChainSyncLimits`) |
| [N7](#n7) | network | Chain-sync node-to-node message size limit | 65,535 bytes in every state | main: 462,000 bytes (the ingress queue size); PR: 65,535, with 462,000 kept as the pending-receive budget | 65,535 bytes in every state | does not conform → conforms | Open PR #3112 (model `chainsync` `ChainSyncLimits`) |
| [N8](#n8) | network | Chain-sync `StMustReply` timeout for a trusted peer | Never times out a trustable peer | Always applies the timeout; has no notion of a trusted peer | Timeout only for peers that are not trustable | conforms (stricter) | Recorded, not changed; whether a peer is trusted is the caller's knowledge |
| [N9](#n9) | network | Chain-sync `GetCurrentTip` answer routing | Each request's continuation receives its own answer | main: whichever caller is registered on a shared channel, so a roll's older tip can answer the call; PR: only the call's own answer | Answers come back in request order to the requester | conforms | Open PR #3094. A library defect: the wire is unaffected |
| [N10](#n10) | network | Handshake query answered before negotiation | Query reply only when the proposal is acceptable and the agreed data asks for it | main: any decodable proposed version that asks for a query gets one, even with no common version or the wrong network magic; PR: after negotiation | Query sends back the supported versions; negotiation fails on a magic mismatch | conforms (implementation choice) → conforms | Open PR #3127 |
| [N11](#n11) | network | Handshake simultaneous open | Supported: a `MsgProposeVersions` received in `Confirm` is read as `MsgReplyVersions` | main: not supported (a proposal in `Confirm` is an error); PR: supported | Supported | does not conform → conforms | Open PR #3127 |
| [N12](#n12) | network | Handshake `MsgQueryReply` without a query | Taken as a query result | Error | Silent | conforms (stricter) | Recorded (model `handshake`) |
| [N13](#n13) | network | Handshake `MsgAcceptVersion` carries the server's own data | Sends the negotiated (agreed) data | Sends its own version data for the chosen version; each side combines the flags itself | The negotiated data is sent back | does not conform | Fixed on local branch `fix/handshake-accept-negotiated-data` (model `handshake` `AcceptCarriesNegotiatedData`), merged as #3194. No wrong outcome: the reference client recomputes the agreement |
| [N14](#n14) | network | Handshake version keys out of order | Recognised keys must ascend, else a decode failure; unrecognised keys skipped | Accepts any order; rejects duplicates | Keys must be unique and ascending | does not conform | Fixed on local branch `fix/handshake-version-key-order` (model `handshake` `UnorderedMapsRejected`, `UnknownKeysTolerated`), merged as #3194; checks recognised keys only, as the reference does |
| [N15](#n15) | network | Block-fetch `Stop` with ranges outstanding | Collects every answer, then sends `MsgClientDone`; a demotion that times out closes the connection | main: gives up after 250 ms without `MsgClientDone` and allows `Start`, so a late reply reaches the new run; PR: abandons only when owed, latches, stops the muxer | `MsgClientDone` only from `StIdle` | does not conform → conforms | Open PR #3114 (chain-sync's identical defect was fixed by merged #3092) |
| [N16](#n16) | network | Block-fetch `RangeDoneFunc` for a request that was never sent | A request's receiver exists only once the request is sent | main: the shutdown drain calls `RangeDoneFunc` for a request whose `RequestRange` returned an error; PR: not | Silent (library API) | conforms | Open PR #3114. Library defect; Dingo works around it |
| [N17](#n17) | network | Block-fetch `StBusy` timeout default | 60 s | main: `NewConfig` sets `BatchStartTimeout` 5 s; PR: 60 s | 60 s | conforms (stricter) → conforms | Open PR #3114 (Dingo already sets 60 s) (model `blockfetch` `BlockFetchLimits`) |
| [N18](#n18) | network | Block-fetch size limit in `StBusy` (and `StIdle` for a pipelining client) | 65,535 bytes | 2,500,000 bytes, because a `MsgBlock` that arrives early is judged against `StBusy` | 65,535 bytes | does not conform | Not fixed; needed by gOuroboros' engine, which judges a message against the state current when it arrives |
| [N19](#n19) | network | Block-fetch `RangeTimeout` | None | A whole range must finish within about 36 hours by default | Silent | conforms (implementation choice) | gOuroboros addition. Local only: it ends the caller's wait and sends nothing |
| [N20](#n20) | network | Tx-submission blocking and non-blocking request rules | Client throws `ProtocolErrorRequestBlocking`, `RequestNonBlocking`, `RequestedNothing`; server picks the style from its FIFO | main: the client does not check; `Server.RequestTxIds` lets the caller pick either style; PR: both enforced | Blocking iff nothing stays unacknowledged; ack or request non-zero | does not conform → conforms | Open PR #3128 (Dingo always sends blocking requests for at least one id) |
| [N21](#n21) | network | Tx-submission request over the window from `NodeToNodeV_16` | From V16 the client clamps the reply to its own window | Always a protocol error | From V16 not an error; reply with as many as fit | does not conform | Fixed in PR #3195 head `8ece4753` (model `txsubmission` `ClampsOverWindow`; the first draft `4b7d5262` clamped a blocking request to an empty reply, `TxSubmissionV16ClampBlockingBug.cfg`) |
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
| [N36](#n36) | network | Local-state-query server: `MsgRelease` without a `ReleaseFunc` | Accepted | main: an error that tears down a client that released; PR: accepted | `MsgRelease` is legal from `StAcquired` | does not conform → conforms | Open PR #3113 (model `localstatequery` `LocalStateQueryServerRelease`) |
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
| [N48](#n48) | network | Local-state-query era filter sets | `toEraCBOR @era`: plain array before Conway (a tag 258 is refused), tag 258 from Conway | main: `GetFilteredDelegationsAndRewardAccounts` always tagged, so refused before Conway; UTxO address and input filters never tagged; a nil filter sent as CBOR null; branch: as the reference | CDDL silent; the era's ledger encoding | does not conform → conforms | Fixed on local branch `fix/localstatequery-era-set-encoding` (`fb802943`), open PR #3286 (model `localstatequery` `LocalStateQueryCodec`) |
| [N49](#n49) | network | Local-state-query `GetAccountState` and `GetGovState` before Conway | Both decoded and answered in every Shelley-based era | main: the client refuses both before Conway; branch: `GetAccountState` sent from Shelley; `GetGovState` still Conway only (its result type is Conway's) | Silent | does not conform → conforms (`GetAccountState`) | `GetAccountState` fixed on local branch `fix/localstatequery-account-state-all-eras` (`ddae722e`), open PR #3287; `GetGovState` recorded (model `localstatequery` `LocalStateQueryCodec`) |
| [N50](#n50) | network | Local-state-query `GetFuturePParams` (Shelley query 33) | Decoded and answered from Conway | main: the server fails with "unknown Block query type: 33"; no client call; branch: decoded and handed to the query callback | Silent | does not conform → conforms (server decode) | Fixed on local branch `fix/localstatequery-decode-future-pparams` (`dd131af9`), open PR #3288; client call not added (model `localstatequery` `LocalStateQueryCodec`) |
| [N51](#n51) | network | Local-state-query queries gOuroboros does not decode or re-encode exactly | `QueryAnytime` (`GetEraStart`) and Byron's own queries decoded; era history written as an indefinite list; UTxO filters keep their tag | `QueryAnytime` and Byron queries fail to decode; decoded UTxO filters re-encode without the tag; era history has no list encoder (each era summary re-encodes exactly) | Silent | does not conform (decode); conforms (re-encode, both forms decode) | Recorded; pinned by `reference_golden_test.go` on `test/localstatequery-reference` |
| [N52](#n52) | network | DMQ: KES evolution a message signature is checked at | The claimed KES period minus the opcert start; the current slot is not used | main: the node's current KES period minus the opcert start, and the opcert window must contain the current period; branch: the claimed period, no current-period check | Silent (verify the KES signature with the opcert's key) | does not conform → conforms | Fixed on local branch `fix/dmq-kes-claimed-period` (`7e1a0820`, `db6103a6`), no PR (model `dmq` `MessageValidityKesAtCurrentBug.cfg`, `MessageValidityExtrasBug.cfg`) |
| [N53](#n53) | network | DMQ: message expiry bounds | Admission: expired if now > expiresAt, too far if expiresAt >= now + 1800 s; mempool drops at expiresAt <= now; sub-second clock | main: now truncated to seconds; expiresAt = now + maxTTL accepted; `IsValidAt` keeps a message a second past expiry; branch: as the reference | Expired messages invalid; too far ahead a violation; no exact bound | does not conform → conforms | Fixed on local branch `fix/dmq-ttl-reference-bounds` (`1f492baf`, `5d48a376`), no PR |
| [N54](#n54) | network | DMQ: message body size | 90 to 2000 bytes, refused at decode, before any other check | main: any size; branch: refused at decode and by the authenticator (`ErrMessageBodySize`) | `messageBody = bstr .size (90..2000)` | does not conform → conforms | Fixed on local branch `fix/dmq-message-body-size` (`9804e9d9`), no PR |
| [N55](#n55) | network | DMQ: batch commit and opcert counters | Each message checked against the counters recorded when it is validated | main: commit re-checks only each pool's last counter in the batch; branch: every counter | Counter strictly lower than one seen is a violation | does not conform → conforms | Fixed on local branch `fix/dmq-commit-recheck-every-counter` (`aa2673b6`), no PR (model `dmq` `MessageValidityBatchFinalOnlyRecheckBug.cfg`) |
| [N56](#n56) | network | DMQ: checks dmq-node does not make, and its rate limit | Counter compared only with counters seen in messages; current slot not consulted; one message per pool per 60 s (`SigTooFrequent`, fatal for node-to-node) | main: counter must not be below the chain-state counter; opcert window must contain the current KES period; no rate limit; branches: as the reference | Neither check required (397-402; 405-411 is a hedged note); rate limiting suggested (528) | does not conform → conforms | Fixed on local branches `fix/dmq-drop-chain-counter-check` (`aa7c8605`), `fix/dmq-kes-claimed-period` (`db6103a6`), `fix/dmq-sig-rate-limit` (`d4c8c2f1`), no PR (model `dmq` `MessageValidityExtrasBug.cfg`, `MessageIngressNoRateLimitBug.cfg`) |
| [N57](#n57) | network | DMQ: bytes the message id and KES signature cover | The payload bytes as received | main: the payload re-encoded from its decoded fields; branch: the decoded bytes | `messageId` = Blake2b-256 of the CBOR payload | does not conform → conforms (for a non-canonical payload) | Fixed on local branch `fix/dmq-payload-preserved-bytes` (`d21d3969`), no PR (model `dmq` `MessagePayloadBytes`) |
| [N58](#n58) | network | DMQ: what node-to-node receipt does with each message | Judged one at a time in `Validate.hs` order; expired, unregistered, not-initialised and duplicate dropped quietly; any other failure closes the connection after the valid ones are kept | main: any failure refuses the whole reply and closes the connection; pool checked before the KES window, signatures before the counter; branch: as the reference | Any failed step is "a protocol violation" (402) | does not conform → conforms | Fixed on local branch `fix/messagesubmission-reference-receipt` (`a12edd17`), no PR (model `dmq` `MessageIngressAllOrNothingBug.cfg`, `MessageIngressMainOrderBug.cfg`) |
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
| [C15](#c15) | consensus | TPraos overlay schedule (d > 0) | A non-active overlay slot is rejected; an active one belongs to a genesis delegate, checked against its delegation with no stake | main: `ValidateHeaderInput` cannot carry d or the genesis delegations, so a valid genesis-delegate header is rejected (no stake, no pool VRF key) and a pool header in a non-active slot is accepted; branch: required `Overlay`, `ErrNotActiveSlot`, `ErrWrongGenesisColdKey`, `ErrWrongGenesisVRFKey` | OVERLAY rule: Active-OBFT and Decentralized | does not conform → conforms | Fixed on local branch `fix/consensus-tpraos-overlay` (`78f2f391`), merged as #3201 (model `consensus-eras`, `OverlayGenesisBug`, `OverlayNonActiveBug`). No production caller: Dingo validates with `VerifyBlock` and its own overlay check |
| [C16](#c16) | consensus | Header envelope: ObsoleteNode, header size, body size | Checked before the protocol rules | main: not in `ValidateHeader`; branch: required `Envelope`, `ErrObsoleteNode`, `ErrHeaderSizeTooLarge`, `ErrBlockSizeTooLarge`; a missing input is the only error (`ErrMissingHeaderInput`) | `chainChecks` | does not conform → conforms | Fixed on the same branch (model `consensus-eras`, `ExtrasBug`, `MissingInputBug`) , merged as #3201|
| [C17](#c17) | consensus | Byron slot to epoch past Byron | The era history (`Summary`) converts every slot | main: `ByronConfig.SlotToEpoch` divides any slot by the Byron epoch length (mainnet slot 4514400 gives 209, not 208); branch: `EndSlot` and `SlotToEpochChecked` (`ErrSlotAfterByron`) | Conversions use each era's own epoch size | does not conform → conforms | Fixed on local branch `fix/consensus-byron-slot-epoch` (`70d83369`), no PR yet (model `consensus-eras`, `GoByronSoundBug`). Only tests call it (model `consensus-eras` `EraHistoryDecode` for the era history decode) |
| [L1](#l1) | ledger | Pool registration when the caller's view is stale | Registered means present in `psStakePools`, which POOLREAP clears at the epoch boundary | main: trusts the caller's `IsPoolRegistered`, so a stale view lets a delegation to (or retirement of) a reaped pool through, and treats re-registering a reaped pool as a re-registration; PR: one epoch-aware predicate | Delegation needs a registered pool; a reaped pool is gone | does not conform → conforms | Open PR #3129 (head `e7b4261d`, main merged in). Dingo's view already satisfies the contract |
| [L2](#l2) | ledger | Transaction id of a body without stored CBOR | A body always carries its serialization; the encoder omits an empty CIP-159 map | main: hashes empty input, the same id for every such body; PR: hashes the body's encoding, omitting empty Dijkstra maps, and gives a body with no valid encoding the zero id | The id is the hash of the body's CBOR | does not conform → conforms | Open PR #3141. Decoded bodies were always right; bodies built in code were wrong. Modelled as a table in `ledger-txid` (model `ledger-txid`) |
| [L3](#l3) | ledger | Conway CC vote with a nil voter key | Not representable | main: `UtxoValidateCCVotingRestrictions` panics; PR: skips it as the sibling rules do | n/a (unreachable from decoded CBOR) | conforms | Open PR #3155. Library defect, hand-built transactions only (model `ledger-governance` `GovVoterNil`) |
| [L4](#l4) | ledger | BadInputs covers only spent inputs | Alonzo: spent and collateral inputs; Babbage: reference inputs too | main: spent inputs only; missing collateral and reference inputs are caught by the witness rules instead; PR: the reference's set, with BadInputs first in each rule list | All of them must exist | conforms | Open PR #3193 at `efd0b081` (model `ledger-utxo` `GoBadInputsComplete`, `GoMissingInputIsBadInputs`) |
| [L5](#l5) | ledger | Byron transaction with no inputs or no outputs | Cannot be decoded (`NonEmpty`) | main: accepted; a no-input, zero-output transaction pays no fee (it counts as redeem-only) | Inputs and outputs non-empty | does not conform | Fixed on a local branch, no PR yet |
| [L6](#l6) | ledger | Byron `maxTxSize` | `TxValidationTxTooLarge` | No check anywhere | `txSize tx ≤ maxTxSize` | does not conform | Open, no branch. Adding it changes the API (`VerifyConfig` or `ValidateAgainstUtxo`) |
| [L7](#l7) | ledger | Byron minimum fee rounding | Summand rounded to a whole lovelace when decoded, then the per-byte part rounded up | The whole sum rounded up | `a + b·txSize ≤ fee`, exact | conforms | Since the fee is a whole number, rounding the sum up is exactly the spec's check; the reference can accept a fee half a lovelace short. Differs only for a fractional summand, which no network has |
| [L8](#l8) | ledger | Byron repeated inputs and witness counts | A repeated input is counted once; witnesses are zipped with inputs, so a short list leaves inputs unchecked | Repeated input rejected; witness count must equal input count | Inputs are a set; every input needs a valid witness | conforms (stricter) | Deliberate. Stricter than the spec only for extra witnesses, which the spec allows |
| [L9](#l9) | ledger | Leios committee with fewer pools than `Nc` | `min(Nc, pools)` seats; the bitfield is sized by the seated committee | Requires exactly `Nc` seats, so every valid certificate from a small committee is refused | Take all pools if fewer than `Nc` | does not conform | Fixed on local branch `fix/leios-committee-size` (`fec72765`), no PR yet. Hits the prototype testnet (committee size 900) |
| [L10](#l10) | ledger | Leios certificate in a later epoch than its announcement | cardano-ledger refuses it (`LeiosCertAnnouncedInPreviousEpoch`); the consensus prototype does not check | Not checked | Not required | conforms | Recorded (model `ledger-leios`) |
| [L11](#l11) | ledger | Node-to-client CertRB with inlined EB transactions | none | Accepts a certifying block whose endorser-block transactions are inlined, over node-to-client only | CertRB carries no transactions on chain | conforms | Local delivery only; the on-chain body is unchanged |
| [L13](#l13) | ledger | Conway vote naming an enacted purpose root | Refused, `GovActionsDoNotExist`: votes resolve against the live proposals only | main: accepted when the caller's `GovActionById` returns the root, which the contract allowed and Dingo does; PR: the contract excludes roots | A vote names a proposal in the governance state | does not conform → conforms | Open PR #3155. Dingo's `GovActionById` must stop returning the current root |
| [L14](#l14) | ledger | Proposed protocol version width in a classic parameter update | Minor is `Word32`; major bounded per era | main: both 16 bits, so a minor above 65,535 is refused; branch: minor 32 bits | Silent on widths | does not conform → conforms | Fixed on local branch `fix/ledger-pparam-update-minor-width`, open PR #3278 (model `ledger-codec`) |
| [L15](#l15) | ledger | Zero-coin output in a PlutusV2/V3 TxInfo | `transValue` always writes the ada entry, `{"": {"": 0}}` at zero | main: Shelley, Mary, Alonzo and Babbage `ToPlutusData` drop the ada entry when the coin is 0; branch: kept | Silent | does not conform → conforms | Fixed on local branch `fix/script-context-zero-ada-output` (`51c2b6f3`), open PR #3281. 25 of the 26 PlutusV3 instances in cardano-ledger's Conway `translations.cbor` failed before the fix. A valid transaction cannot reach it today (every output meets the minimum UTxO) (model `ledger-codec`) |
| [L16](#l16) | ledger | PlutusV1 TxInfo with a redeemer that points at nothing | Ignored: a V1 TxInfo carries no redeemers | `NewTxInfoV1FromTransaction` resolves every redeemer and returns an error | n/a | conforms (stricter) | Phase-1 rejects such a transaction (extraneous redeemer) before any script runs, so the outcome is the same. The golden test clears the Alonzo generator's arbitrary redeemers for V1 |
| [L19](#l19) | ledger | Committee certificate after an in-block UpdateCommittee proposal | Accepted: GOVCERT counts the proposals the block's earlier transactions left as potential members | main: `BlockLedgerState` committee lookups ask only the wrapped state, so the certificate is rejected; branch: in-block proposals count | Silent | does not conform → conforms | Fixed on local branch `fix/ledger-block-state-proposed-committee` (`458e502c`), open PR #3285. Reaches Dingo through `utxoref.StateOverlay` |
| [L20](#l20) | ledger | `VerifyBlock` issuer in a TPraos overlay slot (d > 0) | Active slot: the scheduled genesis delegate, its VRF key, no stake; non-active slot: rejected | main: every issuer looked up in the pool distribution, so valid delegate blocks are rejected and pool blocks in non-active slots accepted; branch: `VerifyConfig.TPraosOverlay` | OVERLAY rule | does not conform → conforms | Fixed on local branch `fix/ledger-verify-block-tpraos-overlay` (`ddc16a74`), open PR #3277. Breaking for callers with stake-pool validation on TPraos blocks. Dingo skips that validation |
| [L21](#l21) | ledger | Leios voting key past its honoured age | Seated keyless once `epoch >= registeredIn + maxKeyAge`, `maxKeyAge = ceil(maxKESEvo * slotsPerKESPeriod / epochLength) + 2`; a certificate it signs is refused (`SignerWithoutKey`) | `DijkstraLeiosCertificateState` asks only for keys "from the snapshot's registered pool parameters"; an aged-out key handed over verifies like any other | Voting keys rotate with a time-to-live | does not conform → conforms | Fixed on local branch `fix/leios-voting-key-age` (`93c3df5d`), no PR yet: gOuroboros judges key age itself, through the new required `DijkstraLeiosKeyAgeContext` method and `KeyRegisteredIn` (breaking). No implementer in Dingo or ouroboros-mock |
| [L22](#l22) | ledger | Leios vote encoding | `[announcing_rb_hash, voter_id (Word16), signature]` | main: `LeiosVote`, carried by LeiosVotes `MsgVote` and the LeiosFetch vote messages, is `[slot, eb_hash, voter_id, signature]`; branch: the CIP shape, `voter_id` 16 bits | `[announcing_rb_hash, voter_id, vote_signature]`; LeiosVotes `MsgLeiosVote` carries it | does not conform → conforms | Fixed on local branch `fix/leios-vote-shape` (`eb4c2421`), no PR yet (breaking; Dingo's `ledger/leios` and `ouroboros` packages use the old fields). The rc-2026w41 prototype vote is the golden vector. A LeiosFetch votes reply is matched by voter only: a vote names its announcing block, not its slot (model `ledger-leios` `LeiosVoteShape`) |
| [L23](#l23) | ledger | Dijkstra committee certificate for a member an earlier level proposed | Accepted: each level's GOVCERT counts the UpdateCommittee proposals the earlier levels left as potential members | main: the governance view consults only the wrapped state, so a top-level (or later sub-transaction) authorization or resignation is rejected | Same rule (Conway GOVCERT isPotentialFutureMember; Dijkstra LEDGER/SUBLEDGER) | does not conform → conforms | Fixed on local branch `fix/dijkstra-committee-proposed-member` (`0a8bde9f`), open PR #3245 |
| [L24](#l24) | ledger | Dijkstra parameter-update well-formedness: eMax and pledge leverage | Refused: a set eMax of zero, or a pledge leverage cap below 1 (removing the cap is allowed) | main: accepted (only Conway's non-zero fields and a non-negative leverage are checked) | Leverage cap at least 1; eMax not listed (see below) | does not conform → conforms | Fixed on local branch `fix/dijkstra-ppu-well-formed` (`9f7e7d38`), open PR #3246 |
| [L25](#l25) | cbor | Tags before a tag 30 rational | At most one tag, and only 30 (`allowTag 30`) | main: every leading tag stripped, so tag 31, tag 258 or tag 30 twice decodes as a rational | RFC 8949 tag 30 is one tag around [n, d] | does not conform → conforms | Fixed on local branch `fix/cbor-rat-single-tag` (`fe4f8206`), open PR #3282 (model `cbor-codec`; untagged bounded ratio still accepted) |
| [L26](#l26) | cbor | Plutus Data constructor whose fields are not a list | Refused (`decodeListOf`) | main: `ConstructorDecoder` and `Value` accept 121(1) or 102([3, 1]); only `ParsedFields`/JSON fail later | Plutus Data CDDL: a constructor's fields are `[* plutus_data]` | does not conform → conforms | Fixed on local branch `fix/cbor-constructor-fields-list` (`a37a8a90`), open PR #3283 (model `cbor-codec`) |
| [L27](#l27) | cbor | Generic `Value` decode of a tag 258 set of maps with composite keys | Not applicable (typed decoders); RFC 8949 allows any item as a map key | main: `Value` and `LazyValue.Decode` fail, including on the cardano-ledger Conway and Dijkstra golden transactions (proposal procedures) | RFC 8949 section 3.1 | does not conform → conforms | Fixed on local branch `fix/cbor-value-set-members` (`3a442a45`), open PR #3284 (model `cbor-codec`) |
| [L28](#l28) | ledger | Bignum MultiAsset quantity | Refused: output quantities use `decodeWord64`, mint quantities `decodeIntegerBounded64` | main: a tag 2/3 bignum quantity is accepted in outputs and mint at every version | CDDL `positive_coin`/`nonZeroInt64` are plain integers | does not conform → conforms | Fixed on local branch `fix/ledger-multiasset-bignum-quantity` (`4ae0d4f9`), open PR #3279 (model `cbor-codec`; Mary pair coin still accepts a bignum) |
| [L29](#l29) | ledger | PlutusV2 cost model in an Alonzo parameter update | Accepted: the pre-Conway cost-model decoder takes PlutusV1 and PlutusV2 (exact parameter counts) in every era | main: Alonzo refuses language 1 (only Babbage accepts it) | Silent on the decoder; the Alonzo spec lists PlutusV1 only | does not conform → conforms | Fixed on local branch `fix/ledger-alonzo-v2-cost-model-update` (`283f75cb`), open PR #3280 (model `ledger-codec`) |
| [L30](#l30) | ledger | Tag 258 on a pre-Conway set-shaped field | Refused before version 9: `decodeSet` (versions 2-8) and the witness decoders' `decodeList` take no tag | main: accepted on pool owners, Alonzo/Babbage collateral, required signers, reference inputs and every Shelley-Babbage witness list | Silent (the CDDL's `set<a>` allows the tag from Conway) | does not conform → conforms | Fixed on local branch `fix/ledger-pre-conway-set-tag` (`e9dd7145`), open PR #3289 (model `ledger-codec`; other tags on witness sets still decode) |
| [L31](#l31) | cbor | `ConstructorEncoder` field list encoding | Non-empty fields as an indefinite list, empty as `0x80` (`encodeData` with the Serialise list instance) | main: a definite list; nil fields as null | Plutus Data CDDL allows either | does not conform → conforms | Fixed on local branch `fix/cbor-constructor-indefinite-fields` (`ad7a4f25`), open PR #3290; changes the bytes and hashes of Data built with it (model `cbor-codec`; four residual shapes) |
| [L32](#l32) | cbor | Map entry order in Value's Plutus Data JSON | Wire order (`plutusDataToJson` over the entry list) | main: entries sorted by their JSON key; Value holds maps as Go maps, so wire order is gone | Silent | does not conform | Open, no branch: needs Value to keep map order (an API change); Value's JSON is used for error and diagnostic output, not consensus |
| [L12](#l12) | ledger | CBOR nesting limit | No nesting limit | 16,384 levels for blocks and ledger data; 1,024 for peer messages | RFC 8949 sets none | conforms | Just above what a 16,384-byte transaction can nest; raising `maxTxSize` would let a valid transaction nest deeper than gOuroboros accepts |
| [P1](#p1) | pipeline | An invalid block in the pipeline | ChainDB records it, ignores it and its successors, and carries on | The pipeline stops (fatal) | Silent | conforms (implementation choice) | Documented in chain-sync's `Config.Pipeline` |
| [P2](#p2) | pipeline | Closing with blocks queued | Every queued block is answered `FailedToAddBlock` | Dropped; a waiting `Fence` gets `ErrPipelineStopped` | Silent | conforms (implementation choice) | Recorded (model `pipeline-cbor`) |
| [P3](#p3) | pipeline | `WaitForDrain` during `Stop` | Rollback is part of chain selection, serialised with adds | main before `1559924b`: returns once `Stop` begins while a block may still commit after the caller's rollback; now: waits for the apply runner | Silent | conforms | Merged #3161 (`1559924b`); kept by #3233 (merge `5cb98604`). Library defect; not reached through chain-sync or Dingo today |
| [P4](#p4) | pipeline | An unread `Results` channel | Chain selection never waits on a follower | main before `1559924b`: stalls the apply runner; now: never blocks commits, drops the oldest result for a reader that falls behind (counted in `ResultsDropped`) | Silent | conforms | Merged #3161 (`1559924b`) |
| [P5](#p5) | pipeline | `WithLosslessResults` | none | Opt-in with an `ApplyFunc`; always on in header-only and trusted decode-only modes: `Results` delivers every committed block and commits wait for the reader | Silent | conforms (implementation choice) | Merged with #3161 (`1559924b`; decode-only modes are lossless by default; Dingo's opt-in is now redundant). Wire: a slower commit only delays chain-sync's next request, which the protocol allows; ledger: unchanged |

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
- **Status.** Open PR #3112. Model `chainsync` `ChainSyncLimitsMainTimeoutBug.cfg` (main) / `ChainSyncLimits.cfg` (merged #3112).

`StMustReply` is where a client waits for the next block. On main a quiet but honest server is dropped after as little as 135 s.

### N7

**Chain-sync node-to-node message size limit** (kind 1: open PR moves to the reference)

- **What differs.** Reference: 65,535 bytes in every state. gOuroboros: main: 462,000 bytes (the ingress queue size); PR: 65,535, with 462,000 kept as the pending-receive budget.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Node-to-node size limits per state" (chain-sync), lines 910-924: table: `StIdle`, `StCanAwait`, `StMustReply`, `StIntersect` all 65535
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/ChainSync/Codec.hs` 43-49 (`smallByteLimit` per state); `ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs` 110-111
- **gOuroboros.** gOuroboros `d0b95845` `protocol/chainsync/chainsync.go` 233, 116-146; PR #3112 head `4032512e4` same file 245-247 (`SmallMaxPendingMessageBytes = 65535`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3112. Model `chainsync` `ChainSyncLimitsMainBug.cfg` (main) / `ChainSyncLimits.cfg` (merged #3112).

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
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/client.go` 113 (`default:` error); PR #3127 head `19c0debbf` `client.go` 125-126, 193. Review: at `78792c96` each side ended with the peer's raw data (reference: the agreed data, `Client.hs` 213-215); fixed at `5826fae1` (model `handshake` `SimAgreedData`, `HandshakeSimOpenRawPeerDataBug.cfg`). CI at `8461ae3a`: a side could end before its own proposal was written, and stopping dropped it, so the peer hung (Go test) or saw the connection close; the reference writes the proposal synchronously before it reads (network-mux `Types.hs` 327-330). Fixed at `97708901` (model `handshake` `HandshakeSimOpenDelivery.tla`, `NoDroppedProposal`, `HandshakeSimOpenDeliveryBug.cfg` deadlock)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3127, head `97708901`

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
- **Status.** Fixed on local branch `fix/handshake-accept-negotiated-data`, merged as #3194; model `handshake` `HandshakeAcceptOwnDataBug.cfg` reproduces main. No wrong outcome found: the reference client recomputes the agreement, and every combining rule is idempotent and commutative
- **Review follow-up.** PR #3194 at `8ab16c0f`: the server's `FinishedFunc` also gets the agreed data (reference `Server.hs` 42-44); model `handshake` `AgreedDataBothSides`, `HandshakeServerRawPeerDataBug.cfg`
- **Review follow-up.** PR #3194 at `97039771` and PR #3127 at `8461ae3a`: a version table entry held as a pointer now agrees like a value; before, it came back unchanged as the side's own data. Verdict: conforms on both branches. Model `handshake` `AgreeHeld`, `HandshakePointerUnagreedBug.cfg`, `HandshakeSimOpenPointerUnagreedBug.cfg`

### N14

**Handshake version keys out of order** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: recognised keys must ascend, else the message fails to decode; unrecognised keys are skipped. gOuroboros: accepts any order; rejects duplicates.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, "Client and Server Implementation" (handshake), lines 655-656: "version numbers ... in the version table are unique and appear in ascending order"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/Handshake/Codec.hs` 101-102 ("encodes proposed map in ascending order and it expects to receive them in this order"), 228-241 (`decodeVersions`: an unrecognised key is skipped, a recognised key must exceed the previous recognised key)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/handshake/collection_decode.go` 85 (duplicate check only)
- **Verdict.** does not conform
- **Status.** Fixed on local branch `fix/handshake-version-key-order`, merged as #3194; model `handshake` `HandshakeKeyOrderBug.cfg` reproduces main. The fix follows the reference: only recognised keys must ascend, and an unrecognised key out of order is accepted. A strict every-key check would refuse such a peer (`HandshakeKeyOrderEveryBug.cfg`)

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
- **Status.** Open PR #3114 at `d10daf24` (head `a93b4116`, main merged in). Library defect; Dingo works around it

### N17

**Block-fetch `StBusy` timeout default** (kind 1: open PR moves to the reference)

- **What differs.** Reference: 60 s. gOuroboros: main: `NewConfig` sets `BatchStartTimeout` 5 s; PR: 60 s.
- **Spec.** ouroboros-network `5f356486ab3e` `docs/network-spec/miniprotocols.tex`, block-fetch "Timeouts per state", line 1235: "`StBusy` & 60s"
- **Reference.** ouroboros-network `5f356486ab3e` `.../Protocol/BlockFetch/Codec.hs` 54; `.../Protocol/Limits.hs` 116-117 (`longWait = Just 60`)
- **gOuroboros.** gOuroboros `d0b95845` `protocol/blockfetch/blockfetch.go` 282; PR #3114 head `395b9c2e7` same file 229, 287
- **Verdict.** conforms (stricter) → conforms
- **Status.** Open PR #3114 (Dingo already sets 60 s). Model `blockfetch` `BlockFetchLimitsMainBug.cfg` (main) / `BlockFetchLimits.cfg` (merged #3114).

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
- **Status.** Fixed in PR #3195, head `e5c47f5f` (main merged in); model `txsubmission` `TxSubmissionV16ClampBug.cfg` reproduces main. Default windows (10 each side) never trigger it. Review: the first draft `4b7d5262` clamped a blocking request on a full window to zero and sent an empty blocking reply (`TxSubmissionV16ClampBlockingBug.cfg`); `8f6c6d5b` refuses a blocking request for nothing or with ids left before clamping, as `Outbound.hs` 182-185 does; `8ece4753` (test only) pins the served side, a blocking request acknowledging the whole window (`TxSubmissionV16RefuseAckedBlockingBug.cfg`). A non-blocking request clamped to zero gets an empty reply, as the reference does (`ProbeNoZeroClamp`)

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
- **Status.** Open PR #3113. Model `localstatequery` `LocalStateQueryServerReleaseMainBug.cfg` (main) / `LocalStateQueryServerRelease.cfg` (merged #3113).

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
- **Status.** Open PR #3160 (head `75953b20`, main merged in). Model: `specs/leios-peras/LeiosNotifySyncOrderBug.cfg` (`SyncAfterStopReportsShutdown`)

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

### N48

**Local-state-query era filter sets** (kind 1: branch moves to the reference)

- **What differs.** Reference: `GetUTxOByAddress`, `GetFilteredDelegationsAndRewardAccounts` and `GetUTxOByTxIn` carry their set with the era's own encoding: a plain array before Conway, where the decoder refuses tag 258, and tag 258 from Conway. gOuroboros: main: the delegations filter always tagged, so a node refuses the query in Shelley through Babbage; the UTxO filters never tagged; a nil filter sent as CBOR null; branch: as the reference.
- **Spec.** No CDDL for queries; the era's ledger encoding applies (cardano-ledger `1210d37f` `libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/Decoder.hs` 943-952, `decodeSet`: tag 258 only below version 2 and allowed from 9)
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Query.hs` 742-761 (encode, `LC.toEraCBOR @era`), 842-850 (decode, `LC.fromEraCBOR @era`); goldens `golden/cardano/QueryVersion3/CardanoNodeToClientVersion19/Query_<Era>_GetUTxOByAddress`, `_GetFilteredDelegationsAndRewardAccounts`, `_GetUTxOByTxIn`
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/localstatequery/client.go` 594, 674, 892; branch `fix/localstatequery-era-set-encoding` `fb802943` `eraFilterSet`, test `TestEraFilterSetEncoding` (23 of 35 cells fail before the fix)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch, open PR #3286. Model `localstatequery` `LocalStateQueryCodecEraSetDecodeBug.cfg`, `LocalStateQueryCodecEraSetBytesBug.cfg` (main) / `LocalStateQueryCodec.cfg` (fix).

### N49

**Local-state-query `GetAccountState` and `GetGovState` before Conway** (kind 1 for `GetAccountState`; kind 2 for `GetGovState`)

- **What differs.** Reference: both decoded and answered in every Shelley-based era. gOuroboros: main: the client refuses both before Conway; branch: `GetAccountState` sent from Shelley. `GetGovState` stays Conway only because `GovStateResult` decodes the Conway governance state.
- **Spec.** Silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Shelley/Ledger/Query.hs` 411-412 (`queryChainAccountState`), 498, 503 (`blockQueryIsSupportedOnVersion`), 872, 882 (decoded without `requireCG`); goldens `Query_<Era>_GetAccountState`, `Query_<Era>_GetGovState` for Shelley to Dijkstra
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/localstatequery/client.go` 941-945, 1341-1345; branch `fix/localstatequery-account-state-all-eras` `ddae722e`, test `TestGetAccountStateEveryShelleyEra` (5 eras fail before the fix)
- **Verdict.** does not conform → conforms (`GetAccountState`); `GetGovState` a missing feature
- **Status.** `GetAccountState` fixed on local branch, open PR #3287; `GetGovState` recorded. Model `localstatequery` `LocalStateQueryCodecAccountStateBug.cfg` (main) / `LocalStateQueryCodec.cfg` (fix); `GetGovState` before Conway is kept as `LocalStateQueryCodecGovStateBeforeConwayBug.cfg`.

### N50

**Local-state-query `GetFuturePParams` (Shelley query 33)** (kind 1: branch moves to the reference)

- **What differs.** Reference: decoded and answered from Conway. gOuroboros: main: a server fails to decode it ("unknown Block query type: 33"); there is no client call. Branch: decoded as `ShelleyFuturePParamsQuery` and handed to the query callback.
- **Spec.** Silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Shelley/Ledger/Query.hs` 419, 507, 886; goldens `Query_Conway_GetFuturePParams`, `Query_Dijkstra_GetFuturePParams`
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/localstatequery/queries.go` 81, 244; branch `fix/localstatequery-decode-future-pparams` `dd131af9`, test `TestDecodeGetFuturePParamsQuery` (both cells fail before the fix)
- **Verdict.** does not conform → conforms (server decode)
- **Status.** Fixed on local branch, open PR #3288; a client call is not added. Model `localstatequery` `LocalStateQueryCodecFuturePParamsBug.cfg` (main) / `LocalStateQueryCodec.cfg` (fix). The server decodes query 33 in every era and leaves the era to the query callback, as for `GetConstitution` (`LocalStateQueryCodecProbeServerEraBug.cfg`).

### N51

**Local-state-query queries gOuroboros does not decode or re-encode exactly** (kind 2: recorded)

- **What differs.** Reference: the hard-fork combinator's `QueryAnytime` (`GetEraStart`) and Byron's own queries are decoded; the era history (`GetInterpreter` result) is written as an indefinite-length list; UTxO address and input filters keep tag 258 from Conway. gOuroboros: `BlockQuery` knows only `QueryIfCurrent` and the hard-fork queries, so `QueryAnytime` and Byron queries fail to decode; decoded UTxO filters are plain slices and re-encode without the tag; the era history reply has no list encoder (each era summary re-encodes byte for byte).
- **Spec.** Silent
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/Combinator/Ledger/Query.hs` 106-108 (`QueryAnytime`); goldens `Query_AnytimeByron`, `Query_AnytimeShelley`, `Query_Byron`, `Result_HardFork`
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/localstatequery/queries.go` 175-199; pinned by `reference_golden_test.go` on `test/localstatequery-reference` `a83f7d2b`
- **Verdict.** does not conform (decode); conforms (re-encode: both forms decode)
- **Status.** Recorded


### N52

**DMQ: KES evolution a message signature is checked at** (kind 1: fixed on a local branch)

- **What differs.** Reference: verifies at `sigKESPeriod - ocertKESPeriod`, after checking the claimed period lies in `[ocertKESPeriod, ocertKESPeriod + maxKESEvo)`; the node's slot plays no part. gOuroboros: main verifies at `currentKESPeriod - ocertKESPeriod`, so a message signed late in one period is refused once the period turns, and one signed at the current period while claiming an earlier one is accepted (dmq-node answers that with `InvalidKESSignature` and disconnects the peer).
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 395-402: "Verify the KES signature of the message body with the KES verification key from the operational certificate" (no period named)
- **Reference.** dmq-node `a267003c14e9` `dmq-node/src/DMQ/Protocol/SigSubmission/Validate.hs` 156-161, 207-212; test generator `dmq-node/test/DMQ/Protocol/SigSubmission/Test.hs` 458 signs at the same evolution
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/common/authentication.go` `verifyKESSignature` and `verifyKesComponents`; branch `fix/dmq-kes-claimed-period` `7e1a0820`, test `TestVerifyMessageKESPeriodAsReference` (3 of 11 cells fail on main)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on a local branch, no PR. The second commit (`db6103a6`) also drops main's check that the opcert window contains the node's current KES period (N56): `CurrentSlot`, `SlotsPerKESPeriod` and `VerifyMessageWithSlot`'s slot become unused and deprecated

### N53

**DMQ: message expiry bounds** (kind 1: fixed on a local branch)

- **What differs.** Reference: `posixNow <= expiresAt` and `expiresAt < now + maxSigExpiresAtDelay` (1800 s), with `now` at sub-second precision. gOuroboros: main truncates `now` to whole seconds and accepts `expiresAt <= now + maxTTL`.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 336-337
- **Reference.** dmq-node `a267003c14e9` `dmq-node/src/DMQ/Protocol/SigSubmission/Validate.hs` 115-122; `dmq-node/src/DMQ/Policy.hs` 60-61
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/common/authentication.go` `TTLValidator.ValidateMessageTTLAt`; branch `fix/dmq-ttl-reference-bounds` `1f492baf`, test `TestValidateMessageTTLAtAsReference`
- **Verdict.** does not conform → conforms
- **Model.** `dmq` `MempoolExpiry.tla`: `MempoolExpiryMainBug.cfg` (main `IsValidAt`) fails `HeldAsReference`; `MempoolExpiry.cfg` (the fix) passes. Truncation alone, with a strict bound, is an equivalent mutant for whole-second expiries.
- **Status.** Fixed on a local branch, no PR. The second commit (`5d48a376`, `TestIsValidAtAsReferenceMempool`) gives `DmqMessage.IsValidAt`, which prunes the local notification queue, the mempool's rule: dmq-node's mempool worker drops a message once `expiresAt <= now` at full precision (`NodeKernel.hs` 313-330). Admission accepts a message arriving exactly at its expiry and the mempool drops it at that instant; both follow the reference

### N54

**DMQ: message body size** (kind 1: fixed on a local branch)

- **What differs.** Reference: the decoder refuses a body under 90 or over 2000 bytes. gOuroboros: main accepts any size, so it can accept and relay a message dmq-node refuses as a decode failure.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 155: "messageBody = bstr .size (90..2000)"
- **Reference.** `dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs` 193-202; `dmq-node/src/DMQ/Policy.hs` 42-49
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/common/authentication.go` `verifyMessageInternal`; branch `fix/dmq-message-body-size` `9804e9d9`, test `TestVerifyMessageBodySizeAsReference`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on a local branch, no PR. The second commit (`52c1b032`, `TestDmqMessageDecodeRefusesBodySize`) refuses the body when decoding, in both the current and legacy shapes, so an expired message with a bad body fails the whole reply and closes the connection, as in dmq-node (model `dmq` `MessageIngressSizeAfterExpiryBug.cfg`). The authenticator keeps its check for locally built messages

### N55

**DMQ: batch commit and opcert counters** (kind 1: fixed on a local branch)

- **What differs.** Reference: one STM transaction checks each message against the counters the earlier ones recorded. gOuroboros: main's `PrepareMessages` commit re-checks only each pool's last counter in the batch, so a batch `[p:1, p:2]` prepared before another commit recorded `p:2` still commits and accepts `p:1`.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 411
- **Reference.** dmq-node `a267003c14e9` `dmq-node/src/DMQ/Protocol/SigSubmission/Validate.hs` 96-100, 183-197
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/common/authentication.go` `PrepareMessages`; branch `fix/dmq-commit-recheck-every-counter` `aa2673b6`, test `TestPrepareMessagesCommitRechecksEveryCounter`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on a local branch, no PR

### N56

**DMQ: checks dmq-node does not make, and its rate limit** (kind 1: fixed on local branches)

- **What differs.** main refuses a message whose opcert counter is below the node's chain-state counter (`PoolOpCertIssueNumber`) and one whose opcert window does not contain the node's current KES period; dmq-node makes neither check, so it accepts and relays such messages. dmq-node refuses a message less than `vcMinSigDelay` (60 s) after the last one it accepted from the same pool (`SigTooFrequent`, checked right after expiry; the time is recorded only on acceptance; node-to-node peers are disconnected, local submitters get an invalid reply); main has no limit.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 397-402 (the required steps: opcert, KES signature, stake, message id; neither check named); 405-411 (a hedged warning, "We also probably need to make sure...", offering the chain, earlier messages or the Mithril registration as counter sources); 528 (rate limiting suggested as a defence)
- **Reference.** dmq-node `a267003c14e9` `dmq-node/src/DMQ/Protocol/SigSubmission/Validate.hs` 124-145, 156-161, 183-197, 207-212; `dmq-node/src/DMQ/Policy.hs` 52-55; `dmq-node/app/Main.hs` 199-221
- **gOuroboros.** gOuroboros `62fa36d1` `protocol/common/authentication.go` `verifyMessageInternal` Step 4, `verifyKESSignature`. Branches: `fix/dmq-drop-chain-counter-check` `aa7c8605` (`TestVerifyMessageIgnoresChainCounter`; on main "issue number is stale"); `fix/dmq-kes-claimed-period` `db6103a6` (the two current-period cells of `TestVerifyMessageKESPeriodAsReference`); `fix/dmq-sig-rate-limit` `d4c8c2f1` (`TestVerifyMessageRateLimitAsReference`, 4 of 7 cases fail on main)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branches, no PR. The rate limit lives in `MessageAuthenticator`, which also re-verifies messages gOuroboros already accepted (relay, notification replay); an accepted ID is exempt, as dmq-node never re-validates a message in its mempool. `MinSigDelay` configures it; negative turns it off (dmq-node's `vcMinSigDelay = 0`)

### N57

**DMQ: bytes the message id and KES signature cover** (kind 1: fixed on a local branch)

- **What differs.** Reference: hashes and verifies the payload bytes exactly as received (`sigSignedBytes`, cut from the wire between two decoder offsets). gOuroboros: main re-encodes the decoded payload, so a payload with a non-minimal integer width that dmq-node accepts gets a different ID and fails its signature.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 370-376
- **Reference.** dmq-node `a267003c14e9` `dmq-node/src/DMQ/Protocol/SigSubmission/Validate.hs` 60-64, 207-212; `dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs` 169-181
- **gOuroboros.** gOuroboros `ebc63eab` `protocol/common/dmq.go` `DmqMessagePayload`; branch `fix/dmq-payload-preserved-bytes` `d21d3969`, test `TestVerifyMessageHashesPayloadBytesAsReceived` (main: "message ID mismatch")
- **Verdict.** does not conform → conforms
- **Status.** Fixed on a local branch, no PR. `DmqMessagePayload` embeds `DecodeStoreCbor`; `MarshalCBOR` emits the decoded bytes, so a relayed message keeps its ID. A legacy-shape payload keeps no bytes (they include the message ID). Model `dmq` `MessagePayloadBytesReencodeBug.cfg` (main) / `MessagePayloadBytes.cfg` (fix); relay mutation `MessagePayloadBytesRelayReencodeBug.cfg`.

### N58

**DMQ: what node-to-node receipt does with each message** (kind 1: fixed on a local branch)

- **What differs.** Reference: the mempool writer reads the clock once, drops messages already held without validating them, validates the rest one at a time, adds the valid ones, then traces `SigExpired`, `PoolNotEligible`, `UnrecognizedPool`, `NotInitialized` and `SigDuplicate` and throws for any other error, closing the connection. The first failing check, in `Validate.hs` order (expiry, rate, id, KES window, pool, counter, signatures), names the error. gOuroboros: main's `messagesubmission.Server.handleReplyMessages` refuses the whole reply and closes the connection when any message fails, including an expired one or one from a pool without stake, and checks the pool before the KES window and the signatures before the counter.
- **Spec.** CIPs `db48da14bff1` `CIP-0137/README.md` 402: "If any of these step fails, the message is considered as invalid, which is a protocol violation"; 336 (an expired message is invalidated, not a violation)
- **Reference.** `dmq-node/app/Main.hs` 199-221; ouroboros-network `4646039f` `ouroboros-network/lib/Ouroboros/Network/TxSubmission/Mempool/Simple.hs` 183-245; dmq-node `a267003c14e9` `dmq-node/src/DMQ/Protocol/SigSubmission/Validate.hs` 115-212
- **gOuroboros.** gOuroboros `ebc63eab` `protocol/messagesubmission/server.go` `handleReplyMessages`; branch `fix/messagesubmission-reference-receipt` `a12edd17`: `TestServerReceivesRepliesAsReference` (5 of 7 cells fail on main), `MessageAuthenticator.PrepareEach`, `ErrStakeDistributionUnavailable`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on a local branch, no PR. The body size is refused at decode (N54), before expiry, as in dmq-node. Duplicates are dropped per connection (`deliveredIDs`) and, with the rate limit, exempt from it node-wide

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
- **Status.** Fixed on local branch `fix/consensus-tpraos-overlay` (`78f2f391`), merged as #3201. Breaking: every caller must now pass `Overlay` for TPraos headers. No production caller in gOuroboros or Dingo

### C16

**Header envelope: ObsoleteNode, header size, body size** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: the protocol major (the header's own in TPraos, the ledger view's in Praos) is at most the node's maximum, the header size at most `maxBlockHeaderSize`, the declared body size at most `maxBlockBodySize`. gOuroboros: main does not check them in `ValidateHeader`; the branch requires `Envelope` in every mode and returns `ErrMissingHeaderInput` alone when an input is missing.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex` 1682-1687 (`chainChecks`)
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Protocol/EnvelopeChecks.hs` 77-91; `Protocol/TPraos.hs` 69-80; `Protocol/Praos.hs` 82-106; cardano-ledger `eras/shelley/impl/src/Cardano/Ledger/Chain.hs` 65-82
- **gOuroboros.** gOuroboros `f9ba2d3c` `consensus/validate.go`; branch `78f2f391` `consensus/overlay.go` (`validateEnvelopeLimits`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on the same branch, merged as #3201. `VerifyBlock` already checks the sizes from protocol parameters

### C17

**Byron slot to epoch past Byron** (kind 4: gOuroboros outside the spec)

- **What differs.** Reference: slot-to-epoch goes through the era history, each era with its own epoch size. gOuroboros: `ByronConfig.SlotToEpoch` uses `slot / SlotsPerEpoch` for any slot; the branch adds `EndSlot` (from the era history) and `SlotToEpochChecked`, which refuses a slot at or past it.
- **Spec.** ouroboros-consensus `ec239d57f618` `docs/tech-reports/report/chapters/hfc/time.tex` 142-177
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/HardFork/History/Qry.hs` 366-378, 496-523
- **gOuroboros.** gOuroboros `f9ba2d3c` `consensus/byron/byron.go` (`SlotToEpoch`); branch `70d83369` same file (`SlotToEpochChecked`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/consensus-byron-slot-epoch` (`70d83369`), no PR yet. Only tests call it. The empty era history decode fixed in the same PR #3205: model `consensus-eras` `EraHistoryDecodeMainBug.cfg` (main) / `EraHistoryDecode.cfg`; a tagged one-era reply still decodes, which the reference refuses (`EraHistoryDecodeTaggedFixBug.cfg`; harmless with a reference peer).

## Ledger

### L1

**Pool registration when the caller's view is stale** (kind 1: open PR moves to the reference)

- **What differs.** Reference: registered means present in `psStakePools`, which POOLREAP clears at the epoch boundary. gOuroboros: main: trusts the caller's `IsPoolRegistered`, so a stale view lets a delegation to (or retirement of) a reaped pool through, and treats re-registering a reaped pool as a re-registration; PR: one epoch-aware predicate.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/delegation.tex` line 1137; `epoch.tex` POOLREAP 564-572: "c ∈ DCertDeleg ⇒ dpool c ∈ dom poolParams"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Deleg.hs` 329-331; `.../Rules/Pool.hs` 299
- **gOuroboros.** gOuroboros `d0b95845` `ledger/shelley/rules.go` 791, 1652; `ledger/common/block_state.go` 747-752; PR #3129 head `97dc89b2` `ledger/common/pool_deposit.go` 43 (`PoolRegistered`), `block_state.go` 163, `ledger/common/rules.go` `LedgerStateCapabilityParent`
- **Review follow-up.** At `24916e07` the Dijkstra voter check read a committee view that hid the epoch, so a vote by a registered pool with a pending retirement was refused (reference: Conway `Rules/Gov.hs` 473, 596-604 accepts any `psStakePools` member). Fixed at `97dc89b2`; model `ledger-shelley` `VoterHidesEpochBug` / `EpochAware`
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3129 (head `e7b4261d`, main merged in). Dingo's view already satisfies the contract

### L2

**Transaction id of a body without stored CBOR** (kind 1: open PR moves to the reference)

- **What differs.** Reference: a body always carries its serialization. gOuroboros: main: hashes empty input, the same id for every such body; PR: hashes the body's encoding. Review follow-up: a Dijkstra body with an empty, non-nil CIP-159 map (keys 24 to 27) failed to encode and fell back to the empty-input hash, so `{TxFee:5}` and `{TxFee:6}` collided again. The encoder now omits an empty map as the reference does, and a body that still cannot be encoded gets the zero id rather than a hash that looks real.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/crypto-details.tex`, "Abstract functions", lines 64-69: "txid ... is implemented as the BLAKE2b-256 hash of the CBOR serialization of the transaction body"
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/TxBody.hs` 518-552 (`encodeTxBodyRaw`: `Omit` on an empty map at keys 24 to 27; the decoder refuses one, 449-452). Otherwise n/a: the reference keeps a decoded or built body's bytes with it, so this state cannot arise
- **gOuroboros.** gOuroboros `d0b95845` `ledger/common/tx.go` 719-721; PR #3141 head `236fdccd` same file 734 (`TransactionBodyId`), `ledger/dijkstra/dijkstra.go` (`validateDijkstra*ForEncoding`)
- **Verdict.** does not conform → conforms
- **Status.** Open PR #3141. Decoded bodies were always right; bodies built in code were wrong. No TLA+ model: the id is a pure function of the body, with no state or interleaving to model, so Go tests cover it (`TestTransactionBodyIdHashesBodyEncoding`, `TestDijkstraBodyIdOmitsEmptyMaps`, `TestDijkstraSubTransactionBodyIdOmitsEmptyMaps`, `TestTransactionBodyIdOfUnencodableBodyIsZero`). The `AGENTS.md` and `CLAUDE.md` wording fix in the same PR cannot affect any model. Model `ledger-txid` `TxBodyIdMainBug.cfg` (main) and `TxBodyIdDraftBug.cfg` (the first draft) / `TxBodyId.cfg` (merged #3141).

### L3

**Conway CC vote with a nil voter key** (kind 1: open PR moves to the reference)

- **What differs.** Reference: not representable. gOuroboros: main: `UtxoValidateCCVotingRestrictions` panics; PR: skips it as the sibling rules do.
- **Spec.** spec silent
- **Reference.** n/a
- **gOuroboros.** gOuroboros `d0b95845` `ledger/conway/rules.go` 4663-4666; PR #3155 head `b5294771` same file 4666
- **Verdict.** conforms
- **Status.** Open PR #3155. Library defect, hand-built transactions only. Model `ledger-governance` `GovVoterNilMainBug.cfg` (main) / `GovVoterNil.cfg` (merged #3155).

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

### L14

**Proposed protocol version in a classic parameter update** (kind 1: local branch moves to the reference)

- **What differs.** Reference: `decodeProtVer` reads a `Word32` minor and a major bounded by the era's `ProtVerHigh + 1`. gOuroboros: major and minor both limited to 16 bits, so a minor above 65,535 is refused; branch: minor up to 32 bits. The major bound still differs (gOuroboros 65,535; reference 3 to 9 by era), but the PPUP version-can-follow rule rejects any such proposal, so only the failure class differs.
- **Spec.** Shelley formal spec `update.tex` (`pvCanFollow`); silent on widths
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/BaseTypes.hs` 212 (`pvMinor :: Word32`), 254-264 (`decodeProtVer`); `eras/shelley/impl/src/Cardano/Ledger/Shelley/PParams.hs` 490-505
- **gOuroboros.** gOuroboros `cc300dc8` `ledger/common/pparam_update_validation.go` 198-212 (`ValidateProtocolParameterUpdateDomains`)
- **Verdict.** does not conform → conforms (minor); major: conforms (outcome)
- **Status.** Fixed on local branch `fix/ledger-pparam-update-minor-width` (`5b42b5aa`), open PR #3278. Allegra shares Shelley's update type, so an era-exact major bound would need its own type. Model `ledger-codec` `ProtVerWidthMainBug.cfg` (main) / `ProtVerWidth.cfg` (fix). The model finds one corner the fix does not follow: the reference computes the next minor in `Word32`, so from `(2, maxBound)` it lets `(2, 0)` follow, which the fix refuses (`ProtVerWidthWrapBug.cfg`).

### L15

**Zero-coin output in a PlutusV2/V3 TxInfo** (kind 1: local branch moves to the reference)

- **What differs.** Reference: an output value is `transValue (MaryValue c m) = transCoinToValue c <> transMultiAsset m`, and `transCoinToValue` is `PV1.singleton adaSymbol adaToken c` for any `c`, so a zero coin still gives an ada entry of 0. gOuroboros main: `ShelleyTransactionOutput`, `MaryTransactionOutput`, `AlonzoTransactionOutput` and `BabbageTransactionOutput` `ToPlutusData` write the ada entry only when the coin is positive. These are the TxOut encodings of a PlutusV3 TxInfo's inputs, reference inputs and outputs (V1/V2 go through `WithZeroAdaAsset`, which was already right).
- **Spec.** Alonzo formal spec `txinfo.tex` (`transValue`); silent on zero
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/TxInfo.hs` 186-187, `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Plutus/TxInfo.hs` 417-418, `eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs` 158; golden `eras/conway/impl/golden/translations.cbor`
- **gOuroboros.** gOuroboros `cc300dc8` `ledger/shelley/shelley.go` 858, `ledger/mary/mary.go` 713, `ledger/alonzo/alonzo.go` 641, `ledger/babbage/babbage.go` 1080
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/script-context-zero-ada-output` (`51c2b6f3`), open PR #3281; test `TestTxOutPlutusDataKeepsZeroAda` fails on main for all four eras. Pinned by `TestTxInfoMatchesLedgerTranslationGoldens` on `test/script-context-reference` (`3b3be7c0`, stacked on the fix). Unreachable on chain today: the minimum-UTxO rule keeps every output's coin positive. Model `ledger-codec` `TxOutValueDataMainBug.cfg` (main) / `TxOutValueData.cfg` (fix).

### L16

**PlutusV1 TxInfo with a redeemer that points at nothing** (kind 3: stricter, same outcome)

- **What differs.** Reference: the Alonzo PlutusV1 `toPlutusTxInfo` never reads redeemers, since `PlutusLedgerApi.V1.Contexts.TxInfo` has no redeemer field. gOuroboros: `NewTxInfoV1FromTransaction` resolves every redeemer's purpose and fails with "does not match any script purpose" on a dangling one.
- **Spec.** n/a
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Plutus/TxInfo.hs` 137-165; plutus `bdc12f105a98` `plutus-ledger-api/src/PlutusLedgerApi/V1/Contexts.hs` 100-111
- **gOuroboros.** gOuroboros `cc300dc8` `ledger/common/script/context.go` 285, `ledger/common/script/purpose.go` 39
- **Verdict.** conforms (stricter)
- **Status.** Recorded. The UTXOW extraneous-redeemer rule rejects such a transaction before phase 2, so no block or mempool outcome differs. 98 of the 100 Alonzo golden instances carry such redeemers; the golden test clears them for V1

### L17

**Reward update arithmetic** (kind 1: local branch moves to the reference)

- **What differs.** Reference: `startStep` takes deltaR1 = floor(min(1, eta) * rho * reserves) with eta = 1 when d >= 0.8 and blocks / floor((1-d) f slots) otherwise, the treasury takes floor(tau * (fees + deltaR1)), and each pool that made blocks earns floor(appPerf * maxPool'), 0 when its pledge exceeds its owners' stake; the leader and non-owner members split it by `calcStakePoolOperatorReward`/`calcStakePoolMemberReward`; before protocol version 7 only registered credentials are computed, from 7 unregistered rewards go to the treasury; deltaR2 returns to the reserves. gOuroboros main: `CalculateRewards` splits the whole pot pro rata by a share formula of its own (no nOpt, no pledge check, no circulation), gives blockless pools perfect performance or equal shares, pays owners as members and gives unregistered members' shares to the operator; `CalculateAdaPots` floors twice, ignores d and the exact rates, and drops any existing rewards pot.
- **Spec.** Shelley formal spec `rewards.tex` (`createRUpd`, `maxPool`, `r_operator`, `r_member`); not in the pinned tree
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/shelley/impl/src/Cardano/Ledger/Shelley/LedgerState/PulsingReward.hs` 89-282, `libs/cardano-ledger-core/src/Cardano/Ledger/State/SnapShots.hs` 141-165, `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rewards.hs` 61-292, `.../LedgerState/IncrementalStake.hs` 95-128, `.../Shelley/Era.hs` 256-257
- **gOuroboros.** gOuroboros `cc300dc8` `ledger/common/rewards.go` (`CalculateAdaPots`, `CalculateRewards`)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-rewards-reference` (`9675856a`, cell walk `bdba9c8b`), open PR #3275. `TestCalculateAdaPotsReferenceTable` (5 cells) and `TestCalculateRewardsReferenceTable` (2) fail on main. Model `specs/ledger-rewards`. Production impact: Dingo computes rewards in its own `ledger/rewards` package; gOuroboros's calculator is reached through `RewardService`, the ouroboros-mock callback and Dingo's conformance state provider. The fix adds `DesiredPools` (required), `DecentralizationRate` and `RewardSnapshot.TotalStake`; callers that leave `DesiredPools` zero now get an error

### L18

**Repeated pool owner in the pledge check** (kind 1: local branch moves to the reference)

- **What differs.** Reference: a pool's owners are a set (`sppOwners :: Set (KeyHash Staking)`), and the self-delegated owners' stake is summed over that set before the pledge check. gOuroboros main: `ValidatePoolPledge` sums once per `PoolOwners` list entry, so an owner listed twice counts twice and can meet a pledge the reference rejects.
- **Spec.** Shelley formal spec: pool owners are a set
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/State/StakePool.hs` 494, `.../State/SnapShots.hs` 230-235, `eras/shelley/impl/src/Cardano/Ledger/Shelley/Rewards.hs` 256
- **gOuroboros.** gOuroboros `cc300dc8` `ledger/common/rewards.go` `ValidatePoolPledge`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-rewards-reference` (`203f3624`, same file as L17), open PR #3275. `TestValidatePoolPledgeCountsEachOwnerOnce` fails 2 of 6 cells on the parent commit. Model `specs/ledger-rewards` `RewardPotsOwnerListBug.cfg`. No caller outside gOuroboros tests (workspace search)

### L19

**Committee certificate after an in-block UpdateCommittee proposal** (kind 1: local branch moves to the reference)

- **What differs.** Reference: LEDGER passes CERTS the committee proposals of the state the block's earlier transactions left, and GOVCERT accepts a hot-key authorization or resignation from a cold credential any of them would add. gOuroboros main: `BlockLedgerState` records the proposal, but `CommitteeMember` and `CommitteeCredentialStateFor(...).CommitteeCredentialMember` ask only the wrapped state, so `UtxoValidateCommitteeCertificates` rejects the later transaction.
- **Spec.** n/a (Conway formal spec GOVCERT, same rule)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/conway/impl/src/Cardano/Ledger/Conway/Rules/GovCert.hs` 190-205, `.../Rules/Ledger.hs` 390-416
- **gOuroboros.** gOuroboros `62fa36d1` `ledger/common/block_state.go` `CommitteeMember`, `blockCommitteeCredentials.CommitteeCredentialMember`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-block-state-proposed-committee` (`458e502c`), open PR #3285. `TestBlockLedgerStateTreatsInBlockCommitteeProposalAsPotentialMember` fails on the parent commit. Model `specs/ledger-block-overlay` `GovOverlayGoMainBug.cfg`. Reaches Dingo's mempool and block builder through `utxoref.StateOverlay`

### L20

**`VerifyBlock` issuer in a TPraos overlay slot** (kind 1: local branch moves to the reference)

- **What differs.** Reference: block application validates the header through PRTCL, whose OVERLAY rule rejects a non-active overlay slot and, in an active one, checks the scheduled genesis delegate's cold key and VRF key with no stake. gOuroboros main: `VerifyBlockState` looks every non-Byron issuer up in `LeaderPoolVrfKeyHash`, the pool distribution, so with stake-pool validation on it rejects every valid genesis-delegate block (all of mainnet Shelley epoch 208, where d = 1) and accepts a pool block in a non-active slot.
- **Spec.** cardano-ledger `1210d37fe6bd` `eras/shelley/formal-spec/chain.tex` 1170-1305
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/Rules/Overlay.hs` 219-282, `libs/cardano-ledger-core/src/Cardano/Ledger/Slot.hs` 117-130; ouroboros-consensus `ec239d57f618` `Ouroboros/Consensus/Ledger/Extended.hs`
- **gOuroboros.** gOuroboros `62fa36d1` `ledger/verify_block.go` `VerifyBlockState`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-verify-block-tpraos-overlay` (`ddc16a74`), open PR #3277: `VerifyConfig.TPraosOverlay`, required for Shelley-to-Alonzo blocks unless `SkipStakePoolValidation`. 11 of 17 `TestVerifyBlockStateTPraosOverlay` cells fail with main's issuer path. The classification duplicates `consensus.classifyOverlaySlot` (C15); sharing one is a follow-up. Dingo calls `VerifyBlock` with stake-pool validation skipped and checks the overlay itself

### L21

**Leios voting key past its honoured age** (kind 1: local branch moves to the reference)

- **What differs.** Reference: committee selection offers a pool's key only while `epoch < registeredIn + maxKeyAge`, `maxKeyAge = ceil(maxKESEvo * slotsPerKESPeriod / epochLength) + 2`; past that the seat is keyless and `verifyLeiosCert` refuses any certificate that marks it. gOuroboros main: verifies against whatever keys the caller hands over, and its interface contract says nothing about age, so a caller following it literally makes gOuroboros accept a certificate the reference refuses.
- **Spec.** CIPs `db48da14bff1` `CIP-0164/README.md`, "Key Registration and Rotation", lines 826-834: voting keys rotate on a cadence "which a corresponding key time-to-live should enforce".
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/State/Leios.hs` 115-121 (`honouredKey`), `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Snap.hs` 157-180 (`maxKeyAgeEpochs`); cardano-base `242f1ebde40b` `cardano-crypto-leios/src/Cardano/Crypto/Leios.hs` 312-315
- **gOuroboros.** gOuroboros `ebc63eab` `ledger/common/state.go` 206-217 (`DijkstraLeiosCertificateState`), `ledger/leios/certificate.go` 102-235
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/leios-voting-key-age` (`93c3df5d`), no PR yet. `DijkstraLeiosCertificateState` gains the required `DijkstraLeiosKeyAgeContext` (epoch, mark-epoch length, KES evolutions and period), each `DijkstraLeiosCommitteeMember` its `KeyRegisteredIn`, and `MaxKeyAgeEpochs` computes the bound. With the check disabled, `TestVerifyDijkstraCertificateKeyAge` (first unhonoured epoch, long aged out) and `TestVerifyBlockStateInlinedCertRb/voting_key_in_epoch_21` fail. Breaking; no implementer of the interface exists in Dingo or ouroboros-mock. Model `ledger-leios` `LeiosVotingAgedKeyCallerBug` (main) and `LeiosVotingAgedKeyFixed` (branch)

### L22

**Leios vote encoding** (kind 1: local branch moves to the reference)

- **What differs.** Reference and CIP: a vote is `[announcing_rb_hash, voter_id, vote_signature]`, the id a `Word16` in the reference, and the LeiosVotes protocol's `MsgLeiosVote` carries it. gOuroboros main: `LeiosVote`, carried by LeiosVotes `MsgVote` and the LeiosFetch vote messages, is an earlier draft's `[slot, eb_hash, voter_id, signature]`, so it cannot decode a reference vote; `LeiosPrototypeVote` has the CIP shape but only LeiosNotify offers use it.
- **Spec.** CIPs `db48da14bff1` `CIP-0164/README.md` 3397-3410 (CDDL `leios_vote`), 1541-1542 (`MsgLeiosVote`)
- **Reference.** ouroboros-consensus `ec239d57f618` `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Leios/Types.hs` 254-278
- **gOuroboros.** gOuroboros `ebc63eab` `ledger/common/leios.go` 71-90; `protocol/leiosvotes/messages.go` 72; `protocol/leiosfetch/validate.go` 141
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/leios-vote-shape` (`eb4c2421`), no PR yet. The vote captured from the rc-2026w41 prototype node decodes and re-encodes byte for byte (fails to decode on main: "cannot decode CBOR array to struct with different number of elements"). The reference ships no golden vote bytes at `ec239d57f618`. `LeiosLegacyVote` keeps the earlier shape for LeiosNotify offers. A LeiosFetch votes reply can now be matched to its request only by voter, since the vote no longer names its slot. Breaking for Dingo (`ledger/leios/manager.go`, `ouroboros/leios_*`). Model `ledger-leios` `LeiosVoteShapeMainBug.cfg` (main) / `LeiosVoteShape.cfg` (fix).

### L23

**Dijkstra committee certificate for a member an earlier level proposed** (kind 1: local branch moves to the reference)

- **What differs.** Reference: a sub-transaction's SUBCERTS get the committee proposals of the state the earlier sub-transactions left, and the top's CERTS those after every sub-transaction, so an authorization or resignation by a cold credential an earlier level's UpdateCommittee proposal would add is accepted; a level's own proposal comes after its certificates and does not count. gOuroboros main: `dijkstraGovernanceStateView` records the earlier levels' proposals, but `CommitteeCredentialMember` consults only tracked committee changes and the wrapped state, so `UtxoValidateCommitteeCertificates` rejects the certificate ("not a CC member"). Same class as L19, inside one batch.
- **Spec.** formal-ledger-specifications `60b68036c8b4` `src/Ledger/Dijkstra/Specification/Ledger.lagda.md` (LEDGER-V: top-level CERTS from the post-SUBLEDGERS state, `allColdCreds govState₁`; SUBLEDGER-V `allColdCreds govState₀`)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/conway/impl/src/Cardano/Ledger/Conway/Rules/GovCert.hs` (`isPotentialFutureMember`), `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/SubLedger.hs` 259-299, `.../Rules/Ledger.hs` 430-478
- **gOuroboros.** gOuroboros `ebc63eab` `ledger/dijkstra/rules.go` `dijkstraGovernanceStateView.CommitteeCredentialMember`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/dijkstra-committee-proposed-member` (`0a8bde9f`), open PR #3245. `TestDijkstraCommitteeCertificateForEarlierLevelProposedMember` fails 2 of 4 cases on the parent commit. Model `specs/ledger-conway-dijkstra` `SubGovGoComMainBug.cfg`; with the fix applied, all 52,416 DRep and committee cells (proposals included) agree with the reference, and 7 fail without it. Only Dijkstra batches with sub-transactions reach it

### L24

**Dijkstra parameter-update well-formedness: eMax and pledge leverage** (kind 1: local branch moves to the reference)

- **What differs.** Reference: Dijkstra's `ppuWellFormed`, which GOV and SUBGOV apply to every ParameterChange proposal (`actionWellFormed`), adds to Conway's conditions that a set `eMax` is not zero and that a set pledge leverage cap is at least 1; an update that removes the cap is allowed. gOuroboros main: `validateDijkstraProtocolParameterUpdate` checks Conway's non-zero fields and only that the leverage is a non-negative ratio, so both proposals are accepted at the top level or in a sub-transaction.
- **Spec.** formal-ledger-specifications `60b68036c8b4` `src/Ledger/Dijkstra/Specification/PParams.lagda.md` 318-326 (`paramsUpdateWellFormed`: `Maybe.All (Maybe.All (1 ≤ l)) maxPledgeLeverage`; it lists no `eMax`, `nOpt` or emptiness condition, which the reference adds, and requires a Leios quorum threshold above 1/2, which the reference does not)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/PParams.hs` 1150-1172
- **gOuroboros.** gOuroboros `0dbd0f11` `ledger/dijkstra/rules.go` `validateDijkstraProtocolParameterUpdate`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/dijkstra-ppu-well-formed` (`9f7e7d38`), open PR #3246. `TestDijkstraParameterUpdateWellFormedEMaxAndPledgeLeverage` fails 2 of 6 cases on the parent commit. Two existing tests that asserted acceptance of a leverage of 0 and 1/2 now expect refusal. Model `specs/ledger-conway-dijkstra` `SubGovGoPpuMainBug.cfg`; with the fix all 1,308 proposal-check cells agree, and 96 fail without it. Where the spec and the reference differ on `eMax` and the Leios quorum, gOuroboros follows the reference

### L25

**Tags before a tag 30 rational** (kind 1: local branch moves to the reference)

- **What differs.** Reference: `decodeRational` (version 9 and later) consumes one tag 30 if present and fails on any other tag number; the list decoder that follows refuses a second tag. gOuroboros main: `Rat.UnmarshalCBOR` calls `SkipTags`, which removes every leading tag of any number.
- **Spec.** RFC 8949 section 3.4 and the IANA tag 30 registration (one tag around a two-element array)
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/Decoder.hs` 465-484 (`decodeRational`), 1347-1354 (`allowTag`)
- **gOuroboros.** gOuroboros `2fe26494` `cbor/tags.go` `Rat.UnmarshalCBOR`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/cbor-rat-single-tag` (`fe4f8206`), open PR #3282. `TestRatAcceptsOnlyOneTag30` fails on the parent for `d81f820102` and `d81ed81e820102`. `TestRatRejectsOversizedArrayBeforeDecoding/nested_tags` asserted the old read-through-every-tag behaviour and now expects the second-tag refusal. Model `cbor-codec` `CborRationalMainBug.cfg`, `CborRationalMainNestedBug.cfg` (main) / `CborRational.cfg` (fix). The model finds the fix incomplete for ledger fields: every `cbor.Rat` ledger field is a `UnitInterval` or `NonNegativeInterval` in the reference, which requires tag 30 at every version (`assertTag 30`, `BaseTypes.hs` 386-428, `Plain.hs` 159-189), and the fix, following `decodeRational`, still accepts the untagged `820102` (`CborRationalBoundedFixBug.cfg`).

### L26

**Plutus Data constructor whose fields are not a list** (kind 1: local branch moves to the reference)

- **What differs.** Reference: `decodeConstr` reads the content of tags 121-127 and 1280-1400, and the second element under tag 102, with `decodeListOf`, so any other item fails. gOuroboros main: `ConstructorDecoder.UnmarshalCBOR` keeps whatever item follows as the fields.
- **Spec.** conway.cddl `constr<a0>` (`#6.121([* a0])` ... `#6.102([uint, [* a0]])`)
- **Reference.** plutus `bdc12f105a98` `plutus-core/plutus-core/src/PlutusCore/Data.hs` 286-307 (`decodeConstr`)
- **gOuroboros.** gOuroboros `2fe26494` `cbor/constructor.go` `ConstructorDecoder.UnmarshalCBOR`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/cbor-constructor-fields-list` (`a37a8a90`), open PR #3283. `TestConstructorFieldsMustBeAList` fails 12 checks on the parent (six encodings, each through `ConstructorDecoder` and `Value`). Model `cbor-codec` `PlutusConstrFieldsMainBug.cfg` (main) / `PlutusConstrFields.cfg` (fix).

### L27

**Generic `Value` decode of a tag 258 set of maps with composite keys** (kind 1: local branch moves to the reference)

- **What differs.** gOuroboros main: `Value` hands tag 258 content to the library's interface decoding, which cannot hold a map keyed by an array or a map. RFC 8949 permits such keys and Conway proposal procedures (a tag 258 set) contain committee-update maps keyed by credentials.
- **Spec.** RFC 8949 section 3.1 (map keys are any data item)
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/conway/impl/golden/tx.cbor` (field 20) decodes with the reference
- **gOuroboros.** gOuroboros `2fe26494` `cbor/value.go` `Value.unmarshalCBOR` (tag branch)
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/cbor-value-set-members` (`3a442a45`), open PR #3284. `TestValueDecodesSetMembersWithCompositeMapKeys` fails on the parent for three encodings and the Conway golden. Model `cbor-codec` `ValueSetMembersMainBug.cfg` (main) / `ValueSetMembers.cfg` (fix). An unrecognised tag around such a map is still refused (`ValueSetMembersOtherTagFixBug.cfg`); no Cardano structure carries one.

### L28

**Bignum MultiAsset quantity** (kind 1: local branch moves to the reference)

- **What differs.** Reference: Mary `decodeMultiAssetMaps` and the mint decoder read each quantity as a plain CBOR integer. gOuroboros main: `MultiAsset[T].UnmarshalCBOR` decodes into `big.Int`-capable targets, which take a bignum.
- **Spec.** conway.cddl `multiasset<positive_coin>` and `mint = multiasset<nonZeroInt64>`
- **Reference.** cardano-ledger `1210d37fe6bd` `eras/mary/impl/src/Cardano/Ledger/Mary/Value.hs` 299-308, 369-393
- **gOuroboros.** gOuroboros `2fe26494` `ledger/common/common.go` `MultiAsset.UnmarshalCBOR`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-multiasset-bignum-quantity` (`4ae0d4f9`), open PR #3279. `TestMultiAssetBignumQuantityAsReference` fails on the parent at pv 8, 9 and 12. Model `cbor-codec` `MultiAssetQuantityMainBug.cfg` (main) / `MultiAssetQuantity.cfg` (fix). The model finds a sibling the fix misses: the coin of a Mary `[coin, multiasset]` pair still accepts a bignum (`82c24105...` decodes with coin 5), which `decodeMaryValue`'s `decodeWord64` refuses (`MultiAssetQuantityCoinInPairFixBug.cfg`).

### L29

**PlutusV2 cost model in an Alonzo parameter update** (kind 1: local branch moves to the reference)

- **What differs.** Reference: the legacy `CostModels` decoder used before version 9 accepts PlutusV1 and PlutusV2. gOuroboros main: `AlonzoProtocolParameterUpdate.ValidateProtocolParameterUpdateVersion` allows only PlutusV1.
- **Spec.** Alonzo ledger spec: `Language` is PlutusV1 only (the reference decoder is wider)
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/CostModels.hs` 307-338
- **gOuroboros.** gOuroboros `2fe26494` `ledger/alonzo/pparams.go` `ValidateProtocolParameterUpdateVersion`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-alonzo-v2-cost-model-update` (`283f75cb`), open PR #3280. `TestAlonzoCostModelUpdateLanguagesAsReference` fails on the parent with "unknown cost model language 1" at pv 5. `classic_ppup_rules_test.go` asserted the old refusal and is updated; conformance vectors pass. Where spec and reference differ, gOuroboros follows the reference. Model `ledger-codec` `CostModelLanguagesMainBug.cfg` (main) / `CostModelLanguages.cfg` (fix).

### L30

**Tag 258 on a pre-Conway set-shaped field** (kind 1: local branch moves to the reference)

- **What differs.** Reference: before protocol version 9, `decodeSet` is `decodeCollection decodeListLenOrIndef` ("set tag 258 is not permitted") and the Shelley and Alonzo witness decoders use `decodeList`, so Shelley to Babbage transactions with a tag on these fields do not decode. gOuroboros main accepted the tag everywhere except transaction inputs.
- **Spec.** Silent (the CDDL's `set<a>` allows the tag from Conway)
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/Decoder.hs` 935-953; `eras/shelley/impl/src/Cardano/Ledger/Shelley/TxWits.hs` 261-273; `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/TxWits.hs` 347-357, 569-580, 660-700, 721-730
- **gOuroboros.** gOuroboros `0fa7a0df` `ledger/common/certs.go` `PoolRegistrationCertificate.UnmarshalCBOR`, `ValidatePreConwayCertificateTypes`; Alonzo and Babbage body and witness-set decoders, Shelley witness set
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/ledger-pre-conway-set-tag` (`e9dd7145`), open PR #3289. `TestPreConwaySetFieldsRefuseTag258` (26 fields across Shelley-Babbage, each with an untagged control) fails all 26 on the parent. Existing tests that asserted tagged owner sets decode pre-Conway, and that tagged duplicate collateral is refused as a duplicate, now expect the tag refusal. Conformance vectors pass. Only tag 258 heads trigger the re-read, so another tag on these fields is still accepted. Model `ledger-codec` `PreConwaySetTagMainBug.cfg`, `PreConwaySetTagMainOtherTagBug.cfg` (main) / `PreConwaySetTag.cfg` (fix). The model finds the fix incomplete: a pre-Conway witness-set field under a tag other than 258 still decodes unless a tag 258 head appears elsewhere in the same map (`PreConwaySetTagOtherTagBug.cfg`; a Shelley vkey list under tag 259 decodes on `e9dd7145`, as do Alonzo fields 0-4 and Babbage fields 0-6).

### L31

**`ConstructorEncoder` field list encoding** (kind 1: local branch moves to the reference)

- **What differs.** Reference: plutus `encodeData` writes a constructor's fields with the Serialise list instance. gOuroboros main encoded the Go slice as a definite list.
- **Spec.** Plutus Data CDDL allows either
- **Reference.** plutus `bdc12f105a98` `plutus-core/plutus-core/src/PlutusCore/Data.hs` 147-160; vectors from `plutus-core/plutus-core/test/CBOR/DataStability.hs`
- **gOuroboros.** gOuroboros `0fa7a0df` `cbor/constructor.go` `ConstructorEncoder.MarshalCBOR`
- **Verdict.** does not conform → conforms
- **Status.** Fixed on local branch `fix/cbor-constructor-indefinite-fields` (`ad7a4f25`), open PR #3290; changes the bytes and hashes of Data built with it. `TestConstructorEncoderAsPlutusDataStability` (two DataStability vectors) and `TestConstructorEncoderFieldListsAsPlutus` fail on the parent. No gOuroboros caller builds datums with it; outside callers are bluefin (`internal/tx`, `internal/miner`), cardano-models (`tuna.go`, `cdns.go`), merkle-patricia-forestry (`proof.go`), shai (`internal/spectrum/models.go`) and vpn-indexer (`internal/txbuilder`), whose built Data and any hashes of it change; their tests that pin bytes need updating. Plain `[]any` List values inside the fields are still definite. Model `cbor-codec` `ConstructorEncodingMainBug.cfg`, `ConstructorEncodingMainSliceBug.cfg` (main) / `ConstructorEncoding.cfg` (fix). Residuals on the fix: a Go array of fields is written definite (`ConstructorEncodingGoArrayFixBug.cfg`), an empty `IndefLengthList` is written `d8799fff` (`ConstructorEncodingEmptyIndefFixBug.cfg`), a byte string over 64 bytes is not split into 64-byte chunks (`ConstructorEncodingLongBytesFixBug.cfg`), and nested lists stay definite (`ConstructorEncodingNestedSliceFixBug.cfg`).

### L32

**Map entry order in Value's Plutus Data JSON** (kind 1: differs from the reference)

- **What differs.** Reference: `plutusDataToJson` renders `Map kvs` in list order. gOuroboros sorts.
- **Spec.** Silent
- **Reference.** cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/Data.hs` 144-150
- **gOuroboros.** gOuroboros `0fa7a0df` `cbor/value.go` `appendAstJsonMap`
- **Verdict.** does not conform
- **Status.** Open, no branch: needs Value to keep map order (an API change); Value's JSON is used for error and diagnostic output, not consensus. Recorded by `TestValueJSONAsReferencePlutusDataToJson`, whose maps are in sorted order

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
- **Status.** Merged #3161 (gOuroboros `1559924b`); #3233 keeps it after merging main (`5cb98604`, model `PipelineLifecycleMainDrain.cfg`). Library defect; not reached through chain-sync or Dingo today

### P4

**An unread `Results` channel** (kind 1: open PR moves to the reference)

- **What differs.** Reference: chain selection never waits on a follower. gOuroboros: main: stalls the apply runner; PR: never blocks commits, drops the oldest result for a reader that falls behind (counted in `ResultsDropped`).
- **Spec.** spec silent
- **Reference.** ouroboros-consensus `ec239d57f618` `.../Storage/ChainDB/Impl/Background.hs` 127 (`addBlockRunner`; followers read the chain themselves)
- **gOuroboros.** gOuroboros `d0b95845` `pipeline/pipeline.go` 701; PR #3161 head `805d32abd` same file 1006-1010
- **Verdict.** conforms
- **Status.** Merged #3161 (gOuroboros `1559924b`)

### P5

**`WithLosslessResults`** (kind 5: gOuroboros-only addition)

- **What differs.** Reference: none. gOuroboros: opt-in with an `ApplyFunc`; always on in header-only and trusted decode-only modes, whose only output is `Results`: every committed block is delivered and commits wait for the reader. At PR head `805d32abd` decode-only modes dropped results unless the caller opted in (review finding; model `pipeline-cbor` `BlockPipelineDecodeOnlyDropBug.cfg`).
- **Spec.** spec silent
- **Reference.** n/a
- **gOuroboros.** PR #3161 head `0dbc3775` `pipeline/pipeline.go` (`Start`, `losslessResults`), `pipeline/options.go` (`LosslessResults`, `WithLosslessResults`)
- **Verdict.** conforms (implementation choice)
- **Status.** On PR #3161 at `0dbc3775` (decode-only modes lossless by default; Dingo's trusted decode-only opt-in is now redundant). Wire: a slower commit only delays chain-sync's next request, which the protocol allows; ledger: unchanged

## Concurrency fixes: library defects, no wire drift

These pull requests fix races, leaks and deadlocks inside gOuroboros. The wire behaviour and the reference rules are unchanged, so they carry no verdict above; the hazard ids are [CONCURRENCY.md](CONCURRENCY.md)'s. Each names the configuration that reproduces `main` (expected to fail) and the one that passes with the fix.

| PR | Hazards | Fails on `main` | Passes with the fix |
| --- | --- | --- | --- |
| #3231 | local message submission answers | `dmq` `LocalMessageSubmissionOwnAnswerNoLockBug.cfg` | `LocalMessageSubmissionOwnAnswer.cfg` |
| #3232 | C8 | `leios-peras` `LeiosFetchRangeDeliveryLeakBug.cfg`, `LeiosFetchRangeDeliveryLeakReleaseBug.cfg` | `LeiosFetchRangeDelivery.cfg`, `LeiosFetchRangeDeliverySecond.cfg` |
| #3233 | C4, C5, C6, C7; P3 | `pipeline-cbor` `PipelineLifecycleParentCancelLeakBug.cfg`, `PipelineLifecycleMuAcrossApplyBug.cfg`, `PipelineLifecycleApplyCallsStopBug.cfg` | `PipelineLifecycleNewStop*.cfg`, `PipelineLifecycleMain*.cfg` |
| #3234 | D1, D2 | `ledger-hash-cache` `TxScopedMemoPanicBug.cfg` | `TxScopedMemo.cfg`, `TxScopedMemoNoPanic.cfg` |
| #3239 | A1, A2, A3 | `connection` `ConnectionTeardownCloseDuringDialBug.cfg`, `ConnectionTeardownWaitGroupBug.cfg`, `ConnectionCloseConcurrentMutualWaitBug.cfg`, `ConnectionTeardownCloseOpenConnBug.cfg` | `ConnectionTeardownFixed.cfg`, `ConnectionCloseConcurrent.cfg` |
| #3253 | A7, A8; callback context | `connection` `ConnectionTeardownNoMuxerJoinBug.cfg`, `ConnectionTeardownMuxerStopPlainBug.cfg`; `engine` `EngineLifecycleCtxRunLoopUnjoinedBug.cfg`, `EngineLifecycleCtxNoMarkerBug.cfg` | `ConnectionTeardownMuxerStop.cfg`, `EngineLifecycleCtx.cfg` |
| #3254 | B1, B2, B3, X1 | `blockfetch` `BlockFetchBusyDeliveryStopLockBug.cfg`, `BlockFetchBusyDeliveryStopJoinBug.cfg` | `BlockFetchBusyDeliveryFixed.cfg`, `BlockFetchBusyDeliveryJoin.cfg` |
| #3264 | B4 | `blockfetch` `BlockFetchClientReaderUnlockedBug.cfg`, `BlockFetchClientReaderOtherInstanceBug.cfg` | `BlockFetchClientReader.cfg` |
| #3272 | B5, B8-B10 and the six restartable servers | `keepalive` `KeepAliveLifecycleReaderUnlockedBug.cfg` | `KeepAliveLifecycleReader.cfg` |
| #3273 | C9, C12, C20 | `keepalive` `KeepAliveLifecycleReaderUnlockedBug.cfg` (same restart; loop joins under #3253) | `KeepAliveLifecycleReader.cfg` |
| #3274 | A9 | `engine` `EngineSendBeforeStartLostBug.cfg`, `EngineSendBeforeStartRaceBug.cfg` | `EngineSendBeforeStart.cfg` |
| #3276 | C13, C14, C15 | `leios-peras` `PerasClientOpMuReentryBug.cfg`, `PerasClientOpMuDoneCtxBug.cfg`, `PerasClientOpMuAwaitPanicBug.cfg`, `PerasClientOpMuAwaitUnjoinedBug.cfg` | `PerasClientOpMu.cfg`, `PerasClientOpMuAnswered.cfg` |

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
- **Leios**: applying an endorser block, checking it against the announced hash and size, applying it at most once, and rollback (model `ledger-leios`); the caller supplies the seated committee: top `Nc` by stake, ties by ascending pool id, keyless when the key is missing or aged out (L21). Vote collection is the caller's too: keep the first valid vote of each seat per election, whichever announcement it is for, and aggregate once the tally reaches the quorum; a certificate cannot show an equivocating seat counted twice (model `ledger-leios` `LeiosVoting`). So is vote timing: drop a vote after its deadline (3 L_hdr + L_vote + L_diff after its slot began) or for an announcement not accepted, accept at most two announcements per election, never record a seat's vote in an election twice even after pruning it, and keep a certificate until the immutable tip passes its slot (model `ledger-leios` `LeiosVoteTiming`).
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
- Leios quorum: CIP-0164 Step 4 says the stake must "exceed" tau, but its formula and the reference (`verifyLeiosCert`, `recordVote`) use `>=`; gOuroboros uses `>=`. Model `ledger-leios`.
- Endorser-block encoding: a bare map with `uint32` sizes (the node) instead of the CIP's array around an ordered map. Model `ledger-leios`.
- Dijkstra parameter-update well-formedness: the reference also refuses a zero `eMax` or `nOpt` and an empty update, and does not require the Leios quorum threshold above 1/2 that the formal spec does (`PParams.lagda.md` 318-326). gOuroboros follows the reference (L24). Model `ledger-conway-dijkstra` `SubGov`.
- Message submission window rules (a non-blocking request may ask for 0 ids if it acknowledges some) and empty `MsgRequestMessages`. Model `dmq`.

## Resolved since the models were written

- Keep-alive server restart after `MsgDone` (merged #3080), and the shutdown race in every restarting server (merged #3087).
- Chain-sync `Stop` without `MsgDone` (merged #3092, now on `main`).
- Handshake accept data and key order, N13 and N14 (merged #3194); TPraos overlay schedule and header envelope, C15 and C16 (merged #3201). Their verdicts above still describe the pinned `main`.

## Does not conform: needs a decision

Entries where gOuroboros on `main` breaks a stated rule, with what would close each one.

No pull request yet (decide whether and how to fix):

- **N18** Block-fetch size limit in `StBusy` (and `StIdle` for a pipelining client). Not fixed; needed by gOuroboros' engine, which judges a message against the state current when it arrives.
- **N21** Tx-submission request over the window from `NodeToNodeV_16`. Fixed in PR #3195 (head `e5c47f5f`).
- **N27** Local-tx-monitor server answers `MsgAwaitAcquire` at once. Opt-in fix in PR #3196 (head `26f0e50a`), which depends on PR #3154 for the client side.
- **N28** Local-tx-monitor `MsgGetMeasures`. Not fixed; a missing feature.
- **N32** Other servers that do not restart after `MsgDone`. Fixed in PR #3197 (head `c107bb53`). Keep-alive, chain-sync, block-fetch, tx-submission, peer-sharing and the three Leios servers do restart on main.
- **C6** Genesis window anchor. Not fixed; correct only if the caller anchors every fragment at one point (model `consensus-genesis`, `OwnAnchorBug`).
- **C8** Genesis window count from `SimpleChainFragment`. The float rounding is fixed on local branch `fix/genesis-window-estimate-rounding` (`74699bf6`, no PR); the estimate itself remains. Callers with real headers should implement `ChainFragment` with a count.
- **C13** The neutral nonce as an identity in the epoch nonce (the rolling part is fixed by #3053). Fixed additively on local branch `fix/nonce-neutral-epoch-and-vrf-input` (`da43d778`), no PR yet: `EpochNonceFromNonces`, `CalculateEpochNonce` deprecated.
- **C14** A neutral epoch nonce in the VRF input. Fixed additively on the same branch, no PR yet: `MkInputVrfFromNonce`, `MkSeedTPraosFromNonce`, `ComputeVRFInputFromNonce`, the `[]byte` builders deprecated. Only a chain with a neutral initial nonce reaches it, in its first epoch.
- **C17** Byron slot to epoch past Byron. Fixed on local branch `fix/consensus-byron-slot-epoch` (`70d83369`), no PR yet.
- **L5** Byron transaction with no inputs or no outputs. Fixed on a local branch, no PR yet.
- **L6** Byron `maxTxSize`. Open, no branch. Adding it changes the API (`VerifyConfig` or `ValidateAgainstUtxo`).
- **L9** Leios committee with fewer pools than `Nc`. Fixed on local branch `fix/leios-committee-size` (`fec72765`), no PR yet. Hits the prototype testnet (committee size 900).

- **L32** Map entry order in Value's Plutus Data JSON. Open, no branch: needs Value to keep map order (an API change); Value's JSON is used for error and diagnostic output, not consensus.
- `IndefLengthByteString` does not check that its chunks are definite byte strings (RFC 8949 F.1); recorded, not changed.

- **N52** DMQ KES signature checked at the current period. Fixed on local branch `fix/dmq-kes-claimed-period` (`7e1a0820`, `db6103a6`), no PR yet.
- **N53** DMQ expiry bounds and `IsValidAt`. Fixed on local branch `fix/dmq-ttl-reference-bounds` (`1f492baf`, `5d48a376`), no PR yet.
- **N54** DMQ body size. Fixed on local branch `fix/dmq-message-body-size` (`9804e9d9`, `52c1b032`), no PR yet; breaking for callers that authenticate bodies under 90 bytes.
- **N55** DMQ batch commit re-check. Fixed on local branch `fix/dmq-commit-recheck-every-counter` (`aa2673b6`), no PR yet.
- **N56** DMQ checks dmq-node lacks, and its rate limit. Fixed on local branches `fix/dmq-drop-chain-counter-check` (`aa7c8605`), `fix/dmq-kes-claimed-period` (`db6103a6`) and `fix/dmq-sig-rate-limit` (`d4c8c2f1`), no PR yet; deprecates `CurrentSlot`, `SlotsPerKESPeriod`, `PoolOpCertIssueNumber`.
- **N57** DMQ payload bytes hashed as received. Fixed on local branch `fix/dmq-payload-preserved-bytes` (`d21d3969`), no PR yet.
- **N58** DMQ node-to-node receipt. Fixed on local branch `fix/messagesubmission-reference-receipt` (`a12edd17`), no PR yet; touches the same function as PR #3130 (they merge with two test-call updates).
Fixed by an open pull request (decide by reviewing and merging it):

- **L14** Proposed protocol minor version above 16 bits. Fixed on local branch `fix/ledger-pparam-update-minor-width` (`5b42b5aa`), open PR #3278.
- **L15** Zero-coin output in a PlutusV2/V3 TxInfo. Fixed on local branch `fix/script-context-zero-ada-output` (`51c2b6f3`), open PR #3281. Unreachable on chain today.
- **L24** Dijkstra parameter-update well-formedness (eMax, pledge leverage). Fixed on local branch `fix/dijkstra-ppu-well-formed` (`9f7e7d38`), open PR #3246.
- **L25** Tags before a tag 30 rational. Fixed on local branch `fix/cbor-rat-single-tag` (`fe4f8206`), open PR #3282.
- **L26** Plutus Data constructor whose fields are not a list. Fixed on local branch `fix/cbor-constructor-fields-list` (`a37a8a90`), open PR #3283.
- **L27** Generic `Value` decode of a tag 258 set of maps with composite keys. Fixed on local branch `fix/cbor-value-set-members` (`3a442a45`), open PR #3284.
- **L28** Bignum MultiAsset quantity. Fixed on local branch `fix/ledger-multiasset-bignum-quantity` (`4ae0d4f9`), open PR #3279.
- **L29** PlutusV2 cost model in an Alonzo parameter update. Fixed on local branch `fix/ledger-alonzo-v2-cost-model-update` (`283f75cb`), open PR #3280.
- **L30** Tag 258 on a pre-Conway set-shaped field. Fixed on local branch `fix/ledger-pre-conway-set-tag` (`e9dd7145`), open PR #3289.
- **L31** `ConstructorEncoder` field list encoding. Fixed on local branch `fix/cbor-constructor-indefinite-fields` (`ad7a4f25`), open PR #3290; changes the bytes and hashes of Data built with it.
- **L23** Dijkstra committee certificate for a member an earlier level proposed. Fixed on local branch `fix/dijkstra-committee-proposed-member` (`0a8bde9f`), open PR #3245.
- **L19** Committee certificate after an in-block UpdateCommittee proposal. Fixed on local branch `fix/ledger-block-state-proposed-committee` (`458e502c`), open PR #3285.
- **L20** `VerifyBlock` issuer in a TPraos overlay slot. Fixed on local branch `fix/ledger-verify-block-tpraos-overlay` (`ddc16a74`), open PR #3277; breaking for callers that validate TPraos issuers.
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

Found by the model in a published fix (route each to its pull request; the fix passes its own cells):

- **L25** (#3282): ledger rationals are `UnitInterval`/`NonNegativeInterval`, which require tag 30; the fix still accepts an untagged ratio (`cbor-codec` `CborRationalBoundedFixBug.cfg`). Fixed on the branch at `aafec34d`: `cbor.Rat` requires one tag 30; query-result plain rationals stay lenient (`CborRational.cfg`, `CborRationalPlain.cfg`).
- **L28** (#3279): the coin of a Mary `[coin, multiasset]` pair still accepts a bignum (`cbor-codec` `MultiAssetQuantityCoinInPairFixBug.cfg`). Fixed at `15156a03` (`MultiAssetQuantity.cfg`).
- **L30** (#3289): a tag other than 258 on a pre-Conway witness-set field still decodes (`ledger-codec` `PreConwaySetTagOtherTagBug.cfg`). Fixed at `37968c05`; `e82a8a6c` also refuses Conway pool owners under a tag other than a single 258 (`PreConwaySetTag.cfg`).
- **L31** (#3290): Go arrays, empty `IndefLengthList`, byte strings over 64 bytes and nested lists are not encoded as plutus `encodeData` does (`cbor-codec` `ConstructorEncoding*FixBug.cfg`). Fixed at `3d91ad2f`, which also chunks bignum magnitudes over 64 bytes (`ConstructorEncoding.cfg`); maps inside fields are still encoded as given.
- **#3205** (merged): a tagged one-era era-history reply still decodes; the reference refuses it (`consensus-eras` `EraHistoryDecodeTaggedFixBug.cfg`). Fixed by PR #3336 (`aad3e65a`, issue #3335; `EraHistoryDecode.cfg`).
- **L14** (#3278): the reference's `Word32` wraparound of the next minor from `maxBound` (`ledger-codec` `ProtVerWidthWrapBug.cfg`); reachable only from a minor already at `maxBound`. Fixed at `5efc10c0` in the classic and hard-fork follow rules (`ProtVerWidth.cfg`).

Also needing a decision, though it conforms: **N37**, because PR #3130 follows dmq-node and so departs from the CIP-0137 text. **L4** is decided by PR #3193: BadInputs checks the reference's set and runs first.
