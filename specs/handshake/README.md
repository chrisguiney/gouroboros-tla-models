# the handshake

The handshake is the first thing two nodes say to each other. The client
sends `MsgProposeVersions`, a table of every version it speaks with the
version data (network magic, query flag, and for node-to-node the diffusion
mode and peer sharing) for each. The server answers once, with
`MsgAcceptVersion`, `MsgRefuse`, or `MsgQueryReply`, and both sides are done.
Nothing else ever runs on mini-protocol 0.

Read [Model `keepalive`](../keepalive/README.md) first: the receive table and the
"checking the checks" ideas carry over.

## What the code does

gOuroboros (`origin/main` at `61046085`):

- `protocol/handshake/handshake.go` has two state maps, `StateMapNtN` and
  `StateMapNtC`: `Propose` (client agency), `Confirm` (server agency), `Done`.
  Both states allow 5760 bytes. Node-to-node waits 10 s in each state;
  node-to-client never times out. `NewClient` and `NewServer` replace the
  waiting side's timeout with `Config.Timeout` (10 s by default).
- `client.go`: `Start` sends the proposal. On `MsgAcceptVersion` the client
  checks the version was proposed, decodes the data, and compares the
  network magic. `MsgRefuse` becomes a typed error. `MsgQueryReply` is
  refused unless the client asked for a query.
- `server.go` (`handleProposeVersions`): first, if **any** proposed version
  that decodes asks for a query, answer `MsgQueryReply`. Otherwise
  intersect the tables, pick the highest common version, and refuse with
  `VersionMismatch` (no common version), `DecodeError` (its data does not
  decode), or `Refused` (magics differ); else accept with the server's own
  data.

## The questions

1. Does the server pick the highest common version (`AcceptsHighestCommon`)?
2. Does it accept only data that decodes with matching magic
   (`AcceptsOnlyMatchingMagic`), and never refuse such a proposal
   (`NoRefusalWhenNegotiable`)?
3. Does every refusal name the right reason (`RefusalReasonsRight`)?
4. Does the server answer a query only for a proposal it would accept
   (`QueryOnlyWhenNegotiable`)?
5. Do both sides end with the same result (`BothSidesAgree`)?
6. Against a rogue server, does the client accept only a version it proposed,
   with its own magic (`ClientAcceptsOnlyProposed`)?
7. Is any state entered that the transition table does not allow
   (`OnlyLegalMoves`, `NeverBothHaveAgency`)?
8. With a silent peer, does node-to-node give up instead of hanging, and does
   node-to-client hang, as the specification intends?
9. Simultaneous open (`HandshakeSimOpen.tla`): when both sides dial at once,
   do both pick the same version (`SymmetricOutcome`, `SimAcceptsHighest`,
   `SameStateWhenQuiet`), and end with the same agreed version data
   (`SimAgreedData`)?
10. Does `MsgAcceptVersion` carry the negotiated data
    (`AcceptCarriesNegotiatedData`)?
11. Does every receiver reject a version table whose recognised keys are
    not in ascending order (`UnorderedMapsRejected`), and accept one with
    an unrecognised key anywhere (`UnknownKeysTolerated`)?

## The answers

Two versions, two magics, and in node-to-node a diffusion-mode flag: every
client table (288) against every server table (24), 6,912 starting pairs
(node-to-client: 80 against 8).

| Config | States | Result |
| --- | --- | --- |
| `Handshake.cfg` (reference, node-to-node) | 27,648 | passes |
| `HandshakeNtC.cfg` (reference, node-to-client) | 2,560 | passes |
| `HandshakeStrictQuery.cfg` (gOuroboros after the fix: strict client) | 27,648 | passes |
| `HandshakeGouroborosBug.cfg` (gOuroboros today: query checked first) | | **fails** `QueryOnlyWhenNegotiable` |
| `HandshakeAcceptOwnDataBug.cfg` (gOuroboros today: accept carries the server's own data) | | **fails** `AcceptCarriesNegotiatedData` |
| `HandshakeKeyOrder.cfg` (reference; client tables in any wire order, with or without an unrecognised key, and one injected table; one magic) | 758,780 | passes |
| `HandshakeKeyOrderUnknown.cfg` (reference; recognised keys ascending, an unrecognised key anywhere) | 47,616 | passes, no failures |
| `HandshakeKeyOrderBug.cfg` (gOuroboros today: key order not checked) | | **fails** `UnorderedMapsRejected` |
| `HandshakeKeyOrderEveryBug.cfg` (strict variant: every key must ascend) | | **fails** `UnknownKeysTolerated` |
| `HandshakeRogue.cfg` (one injected message, reference client) | 2,726,172 | passes |
| `HandshakeRogueStrict.cfg` (the same, gOuroboros client) | 2,726,172 | passes |
| `HandshakeSilentServer.cfg` (node-to-node, server never answers) | 27,648 | passes: the client times out |
| `HandshakeSilentClient.cfg` (node-to-node, client never proposes) | 13,824 | passes: the server times out |
| `HandshakeSilentNtCBug.cfg` (node-to-client, server never answers) | | **deadlock**, by design |
| `HandshakeSimOpen.cfg` (reference) | 4,032 | passes |
| `HandshakeSimOpenGouroborosBug.cfg` (gOuroboros `61046085`: no `MsgReplyVersions`) | | **fails** `NoViolations` |
| `HandshakeSimOpenGouroboros.cfg` (gOuroboros after the fix) | 4,032 | passes |
| `HandshakeSimOpenEarlyReadBug.cfg` (the fix without the wait in `Client.Start`) | | **fails** `NoViolations` |
| `HandshakeSimOpenAsymmetricBug.cfg` (one side's data undecodable by the other) | | **fails** `SymmetricOutcome` |
| `HandshakeSimOpenRawPeerDataBug.cfg` (PR #3127 at `78792c96`: each side ends with the peer's raw data) | | **fails** `SimAgreedData` |
| `HandshakeTable.cfg`, `HandshakeTableGouroboros.cfg` | | print the receive table |

The gOuroboros failure is short: the client proposes only version 1 with the
query flag, the server supports only version 2. The reference refuses with
`VersionMismatch`; gOuroboros answers `MsgQueryReply`. The same happens when
the magics differ (reference: `Refused`) and when only a version that is not
chosen asks for a query (reference: accept the chosen one).

**The data in `MsgAcceptVersion`.** The reference server sends the agreed
data, `acceptableVersion local remote` [R9][R6]; gOuroboros sends its own
data for the chosen version (`AcceptOwnData`). The shortest counterexample:
the client is initiator-only, the server is not; the reference accepts with
initiator-only, gOuroboros with initiator-and-responder. No outcome changes
for a reference client: it recomputes `acceptableVersion` with its own data
[R2], and every combined field (magic equal, diffusion mode `min`, peer
sharing `<>`, query `||`, Peras `min`) is idempotent and commutative, so
`agree(c, agree(s, c)) = agree(c, s)`. The fix
(`fix/handshake-accept-negotiated-data`) sends the agreed data; the
`FinishedFunc` callback still receives the peer's data.

**Key order.** The specification requires every key unique and ascending
[S7]. The reference codec is narrower [R10]: it skips a key its version
codec does not recognise, and fails to decode (a protocol error, not a
`MsgRefuse`) only when a recognised key is not greater than the previous
recognised one. The model follows the reference (`KeyOrderRule =
"Recognised"`). Wire order is a sequence of keys that may include
`Unknown`, a version no receiver recognises. gOuroboros main checks no order
(`"None"`). A strict every-key check (`"Every"`) refuses a peer the
reference accepts, an unrecognised key out of order
(`HandshakeKeyOrderEveryBug.cfg`), so the fix
(`fix/handshake-version-key-order`) checks recognised keys only. Every
encoder sends keys ascending (the reference by `Map` order, gOuroboros by
`SortCoreDeterministic`), so only a broken or hostile peer meets either
check.

The client's strictness about `MsgQueryReply` is harmless: against an honest
server it never fires (`HandshakeStrictQuery.cfg`), because a server only
answers a query the client asked for.

Simultaneous open is safe in the reference. Asymmetric decoding breaks the
symmetry: one side refuses, the other accepts. The specification allows
this ("If any side does not accept any version ... the connection can be
reset"), and the refusing side closes the connection.

### Checking the checks

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `HandshakeLowestBug.cfg` | take the highest common version | `AcceptsHighestCommon` |
| `HandshakeNoMagicBug.cfg` | the server's magic comparison | `AcceptsOnlyMatchingMagic` |
| `HandshakeWrongReasonBug.cfg` | `DecodeError` for undecodable data | `RefusalReasonsRight` |
| `HandshakeClientNoMagicBug.cfg` | the client's magic comparison (rogue server) | `ClientAcceptsOnlyProposed` |
| `HandshakeGouroborosBug.cfg` | negotiating before a query | `QueryOnlyWhenNegotiable` |
| `HandshakeSimOpenGouroborosBug.cfg` | `MsgReplyVersions` | `NoViolations` |
| `HandshakeSimOpenEarlyReadBug.cfg` | proposing before reading | `NoViolations` |
| `HandshakeAcceptOwnDataBug.cfg` | sending the agreed data | `AcceptCarriesNegotiatedData` |
| `HandshakeKeyOrderBug.cfg` | the key-order check | `UnorderedMapsRejected` |
| `HandshakeKeyOrderEveryBug.cfg` | skipping unrecognised keys | `UnknownKeysTolerated` |

Reachability probes, each expected to fail, show the passing configs reach
every answer: `HandshakeProbeAcceptBug.cfg`, `HandshakeProbeQueryBug.cfg`,
`HandshakeProbeMismatchBug.cfg`, `HandshakeProbeDecodeErrorBug.cfg`,
`HandshakeProbeRefusedBug.cfg`, `HandshakeProbeAcceptBelowProposedBug.cfg`
(an accept below a version the client proposed), and
`HandshakeSimOpenProbeRefusedBug.cfg`.

### The modelling mistake

The first rogue run failed `RefusalReasonsRight`. The rogue peer had sent its
own `MsgProposeVersions` before the client's, and the server answered that
one; the invariants compared the answer with the client's table. They now
compare it with the proposal the server actually answered (`heard`).

## The receive table

`HandshakeTable.cfg` prints, for each role, state, and kind of message, what
the receiver does (reference behaviour); `HandshakeTableGouroboros.cfg` the
same with the gOuroboros switches. Differences:

| Cell | Reference | gOuroboros |
| --- | --- | --- |
| client in `Confirm`, `MsgProposeVersions` | `StDone` (read as `MsgReplyVersions`) | violation |
| client in `Confirm`, unsolicited `MsgQueryReply` | `StDone` (query result) | error |
| any role in `Done`, any message | violation: mini-protocol 0 is unknown to the mux [R7] | silently dropped (observed in Go, not modelled) |
| a side that holds agency | the message waits | violation (protocol.Protocol judges on arrival) |

## Go tests and mutations

Branch `test/handshake-state-model`,
`protocol/handshake/statemap_model_test.go`:

- `TestStateMapMatchesModel`, `TestDoneCannotBeLeft`: every within-run cell
  against `StateMapNtN` and `StateMapNtC`.
- `TestReceiveMatchesModel`: a running client and server, both modes, in
  every cell they can rest in (a client cannot rest in `Propose`, a server
  cannot rest in `Confirm`).
- `TestStateMapLimitsMatchSpec`, `TestClientConfirmTimeoutMatchesSpec`:
  5760 bytes, 10 s node-to-node, no node-to-client timeouts.
- `TestServerNegotiationMatchesModel`: ten proposals with the reference
  answer, and the gOuroboros answer where it differs.

Each mutation below fails at least one of them: drop the `MsgQueryReply`
transition; give node-to-client `Confirm` a timeout; ignore
`Config.Timeout` in `NewClient`; accept an unsolicited `MsgQueryReply`;
remove the node-to-node `Confirm` size limit; pick the lowest common version;
skip the server's magic check; refuse a decode failure as `Refused`; give
`Done` a transition.

Branch `fix/handshake-query-after-negotiation` moves the query check after
negotiation, as the reference does. Its test fails on `origin/main` for "no
common version" and "magic mismatch".

Simultaneous open. On `61046085` gOuroboros routes segments by their
direction bit (`muxer/muxer.go`, `readLoop`), so a peer's
`MsgProposeVersions` goes to the handshake server role, which a dialling
connection does not run; two gOuroboros connections opening at once both
fail with `connection shutdown initiated: EOF`.

Branch `fix/handshake-simultaneous-open` follows the reference:

- The reference runs the handshake on the bearer before the mux starts,
  reading every segment whatever its direction bit [R8]. The gOuroboros
  muxer now gives a mini-protocol 0 segment to whichever role is
  registered, but only before `Start`, that is during the handshake.
- `Confirm` gains a transition for `MsgProposeVersions` to `Done`
  (`MsgReplyVersions` [S2][R1]). The client chooses the highest common
  version and checks the magic, the server's rule [R2][R3]. A refusal is
  returned as the typed error and nothing is sent [R1].
- `Client.Start` returns only once its proposal has moved it to `Confirm`
  (`protocol.Protocol.WaitForStateExit`). Without that, the connection can
  start reading while the client still holds agency in `Propose`, and the
  peer's proposal is rejected on arrival: `HandshakeSimOpenEarlyReadBug.cfg`,
  and in Go about one run in 150 of `TestSimultaneousOpen` with the wait
  removed.

- Review of PR #3127 (head `78792c96`, reviewer finding on
  `protocol/handshake/client.go:257`): the branch handed each side the
  peer's raw version data. With different diffusion modes the two
  connections derived opposite full-duplex settings. The reference client
  ends with `acceptVersion vData vData'`, the agreed data (Client.hs
  201-215 [R2]). The model shared the defect: `result` carried no data, so
  nothing could see it. It now records the data each side ends with
  (`data`, `EndData`), and `SimAgreedData` requires both to hold the
  agreement of the two tables; `RawPeerData = TRUE` reproduces the branch
  (`HandshakeSimOpenRawPeerDataBug.cfg`). Fixed in `5826fae1`: the client
  passes `agreedVersionData(own, peer)` to `FinishedFunc`; the new mixed
  diffusion-mode cases in `TestSimultaneousOpen` and
  `TestSimultaneousOpenConnectionsMixedModes` fail without it.
- Same class, not fixed here: on a normal open the gOuroboros server's
  `FinishedFunc` still gets the client's raw data, while the reference
  server ends with the agreed data (Server.hs 42-44). An initiator-only
  server facing a full-duplex client sets its muxer to
  initiator-and-responder instead of responder; its mini-protocols still
  follow its own `fullDuplex`. Not modelled: `Handshake.tla` records no
  per-side data on a normal open.

Tests: `protocol/handshake/simultaneous_open_test.go` (highest common
version, a version only one side speaks, no common version, magic
mismatch, the mismatch lists the side's own versions) and
`connection_simultaneous_open_test.go` (two connections agree; two on
different networks both fail, at least one with `RefusedError`). Every one
fails on `61046085`.

## Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Which version? | Highest common [S5] | `lookupGreatestCommonKey` [R3] | Highest common | Agree |
| Refusal reasons | Mismatch, DecodeError, Refused [S5] | Same [R3] | Same | Agree |
| When is a query answered? | Query "will send back all supported versions" [S4] | Only if acceptOrRefuse accepts and the agreed data asks [R4] | If any decodable proposed version asks, before negotiating | **Differs**; fixed on a branch |
| Unsolicited `MsgQueryReply` | Not stated | Taken as a query result [R2] | Error | Stricter, harmless |
| `MsgQueryReply` in the state machine | Absent [S2] | Present [R1] | Present | Spec out of date |
| Data in `MsgAcceptVersion` | Negotiated data [S7] | Agreed data [R9][R6] | The server's own data; each side's callback gets the peer's data | **Differs**, no wrong outcome found (the reference client recomputes the agreement); fixed on a branch |
| Simultaneous open | Supported [S2][S6] | `MsgReplyVersions` [R1][R2] | Not supported | **Differs**; fixed on a branch |
| Proposal keys in ascending order | Required for every key [S7] | Recognised keys out of order fail to decode; unrecognised keys skipped [R10] | Accepted in any order; duplicates rejected | **Differs** (lenient); fixed on a branch, which follows the reference |
| Size limits | 5760 both states [S3] | 5760 [R5] | 5760 | Agree |
| Timeouts | 10 s both, NtN; none NtC [S3] | `shortWait` = 10 s [R5] | 10 s NtN (overridable), none NtC | Agree |
| Message after Done | Not stated | Connection torn down [R7] | Dropped | Differs, harmless |

## Sources

Pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c)
and gOuroboros `origin/main` at `61046085`. Paths under
`ouroboros-network/framework/lib/Ouroboros/Network/Protocol/Handshake/`
unless noted.

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | `docs/network-spec/miniprotocols.tex` 27-36 | One side has agency; an unexpected message aborts the connection. |
| S2 | same, 449-501 | States, agency, messages, transitions; `MsgReplyVersions` (479-484). |
| S3 | same, 503-536, 575-606, 630-649 | 5760 bytes per state; 10 s timeouts node-to-node; none node-to-client. |
| S4 | same, 541-573, 608-628 | Version data; negotiated data; magic must agree; query inherited from the client. |
| S5 | same, 651-702 | Ascending unique keys; the server's algorithm, steps 1-8. |
| S6 | same, 704-759 | Simultaneous open; the symmetric `acceptable` condition. |
| R1 | `Type.hs` 87-131, 145-153 | Messages and agency; simultaneous open; a refusing side closes without a reason. |
| R2 | `Client.hs` 119-172 | The client's handling of each answer. |
| R3 | `Client.hs` 191-222 | `acceptOrRefuse`, `lookupGreatestCommonKey`. |
| R4 | `Server.hs` 34-48 | Query reply only after acceptance. |
| R5 | `Codec.hs` 54-99, 152-192; `ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs` 113-114 | Byte and time limits; decoding by state. |
| R6 | `cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs` 134-156; `NodeToClient/Version.hs` 123-135 | `acceptableVersion`, `queryVersion`. |
| R7 | `network-mux/src/Network/Mux/Ingress.hs` 122-126 | Unknown mini-protocol tears the connection down. |
| R9 | `Server.hs` 42-44 | `MsgAcceptVersion` carries `encodeData vNumber agreedData`. |
| R10 | `Codec.hs` 197-241 | `decodeVersions`: unrecognised keys skipped (235); recognised keys strictly ascending, else "unordered version" (237-240). |
| S7 | `docs/network-spec/miniprotocols.tex` 572-573, 653-656 | "the negotiated version data is sent back using MsgAcceptVersion"; keys "unique and appear in ascending order". |
| G1 | gOuroboros `protocol/handshake/{handshake,client,server}.go`, `connection.go` 746-800, `muxer/muxer.go` `readLoop` | The code compared. |

## Not modelled

Peer sharing and Peras flags in the agreed data (one diffusion-mode flag
stands for every combined field); key order in `HandshakeSimOpen.tla`;
version numbers gOuroboros cannot decode; the 20 s delay before the reference closes
a query connection; the connection-wide handshake timeout in `connection.go`.

## Running it

```sh
cd specs/handshake
for c in Handshake HandshakeNtC HandshakeStrictQuery HandshakeRogue \
         HandshakeRogueStrict HandshakeSilentServer HandshakeSilentClient \
         HandshakeKeyOrder HandshakeKeyOrderUnknown; do
  ../../bin/tlc -config $c.cfg Handshake.tla
done
../../bin/tlc -config HandshakeSimOpen.cfg HandshakeSimOpen.tla
../../bin/tlc -config HandshakeSimOpenGouroboros.cfg HandshakeSimOpen.tla
../../bin/tlc -config HandshakeTable.cfg HandshakeTable.tla | grep '^<<'
../../bin/tlc -config HandshakeTableGouroboros.cfg HandshakeTable.tla | grep '^<<'
# expected to fail:
for c in HandshakeGouroborosBug HandshakeLowestBug HandshakeNoMagicBug \
         HandshakeWrongReasonBug HandshakeClientNoMagicBug HandshakeSilentNtCBug \
         HandshakeProbeAcceptBug HandshakeProbeQueryBug HandshakeProbeMismatchBug \
         HandshakeProbeDecodeErrorBug HandshakeProbeRefusedBug \
         HandshakeProbeAcceptBelowProposedBug HandshakeAcceptOwnDataBug \
         HandshakeKeyOrderBug HandshakeKeyOrderEveryBug; do
  ../../bin/tlc -config $c.cfg Handshake.tla
done
for c in HandshakeSimOpenGouroborosBug HandshakeSimOpenAsymmetricBug \
         HandshakeSimOpenProbeRefusedBug HandshakeSimOpenEarlyReadBug; do
  ../../bin/tlc -config $c.cfg HandshakeSimOpen.tla
done
```
