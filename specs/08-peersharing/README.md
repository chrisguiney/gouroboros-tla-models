# Model 08: peer-sharing

Peer-sharing is how a node learns about other nodes from a peer. The client
asks "send me up to N peers" (`MsgShareRequest N`) and the server answers with
a list (`MsgSharePeers`). The list may be shorter than N, never longer, and
must fit in the state's 5,760-byte limit.

```
            MsgShareRequest
  StIdle ─────────────────▶ StBusy
     │    ◀─────────────────
     │      MsgSharePeers
     │ MsgDone
     ▼
  StDone
```

| State | Agency | Legal messages | Size limit | Timeout |
| --- | --- | --- | --- | --- |
| `StIdle` | client | `MsgShareRequest` → `StBusy`, `MsgDone` → `StDone` | 5,760 bytes | none |
| `StBusy` | server | `MsgSharePeers` → `StIdle` | 5,760 bytes | 60 s |
| `StDone` | nobody | none | | |

The shape is keep-alive's (Model 01), so read that first. What is new here is
the **amount**: a rule linking a reply to its request, and a size limit that
the largest legal request can break.

## What the code does

In gOuroboros (`protocol/peersharing/`):

- **`StateMap`** (`peersharing.go`) is the table above, with
  `PendingMessageByteLimit` 5,760 in `Idle` and `Busy`, and a 60 s timeout in
  `Busy` only.
- **The client** (`client.go`). `GetPeers(amount uint8)` takes `exchangeLock`,
  records the amount, sends `MsgShareRequest`, and waits for the reply or for
  the protocol to stop. `handleSharePeers` refuses a reply longer than the
  recorded amount with `ErrTooManyPeersShared`. Nothing in the client API
  sends `MsgDone`. `Config.Timeout` (`WithTimeout`) overrides the `Busy`
  timeout for the client.
- **The server** (`server.go`). `handleShareRequest` calls the application's
  `ShareRequestFunc` and cuts its list to `min(amount, MaxSharedPeers)`.
  `MaxSharedPeers` is 230: the most worst-case (IPv6) addresses that encode
  within 5,760 bytes; 255 would not fit. With no `ShareRequestFunc`, or when
  this node advertised `NoPeerSharing`, it answers an empty list.
  `handleDone` restarts the server, with the stop guard of Model 01.

## The questions

1. **`RepliesWithinRequest`**: does an honest server ever send more peers than
   were asked for?
2. **`RepliesFit`**: does an honest server ever send a reply over the size
   limit?
3. **`NeverTakesTooMany`**: does the client ever accept a reply longer than
   its request, even from a rogue server?
4. **`NoFailures`** / **`NoViolations`**: do two honest peers ever hang up;
   do slow honest peers ever see a protocol violation?
5. The keep-alive structural invariants (`OneMessageInFlightPerRun`,
   `NeverBothHaveAgency`, `ViewsAgreeWhenQuiet`) and the step properties
   `OnlyLegalMoves` and `FailuresAreFinal`.
6. Does anything deadlock? `StIdle` has no timeout, so a server may legally
   wait for ever. `Ended` allows exactly that, and nothing else, to stop.

The model is `PeerSharing.tla`. Amounts are `{0, 1, 2}`, the server's peer
source returns 2, and `ByteCap = 1` stands for `MaxSharedPeers`: a request
for 2 is legal but its full answer would not fit. So the small model has the
same shape as 255 against 230.

## The answers

All hold.

| Config | States | Result |
| --- | --- | --- |
| `PeerSharing.cfg`: honest peers, up to two runs | 215 | passes |
| `PeerSharingSlow.cfg`: the server may be slower than the 60 s timeout | 332 | passes (`NoViolations`; timeouts happen) |
| `PeerSharingRogue.cfg`: up to two rogue messages of any kind | 509,178 | passes (`NeverTakesTooMany`, legal moves, no deadlock) |
| `PeerSharingTable.cfg` (with `PeerSharingTable.tla`) | | prints the 30-cell receive table |

Unlike keep-alive, the rogue model has no deadlock without help: the
keep-alive deadlock (a stray message restarting a server that then waits for
ever) is legal here, because the specification gives `StIdle` no timeout.

## Checking the checks

Each safeguard has a switch. Turning it off must break an invariant:

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `PeerSharingNoClampBug.cfg` | the server cuts its list to the amount | `RepliesWithinRequest` |
| `PeerSharingNoCapBug.cfg` | the server cuts its list to `MaxSharedPeers` | `RepliesFit` |
| `PeerSharingNoCountCheckBug.cfg` | the client compares the reply with its request (one rogue message) | `NeverTakesTooMany` |
| `PeerSharingNoRestartBug.cfg` | the server restarts after `MsgDone` | `NoFailures`: the client's second run times out, as in Model 01's keep-alive bug |
| `PeerSharingRogueBug.cfg` | (claims a rogue message cannot cause a hang-up) | `NoFailuresEvenWithRogue` |

The **reachability probes** each claim something never happens; TLC shows
each one does:

| Config (expected to fail) | Shows |
| --- | --- |
| `PeerSharingProbeNoPeersDeliveredBug.cfg` | non-empty replies are delivered |
| `PeerSharingProbeNeverClampsToAmountBug.cfg` | the server does have more peers than were asked for |
| `PeerSharingProbeNeverClampsToCapBug.cfg` | the server does have to cut a reply to fit |
| `PeerSharingProbeNeverRestartsBug.cfg` | the server serves a second run |
| `PeerSharingProbeNeverIdleForeverBug.cfg` | with one rogue request, the connection settles with the server idle for ever |

### The modelling mistake

The idle-for-ever probe first ran with honest peers and **passed**: an honest
client always ends with `MsgDone`, so the server ends in `StDone`, never idle.
The `Ended` clause for an idle server was reached only through a rogue
request after the client finished. The probe now runs with one rogue message.
Without it, that clause could have been hiding a real deadlock.

## The receive table

`PeerSharingTable.tla` prints 2 roles x 3 states x 5 kinds = 30 cells. Kinds:
`MsgShareRequest`, `MsgSharePeers` listing as many peers as asked for,
`OverCountSharePeers` listing one more, `MsgDone`, and `Oversized` (padded
past 5,760 bytes). `Waits` and `Held` mean what they do in Model 01. Ten cells
are `Waits` (the reader holds agency), five are `Held` (client after
`MsgDone`), and the server after `MsgDone` judges as a new run in `StIdle`.

## Go tests and mutations

On branch `test/peersharing-state-model` of gOuroboros (from `origin/main`
`61046085`), `protocol/peersharing/statemap_model_test.go`:

| Test | What it checks |
| --- | --- |
| `TestStateMapMatchesModel` | The within-run cells (over-count left to the running test) against `StateMap`, and its shape: three states, agencies, no pipelining, no match functions. |
| `TestReceiveMatchesModel` | All 30 cells on a running client or server. A peer source that blocks holds the server in `Busy`, so even the server's `Busy` row runs (keep-alive could not). `Waits` cells are checked against gOuroboros's earlier refusal. |
| `TestDoneCannotBeLeft` | No transition leaves `Done`; only `MsgDone` from `Idle` enters it. |
| `TestStateMapTimeoutsMatchSpec` | No `Idle` timeout; 60 s in `Busy` and as the client default. |
| `TestServerAnswersAmountZeroWithNoPeers` / `TestClientRequestingZeroRefusesAnyPeer` | The amount rule at 0, on both sides. |
| `TestShareRequestRefusesAmountAboveWord8` | 255 decodes, 256 is refused (the reference's `Word8`). |
| `TestPeerAddressRefusesWhatReferenceRefuses` | Peer type 2, a port above 16 bits, an address word above 32 bits, an extra element. |

Every new test was shown to fail under a mutation of the package, then
restored:

| Mutation | Fails |
| --- | --- |
| `MsgDone` transition added to `Busy` | `TestStateMapMatchesModel`, `TestDoneCannotBeLeft`, receive `client/inBusy/MsgDone` |
| `Busy` agency set to client | 10 receive cells (both `Busy` rows), `TestClientRequestingZeroRefusesAnyPeer` |
| client count check removed | receive `client/inBusy/OverCountSharePeers`, `TestClientRequestingZeroRefusesAnyPeer` |
| server clamp only to `MaxSharedPeers` | 4 receive cells that read the reply length, `TestServerAnswersAmountZeroWithNoPeers` |
| `handleDone` does not restart | 6 receive cells (server `Done` row, `Idle`/`MsgDone`) |
| `Idle` size limit removed | `TestStateMapMatchesModel`, 2 server `Oversized` cells |
| `BusyTimeout` 10 s; an `Idle` timeout added | `TestStateMapTimeoutsMatchSpec` |
| IPv4 port decoded as 32 bits; peer type 2 decoded as IPv4 | the matching `TestPeerAddressRefusesWhatReferenceRefuses` cases |

The 256-amount test has no mutation: the bound is the Go type `uint8`.

Already covered by existing tests, so not repeated: the byte limit and 230/231
boundary (`limits_test.go`), over- and under-count replies for non-zero
amounts, server clamping, concurrent `GetPeers`, the client `Busy` timeout
(`client_test.go`), the `NoPeerSharing` gating (`server_test.go`), repeated
`MsgDone` on a shared muxer (`server_liveness_test.go`), and the address
encodings, the v11/v12 eight-element IPv6 form, indefinite-length lists and
preflight bounds (`messages_test.go`, `dispatch_test.go`).

## What the model found

- **No protocol defect.** gOuroboros follows the specification on every
  within-run cell, the amount rule, the size limits and the timeouts.
- **A documentation defect.** `WithTimeout` was documented as "the timeout for
  the handshake operation", and the README said it overrides the server's
  timeout. Only `NewClient` reads it. Fixed on branch
  `fix/peersharing-timeout-doc` (documentation only).
- **The restart lifecycle is keep-alive's.** `handleDone` is the same
  `StopForRestart`, guarded `initProtocol`, `CancelRestart` sequence that
  `KeepAliveLifecycle.tla` checked, and connection shutdown calls the
  peer-sharing server's `Stop`. Model 01's conclusions apply unchanged.

## Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| States, agency, transitions | [S2] | Same [R1] | Same | agree |
| `StDone` agency | not in the table [S2]; [S1] | `NobodyAgency` [R1] | `AgencyNone` | agree |
| Amount type | "Ideally ... limited by a protocol level constant" [S2] | `Word8`; no other protocol limit [R1][C1] | `uint8` | agree |
| Reply longer than the request | "a protocol error" [S2] | client throws `PeerSharingProtocolViolation` [R3] | `ErrTooManyPeersShared` | agree |
| How many peers the server sends | "not bigger than the value specified in the request" [S2] | `min(10, amount)` (policy) [R3] | `min(amount, 230)` | agree on the rule; the cap is a policy choice |
| Size limit | 5,760 bytes `StIdle`, `StBusy` [S3] | same [R2]; ingress queue 5,760 [R6] | 5,760 both | agree |
| Timeouts | none `StIdle`, 60 s `StBusy` [S3] | `waitForever`, `longWait` = 60 s [R2][R7] | same; client configurable | agree |
| Timer on the side holding agency | "how much time the receiver side can wait" [S3] | only the awaiting side is timed (Model 01, S8) | the server also times its own `Busy` (60 s), so a peer source slower than that ends the connection from the server side | differs; same outcome, since the client would time out at 60 s too |
| Message while the reader holds agency | not stated | waits, judged later (Model 01, S8) | refused at once | differs, as in keep-alive; only a misbehaving peer is affected |
| Server after `MsgDone` | restart [S7] | restart | restart | agree |
| Client sends `MsgDone` | "Terminating message" [S2] | on `Terminate` [R3] | never through the API | differs; the connection closes instead |
| `ShareRequest` when peer sharing was negotiated off | "won't even have the ... server running" [S2 1770-1771] | protocol 10 not registered [R5]; a segment for it is `UnknownMiniProtocol`, which tears down the connection [R6] | answers an empty list | differs; gOuroboros is more lenient, by design (its README) |
| IPv4 address | CDDL `[0, word32, port]` [S4] | network-order word read as a host word [R4] | little-endian word | agree (existing test) |
| IPv6 address, v14 | `[1, w1..w4, port]` [S4] | four big-endian words, flow and scope dropped [R4] | same | agree |
| IPv6, v11/v12 8-element form | obsolete CDDL | not decoded: versions below 14 are gone [R4][R8] | accepted on decode | gOuroboros more lenient; harmless |
| IPv4-mapped IPv6 (`::ffff:a.b.c.d`) | not stated | a `SockAddrInet6` encodes as IPv6 [R4] | encoded as IPv4 (`net.IP.To4`) | differs; same endpoint on a dual-stack host |
| Declared address list length | CDDL arrays | ignored; reads 3 or 5 fields [R4] | checked | gOuroboros stricter, refusing only malformed input |

## Sources

Pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c)
and gOuroboros `origin/main` at `61046085`. Paths below are relative to that
commit.

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | `docs/network-spec/miniprotocols.tex` lines 27-36, 96-98 | One side has agency; an unexpected message aborts the connection; one `StDone` where nobody sends. |
| S2 | `docs/network-spec/miniprotocols.tex` lines 1653-1708, 1759-1771, 1794-1796 | Peer-sharing states, agency, messages; "It is a protocol error to send more peers than it was requested" (1702); amount "ideally ... limited by a protocol level constant" (1695-1697); a peer with sharing disabled has no server running (1770-1771). |
| S3 | `docs/network-spec/miniprotocols.tex` lines 1710-1743 | 5,760 bytes in `StIdle` and `StBusy`; timeouts "-" and 60 s; violations SHOULD tear the connection down. |
| S4 | `cardano-diffusion/protocols/cddl/specs/peer-sharing-v14.cddl` lines 9-18; `obsolete/peer-sharing-v11-12.cddl` lines 17-18 | Wire forms; the old eight-element IPv6 address. |
| S7 | `docs/network-spec/connection-manager.tex` lines 489-503 | A cleanly terminated server-side mini-protocol is restarted (as in Model 01). |
| R1 | `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/PeerSharing/Type.hs` lines 26-31, 74-93 | `PeerSharingAmount` is a `Word8`; messages; `StDone = NobodyAgency`. |
| R2 | `.../Protocol/PeerSharing/Codec.hs` lines 58-77, 79-93, 123-161 | Decoding by state, "unexpected key"; non-empty lists are encoded indefinite-length, both forms decoded; 4 x 1440 bytes per state; `waitForever`, `longWait`. |
| R3 | `ouroboros-network/lib/Ouroboros/Network/PeerSharing.hs` lines 112-133, 171-174, 229-237 | Client sends `MsgDone` on `Terminate`; throws on a longer reply; server sends `min(ps_POLICY_PEER_SHARE_MAX_PEERS = 10, amount)`. |
| R4 | `ouroboros-network/api/lib/Ouroboros/Network/PeerSelection/PeerSharing/Codec.hs` lines 29-65 | `encodeRemoteAddress` / `decodeRemoteAddress`: version ignored, declared length ignored, IPv6 flow and scope set to 0. |
| R5 | `cardano-diffusion/lib/Cardano/Network/NodeToNode.hs` lines 371-381, 572-580; `cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs` line 146; `ouroboros-network/api/lib/Ouroboros/Network/PeerSelection/PeerSharing.hs` lines 29-33 | The mini-protocol is registered only when both sides enable sharing; ingress queue 4 x 1440. |
| R6 | `network-mux/src/Network/Mux/Ingress.hs` line 126 | A segment for an unregistered mini-protocol throws `UnknownMiniProtocol`. |
| R7 | `ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs` lines 116-120 | `longWait = Just 60`, `waitForever = Nothing`. |
| R8 | `cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs` lines 65-111 | Only versions 14-17 remain. |
| C1 | `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/PeerSharing/Client.hs` lines 10-36, `Server.hs` lines 12-36 | Client: `Yield` then `Await`, or `MsgDone`. Server: `Await` in `StIdle`, answer, loop; `MsgDone` ends. |
| G1 | gOuroboros `protocol/peersharing/peersharing.go`, `client.go`, `server.go`, `messages.go`; `protocol/protocol.go` `stateLoop` | `StateMap`, `MaxSharedPeers`, `GetPeers`, `handleSharePeers`, `handleShareRequest`, `handleDone`; timers are set on entry to any state with agency, local or remote. |

## Not modelled

Real time, exact byte sizes (`ByteCap` stands for them; the 230/231 boundary
is tested in Go), the `NoPeerSharing` gating (a flag, not a state; see the
table), the restart goroutines (Model 01's `KeepAliveLifecycle.tla`), the
reference's client registry and peer selection policy, and address encoding
(tested in Go).

## Running it

```sh
cd specs/08-peersharing
../../bin/tlc -config PeerSharing.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingSlow.cfg PeerSharing.tla
../../bin/tlc -workers auto -config PeerSharingRogue.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingTable.cfg PeerSharingTable.tla | grep '^<<'
# expected to fail:
../../bin/tlc -config PeerSharingNoClampBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingNoCapBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingNoCountCheckBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingNoRestartBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingRogueBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingProbeNoPeersDeliveredBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingProbeNeverClampsToAmountBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingProbeNeverClampsToCapBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingProbeNeverRestartsBug.cfg PeerSharing.tla
../../bin/tlc -config PeerSharingProbeNeverIdleForeverBug.cfg PeerSharing.tla
```
