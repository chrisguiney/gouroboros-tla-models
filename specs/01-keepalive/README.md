# Model 01: keep-alive

The first real gOuroboros model. Read [Your first model](../../docs/02-first-model.md)
before this one; this page only explains what is new.

## The protocol

Keep-alive lets each side of a node-to-node connection check that the other is
still there.

```
            MsgKeepAlive
  StClient ─────────────────▶ StServer
     │    ◀─────────────────
     │     MsgKeepAliveResponse
     │ MsgDone
     ▼
  StDone
```

| State | Who may send (agency) | Legal messages |
| --- | --- | --- |
| `StClient` | client | `MsgKeepAlive` → `StServer`, `MsgDone` → `StDone` |
| `StServer` | server | `MsgKeepAliveResponse` → `StClient` |
| `StDone` | nobody | none |

In gOuroboros this table is `StateMap` in `protocol/keepalive/keepalive.go`.
The model's states, transitions, agency, and timeouts are checked against the
sources below rather than taken from `StateMap`, so comparing the two means
something. (The first draft was written from memory and checked against these
sources afterwards; every rule except one matched. See
[Open question](#open-question-messages-after-done).)

## Sources

All pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c),
the reference Haskell implementation and the home of the network
specification. The `.tla` file cites them as `[S1]` to `[S3]`.

| Ref | Source | What the model takes from it |
| --- | --- | --- |
| S1 | [`docs/network-spec/miniprotocols.tex`, "Protocols as State Machines", lines 27-36 and 96-98](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36) | Only one side has agency at a time. "If either side receives a message that is not expected according to the mini-protocol the communication is aborted (the connection is closed)." Every mini-protocol ends in a single `StDone` where nobody has agency. |
| S2 | [`docs/network-spec/miniprotocols.tex`, "Keep Alive Mini Protocol", lines 1560-1650](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1560-L1650) | The state machine, the agency table, the cookie rule, size limits (65535 bytes per state), and timeouts (97 s in `StClient`, 60 s in `StServer`). |
| S3 | [`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Type.hs`, lines 89-106](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Type.hs#L89-L106) | The three message types with their from- and to-states, and `StateAgency StDone = NobodyAgency` (S2's agency table leaves `StDone` out). |

The message encodings (`[0, cookie]`, `[1, cookie]`, `[2]`) are in
[`cardano-diffusion/protocols/cddl/specs/keep-alive.cddl`](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/cardano-diffusion/protocols/cddl/specs/keep-alive.cddl);
the model does not need them.

### Rendered versions (easier to read)

| Ref | Rendered |
| --- | --- |
| S1 | [Network specification PDF](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf), section 3.2 "Protocols as State Machines", page 10 |
| S2 | Same PDF, section 3.10 "Keep Alive Mini Protocol", page 33 |
| S3 | [Haddock for `Ouroboros.Network.Protocol.KeepAlive.Type`](https://ouroboros-network.cardano.intersectmbo.org/ouroboros-network/protocols/Ouroboros-Network-Protocol-KeepAlive-Type.html) |

The rendered site is rebuilt nightly from the `main` branch, so it always
shows the latest version and the section and page numbers can move. Read it
for convenience; cite the pinned source files above. When this was written
(2026-11-23) the PDF matched the pinned commit: `miniprotocols.tex` last
changed on 2026-11-05, before the PDF was built.

## What is new compared with the hello model

**Each side has its own view.** `view["Client"]` and `view["Server"]` are the
state each side *believes* the protocol is in. Messages travel through
`inbox`, so for a moment the two views differ. That gap is where real protocol
bugs live, and the invariant `ViewsAgreeWhenQuiet` checks that it always
closes.

**The receive rule.** `Receive(r, s, m)` says what side `r` must do when message
`m` arrives while it believes the state is `s`:

1. If `s` is `StDone`, ignore the message. **Unsourced**; see
   [Open question](#open-question-messages-after-done).
2. If the peer had agency and `s` has a transition for `m`, accept it. (S1, S2)
3. Otherwise it is a **violation**: hang up. (S1)

**A misbehaving peer.** `Inject` lets a rogue peer push any message into any
inbox at any time, up to `RogueMessages` times. This is how the model asks
"what happens if the other side breaks the rules?"

**Timeouts.** `Timeout` fires only when a side is waiting for its peer and
nothing else can ever happen. Turning timeouts off shows why they are needed.

New TLA+ syntax is explained in comments the first time it appears, and in the
[glossary](../../docs/glossary.md).

## Run it

```sh
make keepalive         # honest peers, and rogue peers: both pass
make keepalive-table   # print the 18-cell receive table
make keepalive-bugs    # two deliberately failing configs, with traces
```

| Config | Checks | Result |
| --- | --- | --- |
| `KeepAlive.cfg` | Two honest peers: no failures, one message in flight, never both have agency, views agree, only legal moves, endings are final. | Passes: 21 distinct states. |
| `KeepAliveRogue.cfg` | Up to two rogue messages: still only legal moves, endings final, and no deadlock. | Passes: 1,018 distinct states. |
| `KeepAliveRogueBug.cfg` | Claims a rogue message never causes a hang-up. | Fails in 2 steps: a rogue `MsgKeepAlive` sent *to the client*. |
| `KeepAliveNoTimeoutBug.cfg` | Rogue peer, timeouts off. | **Deadlock** in 4 steps: a rogue `MsgDone` ends the server, the server ignores the client's next ping, and the client waits forever. |
| `KeepAliveTable.cfg` | Prints the receive rule. | 18 rows. |

## States that cannot be entered

The property `OnlyLegalMoves` says a side's state only changes along a row of
the transition table, or to a failure. TLC checks it in every step of every
behavior, including those with rogue messages. So, for example:

- `StServer` is entered only by `MsgKeepAlive` from `StClient`.
- `StDone` is entered only by `MsgDone` from `StClient`, and never left
  (`EndingsAreFinal`).
- A side never accepts a message from a peer that did not have agency: it
  hangs up instead.

## The Go tests this model drove

`protocol/keepalive/statemap_model_test.go` in gOuroboros:

| Test | What it checks |
| --- | --- |
| `TestStateMapMatchesModel` | All 18 receive cells against `StateMap`, including cells no running program can reach. |
| `TestServerReceiveMatchesModel` | A running server in `StClient` and `StDone`, sent every message. |
| `TestClientReceiveMatchesModel` | A running client in `StClient`, `StServer`, and `StDone`, sent every message. |
| `TestDoneCannotBeLeft` | No transition leaves `StDone`; only `MsgDone` from `StClient` enters it. |
| `TestClientTimesOutWhenServerFallsSilent` | The deadlock trace above: gOuroboros escapes it with its state timeout. |

The tests were shown to fail when gOuroboros was deliberately broken: adding a
`MsgDone` transition to `StServer`, and letting a message through without
agency.

## What the model found

- **gOuroboros agrees with the model on all 18 cells.** On the 12 sourced
  cells that means gOuroboros follows the specification. The 6 `StDone` cells
  are unsourced and may disagree with it; see the open question above.
- **The gOuroboros client never sends `MsgDone`.** The specification allows it
  and the server handles it, but nothing in the client API sends it, so a real
  gOuroboros client never reaches `StDone`; the test reaches it by sending
  `MsgDone` directly. Whether the client should end the protocol cleanly on
  shutdown is an open question for the maintainers.
- The model says why `ClientTimeout` and `ServerTimeout` exist: without them,
  one stray message can hang a connection forever.

## Open question: messages after Done

The model ignores any message that arrives after `StDone`. That rule came from
gOuroboros's behavior, not from a source: a gOuroboros client drains such
messages silently, and a gOuroboros server leaves them unread for a restarted
instance (the keep-alive server is never restarted, so they are never read).

S1 says the opposite, read literally: after `MsgDone` "both sides agree that
the mini-protocol has terminated", so any later message "is not expected
according to the mini-protocol" and "the communication is aborted". Under that
reading the six `StDone` rows of the receive table should be `Violation`, and
the gOuroboros tests that check those rows (`.../inDone/...`) are pinning
behavior the specification does not allow.

S1 does not say what the reference implementation does with a responder that
receives a new conversation after `MsgDone`, which is the case a server
restart exists for. That needs reading the reference implementation's
multiplexer and inbound governor before deciding.

## Not modelled yet

Cookies (S2: "It is a protocol error if the cookie received back with
MsgKeepAliveResponse does not match"; gOuroboros already tests this in
`client_cookie_test.go`), real time, message sizes, and the goroutines inside
gOuroboros. Those come later, one at a time.
