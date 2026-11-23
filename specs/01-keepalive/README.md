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

That is one **run** of the protocol. A connection can hold several runs one
after another: when a run ends in `StDone`, a new one can start in `StClient`
(sources S4 to S6 below).

In gOuroboros the table is `StateMap` in `protocol/keepalive/keepalive.go`.
The model's rules are checked against the sources below rather than taken from
`StateMap`, so comparing the two means something. (The first draft was written
from memory and checked against the sources afterwards. One rule was wrong,
and checking it found a gOuroboros bug: see
[Settled: messages after Done](#settled-messages-after-done).)

## Sources

All pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c),
the reference Haskell implementation and the home of the network
specification. The `.tla` file cites them as `[S1]` to `[S6]`.

| Ref | Source | What the model takes from it |
| --- | --- | --- |
| S1 | [`docs/network-spec/miniprotocols.tex`, "Protocols as State Machines", lines 27-36 and 96-98](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36) | Only one side has agency at a time. "If either side receives a message that is not expected according to the mini-protocol the communication is aborted (the connection is closed)." Every mini-protocol ends in a single `StDone` where nobody has agency. |
| S2 | [`docs/network-spec/miniprotocols.tex`, "Keep Alive Mini Protocol", lines 1560-1650](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1560-L1650) | The state machine, the agency table, the cookie rule, size limits (65535 bytes per state), and timeouts (97 s in `StClient`, 60 s in `StServer`). |
| S3 | [`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Type.hs`, lines 89-106](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Type.hs#L89-L106) | The three message types with their from- and to-states, and `StateAgency StDone = NobodyAgency` (S2's agency table leaves `StDone` out). |
| S4 | [`network-mux/src/Network/Mux.hs`, lines 362-378 and 512](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L362-L378) | When a run ends, the bytes it did not read are put back on the mini-protocol's queue for the next run. "Protocols that runs to completion are not automatically restarted" by the multiplexer itself. |
| S5 | [`network-mux/src/Network/Mux.hs`, lines 846-852](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L846-L852) | A mini-protocol may be started again on the same connection; only one that is still running is refused (`ProtocolAlreadyRunning`). |
| S6 | [`ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs`, lines 433-475](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L433-L475) | A responder (server) mini-protocol that ends cleanly is restarted (`TrResponderRestarted`) while the connection stays registered. |

The message encodings (`[0, cookie]`, `[1, cookie]`, `[2]`) are in
[`cardano-diffusion/protocols/cddl/specs/keep-alive.cddl`](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/cardano-diffusion/protocols/cddl/specs/keep-alive.cddl);
the model does not need them.

### Rendered versions (easier to read)

| Ref | Rendered |
| --- | --- |
| S1 | [Network specification PDF](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf), section 3.2 "Protocols as State Machines", page 10 |
| S2 | Same PDF, section 3.10 "Keep Alive Mini Protocol", page 33 |
| S3 | [Haddock for `Ouroboros.Network.Protocol.KeepAlive.Type`](https://ouroboros-network.cardano.intersectmbo.org/ouroboros-network/protocols/Ouroboros-Network-Protocol-KeepAlive-Type.html) |

S4 to S6 are implementation code with no rendered prose; read the source.

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

**The receive rule.** Within a run, `Receive(r, s, m)` says what side `r` must
do when message `m` arrives while it believes the state is `s`:

1. If the peer had agency and `s` has a transition for `m`, accept it. (S1, S2)
2. Otherwise it is a **violation**: hang up. (S1)

**Runs.** After `StDone` no run is reading. `ClientRestart` lets the client
start another run (S5, up to `MaxRuns`). A server restarts when a message
arrives, and the new run reads it starting from `StClient` (S6). Messages for
a client with no new run stay in its inbox, unread (S4). `ReceiveTable` puts
all of this in one table, printed by `make keepalive-table`.

**A switch for gOuroboros's behavior.** `ServerRestarts = TRUE` is the reference
behavior. `ServerRestarts = FALSE` is gOuroboros today, whose keep-alive server
never restarts.

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
make keepalive-bugs    # the deliberately failing configs, with traces
```

| Config | Checks | Result |
| --- | --- | --- |
| `KeepAlive.cfg` | Two honest peers, up to two runs: no failures, one message in flight per run, never both have agency, views agree, only legal moves, failures are final. | Passes: 61 distinct states. |
| `KeepAliveRogue.cfg` | Up to two rogue messages: still only legal moves, failures final, and no deadlock. | Passes: 3,253 distinct states. |
| `KeepAliveGouroborosBug.cfg` | Honest peers, but the server does not restart (gOuroboros today). | **Fails after 5 steps**: see below. |
| `KeepAliveRogueBug.cfg` | Claims a rogue message never causes a hang-up. | Fails after 2 steps: a rogue `MsgKeepAlive` sent *to the client*. |
| `KeepAliveNoTimeoutBug.cfg` | Rogue peer, timeouts off. | **Deadlock**: after the client has finished for good, a rogue `MsgKeepAlive` restarts the server, which then waits for a client that will never speak. |
| `KeepAliveTable.cfg` | Prints the receive table. | 18 rows. |

A first attempt at `KeepAlive.cfg` broke the invariant "only one message is
ever in flight": a client can send `MsgDone`, start a new run, and send
`MsgKeepAlive` before the server reads the `MsgDone`. That is allowed, and is
exactly why S4 keeps a finished run's unread bytes, so the invariant was
corrected to hold per run (`OneMessageInFlightPerRun`). A model that disagrees
with a source is wrong; a model that disagrees with your intuition is
teaching you something.

## States that cannot be entered

The property `OnlyLegalMoves` says a side's state only changes along a row of
the transition table, to a failure, or from `StDone` to the start of a new run.
TLC checks it in every step of every behavior, including those with rogue
messages. So, for example:

- `StServer` is entered only by `MsgKeepAlive` in `StClient`.
- `StDone` is entered only by `MsgDone` in `StClient`. Within a run it is never
  left; the next message belongs to a new run.
- A side never accepts a message from a peer that did not have agency: it
  hangs up instead.
- A side that hung up stays hung up (`FailuresAreFinal`).

## Settled: messages after Done

The first draft of the model said a message after `StDone` is ignored. That
rule had no source; it copied what gOuroboros does. Read literally, S1 said the
opposite: a message after the protocol has terminated is unexpected, so the
connection is closed. Reading the reference implementation settled it, and
neither was right:

- **Server**: the inbound governor restarts a responder that ended cleanly
  (S6), and the multiplexer keeps any bytes that arrived after `MsgDone` for
  the next run (S4). So a message after `MsgDone` is the first message of a
  **new run**, read in `StClient`: `MsgKeepAlive` is answered, and an
  out-of-turn `MsgKeepAliveResponse` is a violation.
- **Client**: nothing restarts it unless its owner starts a new run (S5). The
  bytes wait, unread, on its queue (S4). That is `Held` in the table.

S1's rule applies within a run. The reference implementation applies it to
the run that is reading.

### The bug

**gOuroboros's keep-alive server never restarts after `MsgDone`.** Every other
gOuroboros server with a `MsgDone` (chain-sync, block-fetch, tx-submission,
peer-sharing, and the Leios servers) does: their `handleDone` calls
`StopForRestart`, builds a new protocol instance, and starts it. The
keep-alive server's `handleDone` only calls the optional `DoneFunc`.

`KeepAliveGouroborosBug.cfg` shows what that does, with two honest peers:

1. The client sends `MsgDone`; the server reads it and ends its run.
2. The client starts a second run on the same connection and sends
   `MsgKeepAlive`.
3. The server never reads it. The client waits, and times out.

On a real connection that timeout is 60 s (S2), after which "the connection
SHOULD be torn down": a peer that restarts keep-alive loses its whole
connection to a gOuroboros node. S5 and S6 show that the reference
implementation supports a new run on the same connection; this model has not
yet established how often a real peer does it.

The gOuroboros tests `TestServerReceiveMatchesModel/server/inDone/*` reproduce
it: they fail against gOuroboros today and pass once the server restarts (a
prototype restart following chain-sync's `handleDone` made them pass, and was
then reverted).

## The Go tests this model drove

`protocol/keepalive/statemap_model_test.go` in gOuroboros:

| Test | What it checks |
| --- | --- |
| `TestStateMapMatchesModel` | The 12 within-run receive cells against `StateMap`, including cells no running program can reach. |
| `TestServerReceiveMatchesModel` | A running server in `StClient`, and after `MsgDone`, sent every message. The after-`MsgDone` cases fail today: that is the bug. |
| `TestClientReceiveMatchesModel` | A running client in `StClient`, `StServer`, and `StDone`, sent every message. |
| `TestDoneCannotBeLeft` | No transition leaves `StDone` within a run; only `MsgDone` in `StClient` enters it. |
| `TestClientTimesOutWhenServerFallsSilent` | S2's `StServer` timeout: a client whose ping is never answered gives up. |

The tests were shown to fail when gOuroboros was deliberately broken: adding a
`MsgDone` transition to `StServer`, and letting a message through without
agency.

## What the model found

- **A bug**: the keep-alive server does not restart after `MsgDone`. See
  [The bug](#the-bug).
- **gOuroboros matches the specification on all 12 within-run cells**, and the
  client side after `MsgDone` matches the reference implementation (the
  message is not processed and raises no error).
- **The gOuroboros client never sends `MsgDone`.** The reference client sends
  it when told to terminate (`Ouroboros.Network.KeepAlive`, `Terminate ->
  SendMsgDone`), but nothing in the gOuroboros client API does, so a
  gOuroboros client never reaches `StDone`. The tests reach it by sending
  `MsgDone` directly.
- A small difference with no visible effect yet: after `MsgDone` a gOuroboros
  client discards later messages, while the reference implementation keeps
  them for a next run (S4) and tears the connection down if too many pile up.
- The model shows why the state timeouts exist: without them, one stray
  message can hang a connection forever.

## Not modelled yet

Cookies (S2: "It is a protocol error if the cookie received back with
MsgKeepAliveResponse does not match"; gOuroboros already tests this in
`client_cookie_test.go`), real time, message sizes, ingress queue limits, and
the goroutines inside gOuroboros. Those come later, one at a time.
