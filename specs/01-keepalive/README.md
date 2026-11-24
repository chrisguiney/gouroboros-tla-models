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
The model follows the specification wherever it speaks, and the reference
implementation where it is silent, rather than `StateMap`, so comparing the
two means something. (The first draft was written from memory and checked
against the sources afterwards. One rule was wrong, and checking it found a
gOuroboros bug: see [The bug](#the-bug).)

## Sources

All pinned to [IntersectMBO/ouroboros-network commit `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c),
the reference Haskell implementation and the home of the network
specification, except S8. The `.tla` file cites them as `[S1]` to `[S9]`.

| Ref | Source | What the model takes from it |
| --- | --- | --- |
| S1 | [`docs/network-spec/miniprotocols.tex`, "Protocols as State Machines", lines 27-36 and 96-98](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L27-L36) | Only one side has agency at a time. "If either side receives a message that is not expected according to the mini-protocol the communication is aborted (the connection is closed)." Every mini-protocol ends in a single `StDone` where nobody has agency. |
| S2 | [`docs/network-spec/miniprotocols.tex`, "Keep Alive Mini Protocol", lines 1560-1650](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/miniprotocols.tex#L1560-L1650) | The state machine, the agency table, the cookie rule, size limits (65535 bytes per state), and timeouts (97 s in `StClient`, 60 s in `StServer`). |
| S3 | [`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Type.hs`, lines 89-106](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Type.hs#L89-L106) | The three message types with their from- and to-states, and `StateAgency StDone = NobodyAgency` (S2's agency table leaves `StDone` out). |
| S4 | [`network-mux/src/Network/Mux.hs`, lines 362-378 and 512](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L362-L378) | When a run ends, the bytes it did not read are put back on the mini-protocol's queue for the next run. "Protocols that runs to completion are not automatically restarted" by the multiplexer itself. |
| S5 | [`network-mux/src/Network/Mux.hs`, lines 846-852](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/network-mux/src/Network/Mux.hs#L846-L852) | A mini-protocol may be started again on the same connection; only one that is still running is refused (`ProtocolAlreadyRunning`). |
| S6 | [`ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs`, lines 433-475](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L433-L475) | A responder (server) mini-protocol that ends cleanly is restarted (`TrResponderRestarted`) while the connection stays registered. |
| S7 | [`docs/network-spec/connection-manager.tex`, "Inbound side: the inbound governor", lines 489-503](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/docs/network-spec/connection-manager.tex#L489-L503) | The specification's statement of S6: "when a server-side mini-protocol terminates cleanly (usually because the client chose to terminate it), then the server side of the mini-protocol should be restarted in its initial state in case the client wishes to use the protocol again later." |
| S8 | [IntersectMBO/typed-protocols `8fa4ed2f` (version 1.2.2.0), `typed-protocols/src/Network/TypedProtocol/Driver.hs`, lines 145-176](https://github.com/IntersectMBO/typed-protocols/blob/8fa4ed2f5bfece84b323f6d80e0b61f4153b6975/typed-protocols/src/Network/TypedProtocol/Driver.hs#L145-L176) | The driver every reference mini-protocol runs on. It reads a message only at `Await`, when the peer has agency, and never complains about trailing data: "we want to allow for one protocols to be run after another on the same channel". ouroboros-network requires `typed-protocols ^>=1.2`; that this exact commit is the version it builds with was not checked. |
| S9 | [`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Codec.hs`, lines 58-116](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Codec.hs#L58-L116) | Decoding depends on the reader's current state; any other message fails with "unexpected key", which aborts the connection. Time limits 97 s and 60 s, the latter marked `TODO: ... should be 10s`. |

The message encodings (`[0, cookie]`, `[1, cookie]`, `[2]`) are in
[`cardano-diffusion/protocols/cddl/specs/keep-alive.cddl`](https://github.com/IntersectMBO/ouroboros-network/blob/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c/cardano-diffusion/protocols/cddl/specs/keep-alive.cddl);
the model does not need them.

### Rendered versions (easier to read)

| Ref | Rendered |
| --- | --- |
| S1 | [Network specification PDF](https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf), section 3.2 "Protocols as State Machines", page 10 |
| S2 | Same PDF, section 3.10 "Keep Alive Mini Protocol", page 33 |
| S3 | [Haddock for `Ouroboros.Network.Protocol.KeepAlive.Type`](https://ouroboros-network.cardano.intersectmbo.org/ouroboros-network/protocols/Ouroboros-Network-Protocol-KeepAlive-Type.html) |
| S7 | Same PDF, section 5.7 "Inbound side: the inbound governor", page 53 |

S4, S5, S6, S8, and S9 are implementation code with no rendered prose; read
the source.

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

**Messages are records.** A message is
`[type |-> "MsgKeepAlive", cookie |-> 0, oversized |-> FALSE]`, like a Go
struct. Two cookie values are enough to tell a matching cookie from a wrong
one, and `oversized` stands for "bigger than the state's 65535-byte limit"
without modelling sizes.

**Reading only when it is the peer's turn.** A side reads its inbox only while
its peer has agency (S8). A message that arrives early waits, and is judged
when it is finally read, against the state at that moment (S9).

**Judging a message** (`Judge`). When a side reads a message:

1. Over the size limit: tear down (S2).
2. Not legal in the reader's state: abort (S1).
3. A response whose cookie does not match the ping: protocol error (S2).
4. Otherwise follow the transition (S2).

**Runs.** After `StDone` no run is reading. `ClientRestart` lets the client
start another run (S5, up to `MaxRuns`). A server restarts when a message
arrives, and the new run reads it starting from `StClient` (S7, S6). Messages
for a client with no new run stay in its inbox, unread (S4).

**Switches.**

| Constant | `TRUE` | `FALSE` |
| --- | --- | --- |
| `ServerRestarts` | The specification (S7) | gOuroboros today: the bug |
| `UseTimeouts` | The state timeouts of S2 are in force | No timeouts, to show why they exist |
| `SlowPeers` | A peer may be slower than the timeout allows, so a timeout may fire whenever a side is waiting | Peers answer in time; a timeout fires only when nothing could ever arrive |

**A misbehaving peer.** `Inject` lets a rogue peer push any message (any type,
either cookie, oversized or not) into any inbox at any time, up to
`RogueMessages` times.

New TLA+ syntax is explained in comments the first time it appears, and in the
[glossary](../../docs/glossary.md).

## The receive table

`make keepalive-table` prints what happens to every kind of message, for each
role and state: 2 roles x 3 states x 5 kinds = 30 cells. The kinds are
`MsgKeepAlive`, `MsgKeepAliveResponse` (right cookie), `WrongCookieResponse`,
`MsgDone`, and `Oversized`. Besides a new state or `Violation`, a cell can be:

- **`Waits`**: the reader holds agency, so it does not read the message yet.
  It is judged when the peer next holds agency. All 10 cells where the reader
  holds agency are `Waits`.
- **`Held`**: the client's run is over and nothing reads the message.

After `MsgDone` a server judges the message as the first of a new run, in
`StClient`.

## Run it

```sh
make keepalive         # honest, slow, and rogue peers: all pass
make keepalive-table   # print the 30-cell receive table
make keepalive-bugs    # the deliberately failing configs, with traces
```

| Config | Checks | Result |
| --- | --- | --- |
| `KeepAlive.cfg` | Two honest peers that answer in time, up to two runs: no failures, one message in flight per run, responses echo cookies, never both have agency, views agree, only legal moves, failures are final. | Passes: 130 distinct states. |
| `KeepAliveSlow.cfg` | Honest but possibly slow peers: a timeout may end the connection, but never a protocol violation; only legal moves. | Passes: 272 distinct states. |
| `KeepAliveRogue.cfg` | Up to two rogue messages of any kind: still only legal moves, failures final, and no deadlock. | Passes: 83,394 distinct states. |
| `KeepAliveGouroborosBug.cfg` | Honest peers, but the server does not restart (gOuroboros today). | **Fails after 5 steps**: see [The bug](#the-bug). |
| `KeepAliveRogueBug.cfg` | Claims a rogue message never causes a hang-up. | Fails after 3 steps: a rogue `MsgKeepAlive` sent *to the client* waits until the client pings, is then read while waiting for a response, and is a violation. |
| `KeepAliveNoTimeoutBug.cfg` | Rogue peer, timeouts off. | **Deadlock**: after the client has finished for good, a rogue `MsgKeepAlive` restarts the server, which then waits for a client that will never speak. |
| `KeepAliveTable.cfg` | Prints the receive table. | 30 rows. |

`make keepalive` runs the first three; `make check` runs every config not
named `*Bug.cfg`. The rogue check takes a few seconds; it is the largest.

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
TLC checks it in every step of every behavior, including those with slow and
rogue peers. So, for example:

- `StServer` is entered only by `MsgKeepAlive` in `StClient`.
- `StDone` is entered only by `MsgDone` in `StClient`. Within a run it is never
  left; the next message belongs to a new run.
- No message is ever accepted with the wrong cookie, oversized, or in a state
  that does not allow it.
- A side that hung up stays hung up (`FailuresAreFinal`).

## Settled: messages after Done

The first draft of the model said a message after `StDone` is ignored. That
rule had no source; it copied what gOuroboros does. Reading only the
mini-protocol chapter (S1), the opposite looked right: a message after the
protocol has terminated is unexpected, so the connection is closed. The
reference implementation and a later chapter of the specification settled it,
and neither was right:

- **Server**: the specification says a server-side mini-protocol that
  terminates cleanly "should be restarted in its initial state in case the
  client wishes to use the protocol again later" (S7). The inbound governor
  does exactly that (S6), and the multiplexer keeps any bytes that arrived
  after `MsgDone` for the next run (S4). So a message after `MsgDone` is the
  first message of a **new run**, read in `StClient`.
- **Client**: nothing restarts it unless its owner starts a new run (S5). The
  bytes wait, unread, on its queue (S4). That is `Held` in the table.

The lesson for modelling: a rule's source can be in a different chapter from
the protocol's own section, so search the whole specification before calling
it silent.

## The bug

**gOuroboros's keep-alive server never restarts after `MsgDone`**, which the
specification requires (S7). Every other gOuroboros server with a `MsgDone`
(chain-sync, block-fetch, tx-submission, peer-sharing, and the Leios servers)
does: their `handleDone` calls `StopForRestart`, builds a new protocol
instance, and starts it. The keep-alive server's `handleDone` only calls the
optional `DoneFunc`.

`KeepAliveGouroborosBug.cfg` shows what that does, with two honest peers:

1. The client sends `MsgDone` and starts a second run on the same connection.
2. The server reads the `MsgDone` and ends its run.
3. The client sends `MsgKeepAlive`. The server never reads it. The client
   waits, and times out.

On a real connection that timeout is 60 s (S2), after which "the connection
SHOULD be torn down": a peer that restarts keep-alive loses its whole
connection to a gOuroboros node. The specification and reference
implementation both support a new run on the same connection; this model has
not established how often a real peer does it.

## Do the specification, the reference, and the model agree?

Checked on 2026-11-23 against the sources above.

| Topic | Specification | Reference implementation | This model | gOuroboros |
| --- | --- | --- | --- | --- |
| States, messages, transitions | S2 | Same (S3) | Same | Same |
| Agency per state | S2, S1 for `StDone` | Same (S3) | Same | Same |
| Wrong message for the reader's state | Abort (S1) | Abort: "unexpected key" (S9) | Violation | Violation |
| When a message from a peer without agency is judged | Not stated | When the peer next has agency, against that state (S8) | Same as reference (`Waits`) | On arrival: violation |
| Cookie mismatch | Protocol error (S2) | `KeepAliveCookieMissmatch` thrown (client) | Violation | Error |
| Over the size limit | Tear down (S2) | `smallByteLimit` (S9; value not checked) | Violation | Error |
| Server after `MsgDone` | Restart (S7) | Restart (S4, S6) | Restart | **Does not restart: the bug** |
| Client after `MsgDone` | Not stated | Bytes held for a next run (S4) | Held | Discarded |
| Timeouts | 97 s `StClient`, 60 s `StServer` (S2) | Same, `StServer` marked "should be 10s" (S9) | A slow peer may trigger either; no clock | 97 s; `StServer` 10 s by default (`WithTimeout`) |

The model now follows the specification wherever it speaks, and the reference
implementation where it is silent.

### Where gOuroboros differs without being wrong

- **Early messages.** gOuroboros judges a message the moment it arrives, so a
  message from a peer without agency is a violation at once; the reference
  waits and judges it later. Usually both end in a violation, the reference
  just later. But a client that sends a second `MsgKeepAlive` before the first
  is answered gets both answered by the reference, while gOuroboros hangs up.
  Only a misbehaving peer does this, and the specification does not say which
  is right. These are the 10 `Waits` cells; the Go tests check gOuroboros's
  stricter behavior there and say so.
- **Client after `MsgDone`.** gOuroboros discards later messages; the
  reference keeps them for a next run, and tears the connection down if too
  many pile up. No visible effect while the gOuroboros client never restarts.
- **The `StServer` timeout.** gOuroboros's client defaults to 10 s, the
  value the reference's `TODO` asks for, where the specification says 60 s.
  It gives up on a slow server sooner; stricter, not broken.

## The restart lifecycle (`KeepAliveLifecycle.tla`)

`KeepAlive.tla` says *what* must happen after `MsgDone`: a new run. A second,
smaller module checks *how* gOuroboros does it, one level down: its
goroutines. Each step is one line, or one locked block, of gOuroboros code, so
TLC tries every way two goroutines can interleave:

- **The restart**, run by the old instance's receive loop when `MsgDone`
  arrives (`handleDone` in `protocol/keepalive/server.go`): stop the old
  instance (`StopForRestart`), install a new one under `protocolMu`, start it.
- **The muxer slot** for the keep-alive server: one receiver per protocol and
  role, shared by instances one after another. `Stop` unregisters it;
  `StopForRestart` *suspends* it, so it keeps buffering for the next
  instance; `Start` registers or resumes it.
- **A stopper**, one of: `Server.Stop()`, which reads the current instance
  under the lock and stops it; or connection shutdown (`stopProtocols` in
  `connection.go`), which reads `ProtocolInstance()`, stops it, then stops
  the muxer.

```sh
make keepalive-lifecycle
```

| Config | Checks | Result |
| --- | --- | --- |
| `KeepAliveLifecycleStopBug.cfg` | The fix as first written: `Server.Stop()` racing a restart. | **Fails after 5 steps**: the restart stops the old instance; `Stop` reads that same, already stopped, instance and stops it again, which does nothing; the restart installs and starts a new instance. `Stop` returned, and keep-alive is still served. |
| `KeepAliveLifecycleSlotBug.cfg` | The guard as first written. | **Fails after 5 steps**: `StopForRestart` suspends the slot; `Stop` then cancels the restart, and nothing releases the slot. It keeps buffering the client's bytes, charged against the connection's ingress budget, until the connection closes. |
| `KeepAliveLifecycle.cfg` | With `StopGuard` and `CancelUnregisters`: `Stop` sets a flag under the lock, and a restart that sees it installs nothing and unregisters the slot. | Passes: 33 distinct states. Never two instances running; `Stop` always wins; nothing stays registered. |
| `KeepAliveLifecycleCloseBug.cfg` | Connection shutdown racing a restart, as gOuroboros did before the fix for issue #3085 (`ShutdownStopsServer = FALSE`). | **Fails**: shutdown stops the old instance and the muxer while the restart is between its steps; the restart then starts its new instance on a stopped muxer, which fails to register and raises "could not register protocol with muxer". |
| `KeepAliveLifecycleClose.cfg` | The same with the fix: connection shutdown calls the server's `Stop`. | Passes: 44 distinct states. No restart starts an instance after shutdown. |

The first result changed the gOuroboros fix before it was published: the
guard was added, with a Go test (`TestServerStopWinsOverRestart`) that calls
`Stop` from the server's `DoneFunc`, which runs inside the same window. The
test failed 3 times out of 3 without the guard.

The slot result came the other way round. The first version of this module
tracked only whether each instance ran, not its muxer registration, so it
passed the guard as written; a review bot then reported the suspended
receiver. Adding the slot to the model reproduced it, and
`TestServerStopAfterRestartBeganReleasesReceiver` failed 20 times out of 20
before the fix. A model only checks what it represents: leave out a piece of
state and every bug in that state passes.

The second result is not specific to keep-alive. Connection shutdown used to
stop only the instance it read, never a server's `Stop`, so no guard inside
the server could see it, and every gOuroboros server that restarts after
`MsgDone` (chain-sync, block-fetch, tx-submission, peer-sharing, and the
Leios servers) had the same window.

At first it looked harmless: the error the late start raises is dropped, and
nothing is left running once the muxer stops. Model 02 put bytes and the
connection around it and showed the harm: the restarted instance can handle a
message, running application callbacks, after `stopProtocols`. A Go test then
reproduced it with chain-sync on gOuroboros's `main`, 10 times out of 10.
Reported as gOuroboros issue #3085; pull request #3087, in review, fixes
it: each restarting server has its own guarded `Stop`, and `stopProtocols`
calls it.
The constant `ShutdownStopsServer` switches between the two behaviors.

## The Go tests this model drove

`protocol/keepalive/statemap_model_test.go` in gOuroboros holds the same 30
cells as `make keepalive-table`.

| Test | What it checks |
| --- | --- |
| `TestStateMapMatchesModel` | The within-run cells against `StateMap`, including cells no running program can reach. Cookie cells are left to the running tests, since the client checks cookies, not `StateMap`. |
| `TestReceiveMatchesModel` | Every cell a running client or server can rest in (25 of 30; a server never rests in `StServer`): drive it there, send the message, check the outcome. |
| `TestDoneCannotBeLeft` | No transition leaves `StDone` within a run; only `MsgDone` in `StClient` enters it. |
| `TestClientTimesOutWhenServerFallsSilent` | S2's `StServer` timeout: a client whose ping is never answered gives up. |
| `TestStateMapTimeoutsMatchSpec` | The per-state timeouts are 97 s and 60 s. |
| `TestServerStopWinsOverRestart` | `KeepAliveLifecycleStopBug.cfg`'s trace: `Stop` during a restart still stops the server. |
| `TestServerStopAfterRestartBeganReleasesReceiver` | `KeepAliveLifecycleSlotBug.cfg`'s trace: a restart cancelled by `Stop` releases the muxer receiver. |
| `TestServerStopAfterRestartBeganReleasesReceiver` in `protocol/chainsync` (pull request #3087) | The same trace for the servers that share chain-sync's restart code. |

Against gOuroboros today, exactly six cells fail, all from the bug: the server
after `MsgDone` (five kinds), and `MsgDone` followed by a new run. A prototype
server restart, following chain-sync's `handleDone`, made all six pass and was
then reverted. Every other cell was shown to fail when gOuroboros was
deliberately broken: a `MsgDone` transition added to `StServer`, a message let
through without agency, a client that ignores cookies, and a missing size
limit.

## What the model found

- **A bug**: the keep-alive server does not restart after `MsgDone`. See
  [The bug](#the-bug). Reported as gOuroboros issue #3076, fixed by pull
  request #3080 (merged). Pull request #3077 had the same change and was
  closed in favor of #3080 to re-sign its commits.
- **Two bugs in that fix**: `Stop` could lose to a restart in progress
  (caught before publishing), and a restart cancelled by `Stop` left its
  muxer receiver suspended (caught in review, then modelled). See
  [The restart lifecycle](#the-restart-lifecycle-keepalivelifecycletla).
- **A shutdown bug in every restarting server**: during a connection close, a
  restart could start an instance after the old one was stopped, and serve a
  message. Reproduced in Go, reported as gOuroboros issue #3085; the fix,
  pull request #3087, is in review. Same section, and
  [Model 02, part 2](../02-connection/README.md#part-2-stop-and-shutdown-during-a-restart-muxhandovertla).
- **gOuroboros follows the specification** on every within-run cell,
  including cookies and size limits.
- **The gOuroboros client never sends `MsgDone`.** The reference client sends
  it when told to terminate (`Ouroboros.Network.KeepAlive`, `Terminate ->
  SendMsgDone`), but nothing in the gOuroboros client API does, so a
  gOuroboros client never reaches `StDone`. The tests reach it by sending
  `MsgDone` directly.
- **Timeouts are needed**: without them one stray message can hang a
  connection forever (`KeepAliveNoTimeoutBug.cfg`), and a slow but honest peer
  never causes a protocol violation, only a timeout (`KeepAliveSlow.cfg`).

## Not modelled yet

Real time (the model has no clock, so it cannot check that the client's ping
interval is shorter than the server's 97 s timeout), exact message sizes,
ingress queue limits, and the goroutines inside gOuroboros. Those come later,
one at a time.
