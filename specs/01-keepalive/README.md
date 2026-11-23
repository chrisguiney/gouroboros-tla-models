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
The model is written from the Ouroboros network specification instead,
so comparing the two means something.

## What is new compared with the hello model

**Each side has its own view.** `view["Client"]` and `view["Server"]` are the
state each side *believes* the protocol is in. Messages travel through
`inbox`, so for a moment the two views differ. That gap is where real protocol
bugs live, and the invariant `ViewsAgreeWhenQuiet` checks that it always
closes.

**The receive rule.** `Receive(r, s, m)` says what side `r` must do when message
`m` arrives while it believes the state is `s`:

1. If `s` is `StDone`, ignore the message.
2. If the peer had agency and `s` has a transition for `m`, accept it.
3. Otherwise it is a **violation**: hang up.

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

- **gOuroboros agrees with the model on all 18 cells.** No bug in the
  keep-alive state machine.
- **The gOuroboros client never sends `MsgDone`.** The specification allows it
  and the server handles it, but nothing in the client API sends it, so a real
  gOuroboros client never reaches `StDone`; the test reaches it by sending
  `MsgDone` directly. Whether the client should end the protocol cleanly on
  shutdown is an open question for the maintainers.
- The model says why `ClientTimeout` and `ServerTimeout` exist: without them,
  one stray message can hang a connection forever.

## Not modelled yet

Cookies (a response must echo the ping's cookie; gOuroboros already tests this
in `client_cookie_test.go`), real time, message sizes, and the goroutines
inside gOuroboros. Those come later, one at a time.
