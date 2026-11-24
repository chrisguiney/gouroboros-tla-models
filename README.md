# gouroboros TLA+ models

Formal models of [gouroboros](https://github.com/blinklabs-io/gouroboros), the
Go implementation of Cardano's Ouroboros network protocols. We use them to find
bugs and to work out which Go tests need to exist.

**You do not need to know TLA+ to start here.** The docs assume you know Go and
nothing else.

## Quick start

```sh
make install     # download Java + TLA+ tools into .tools/ (no sudo, ~200 MB)
make hello       # check a tiny model; ends with "No error has been found."
make hello-bug   # watch TLC catch a bug and print the steps that cause it
```

`make help` lists every command.

## Learning path

Read these in order. Each one builds on the last.

1. [Installing TLA+](docs/01-install.md): what `make install` does, editor setup, and troubleshooting.
2. [Your first model](docs/02-first-model.md): `specs/00-hello/Hello.tla` line by line, and how to read TLC's output.
3. [How this finds gouroboros bugs](docs/approach.md): the plan for turning models into Go tests.
4. [Model 01: keep-alive](specs/01-keepalive/README.md): the first real
   gouroboros model, the Go tests it drove, and what it found.
5. [Model 02: the connection](specs/02-connection/README.md): the
   multiplexer, and messages surviving a restart.
6. [Model 03: the protocol engine](specs/03-engine/README.md): the code every
   mini-protocol runs on, starting with how it admits incoming messages.
7. [Model 04: chain-sync](specs/04-chainsync/README.md): the client's sync
   window, stopping and restarting, its queries, and the protocol with its
   limits and timeouts.
8. [Model 05: the handshake](specs/05-handshake/README.md): version
   negotiation, queries, and simultaneous open.
9. [Model 06: block-fetch](specs/06-blockfetch/README.md): matching each
   batch to its request, and stopping with ranges outstanding.
10. [Model 07: tx-submission](specs/07-txsubmission/README.md): the
    acknowledgement window and the blocking-style rules.
11. [Model 08: peer-sharing](specs/08-peersharing/README.md): the amount
    rules, size limits and timeouts.
12. [Model 09: local tx](specs/09-localtx/README.md): local tx submission
    and the local tx monitor's acquire, query and release.
12. [Model 10: local-state-query](specs/10-localstatequery/README.md):
    acquiring, querying, releasing, and the client's concurrent calls.
13. [Model 11: message queue](specs/11-dmq/README.md): message
    submission (CIP-0137), local submission and notification.
14. [Model 12: Leios and Peras](specs/12-leios-peras/README.md): the
    experimental notify, fetch and vote protocols.
15. [Model 13: consensus](specs/13-consensus/README.md): chain selection,
    operational certificates and KES, and the Byron PBFT window.
16. [Model 14: the Shelley ledger](specs/14-ledger-shelley/README.md):
    certificate lifecycles, deposits, stake snapshots, value preservation.
17. [Model 15: Conway governance](specs/15-ledger-governance/README.md):
    proposals, voting, ratification, enactment and refunds.
18. [Model 16: block pipeline and CBOR](specs/16-pipeline-cbor/README.md):
    ordered apply, rollback fencing, drain, and preserved bytes.
19. [Model 18: Genesis density](specs/18-consensus-genesis/README.md):
    the density rule beside the reference's GDD governor and Limit on
    Eagerness.
20. [Model 19: the Byron ledger](specs/19-ledger-byron/README.md): the
    UTxO rule, fees and heavyweight delegation.
21. [Model 20: the Leios ledger side](specs/20-ledger-leios/README.md):
    certification, endorser-block application, rollback and the
    certificate's committee.
22. [Glossary](docs/glossary.md): keep it open while you read anything else.

`make models` checks every configuration of every model; a configuration
named `*Bug.cfg` is expected to fail, and the script says so if it does not.

## What is in the repository

| Path | What it is |
| --- | --- |
| `specs/` | One directory per model. Each has a `.tla` (the model) and one or more `.cfg` files (what to check). |
| `specs/00-hello/` | The training-wheels model. Start here. |
| `bin/tlc` | Runs the model checker. |
| `bin/sany` | Checks a model for syntax errors without running it. |
| `scripts/install-tla.sh` | The installer behind `make install`. |
| `.tools/` | The downloaded Java and TLA+ tools. Not committed; delete it to uninstall. |

## The one-paragraph explanation

A Go test checks one path through the code: the one the test author thought of.
A TLA+ model describes every move each side of a protocol is allowed to make,
and the model checker (TLC) tries **every** order those moves can happen in,
checking your rules after each one. When a rule breaks, TLC prints the exact
sequence of steps that broke it. Those sequences are the test cases nobody
thought to write.
