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
6. [Glossary](docs/glossary.md): keep it open while you read anything else.

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
