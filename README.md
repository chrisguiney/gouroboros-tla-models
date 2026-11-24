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
19. [Model 17: the UTXO rule](specs/17-ledger-utxo/README.md): value,
    fees, outputs, validity intervals, collateral and IsValid from Shelley
    to Babbage.
20. [Model 18: Genesis density](specs/18-consensus-genesis/README.md):
    the density rule beside the reference's GDD governor and Limit on
    Eagerness.
21. [Model 19: the Byron ledger](specs/19-ledger-byron/README.md): the
    UTxO rule, fees and heavyweight delegation.
22. [Model 20: the Leios ledger side](specs/20-ledger-leios/README.md):
    certification, endorser-block application, rollback and the
    certificate's committee.
23. [Model 21: the epoch nonce](specs/21-consensus-nonce/README.md): the
    evolving and candidate nonces, the freeze window and the tick.
24. [Drift](DRIFT.md): every place gOuroboros differs from the reference, with the spec's verdict.
25. [Glossary](docs/glossary.md): keep it open while you read anything else.
26. [Concurrency inventory](CONCURRENCY.md): every lock, goroutine and channel in gOuroboros, the hazards among them, and which concurrency models to write next.

`make models` checks every configuration of every model; a configuration
named `*Bug.cfg` is expected to fail, and the script says so if it does not.

## Reading a formula literally

Each definition in the models carries two English readings:

- **In English** says what the definition means, in everyday words.
- **Literally** reads the formula symbol by symbol, so you can match each
  word to the symbol it came from.

For example:

```tla
\* In English: "Message type t is legal in state s if some row of the
\* table starts with s and t."
\* Literally: "IsLegal of s and t is defined as: there exists a tr that
\*   is a member of Transitions such that element 1 of tr equals s and
\*   element 2 of tr equals t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
```

The literal readings use these words for each symbol:

| Symbol | Read as |
| --- | --- |
| `A == e` | "A is defined as e" |
| `F(x, y)` | "F of x and y" |
| `x \in S` | "x is a member of S" |
| `x \notin S` | "x is not a member of S" |
| `S \subseteq T` | "S is a subset of T" |
| `S \cup T`, `S \cap T`, `S \ T` | "the union of S and T", "the intersection of S and T", "S without the members of T" |
| `\A x \in S : P` | "for all x in S, P" |
| `\E x \in S : P` | "there exists an x in S such that P" |
| `CHOOSE x \in S : P` | "the x, chosen from S, such that P" |
| `P /\ Q`, `P \/ Q`, `~P` | "P and Q", "P or Q", "P is not true" |
| `P => Q` | "if P, then Q" |
| `P <=> Q` | "P if and only if Q" |
| `x = y`, `x /= y` | "x equals y", "x does not equal y" |
| `x'` | "x in the next state" |
| `UNCHANGED x` | "x is unchanged" |
| `IF a THEN b ELSE c` | "if a then b, else c" |
| `CASE a -> x [] b -> y [] OTHER -> z` | "in the case a, x; in the case b, y; in every other case, z" |
| `LET n == e IN body` | "letting n be e: body" |
| `{a, b}` | "the set containing a and b" |
| `{e : x \in S}` | "the set of e, for every x that is a member of S" |
| `{x \in S : P}` | "the set of every x in S such that P" |
| `[x \in S \|-> e]` | "the function that maps every x in S to e" |
| `[S -> T]` | "the set of functions from S to T" |
| `f[x]` | "f of x" (for a tuple or sequence: "element x of f") |
| `[f EXCEPT ![k] = v]` | "f except that its k entry is v" (`@` is "the old entry") |
| `[a \|-> 1, b \|-> 2]`, `r.a` | "the record whose field a is 1 and field b is 2", "r's a" |
| `<<a, b>>` | "the tuple of a and b" |
| `DOMAIN f` | "the domain of f" |
| `Cardinality(S)` | "the number of members of S" |
| `a..b` | "a through b" |
| `Seq(S)` | "the set of sequences of members of S" |
| `Append(s, x)`, `Head(s)`, `Tail(s)`, `Len(s)` | "s with x appended", "the head of s", "the tail of s", "the length of s" |
| `ENABLED A` | "A is enabled" |
| `[][A]_v` | "always, every step is an A step or a step that leaves v unchanged" |
| `<>P` | "eventually P" |
| `P ~> Q` | "P leads to Q" |
| `WF_v(A)`, `SF_v(A)` | "weak fairness of A", "strong fairness of A" |
| `x # y` | "x does not equal y" (same as `/=`) |
| `x \div y`, `x % y` | "x integer-divided by y", "x modulo y" |
| `s \o t` | "s followed by t" |
| `SubSeq(s, m, n)` | "the subsequence of s from element m through element n" |
| `SelectSeq(s, LAMBDA x : P)` | "the subsequence of s made of every x such that P" |
| `SUBSET S` | "the set of subsets of S" |
| `UNION S` | "the union of all the sets in S" |
| `S \X T` | "the Cartesian product of S and T" (every pair of a member of S and a member of T) |
| `[r EXCEPT !.f = v]` | "r except that its f field is v" |
| `RECURSIVE F(_)` | "F is defined recursively" (the reading sits above this line) |
| `ASSUME P` | "it is assumed that P" |

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
