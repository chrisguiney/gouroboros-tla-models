# Your first model

Open `specs/00-hello/Hello.tla` next to this page. It is a toy version of
gouroboros's keep-alive mini-protocol (`protocol/keepalive` in gouroboros):

- The **client** sends a ping.
- The **server** answers with a pong.
- Repeat. When it is the client's turn, it may say "done" instead.

## The big idea

A TLA+ model describes a system as:

1. **Variables**: the things that can change.
2. **An initial state**: the starting value of every variable.
3. **Actions**: the steps that are allowed to happen, each written as
   "when *this* is true, the variables may change like *that*."

That is it. There are no loops and no function calls. TLC, the model checker,
starts at the initial state, tries every action that is allowed, and repeats
from every state it reaches until it has seen them all.

Then you add **invariants**: rules that must be true in every state. If any
reachable state breaks one, TLC shows you how it got there.

## Line by line

### The header

```tla
---------------------------- MODULE Hello ----------------------------
EXTENDS Naturals
```

Every file is one module, and the module name must match the file name.
`EXTENDS Naturals` imports numbers and `+`, `-`, `<`, `..`. Like a Go
`import`.

`(* ... *)` is a block comment and `\*` is a line comment.

### A constant

```tla
MaxPings == 3
```

`==` means "is defined as". This is like a Go `const`. A real client pings
forever, but TLC needs a finite number of states to finish, so we cap it.

### Variables

```tla
VARIABLES state, pings, pongs
vars == <<state, pings, pongs>>
```

Three variables. A **state** in TLA+ is one assignment of a value to every
variable, for example `state = "Server", pings = 1, pongs = 0`. `<<a, b, c>>`
is a tuple; `vars` just groups them so we can say "none of them changed".

Notice there are no types. A variable can hold anything. We will add a rule
that checks the types later (`TypeOK`).

### The initial state

```tla
Init ==
    /\ state = "Client"
    /\ pings = 0
    /\ pongs = 0
```

`/\` means **and**. A list of `/\` lines is just a bulleted list of things that
are all true. Here `=` is a comparison, not assignment: `Init` is true of
exactly one state, so that is where we start.

### Actions

```tla
SendPing ==
    /\ state = "Client"
    /\ pings < MaxPings
    /\ state' = "Server"
    /\ pings' = pings + 1
    /\ UNCHANGED pongs
```

This is the key idea of TLA+. Read the prime (`'`) as "in the next state".

- `state = "Client"` and `pings < MaxPings` mention only current values. They
  are the **guard**: this step can only happen when they are true. In
  gouroboros terms, the client must have **agency**.
- `state' = "Server"` and `pings' = pings + 1` say what the next state looks
  like.
- `UNCHANGED pongs` is shorthand for `pongs' = pongs`. Every action must say
  what happens to **every** variable, even the ones it leaves alone. Forgetting
  this is the most common beginner mistake, and TLC will complain loudly.

`SendPong` and `SendDone` follow the same pattern. `Finished` lets the model
sit in `"Done"` forever, so TLC knows that is a proper ending and not the
protocol getting stuck.

### Putting it together

```tla
Next == SendPing \/ SendPong \/ SendDone \/ Finished
Spec == Init /\ [][Next]_vars
```

`\/` means **or**. `Next` is "any one of these steps". `Spec` reads as: start in
`Init`, and then every step (`[]` means "always") is a `Next` step. You will
write this `Spec` line, unchanged, at the bottom of almost every model.

### Invariants

```tla
PongsMatchPings ==
    /\ pongs <= pings
    /\ pings - pongs <= 1

AgencyMatchesOutstandingPing ==
    (state = "Server") <=> (pings - pongs = 1)
```

These are the rules we believe about the protocol. "The server never answers a
ping that was not sent." "It is the server's turn exactly when one ping is
waiting." TLC checks them in every state it finds.

## The config file

`Hello.cfg` tells TLC what to run:

```
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT PongsMatchPings
INVARIANT AgencyMatchesOutstandingPing
```

One model can have several configs: different sizes, or different rules to
check.

## Run it

```sh
make hello
```

The lines that matter:

```
Model checking completed. No error has been found.
15 states generated, 11 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 8.
```

- **11 distinct states**: every situation the protocol can be in, with up to
  3 pings. TLC checked all three invariants in each one.
- **15 generated**: some steps led to states TLC had already seen.
- **depth 8**: the longest path from the start without repeating a state
  (ping, pong, ping, pong, ping, pong, done, plus the start).

A Go test of this protocol would check one or two of those paths. TLC checked
all of them.

## Watch it find a bug

`Hello.tla` also defines a rule that is deliberately wrong:

```tla
NeverDoneAfterPong == ~(state = "Done" /\ pongs > 0)
```

"The client never says done after getting a pong." That is false, and
`HelloBug.cfg` asks TLC to check it:

```sh
make hello-bug
```

```
Error: Invariant NeverDoneAfterPong is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ state = "Client"
/\ pings = 0
/\ pongs = 0

State 2: <SendPing line 53, col 5 to line 57, col 22 of module Hello>
/\ state = "Server"
/\ pings = 1
/\ pongs = 0

State 3: <SendPong ...>
/\ state = "Client"
/\ pings = 1
/\ pongs = 1

State 4: <SendDone ...>
/\ state = "Done"
/\ pings = 1
/\ pongs = 1
```

This is a **counterexample trace**: the exact sequence of actions that leads
to the broken rule, with every variable shown at each step. TLC always finds
the **shortest** one. In this project, a trace like this is a ready-made Go
test case: send ping, receive pong, send done, and check what gouroboros does.

## Try it yourself

Each of these takes one edit. Run `make hello` after each, read the result,
then undo the edit.

1. Change `MaxPings == 3` to `MaxPings == 10`. How many distinct states now?
2. Delete the line `/\ UNCHANGED pings` from `SendPong`. What does TLC say?
3. Change the guard of `SendPong` from `state = "Server"` to `TRUE`, so the
   server can answer any time. Which invariant catches it, and what is the
   shortest trace?
4. Remove `Finished` from `Next`. TLC reports a **deadlock**: a state where no
   step is possible. Real protocols deadlock too; this is one of the bug
   classes we will hunt for in gouroboros.

Next: [How this finds gouroboros bugs](approach.md).
