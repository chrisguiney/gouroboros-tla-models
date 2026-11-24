# How this finds gouroboros bugs

## Why gouroboros suits TLA+

Every Ouroboros mini-protocol (handshake, chain-sync, block-fetch,
tx-submission, keep-alive, local-state-query, and the rest) is a state machine.
In gouroboros each one declares that machine explicitly as a
`protocol.StateMap`: the states, which side has **agency** (the right to send)
in each, and which message moves to which next state. For example,
`protocol/keepalive/keepalive.go`:

```go
StateClient: protocol.StateMapEntry{
    Agency: protocol.AgencyClient,
    Transitions: []protocol.StateTransition{
        {MsgType: MessageTypeKeepAlive, NewState: StateServer},
        {MsgType: MessageTypeDone,      NewState: StateDone},
    },
},
```

That table maps almost one-to-one onto TLA+ actions. The bugs rarely live in
the table itself. They live in what surrounds it: two goroutines sending and
receiving at once, pipelined requests, timeouts, message size limits,
shutdown in the middle of a conversation, and the shared multiplexer that
carries every protocol over one connection. Those are the places where the
order of events matters, and exploring every order is what TLC is for.

## The loop

1. **Model** one protocol: start from the gouroboros `StateMap` and the
   Ouroboros network specification, then add the concurrency gouroboros
   actually has (send loop, receive loop, queues, timeouts).
2. **Write the rules** as invariants: both sides always agree on the state;
   only the side with agency sends; no message is accepted in the wrong state;
   a pipelined client never has more outstanding requests than allowed;
   shutdown never leaves a goroutine waiting forever (deadlock).
3. **Check** with TLC. Each violation is either a mistake in the model (fix the
   model) or a real sequence gouroboros could hit (go to step 4).
4. **Reproduce in Go**: turn the counterexample trace into a test in
   gouroboros, using its existing test helpers and `ouroboros-mock`
   fixtures. If the test fails, that is a bug. Fix it in gouroboros with the
   test as proof.
5. **Cover the states**: even when the model passes, the list of distinct
   states and transitions is a checklist. Every one should be reached by some
   Go test. Gaps are tests to write.

## Order of work

Smallest and most self-contained first, so we learn the method before the hard
protocols:

1. keep-alive: three states. Done:
   [`specs/keepalive`](../specs/keepalive/README.md).
2. handshake: version negotiation, still small.
3. chain-sync: pipelining and rollbacks; where real bugs are likely.
4. block-fetch and tx-submission: batching and flow control.
5. the multiplexer: many protocols sharing one connection.

## What a model is not

A model is a simplified description we write by hand, so it can be wrong.
A model that passes proves the **model** is correct, not the Go code. That is
why step 4 always ends in a Go test against the real code: the model tells us
where to look, and the test is the evidence.
