------------------------ MODULE EngineRoundTripVerdict ------------------------
(***************************************************************************)
(* Model `engine`, slice 7: what a test can observe when a client sends    *)
(* a second request before the server has answered the first, and the      *)
(* protocol does not pipeline.                                             *)
(*                                                                         *)
(* Based on protocol/protocol.go (readLoop, recvLoop,                      *)
(* reserveInboundAdmission) and protocol/message_scanner_test.go           *)
(* (TestReadLoopRejectsUndeclaredRequestAcrossRoundTrip). Symbols are      *)
(* explained in specs/keepalive/KeepAlive.tla's header.                    *)
(*                                                                         *)
(* The scenario: a server whose states are Idle (client has agency) and    *)
(* Busy (server has agency, no pipelined types). One segment carries two   *)
(* Request messages. readLoop admits the first and queues it. recvLoop     *)
(* then (1) applies the Idle->Busy transition, (2) runs the handler,       *)
(* which counts itself and (3) applies the reply, Busy->Idle. Every state  *)
(* change bumps the generation and clears peerAgencyReserved.              *)
(*                                                                         *)
(* readLoop meanwhile takes a snapshot of (state, generation) when the     *)
(* second message starts, then decides admission against the state at     *)
(* that moment, by the rules of reserveInboundAdmission:                   *)
(*   - Idle, generation moved since the snapshot (and not by one from a    *)
(*     peer-agency snapshot): refuse; unchanged and reserved: wait;        *)
(*     unchanged and not reserved: admit.                                  *)
(*   - Busy (we hold agency, nothing declared pipelined): refuse.          *)
(* A refusal is reported on the error channel. The test reads that error   *)
(* and then asserts how many times the handler has run.                    *)
(*                                                                         *)
(* Sources. gOuroboros protocol.go as above. IntersectMBO/typed-protocols *)
(* commit 8fa4ed2f5bfe, typed-protocols/src/Network/TypedProtocol/         *)
(* Driver.hs lines 161-163 [S1]: a peer reads only while awaiting, so a    *)
(* coalesced second request is judged against the state after the reply,   *)
(* as DRIFT.md N1 records.                                                 *)
(*                                                                         *)
(* Gated = FALSE: the handler replies as soon as it has run, and the test *)
(*   reads the handler count when the error arrives (the test as written). *)
(* Gated = TRUE: the handler waits for the test to release it after the    *)
(*   error, and the test waits for the handler to have run before it       *)
(*   reads the error.                                                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Gated      \* TRUE: handshake between test and handler

VARIABLES
    st,        \* the protocol state: "Idle" or "Busy"
    gen,       \* its generation
    reserved,  \* peerAgencyReserved
    queued,    \* TRUE while the first message waits for recvLoop
    recv,      \* recvLoop: "wait", "transitioned", "handled", "replied"
    handled,   \* how many times the handler has run
    rd,        \* readLoop on message 2: "start", "snapped", "refused", "admitted"
    snapSt,    \* snapshot state
    snapGen,   \* snapshot generation
    obs,       \* the test: "none", "sawError", "done"
    seen,      \* handled count when the test read the error
    released   \* TRUE once the test has released a gated handler

vars == <<st, gen, reserved, queued, recv, handled, rd, snapSt, snapGen, obs,
          seen, released>>

\* In English: "The first message has been admitted and queued; the state has
\* not moved yet; nothing has been decided about the second."
Init == /\ st = "Idle" /\ gen = 0 /\ reserved = TRUE /\ queued = TRUE
        /\ recv = "wait" /\ handled = 0 /\ rd = "start"
        /\ snapSt = "Idle" /\ snapGen = 0 /\ obs = "none" /\ seen = 0
        /\ released = FALSE

\* In English: "recvLoop takes the queued message and applies Idle -> Busy."
Transition == /\ queued /\ recv = "wait"
              /\ st' = "Busy" /\ gen' = gen + 1 /\ reserved' = FALSE
              /\ queued' = FALSE /\ recv' = "transitioned"
              /\ UNCHANGED <<handled, rd, snapSt, snapGen, obs, seen, released>>

\* In English: "recvLoop runs the handler, which counts itself."
Handle == /\ recv = "transitioned"
          /\ handled' = handled + 1 /\ recv' = "handled"
          /\ UNCHANGED <<st, gen, reserved, queued, rd, snapSt, snapGen, obs,
                         seen, released>>

\* In English: "The handler's reply applies Busy -> Idle; a gated handler
\* waits for the test's release first."
Reply == /\ recv = "handled" /\ (~Gated \/ released)
         /\ st' = "Idle" /\ gen' = gen + 1 /\ reserved' = FALSE
         /\ recv' = "replied"
         /\ UNCHANGED <<queued, handled, rd, snapSt, snapGen, obs, seen,
                        released>>

\* In English: "readLoop snapshots the state when message 2 starts."
Snapshot == /\ rd = "start"
            /\ rd' = "snapped" /\ snapSt' = st /\ snapGen' = gen
            /\ UNCHANGED <<st, gen, reserved, queued, recv, handled, obs, seen,
                           released>>

\* In English: "readLoop decides admission of message 2 against the state now."
Decide ==
    /\ rd = "snapped"
    /\ IF st = "Busy"
          THEN /\ rd' = "refused" /\ UNCHANGED reserved
          ELSE IF gen # snapGen /\ ~(gen = snapGen + 1 /\ snapSt = "Idle")
          THEN /\ rd' = "refused" /\ UNCHANGED reserved
          ELSE IF ~reserved
          THEN /\ rd' = "admitted" /\ reserved' = TRUE
          ELSE /\ rd' = rd /\ UNCHANGED reserved   \* wait and ask again
    /\ UNCHANGED <<st, gen, queued, recv, handled, snapSt, snapGen, obs, seen,
                   released>>

\* In English: "The test reads the error; a gated test first waits for the
\* handler, an ungated one reads the count at once."
Observe == /\ rd = "refused" /\ obs = "none" /\ (~Gated \/ handled >= 1)
           /\ obs' = "sawError" /\ seen' = handled
           /\ UNCHANGED <<st, gen, reserved, queued, recv, handled, rd, snapSt,
                          snapGen, released>>

\* In English: "The test releases a gated handler and finishes."
Release == /\ obs = "sawError"
           /\ obs' = "done" /\ released' = TRUE
           /\ UNCHANGED <<st, gen, reserved, queued, recv, handled, rd, snapSt,
                          snapGen, seen>>

\* In English: "Everything has finished, or message 2 was admitted and the
\* test would time out; stay put so TLC reports only real deadlocks."
Finished == /\ ( (obs = "done" /\ recv = "replied")
                 \/ rd = "admitted" )
            /\ UNCHANGED vars

Next == Transition \/ Handle \/ Reply \/ Snapshot \/ Decide \/ Observe
        \/ Release \/ Finished

Spec == Init /\ [][Next]_vars

\* The test's second assertion: when it reads the error the handler has run once.
HandlerRanBeforeError == obs # "none" => seen = 1
\* The test's first assertion: message 2 is always refused, never admitted.
AlwaysRefused == rd # "admitted"
=============================================================================
