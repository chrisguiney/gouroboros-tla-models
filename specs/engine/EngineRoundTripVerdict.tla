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
(* A refusal calls SendError, which stops the protocol. stateLoop         *)
(* publishes the Idle->Busy state before it answers recvLoop's request on  *)
(* that request's errorChan, so readLoop can refuse message 2 and stop the *)
(* protocol before recvLoop has the answer. requestStateTransition then    *)
(* selects between the answer and stopChan, and may return                 *)
(* ErrProtocolShuttingDown; recvLoop returns without running the handler.  *)
(*                                                                         *)
(* Gated = FALSE: the handler replies as soon as it has run, and the test *)
(*   reads the handler count when the error arrives (the original test).   *)
(* Gated = TRUE: the handler waits for the test to release it after the    *)
(*   error.                                                                *)
(* WaitHandler = TRUE: the test waits for the handler to have run before   *)
(*   it reads the error. WaitHandler = FALSE: the test reads the error     *)
(*   first, then checks the state and that the handler ran at most once.   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Gated,      \* TRUE: the handler holds its reply until released
         WaitHandler \* TRUE: the test waits for the handler before the error

VARIABLES
    st,        \* the protocol state: "Idle" or "Busy"
    gen,       \* its generation
    reserved,  \* peerAgencyReserved
    queued,    \* TRUE while the first message waits for recvLoop
    recv,      \* recvLoop: "wait", "applied", "transitioned", "handled",
               \* "replied", "quit"
    handled,   \* how many times the handler has run
    rd,        \* readLoop on message 2: "start", "snapped", "refused", "admitted"
    snapSt,    \* snapshot state
    snapGen,   \* snapshot generation
    obs,       \* the test: "none", "sawError", "done"
    seen,      \* handled count when the test read the error
    released,  \* TRUE once the test has released a gated handler
    stopped,   \* TRUE once SendError has stopped the protocol
    seenSt     \* the state when the test read the error

vars == <<st, gen, reserved, queued, recv, handled, rd, snapSt, snapGen, obs,
          seen, released, stopped, seenSt>>

\* In English: "The first message has been admitted and queued; the state has
\* not moved yet; nothing has been decided about the second."
Init == /\ st = "Idle" /\ gen = 0 /\ reserved = TRUE /\ queued = TRUE
        /\ recv = "wait" /\ handled = 0 /\ rd = "start"
        /\ snapSt = "Idle" /\ snapGen = 0 /\ obs = "none" /\ seen = 0
        /\ released = FALSE /\ stopped = FALSE /\ seenSt = "Idle"

\* In English: "recvLoop takes the queued message and stateLoop publishes
\* Idle -> Busy; recvLoop has not yet received stateLoop's answer."
Transition == /\ queued /\ recv = "wait" /\ ~stopped
              /\ st' = "Busy" /\ gen' = gen + 1 /\ reserved' = FALSE
              /\ queued' = FALSE /\ recv' = "applied"
              /\ UNCHANGED <<handled, rd, snapSt, snapGen, obs, seen, released,
                             stopped, seenSt>>

\* In English: "requestStateTransition receives stateLoop's answer. Once the
\* protocol is stopped, its select may take the answer or stopChan."
Learn == /\ recv = "applied"
         /\ recv' = "transitioned"
         /\ UNCHANGED <<st, gen, reserved, queued, handled, rd, snapSt, snapGen,
                        obs, seen, released, stopped, seenSt>>

\* In English: "recvLoop sees the stop first and returns: from its idle
\* select, from requestStateTransition (ErrProtocolShuttingDown), or from
\* a released handler's reply transition."
Quit == /\ stopped
        /\ \/ recv \in {"wait", "applied"}
           \/ recv = "handled" /\ (~Gated \/ released)
        /\ recv' = "quit"
        /\ UNCHANGED <<st, gen, reserved, queued, handled, rd, snapSt, snapGen,
                       obs, seen, released, stopped, seenSt>>

\* In English: "recvLoop runs the handler, which counts itself."
Handle == /\ recv = "transitioned"
          /\ handled' = handled + 1 /\ recv' = "handled"
          /\ UNCHANGED <<st, gen, reserved, queued, rd, snapSt, snapGen, obs,
                         seen, released, stopped, seenSt>>

\* In English: "The handler's reply applies Busy -> Idle; a gated handler
\* waits for the test's release first."
Reply == /\ recv = "handled" /\ (~Gated \/ released)
         /\ st' = "Idle" /\ gen' = gen + 1 /\ reserved' = FALSE
         /\ recv' = "replied"
         /\ UNCHANGED <<queued, handled, rd, snapSt, snapGen, obs, seen,
                        released, stopped, seenSt>>

\* In English: "readLoop snapshots the state when message 2 starts."
Snapshot == /\ rd = "start"
            /\ rd' = "snapped" /\ snapSt' = st /\ snapGen' = gen
            /\ UNCHANGED <<st, gen, reserved, queued, recv, handled, obs, seen,
                           released, stopped, seenSt>>

\* In English: "readLoop decides admission of message 2 against the state now;
\* a refusal goes through SendError, which stops the protocol."
Decide ==
    /\ rd = "snapped"
    /\ IF st = "Busy"
          THEN /\ rd' = "refused" /\ UNCHANGED reserved /\ stopped' = TRUE
          ELSE IF gen # snapGen /\ ~(gen = snapGen + 1 /\ snapSt = "Idle")
          THEN /\ rd' = "refused" /\ UNCHANGED reserved /\ stopped' = TRUE
          ELSE IF ~reserved
          THEN /\ rd' = "admitted" /\ reserved' = TRUE /\ UNCHANGED stopped
          ELSE /\ rd' = rd /\ UNCHANGED <<reserved, stopped>> \* ask again
    /\ UNCHANGED <<st, gen, queued, recv, handled, snapSt, snapGen, obs, seen,
                   released, seenSt>>

\* In English: "The test reads the error, first waiting for the handler if
\* WaitHandler, and records the handler count and the state."
Observe == /\ rd = "refused" /\ obs = "none" /\ (~WaitHandler \/ handled >= 1)
           /\ obs' = "sawError" /\ seen' = handled /\ seenSt' = st
           /\ UNCHANGED <<st, gen, reserved, queued, recv, handled, rd, snapSt,
                          snapGen, released, stopped>>

\* In English: "The test releases a gated handler and finishes."
Release == /\ obs = "sawError"
           /\ obs' = "done" /\ released' = TRUE
           /\ UNCHANGED <<st, gen, reserved, queued, recv, handled, rd, snapSt,
                          snapGen, seen, stopped, seenSt>>

\* In English: "Everything has finished, or message 2 was admitted and the
\* test would time out; stay put so TLC reports only real deadlocks."
Finished == /\ ( (obs = "done" /\ recv \in {"replied", "quit"})
                 \/ rd = "admitted" )
            /\ UNCHANGED vars

Next == Transition \/ Learn \/ Quit \/ Handle \/ Reply \/ Snapshot \/ Decide \/ Observe
        \/ Release \/ Finished

Spec == Init /\ [][Next]_vars

\* The test's second assertion: when it reads the error the handler has run once.
HandlerRanBeforeError == obs # "none" => seen = 1
\* The test's first assertion: message 2 is always refused, never admitted.
AlwaysRefused == rd # "admitted"
\* A test waiting for the handler can wait forever: recvLoop quit before it.
NoStall == ~(WaitHandler /\ obs = "none" /\ rd = "refused" /\ recv = "quit"
             /\ handled = 0)
\* What the error proves: the first request's transition was applied and its
\* reply is still held, and message 2 never reached the handler.
RefusedInBusy == obs # "none" => seenSt = "Busy"
AtMostOneHandled == handled <= 1
=============================================================================
