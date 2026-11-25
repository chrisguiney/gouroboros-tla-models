------------------------ MODULE LeiosNotifyPipelinedQuit ------------------------
(***************************************************************************)
(* Model `leios-peras`, LeiosNotifyPipelinedQuit: the gOuroboros          *)
(* LeiosNotify server answering a burst of pipelined requests followed by *)
(* MsgQuit, and how many times it asks its notification source.           *)
(*                                                                         *)
(* The server (protocol/leiosnotify/server.go) runs:                       *)
(*   read loop      reads each message off the wire in order and fires the *)
(*                  quit signal the moment it reads MsgQuit, before the    *)
(*                  message is queued (MessageReceivedFunc).               *)
(*   receive loop   takes one queued message at a time, and takes the next *)
(*                  request only once the previous one is answered         *)
(*                  (protocol.go recvLoop waits for peerHasAgency). A      *)
(*                  request starts a handler goroutine and returns.        *)
(*   handler        serveRequestNext: if the quit signal has fired it      *)
(*                  answers MsgCanceled without asking the source;         *)
(*                  otherwise it asks the source and, once the quit signal *)
(*                  fires, answers MsgCanceled.                            *)
(* The handler goroutine starts at an arbitrary later moment, so whether   *)
(* the source is asked at all depends on whether the read loop got to      *)
(* MsgQuit first.                                                          *)
(*                                                                         *)
(* A test that sends the whole burst and MsgQuit back to back, with a      *)
(* source that never returns, and then asserts the source was asked        *)
(* exactly once (TestServerCancelsEveryPipelinedRequest) assumes the       *)
(* handler ran before the read loop reached MsgQuit. This module asks      *)
(* whether the protocol promises that.                                     *)
(*                                                                         *)
(* Questions:                                                              *)
(*   EveryRequestCanceled the client gets MsgCanceled for each request,    *)
(*                        then MsgDone.                                    *)
(*   SourceAskedAtMostOnce a request read after the quit signal fired never*)
(*                        reaches the source.                              *)
(*   SourceAskedOnce      the source is asked exactly once.               *)
(*   Deadlock             TLC checks it; the only stop is Finished.        *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [R1] ouroboros-consensus ec239d57f618, .../LeiosNotify/Type.hs        *)
(*        126-162: Idle(client) -Req-> Busy, Idle -MsgQuit-> Quit,         *)
(*        Busy(server) -notification or MsgCanceled-> Idle,                *)
(*        Quit(server) -MsgDone-> Done.                                    *)
(*   [R3] .../LeiosNotify/Server.hs 51-57, 94-134: once MsgQuit arrives    *)
(*        the server answers every outstanding request with MsgCanceled,   *)
(*        then MsgDone. Nothing says how often the source is consulted.    *)
(*   [G1] gOuroboros 7e29631f, protocol/leiosnotify/server.go              *)
(*        (initProtocol MessageReceivedFunc, messageHandler,               *)
(*        serveRequestNext).                                               *)
(*   [G2] protocol/protocol.go recvLoop: a message admitted while the      *)
(*        server holds agency waits for peerHasAgency.                     *)
(*                                                                         *)
(* Not modelled: a source that returns, byte budgets, timeouts, and the    *)
(* server having no source (it parks the request and cancels on quit).     *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Requests,            \* pipelined requests the client sends before MsgQuit
    HandlerChecksQuit,   \* TRUE as in [G1]; FALSE is a mutation (no early cancel)
    ClientWaitsForSource \* FALSE: the client sends everything back to back
                         \* TRUE: it sends the rest only after the source was asked

VARIABLES
    sent,        \* messages the client has written: requests, then MsgQuit
    read,        \* messages the read loop has taken off the wire
    quitFired,   \* the quit signal has fired (the read loop read MsgQuit)
    queue,       \* messages read and not yet taken by the receive loop
    srv,         \* the server: "Idle", "Busy", "Done"
    handler,     \* the request's handler: "None", "Spawned", "Asking"
    sourceCalls, \* times the notification source was asked
    canceled     \* MsgCanceled replies sent

vars == <<sent, read, quitFired, queue, srv, handler, sourceCalls, canceled>>

\* In English: "Nothing sent, read, queued, answered or asked."
Init ==
    /\ sent = 0 /\ read = 0 /\ quitFired = FALSE /\ queue = <<>>
    /\ srv = "Idle" /\ handler = "None" /\ sourceCalls = 0 /\ canceled = 0

\* In English: "The client writes its next message: a request, then, after
\* the last, MsgQuit. In the handshaking variant it waits for the source to
\* have been asked before sending anything after the first request."
Send ==
    /\ sent < Requests + 1
    /\ (~ClientWaitsForSource \/ sent < 1 \/ sourceCalls >= 1)
    /\ sent' = sent + 1
    /\ UNCHANGED <<read, quitFired, queue, srv, handler, sourceCalls, canceled>>

\* In English: "The read loop takes the next message off the wire, fires the
\* quit signal if it is MsgQuit, and queues it [G1]."
Read ==
    /\ read < sent
    /\ read' = read + 1
    /\ IF read + 1 = Requests + 1
       THEN quitFired' = TRUE /\ queue' = Append(queue, "Quit")
       ELSE UNCHANGED quitFired /\ queue' = Append(queue, "Req")
    /\ UNCHANGED <<sent, srv, handler, sourceCalls, canceled>>

\* In English: "The receive loop takes the oldest queued message once the
\* server holds no unanswered request [G2]. A request starts a handler
\* goroutine; MsgQuit is answered with MsgDone."
Take ==
    /\ queue /= <<>> /\ srv = "Idle"
    /\ queue' = Tail(queue)
    /\ IF Head(queue) = "Req"
       THEN srv' = "Busy" /\ handler' = "Spawned"
       ELSE srv' = "Done" /\ UNCHANGED handler
    /\ UNCHANGED <<sent, read, quitFired, sourceCalls, canceled>>

\* In English: "The handler goroutine runs. If the quit signal has fired it
\* answers MsgCanceled; otherwise it asks the source [G1]. With the mutation
\* it always asks."
Handle ==
    /\ handler = "Spawned"
    /\ IF quitFired /\ HandlerChecksQuit
       THEN /\ canceled' = canceled + 1 /\ srv' = "Idle" /\ handler' = "None"
            /\ UNCHANGED sourceCalls
       ELSE /\ sourceCalls' = sourceCalls + 1 /\ handler' = "Asking"
            /\ UNCHANGED <<canceled, srv>>
    /\ UNCHANGED <<sent, read, quitFired, queue>>

\* In English: "The source never returns; once the quit signal fires the
\* handler stops waiting and answers MsgCanceled [G1]."
Cancel ==
    /\ handler = "Asking" /\ quitFired
    /\ canceled' = canceled + 1 /\ srv' = "Idle" /\ handler' = "None"
    /\ UNCHANGED <<sent, read, quitFired, queue, sourceCalls>>

\* In English: "The connection is over: the server answered MsgQuit."
Finished == srv = "Done"

Next ==
    \/ Send \/ Read \/ Take \/ Handle \/ Cancel
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "When the server is done, every request was answered with
\* MsgCanceled."
EveryRequestCanceled == Finished => canceled = Requests

\* In English: "The source is asked at most once."
SourceAskedAtMostOnce == sourceCalls <= 1

\* In English: "When the server is done, the source was asked exactly once."
SourceAskedOnce == Finished => sourceCalls = 1
=============================================================================
