--------------------------- MODULE ConnectionEngines ---------------------------
(***************************************************************************)
(* Part 8: one connection with its mini-protocol engines, goroutine by     *)
(* goroutine. ConnectionLifecycle.tla (part 7) folds every mini-protocol   *)
(* into one callback; this module gives each engine its own send loop,     *)
(* receive loop with handler, done watcher, a bounded send queue and a     *)
(* muxer sender, and adds the keep-alive client's timer, so teardown is    *)
(* checked against everything a connection starts.                         *)
(*                                                                         *)
(* gOuroboros 0c00b799 (origin/main, v0.222.0). Goroutines:                *)
(*   setup     setupConnection (connection.go:853-1290): waits for the     *)
(*             handshake, its timer or a refusal (:1029-1049), starts the  *)
(*             protocol-error forwarder (:1063, goTracked :519) and each   *)
(*             engine, then opens the muxer gate (:1293)                   *)
(*   sd        the shutdown goroutine (:873-876, shutdown :467-506):       *)
(*             stopProtocols, muxer Stop, CloseProtocolLoops,              *)
(*             WaitProtocolLoops, fence and waitGroup.Wait, close the      *)
(*             owned errorChan, close connClosedChan                       *)
(*   fwdMux    the muxer-error forwarder (:904-932)                        *)
(*   fwdProto  the protocol-error forwarder (:1063-1076)                   *)
(*   user      Close (:318-359) from outside any callback                  *)
(*   mr        the muxer read loop (muxer.go:1540), behind the start gate  *)
(*   mclean    the muxer cleanup goroutine (muxer.go:1115-1129)            *)
(*   msnd[p]   the muxer sender of engine p (muxer.go:1317-1347)           *)
(*   rv[p]     engine p's recvLoop running MessageHandlerFunc              *)
(*             (protocol.go:2471-2549); its readLoop is folded into mr's   *)
(*             delivery (MuxHandover.tla holds that detail)                *)
(*   sl[p]     engine p's sendLoop (protocol.go:1449-1772)                 *)
(*   w[p]      engine p's done watcher (protocol.go:508-512)               *)
(*   kaClean   the keep-alive client's cleanup goroutine                   *)
(*             (keepalive/client.go:114-122)                               *)
(*   kaCb      the keep-alive timer's AfterFunc callback, sendKeepAlive    *)
(*             (keepalive/client.go:128-168)                               *)
(*   app       an application goroutine calling SendMessage on engine     *)
(*             "cs" (protocol.go:1003, enqueueMessage :1076-1156)          *)
(* The engines' state loops are folded into one step that raises a         *)
(* protocol error, as a state timeout does (EngineTimer.tla holds when).   *)
(*                                                                         *)
(* Every channel is a GoConcurrency channel or signal: sendQueueChan with  *)
(* capacity QCap (80 in Go), the muxer's per-protocol sender channel with  *)
(* capacity SegCap (10 in Go), recvQueueChan with capacity 1, errorChan    *)
(* and the muxer's error channel (capacity 10: never full here).           *)
(*                                                                         *)
(* Each engine is checked against the Engine interface                    *)
(* (specs/common/Engine.tla) through a refinement mapping                  *)
(* (EnginesRefine); the connection's own steps read and write the engines  *)
(* only through the interface's objects: stopChan, doneChan, the join,    *)
(* started, reg and sendQ.                                                 *)
(*                                                                         *)
(* Reference: ouroboros-network network-mux Network.Mux run and stop      *)
(* (Mux.hs:195-197, 244-300, 513-550, 623-634) and docs/network-spec      *)
(* mux.tex:111-131; see README part 8 for the three-way comparison.       *)
(*                                                                         *)
(* How to read the symbols: see specs/keepalive/KeepAlive.tla's header.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, GoConcurrency

CONSTANTS
    Protos,         \* engine ids: "ka" (keep-alive client) and "cs" (a
                    \* client with an application caller and replies)
    QCap,           \* sendQueueChan's capacity (80 in Go)
    SegCap,         \* the muxer sender channel's capacity (10 in Go)
    AppMsgs,        \* how many messages the application sends on "cs"
    PeerMsgs,       \* how many messages the peer sends after the handshake
    Sources,        \* teardown sources the environment may use: "close",
                    \* "eof", "protoErr", "hsTimeout", "hsRefuse"
    BearerMayBlock, \* TRUE: the peer may stop reading, so writes block
    WatcherJoined,  \* TRUE: the done watcher is joined (the fix)
    KaJoined        \* TRUE: the keep-alive cleanup and its timer callback
                    \* are joined (the fix); FALSE: gOuroboros 0c00b799

ASSUME Protos \subseteq {"ka", "cs"}
ASSUME Sources \subseteq {"close", "eof", "protoErr", "hsTimeout", "hsRefuse"}

VARIABLES
    setup,      \* setup's next step, "ok" or "err" once it returned
    toStart,    \* engines setup has not started yet
    cDone,      \* the connection's doneChan is closed
    errChan,    \* the owned errorChan (a GoConcurrency channel)
    errs,       \* errors delivered on errorChan in total
    protoErr,   \* errors queued on protoErrorChan
    fwdMux,     \* the muxer-error forwarder: "run" or "exited"
    fwdProto,   \* the protocol-error forwarder: "none", "run" or "exited"
    sd,         \* the shutdown goroutine's next step
    user,       \* "idle", "waitConn", "waitLoops" or "returned"
    connClosed, \* connClosedChan is closed
    loopsClosed,\* the muxer refuses new protocol loops
    panicked,   \* a send on a closed channel or a close of a closed one
    mux,        \* the muxer: gate, done, connShut, errQ, errClosed, cleaned
    mr,         \* the muxer read loop: "gate", "read", "exited"
    mclean,     \* the muxer cleanup goroutine: "wait", "join", "exited"
    msnd,       \* msnd[p]: "none", "run", "write", "exited"
    senderCh,   \* senderCh[p]: the muxer sender channel of engine p
    wire,       \* peer messages not read yet: a sequence of engine ids
    peerSent,   \* peer messages sent so far
    peerEOF,    \* the peer closed its end
    blocked,    \* the peer stopped reading
    started,    \* started[p]: Start started p's loops
    constructed,\* the engines exist (setup passed lockProtocolSetup)
    stopChan,   \* stopChan[p] is closed
    doneChan,   \* doneChan[p] (DoneChan) is closed
    recvDone,   \* recvDoneChan[p] is closed
    sendDone,   \* sendDoneChan[p] is closed
    sendQ,      \* sendQ[p]: sendQueueChan
    recvQ,      \* recvQ[p]: recvQueueChan
    reg,        \* reg[p]: "none", "registered", "released"
    rv,         \* rv[p]: "none", "wait", "handle", "enq", "exited"
    sl,         \* sl[p]: "none", "wait", "hold", "exited"
    w,          \* w[p]: "none", "w1", "w2", "exited"
    app,        \* the application caller: "idle", "enq", "done"
    appSent,    \* messages the application queued
    kaTimer,    \* the keep-alive timer (GoConcurrency timer states)
    kaCb,       \* the timer callback: "none", "enq", "arm"
    kaClean,    \* the cleanup goroutine: "none", "wait", "join", "exited"
    timedOut    \* engines whose state timer has fired

conn   == <<setup, toStart, cDone, errChan, errs, protoErr, fwdMux, fwdProto,
            sd, user, connClosed, loopsClosed, panicked>>
\* In English: "conn without panicked, for steps that may panic."
connNP == <<setup, toStart, cDone, errChan, errs, protoErr, fwdMux, fwdProto,
            sd, user, connClosed, loopsClosed>>
muxv   == <<mux, mr, mclean, msnd, senderCh>>
peer   == <<wire, peerSent, peerEOF, blocked>>
eng    == <<started, constructed, stopChan, doneChan, recvDone, sendDone,
            sendQ, recvQ, reg, rv, sl, w>>
ka     == <<app, appSent, kaTimer, kaCb, kaClean, timedOut>>
vars   == <<conn, muxv, peer, eng, ka>>

-----------------------------------------------------------------------------
(* Helpers *)

\* In English: "Goroutine state s means the goroutine is not running."
Gone(s) == s \in {"none", "exited"}

\* In English: "The goroutines of engine p that WaitProtocolLoops waits for:
\* recvLoop and sendLoop (and readLoop and stateLoop, folded here); the
\* done watcher only under WatcherJoined; the keep-alive cleanup only under
\* KaJoined, where it is started with RunLoop."
Tracked(p) ==
    {"rv", "sl"} \cup (IF WatcherJoined THEN {"w"} ELSE {})
                 \cup (IF KaJoined /\ p = "ka" THEN {"kaClean"} ELSE {})

\* In English: "The state of goroutine g of engine p."
G(g, p) == CASE g = "rv" -> rv[p]
             [] g = "sl" -> sl[p]
             [] g = "w"  -> w[p]
             [] g = "kaClean" -> kaClean

\* In English: "Every goroutine of engine p that the join counts is over."
Joined(p) == \A g \in Tracked(p) : Gone(G(g, p))

\* In English: "WaitProtocolLoops would return: every engine's counted
\* goroutines are over."
AllJoined == \A p \in Protos : Joined(p)

\* In English: "Engine p's recvLoop is inside MessageHandlerFunc."
Handling(p) == rv[p] \in {"handle", "enq"}

\* In English: "engine p after stop(false), run inline (protocol.go:584-626):
\* stopped and stopChan closed, the role unregistered, and DoneChan closed
\* at once if the loops never started."
StopEngine(p) ==
    /\ stopChan' = [stopChan EXCEPT ![p] = TRUE]
    /\ reg' = [reg EXCEPT ![p] = "released"]
    /\ doneChan' = [doneChan EXCEPT ![p] = @ \/ ~started[p]]

\* In English: "closeWithError (connection.go:540-548): the first closer of
\* doneChan also sends err without blocking; a later call does nothing."
CloseWithError ==
    IF cDone
    THEN UNCHANGED <<cDone, errChan, errs, panicked>>
    ELSE /\ cDone' = TRUE
         /\ panicked' = (panicked \/ SendPanics(errChan))
         /\ errChan' = IF CanSend(errChan) THEN Send(errChan, "err") ELSE errChan
         /\ errs' = errs + 1

\* In English: "The muxer's sendError (muxer.go:1225-1243): unless it is
\* already done, queue the error without blocking and stop the muxer."
MuxSendError ==
    IF mux.done THEN UNCHANGED <<mux, panicked>>
    ELSE /\ panicked' = (panicked \/ mux.errClosed)
         /\ mux' = [mux EXCEPT !.errQ = @ + 1, !.done = TRUE]

\* In English: "A SendMessage on engine p may give up: shutting down."
SendGivesUp(p) == stopChan[p] \/ doneChan[p] \/ mux.done

-----------------------------------------------------------------------------
Init ==
    /\ setup = "hs" /\ toStart = Protos /\ cDone = FALSE
    /\ errChan = Chan(10) /\ errs = 0 /\ protoErr = 0
    /\ fwdMux = "run" /\ fwdProto = "none" /\ sd = "wait"
    /\ user = "idle" /\ connClosed = FALSE /\ loopsClosed = FALSE
    /\ panicked = FALSE
    /\ mux = [gate |-> FALSE, done |-> FALSE, connShut |-> FALSE,
              errQ |-> 0, errClosed |-> FALSE, cleaned |-> FALSE]
    /\ mr = "gate" /\ mclean = "wait"
    /\ msnd = [p \in Protos |-> "none"]
    /\ senderCh = [p \in Protos |-> Chan(SegCap)]
    /\ wire = <<>> /\ peerSent = 0 /\ peerEOF = FALSE /\ blocked = FALSE
    /\ started = [p \in Protos |-> FALSE] /\ constructed = FALSE
    /\ stopChan = [p \in Protos |-> FALSE]
    /\ doneChan = [p \in Protos |-> FALSE]
    /\ recvDone = [p \in Protos |-> FALSE]
    /\ sendDone = [p \in Protos |-> FALSE]
    /\ sendQ = [p \in Protos |-> Chan(QCap)]
    /\ recvQ = [p \in Protos |-> Chan(1)]
    /\ reg = [p \in Protos |-> "none"]
    /\ rv = [p \in Protos |-> "none"] /\ sl = [p \in Protos |-> "none"]
    /\ w = [p \in Protos |-> "none"]
    /\ app = "idle" /\ appSent = 0
    /\ kaTimer = TimerIdle /\ kaCb = "none" /\ kaClean = "none"
    /\ timedOut = {}

-----------------------------------------------------------------------------
(* The peer and the bearer. *)

\* In English: "The peer sends a message for engine p, after the handshake."
PeerSend(p) ==
    /\ setup \in {"start", "ok"} /\ ~peerEOF /\ peerSent < PeerMsgs
    /\ wire' = Append(wire, p) /\ peerSent' = peerSent + 1
    /\ UNCHANGED <<conn, muxv, peerEOF, blocked, eng, ka>>

\* In English: "The peer closes its end; the read loop will see EOF."
PeerClose ==
    /\ "eof" \in Sources /\ ~peerEOF /\ setup = "ok"
    /\ peerEOF' = TRUE
    /\ UNCHANGED <<conn, muxv, wire, peerSent, blocked, eng, ka>>

\* In English: "The peer stops reading: every write now blocks until the
\* muxer closes the conn."
PeerStall ==
    /\ BearerMayBlock /\ ~blocked
    /\ blocked' = TRUE
    /\ UNCHANGED <<conn, muxv, wire, peerSent, peerEOF, eng, ka>>

-----------------------------------------------------------------------------
(* setupConnection *)

\* In English: "The handshake finishes (FinishedFunc closes
\* handshakeFinishedChan, :1000); setup's select takes it."
SetupHandshake ==
    /\ setup = "hs" /\ ~cDone
    /\ setup' = "lock"
    /\ UNCHANGED <<toStart, cDone, errChan, errs, protoErr, fwdMux, fwdProto,
                   sd, user, connClosed, loopsClosed, panicked, muxv, peer,
                   eng, ka>>

\* In English: "Setup's select takes the handshake timer, a handshake
\* error, or doneChan, and calls Close (:1035-1049): requestClose, then
\* wait."
SetupFails ==
    /\ setup = "hs"
    /\ \/ "hsTimeout" \in Sources /\ UNCHANGED protoErr
       \/ "hsRefuse" \in Sources /\ UNCHANGED protoErr
       \/ cDone /\ UNCHANGED protoErr
    /\ cDone' = TRUE
    /\ setup' = "closeWait"
    /\ UNCHANGED <<toStart, errChan, errs, fwdMux, fwdProto, sd, user,
                   connClosed, loopsClosed, panicked, muxv, peer, eng, ka>>

\* In English: "Setup's Close waits for connClosedChan, then for the loops,
\* and setup returns an error."
SetupCloseWait ==
    \/ setup = "closeWait" /\ connClosed /\ setup' = "closeLoops"
       /\ UNCHANGED <<toStart, cDone, errChan, errs, protoErr, fwdMux, fwdProto,
                      sd, user, connClosed, loopsClosed, panicked, muxv, peer,
                      eng, ka>>
    \/ setup = "closeLoops" /\ AllJoined /\ setup' = "err"
       /\ UNCHANGED <<toStart, cDone, errChan, errs, protoErr, fwdMux, fwdProto,
                      sd, user, connClosed, loopsClosed, panicked, muxv, peer,
                      eng, ka>>

\* In English: "lockProtocolSetup (:670-684): under protocolMu, if doneChan
\* is closed setup gives up; otherwise the engines are constructed, so
\* stopProtocols will find them. The protocol-error forwarder is started
\* by goTracked, which starts nothing once doneChan is closed."
SetupLock ==
    /\ setup = "lock"
    /\ IF cDone
       THEN /\ setup' = "err"
            /\ UNCHANGED <<constructed, fwdProto>>
       ELSE /\ setup' = "start"
            /\ constructed' = TRUE
            /\ fwdProto' = "run"
    /\ UNCHANGED <<toStart, cDone, errChan, errs, protoErr, fwdMux, sd, user,
                   connClosed, loopsClosed, panicked, muxv, peer, started,
                   stopChan, doneChan, recvDone, sendDone, sendQ, recvQ, reg, rv,
                   sl, w, ka>>

\* In English: "Setup starts engine p (Protocol.Start, protocol.go:457-525,
\* one lifecycleMu section): nothing if p was stopped; if the muxer is done
\* or refuses new loops, DoneChan closes and no loop starts; otherwise
\* register, start recvLoop, sendLoop, the watcher and the muxer sender.
\* For the keep-alive client, Start then starts its cleanup goroutine and
\* sends the first keep-alive inline, arming the timer
\* (keepalive/client.go:101-125)."
SetupStart(p) ==
    /\ setup = "start" /\ p \in toStart
    /\ toStart' = toStart \ {p}
    /\ setup' = IF toStart' = {} THEN "gate" ELSE "start"
    /\ LET runs == ~stopChan[p] /\ ~mux.done /\ ~loopsClosed
           refused == ~stopChan[p] /\ ~runs
           kaRuns == p = "ka" /\ runs
       IN
       /\ started' = [started EXCEPT ![p] = runs]
       /\ reg' = [reg EXCEPT ![p] = IF runs THEN "registered" ELSE @]
       /\ doneChan' = [doneChan EXCEPT ![p] = @ \/ refused]
       /\ rv' = [rv EXCEPT ![p] = IF runs THEN "wait" ELSE @]
       /\ sl' = [sl EXCEPT ![p] = IF runs THEN "wait" ELSE @]
       /\ w' = [w EXCEPT ![p] = IF runs THEN "w1" ELSE @]
       /\ msnd' = [msnd EXCEPT ![p] = IF runs THEN "run" ELSE @]
       /\ kaClean' = IF p = "ka" /\ (~KaJoined \/ runs) THEN "wait" ELSE kaClean
       /\ sendQ' = [sendQ EXCEPT ![p] = IF kaRuns THEN Send(@, "ping") ELSE @]
       /\ kaTimer' = IF kaRuns THEN TimerArmed ELSE kaTimer
    /\ UNCHANGED <<cDone, errChan, errs, protoErr, fwdMux, fwdProto, sd, user,
                   connClosed, loopsClosed, panicked, mux, mr, mclean, senderCh,
                   peer, constructed, stopChan, recvDone, sendDone, recvQ,
                   app, appSent, kaCb, timedOut>>

\* In English: "Setup opens the muxer gate (muxer.Start) and returns nil."
SetupGate ==
    /\ setup = "gate"
    /\ setup' = "ok"
    /\ mux' = [mux EXCEPT !.gate = TRUE]
    /\ UNCHANGED <<toStart, cDone, errChan, errs, protoErr, fwdMux, fwdProto,
                   sd, user, connClosed, loopsClosed, panicked, mr, mclean,
                   msnd, senderCh, peer, eng, ka>>

-----------------------------------------------------------------------------
(* The user's Close (connection.go:318-359), from outside any callback. *)

UserClose ==
    /\ "close" \in Sources /\ user = "idle" /\ setup = "ok"
    /\ user' = "waitConn" /\ cDone' = TRUE
    /\ UNCHANGED <<setup, toStart, errChan, errs, protoErr, fwdMux, fwdProto,
                   sd, connClosed, loopsClosed, panicked, muxv, peer, eng, ka>>

UserWait ==
    \/ user = "waitConn" /\ connClosed /\ user' = "waitLoops"
    \/ user = "waitLoops" /\ AllJoined /\ user' = "returned"

UserStep == UserWait /\ UNCHANGED <<setup, toStart, cDone, errChan, errs,
                   protoErr, fwdMux, fwdProto, sd, connClosed, loopsClosed,
                   panicked, muxv, peer, eng, ka>>

-----------------------------------------------------------------------------
(* The forwarders. *)

\* In English: "The muxer-error forwarder's select: doneChan, or an error
\* (closeWithError), or the muxer's closed error channel."
FwdMux ==
    /\ fwdMux = "run"
    /\ \/ cDone /\ UNCHANGED <<cDone, errChan, errs, panicked, mux>>
       \/ mux.errQ > 0 /\ mux' = [mux EXCEPT !.errQ = @ - 1] /\ CloseWithError
       \/ mux.errClosed /\ mux.errQ = 0
          /\ UNCHANGED <<cDone, errChan, errs, panicked, mux>>
    /\ fwdMux' = "exited"
    /\ UNCHANGED <<setup, toStart, protoErr, fwdProto, sd, user, connClosed,
                   loopsClosed, mr, mclean, msnd, senderCh, peer, eng, ka>>

\* In English: "The protocol-error forwarder's select: doneChan or an
\* error."
FwdProto ==
    /\ fwdProto = "run"
    /\ \/ cDone /\ UNCHANGED <<cDone, errChan, errs, panicked, protoErr>>
       \/ protoErr > 0 /\ protoErr' = protoErr - 1 /\ CloseWithError
    /\ fwdProto' = "exited"
    /\ UNCHANGED <<setup, toStart, fwdMux, sd, user, connClosed, loopsClosed,
                   muxv, peer, eng, ka>>

-----------------------------------------------------------------------------
(* The shutdown goroutine. *)

\* In English: "Shutdown, one step per wait: on doneChan, stopProtocols
\* signals every constructed engine; muxer.Stop and wait for its cleanup;
\* CloseProtocolLoops; WaitProtocolLoops; fence and waitGroup.Wait (the
\* forwarders); close the owned errorChan and connClosedChan."
Shutdown ==
    \/ /\ sd = "wait" /\ cDone /\ sd' = "muxStop"
       /\ IF constructed
          THEN /\ stopChan' = [p \in Protos |-> TRUE]
               /\ reg' = [p \in Protos |-> "released"]
               /\ doneChan' = [p \in Protos |-> doneChan[p] \/ ~started[p]]
          ELSE UNCHANGED <<stopChan, reg, doneChan>>
       /\ UNCHANGED <<mux, loopsClosed, errChan, connClosed, panicked>>
    \/ /\ sd = "muxStop" /\ sd' = "muxWait"
       /\ mux' = [mux EXCEPT !.done = TRUE]
       /\ UNCHANGED <<stopChan, reg, doneChan, loopsClosed, errChan, connClosed,
                      panicked>>
    \/ /\ sd = "muxWait" /\ mux.cleaned /\ sd' = "loopsWait"
       /\ loopsClosed' = TRUE
       /\ UNCHANGED <<stopChan, reg, doneChan, mux, errChan, connClosed, panicked>>
    \/ /\ sd = "loopsWait" /\ AllJoined /\ sd' = "wg"
       /\ UNCHANGED <<stopChan, reg, doneChan, mux, loopsClosed, errChan,
                      connClosed, panicked>>
    \/ /\ sd = "wg" /\ Gone(fwdMux) /\ Gone(fwdProto) /\ sd' = "exited"
       /\ panicked' = (panicked \/ ClosePanics(errChan))
       /\ errChan' = Close(errChan)
       /\ connClosed' = TRUE
       /\ UNCHANGED <<stopChan, reg, doneChan, mux, loopsClosed>>

ShutdownStep ==
    /\ Shutdown
    /\ UNCHANGED <<setup, toStart, cDone, errs, protoErr, fwdMux, fwdProto, user,
                   mr, mclean, msnd, senderCh, peer, started, constructed,
                   recvDone, sendDone, sendQ, recvQ, rv, sl, w, ka>>

-----------------------------------------------------------------------------
(* The muxer. *)

\* In English: "The read loop: before the gate it waits (handshake segments
\* are folded into SetupHandshake); then it reads a message and puts it on
\* its engine's receive queue, dropping it if the engine is not
\* registered; it waits while that queue is full; on EOF or a closed conn
\* it reports the error and stops the muxer; on done it exits."
MuxRead ==
    /\ mr \in {"gate", "read"}
    /\ \/ mux.done /\ mr' = "exited"
          /\ UNCHANGED <<mux, panicked, wire, recvQ>>
       \/ mr = "gate" /\ mux.gate /\ ~mux.done /\ mr' = "read"
          /\ UNCHANGED <<mux, panicked, wire, recvQ>>
       \/ /\ mr = "read" /\ ~mux.done /\ wire /= <<>>
          /\ LET p == Head(wire) IN
             \/ reg[p] /= "registered" /\ wire' = Tail(wire)
                /\ UNCHANGED recvQ
             \/ reg[p] = "registered" /\ CanSend(recvQ[p])
                /\ wire' = Tail(wire)
                /\ recvQ' = [recvQ EXCEPT ![p] = Send(@, "msg")]
          /\ UNCHANGED <<mr, mux, panicked>>
       \/ /\ mr = "read" /\ wire = <<>> /\ (peerEOF \/ mux.connShut)
          /\ MuxSendError /\ mr' = "exited"
          /\ UNCHANGED <<wire, recvQ>>
    /\ UNCHANGED <<connNP, mclean, msnd, senderCh, peerSent, peerEOF,
                   blocked, started, constructed, stopChan, doneChan, recvDone,
                   sendDone, sendQ, reg, rv, sl, w, ka>>

\* In English: "Engine p's muxer sender: on done it exits; it takes a
\* segment and writes it; a write blocks while the peer does not read,
\* until the cleanup closes the conn, when it fails, reports the error and
\* exits. A closed sender channel (sendLoop exited) ends it too."
MuxSend(p) ==
    /\ \/ /\ msnd[p] = "run"
          /\ \/ mux.done /\ msnd' = [msnd EXCEPT ![p] = "exited"]
                /\ UNCHANGED <<senderCh, mux, panicked>>
             \/ ChanLen(senderCh[p]) > 0
                /\ senderCh' = [senderCh EXCEPT ![p] = Recv(@)]
                /\ msnd' = [msnd EXCEPT ![p] = "write"]
                /\ UNCHANGED <<mux, panicked>>
             \/ senderCh[p].closed /\ ChanLen(senderCh[p]) = 0
                /\ msnd' = [msnd EXCEPT ![p] = "exited"]
                /\ UNCHANGED <<senderCh, mux, panicked>>
       \/ /\ msnd[p] = "write"
          /\ \/ ~blocked /\ ~mux.connShut /\ msnd' = [msnd EXCEPT ![p] = "run"]
                /\ UNCHANGED <<mux, panicked>>
             \/ mux.connShut /\ MuxSendError
                /\ msnd' = [msnd EXCEPT ![p] = "exited"]
          /\ UNCHANGED senderCh
    /\ UNCHANGED <<connNP, mr, mclean, peer, eng, ka>>

\* In English: "The muxer cleanup: on done close the conn; wait for the
\* read loop and every sender; close the muxer's error channel."
MuxClean ==
    /\ \/ mclean = "wait" /\ mux.done /\ mclean' = "join"
          /\ mux' = [mux EXCEPT !.connShut = TRUE]
          /\ UNCHANGED panicked
       \/ mclean = "join" /\ Gone(mr) /\ \A p \in Protos : Gone(msnd[p])
          /\ mclean' = "exited"
          /\ panicked' = (panicked \/ mux.errClosed)
          /\ mux' = [mux EXCEPT !.errClosed = TRUE, !.cleaned = TRUE]
    /\ UNCHANGED <<connNP, mr, msnd, senderCh, peer, eng, ka>>

-----------------------------------------------------------------------------
(* Engine p's goroutines. *)

\* In English: "recvLoop: it leaves on stopChan, sendDoneChan or the muxer's
\* done; or it takes a message and runs the handler."
RecvWait(p) ==
    /\ rv[p] = "wait"
    /\ \/ (stopChan[p] \/ sendDone[p] \/ mux.done)
          /\ rv' = [rv EXCEPT ![p] = "exited"]
          /\ recvDone' = [recvDone EXCEPT ![p] = TRUE]
          /\ UNCHANGED recvQ
       \/ ChanLen(recvQ[p]) > 0
          /\ recvQ' = [recvQ EXCEPT ![p] = Recv(@)]
          /\ rv' = [rv EXCEPT ![p] = "handle"]
          /\ UNCHANGED recvDone
    /\ UNCHANGED <<conn, muxv, peer, started, constructed, stopChan, doneChan,
                   sendDone, sendQ, reg, sl, w, ka>>

\* In English: "The handler returns; or, on "cs", it replies with
\* SendMessage; or it finds a protocol violation and calls SendError
\* (protocol.go:1159-1182): unless stopping, queue the error without
\* blocking and stop the engine inline."
Handle(p) ==
    /\ rv[p] = "handle"
    /\ \/ rv' = [rv EXCEPT ![p] = "wait"]
          /\ UNCHANGED <<protoErr, stopChan, reg, doneChan>>
       \/ p = "cs" /\ rv' = [rv EXCEPT ![p] = "enq"]
          /\ UNCHANGED <<protoErr, stopChan, reg, doneChan>>
       \/ "protoErr" \in Sources /\ rv' = [rv EXCEPT ![p] = "wait"]
          /\ IF stopChan[p] \/ doneChan[p]
             THEN UNCHANGED <<protoErr, stopChan, reg, doneChan>>
             ELSE protoErr' = protoErr + 1 /\ StopEngine(p)
    /\ UNCHANGED <<setup, toStart, cDone, errChan, errs, fwdMux, fwdProto, sd,
                   user, connClosed, loopsClosed, panicked, muxv, peer, started,
                   constructed, recvDone, sendDone, sendQ, recvQ, sl, w, ka>>

\* In English: "The handler's SendMessage: the enqueue select (protocol.go:
\* 1131-1139) puts the reply on sendQueueChan when it has room, or gives
\* up on stopChan, DoneChan or the muxer's done."
HandleEnq(p) ==
    /\ rv[p] = "enq"
    /\ \/ CanSend(sendQ[p]) /\ sendQ' = [sendQ EXCEPT ![p] = Send(@, "reply")]
       \/ SendGivesUp(p) /\ UNCHANGED sendQ
    /\ rv' = [rv EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<conn, muxv, peer, started, constructed, stopChan, doneChan,
                   recvDone, sendDone, recvQ, reg, sl, w, ka>>

\* In English: "sendLoop: it leaves on stopChan or recvDoneChan, closing the
\* muxer sender channel and sendDoneChan; or it takes a message and hands
\* it to the muxer sender, waiting while that channel is full."
Sender(p) ==
    /\ \/ /\ sl[p] \in {"wait", "hold"} /\ (stopChan[p] \/ recvDone[p])
          /\ sl' = [sl EXCEPT ![p] = "exited"]
          /\ panicked' = (panicked \/ ClosePanics(senderCh[p]))
          /\ senderCh' = [senderCh EXCEPT ![p] = Close(@)]
          /\ sendDone' = [sendDone EXCEPT ![p] = TRUE]
          /\ UNCHANGED sendQ
       \/ /\ sl[p] = "wait" /\ ChanLen(sendQ[p]) > 0
          /\ sendQ' = [sendQ EXCEPT ![p] = Recv(@)]
          /\ sl' = [sl EXCEPT ![p] = "hold"]
          /\ UNCHANGED <<panicked, senderCh, sendDone>>
       \/ /\ sl[p] = "hold" /\ CanSend(senderCh[p])
          /\ senderCh' = [senderCh EXCEPT ![p] = Send(@, "seg")]
          /\ sl' = [sl EXCEPT ![p] = "wait"]
          /\ UNCHANGED <<panicked, sendQ, sendDone>>
    /\ UNCHANGED <<setup, toStart, cDone, errChan, errs, protoErr, fwdMux,
                   fwdProto, sd, user, connClosed, loopsClosed, mux, mr, mclean,
                   msnd, peer, started, constructed, stopChan, doneChan,
                   recvDone, recvQ, reg, rv, w, ka>>

\* In English: "The done watcher: recvDoneChan, then sendDoneChan, then
\* closeDone."
Watcher(p) ==
    /\ \/ w[p] = "w1" /\ recvDone[p] /\ w' = [w EXCEPT ![p] = "w2"]
          /\ UNCHANGED doneChan
       \/ w[p] = "w2" /\ sendDone[p] /\ w' = [w EXCEPT ![p] = "exited"]
          /\ doneChan' = [doneChan EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<conn, muxv, peer, started, constructed, stopChan, recvDone,
                   sendDone, sendQ, recvQ, reg, rv, sl, ka>>

\* In English: "Engine p's state timer fires once while it runs, and
\* stateLoop calls SendError (EngineTimer.tla: when it is armed)."
StateTimeout(p) ==
    /\ "protoErr" \in Sources /\ started[p] /\ p \notin timedOut
    /\ ~stopChan[p] /\ ~doneChan[p]
    /\ timedOut' = timedOut \cup {p}
    /\ protoErr' = protoErr + 1
    /\ StopEngine(p)
    /\ UNCHANGED <<setup, toStart, cDone, errChan, errs, fwdMux, fwdProto, sd,
                   user, connClosed, loopsClosed, panicked, muxv, peer, started,
                   constructed, recvDone, sendDone, sendQ, recvQ, rv, sl, w,
                   app, appSent, kaTimer, kaCb, kaClean>>

-----------------------------------------------------------------------------
(* The application caller on "cs" and the keep-alive client. *)

\* In English: "The application calls SendMessage: the pre-check returns
\* an error when shutting down; the enqueue select waits for room, or
\* gives up the same way. It stops after AppMsgs messages or an error."
App ==
    /\ "cs" \in Protos /\ setup = "ok"
    /\ \/ app = "idle" /\ appSent < AppMsgs
          /\ app' = (IF SendGivesUp("cs") THEN "done" ELSE "enq")
          /\ UNCHANGED <<sendQ, appSent>>
       \/ app = "enq" /\ CanSend(sendQ["cs"])
          /\ sendQ' = [sendQ EXCEPT !["cs"] = Send(@, "req")]
          /\ appSent' = appSent + 1
          /\ app' = IF appSent' = AppMsgs THEN "done" ELSE "idle"
       \/ app = "enq" /\ SendGivesUp("cs") /\ app' = "done"
          /\ UNCHANGED <<sendQ, appSent>>
    /\ UNCHANGED <<conn, muxv, peer, started, constructed, stopChan, doneChan,
                   recvDone, sendDone, recvQ, reg, rv, sl, w, kaTimer, kaCb,
                   kaClean, timedOut>>

\* In English: "The keep-alive timer fires: time.AfterFunc starts
\* sendKeepAlive on a goroutine of its own."
KaFire ==
    /\ "ka" \in Protos /\ CanFire(kaTimer) /\ kaCb = "none"
    /\ kaTimer' = TimerFired /\ kaCb' = "enq"
    /\ UNCHANGED <<conn, muxv, peer, eng, app, appSent, kaClean, timedOut>>

\* In English: "sendKeepAlive: SendMessage (queue the keep-alive, or give up
\* when shutting down), then startTimer, which arms a new timer only if the
\* engine is neither stopping nor done (keepalive/client.go:153-168, checked
\* under timerMutex, which the cleanup also takes: one step)."
KaCallback ==
    /\ \/ kaCb = "enq" /\ CanSend(sendQ["ka"])
          /\ sendQ' = [sendQ EXCEPT !["ka"] = Send(@, "ping")]
          /\ kaCb' = "arm" /\ UNCHANGED kaTimer
       \/ kaCb = "enq" /\ SendGivesUp("ka") /\ kaCb' = "arm"
          /\ UNCHANGED <<sendQ, kaTimer>>
       \/ kaCb = "arm" /\ kaCb' = "none" /\ UNCHANGED sendQ
          /\ kaTimer' = IF stopChan["ka"] \/ doneChan["ka"] THEN kaTimer
                        ELSE TimerArmed
    /\ UNCHANGED <<conn, muxv, peer, started, constructed, stopChan, doneChan,
                   recvDone, sendDone, recvQ, reg, rv, sl, w, app, appSent,
                   kaClean, timedOut>>

\* In English: "The keep-alive cleanup. gOuroboros: a bare goroutine that
\* waits for DoneChan and stops the timer. KaJoined: a RunLoop loop that
\* waits for StopChan, stops the timer, then waits for a callback already
\* running."
KaCleanup ==
    /\ \/ kaClean = "wait"
          /\ (IF KaJoined THEN stopChan["ka"] ELSE doneChan["ka"])
          /\ kaTimer' = StopTimer(kaTimer)
          /\ kaClean' = IF KaJoined THEN "join" ELSE "exited"
       \/ kaClean = "join" /\ kaCb = "none" /\ kaClean' = "exited"
          /\ UNCHANGED kaTimer
    /\ UNCHANGED <<conn, muxv, peer, eng, app, appSent, kaCb, timedOut>>

-----------------------------------------------------------------------------
\* In English: "Everything has finished: Close returned (or setup failed
\* and returned), the application gave up or finished, and every goroutine
\* of the connection, the muxer and the engines is over."
Owned == {"sd", "fwdMux", "fwdProto", "mr", "mclean", "kaClean", "kaCb"}

\* In English: "Every goroutine the connection started has exited, and no
\* timer is armed that would start one."
NothingRuns ==
    /\ Gone(sd) /\ Gone(fwdMux) /\ Gone(fwdProto) /\ Gone(mr) /\ Gone(mclean)
    /\ Gone(kaClean) /\ kaCb = "none" /\ kaTimer /= TimerArmed
    /\ \A p \in Protos : Gone(msnd[p]) /\ Gone(rv[p]) /\ Gone(sl[p]) /\ Gone(w[p])

Finished ==
    /\ user = "returned" \/ setup = "err" \/ ("close" \notin Sources /\ connClosed)
    /\ app \in {"done"} \/ "cs" \notin Protos \/ setup = "err"
    /\ NothingRuns

\* In English: "The code's steps."
Code ==
    \/ SetupHandshake \/ SetupFails \/ SetupCloseWait \/ SetupLock
    \/ \E p \in Protos : SetupStart(p)
    \/ SetupGate \/ UserStep \/ FwdMux \/ FwdProto \/ ShutdownStep
    \/ MuxRead \/ MuxClean
    \/ \E p \in Protos : MuxSend(p) \/ RecvWait(p) \/ Handle(p) \/ HandleEnq(p)
                         \/ Sender(p) \/ Watcher(p)
    \/ App \/ KaCallback \/ KaCleanup

\* In English: "The environment's steps: the peer, the user's Close, the
\* keep-alive timer and the state timers."
Env ==
    \/ \E p \in Protos : PeerSend(p) \/ StateTimeout(p)
    \/ PeerClose \/ PeerStall \/ UserClose \/ KaFire

Next == Code \/ Env \/ (Finished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

\* In English: "Fairness for liveness: every step of the code that stays
\* enabled is eventually taken, each goroutine's steps on their own (weak
\* fairness on Code as a whole would let the keep-alive timer's steps
\* starve setup). The environment needs none; Close is called when the
\* liveness config makes it."
FairSpec ==
    /\ Spec
    /\ WF_vars(SetupHandshake) /\ WF_vars(SetupCloseWait) /\ WF_vars(SetupLock)
    /\ WF_vars(SetupGate) /\ WF_vars(UserStep) /\ WF_vars(UserClose)
    /\ WF_vars(FwdMux) /\ WF_vars(FwdProto) /\ WF_vars(ShutdownStep)
    /\ WF_vars(MuxRead) /\ WF_vars(MuxClean)
    /\ WF_vars(App) /\ WF_vars(KaCallback) /\ WF_vars(KaCleanup)
    /\ \A p \in Protos :
        /\ WF_vars(SetupStart(p)) /\ WF_vars(MuxSend(p)) /\ WF_vars(RecvWait(p))
        /\ WF_vars(Handle(p)) /\ WF_vars(HandleEnq(p)) /\ WF_vars(Sender(p))
        /\ WF_vars(Watcher(p))

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ errs \in Nat /\ protoErr \in Nat
    /\ \A p \in Protos : ChanLen(sendQ[p]) <= QCap /\ ChanLen(senderCh[p]) <= SegCap

\* In English: "No goroutine sends on a closed channel or closes a closed
\* one."
NoPanic == ~panicked

\* In English: "ErrorChan carries at most one error per connection."
AtMostOneError == errs <= 1

\* In English: "When Close has returned, no goroutine the connection, its
\* muxer or its engines started is running, and no timer is armed to start
\* one: Close's doc, "waits until every mini-protocol goroutine and every
\* muxer goroutine has returned"."
NothingOutlivesClose == user = "returned" => NothingRuns

\* In English: "When Close has returned, every started engine's DoneChan is
\* closed: Stop's doc, applied to every engine Close stops."
DoneAfterClose == user = "returned" => \A p \in Protos : started[p] => doneChan[p]

\* In English: "Only the goroutines a callback could observe: when Close has
\* returned, no engine loop, muxer goroutine or forwarder runs (the part of
\* NothingOutlivesClose gOuroboros already promises)."
LoopsJoinedAfterClose ==
    user = "returned" =>
        /\ Gone(sd) \/ sd = "exited"
        /\ Gone(fwdMux) /\ Gone(fwdProto) /\ Gone(mr) /\ Gone(mclean)
        /\ \A p \in Protos : Gone(msnd[p]) /\ Gone(rv[p]) /\ Gone(sl[p])

-----------------------------------------------------------------------------
(* Each engine refines the Engine interface. *)

E(p) == INSTANCE Engine WITH
    QCap <- QCap, DoneAfterJoin <- WatcherJoined,
    started <- started[p], stopChan <- stopChan[p], sendQ <- sendQ[p],
    handler <- Handling(p), doneChan <- doneChan[p],
    loopsDone <- stopChan[p] /\ Joined(p),
    reg <- reg[p], connClosed <- mux.done

\* In English: "Every engine starts in the interface's initial state, and
\* every step, seen through each engine's mapping, is an interface step of
\* that engine or leaves its interface objects alone. (TLC checks a
\* quantified box formula written this way, not as a quantified Spec.)"
EngineStep(p) == E(p)!Next \/ UNCHANGED E(p)!evars

EnginesRefine ==
    /\ \A p \in Protos : E(p)!Init
    /\ [][\A p \in Protos : EngineStep(p)]_vars

-----------------------------------------------------------------------------
(* Liveness *)

\* In English: "Close, once called, returns."
CloseReturns == user = "waitConn" ~> user = "returned"

\* In English: "Setup returns."
SetupReturns == <>(setup \in {"ok", "err"})

\* In English: "The application's SendMessage never blocks for ever."
AppReturns == app = "enq" ~> app /= "enq"
=============================================================================
