--------------------------- MODULE HandshakeTimeout ---------------------------
(***************************************************************************)
(* The connection-wide handshake timeout of setupConnection, and the       *)
(* handshake protocol's FinishedFunc racing it, one Go step per action.    *)
(* ConnectionTeardown.tla checks the order of shutdown while Dial runs;    *)
(* this module adds the handshake instance itself: when setupConnection    *)
(* publishes c.handshake relative to a shutdown that reads it, which       *)
(* select case setupConnection returns through, and whether the handshake  *)
(* loops, which run FinishedFunc, have returned by then.                   *)
(*                                                                         *)
(* Goroutines (gOuroboros 7cd17437, connection.go):                        *)
(*   setup  setupConnection (:838): publish c.handshake = handshake.New    *)
(*          with no lock (:997); Start it (:999-1001), which registers     *)
(*          with the muxer and starts its loops unless the muxer has       *)
(*          stopped or closed its loop pool; select (:1007) on doneChan    *)
(*          (return), a protocol error (Close, return), handshakeFinished  *)
(*          (go on) or the handshake timer (Close, return);                *)
(*          lockProtocolSetup (:650), which refuses once doneChan is       *)
(*          closed; start the mini-protocols.                              *)
(*   user   Close from another goroutine while Dial runs (optional).       *)
(*   sd     shutdown (:459): stopProtocols reads c.handshake under         *)
(*          protocolMu and signals its Stop; muxer.Stop and                *)
(*          CloseProtocolLoops; WaitProtocolLoops; close(connClosedChan).  *)
(*   hs     the handshake protocol's loops: FinishedFunc runs once on its  *)
(*          receive loop, writing handshakeVersion (read by                *)
(*          ProtocolVersion) and closing handshakeFinishedChan; or the     *)
(*          protocol reports an error; the loops return once the protocol  *)
(*          or the muxer stops.                                            *)
(*   Close  (:311) closes doneChan once (onceClose) and waits for          *)
(*          connClosedChan and for the protocol loops.                     *)
(*                                                                         *)
(* No specification source: this is gOuroboros's own Go API. The timer is  *)
(* abstract: it may fire at any step while setup waits, which covers any   *)
(* duration. Go rules used: select picks at random among ready cases; two  *)
(* accesses to one variable, one a write, race unless a lock or channel    *)
(* orders them (the Go memory model).                                      *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    ConcurrentClose,  \* TRUE: the user may call Close while Dial runs
    HandshakeError,   \* TRUE: the handshake protocol may report an error
    Fix,              \* a subset of {"publishLocked", "joinOnDone"}:
                      \* "publishLocked": publish c.handshake under
                      \*   protocolMu after checking doneChan, as
                      \*   lockProtocolSetup does for the mini-protocols,
                      \*   and give up if it is closed;
                      \* "joinOnDone": on the doneChan case, Close too, so
                      \*   setup returns only once the teardown has joined
                      \*   the handshake loops, as the other failure cases do.
    Mutation          \* a subset of {"noCloseOnTimeout", "noSetupGuard"}:
                      \* "noCloseOnTimeout": the timer case returns without
                      \*   Close;
                      \* "noSetupGuard": lockProtocolSetup does not check
                      \*   doneChan.

ASSUME Fix \subseteq {"publishLocked", "joinOnDone"}
ASSUME Mutation \subseteq {"noCloseOnTimeout", "noSetupGuard"}
ASSUME ConcurrentClose \in BOOLEAN /\ HandshakeError \in BOOLEAN

VARIABLES
    setup,          \* setup's next step: "publish", "start", "wait",
                    \*   "closeWait" (Close, then wait), "lockSetup",
                    \*   "returned"
    result,         \* what setup returned: "none", "ok", "shutdown",
                    \*   "error", "timeout", "refused"
    hsCreated,      \* c.handshake is set
    hsStopped,      \* Stop was signalled on the handshake instance
    hsLoops,        \* the handshake loops: "none", "running", "exited",
                    \*   "refused" (Start found the muxer gone)
    finished,       \* FinishedFunc ran (handshakeFinishedChan closed)
    finishedLate,   \* FinishedFunc ran after setup returned a failure
    protoErr,       \* an error is queued on protoErrorChan
    timerFired,     \* the handshake timer fired
    doneClosed,     \* doneChan is closed
    userClosed,     \* the user's concurrent Close has run
    sd,             \* shutdown's next step: "wait", "stopProtocols",
                    \*   "muxer", "waitLoops", "done"
    sdRuns,         \* how many times shutdown's body has started
    sdReadHs,       \* stopProtocols has read c.handshake
    muxerStopped,   \* muxer.Stop and CloseProtocolLoops have run
    racyWrite,      \* setup wrote c.handshake while shutdown could read it
                    \*   with nothing ordering the two
    miniStarted,    \* the mini-protocols were started
    miniAfterDone,  \* they were started after doneChan closed
    startAfterDone  \* the handshake was started after shutdown had read
                    \*   the protocol list without it, so nothing stops it

vars == <<setup, result, hsCreated, hsStopped, hsLoops, finished,
          finishedLate, protoErr, timerFired, doneClosed, userClosed, sd,
          sdRuns, sdReadHs, muxerStopped, racyWrite, miniStarted,
          miniAfterDone, startAfterDone>>

\* In English: "Setup has published doneChan and created the muxer; nothing
\* else has happened."
Init ==
    /\ setup = "publish"
    /\ result = "none"
    /\ hsCreated = FALSE /\ hsStopped = FALSE /\ hsLoops = "none"
    /\ finished = FALSE /\ finishedLate = FALSE
    /\ protoErr = FALSE /\ timerFired = FALSE
    /\ doneClosed = FALSE /\ userClosed = FALSE
    /\ sd = "wait" /\ sdRuns = 0 /\ sdReadHs = FALSE
    /\ muxerStopped = FALSE
    /\ racyWrite = FALSE
    /\ miniStarted = FALSE /\ miniAfterDone = FALSE /\ startAfterDone = FALSE

\* In English: "setup has returned with a failure."
Failed == result \in {"shutdown", "error", "timeout", "refused"}

-----------------------------------------------------------------------------
(* setupConnection. *)

\* In English: "Publish c.handshake. With no lock, a write after doneChan
\* closed races shutdown's read. With the fix, the write happens under
\* protocolMu after checking doneChan, and a closed doneChan makes setup
\* give up."
SetupPublish ==
    /\ setup = "publish"
    /\ IF "publishLocked" \in Fix /\ doneClosed
          THEN /\ setup' = "returned" /\ result' = "shutdown"
               /\ UNCHANGED <<hsCreated, racyWrite>>
          ELSE /\ hsCreated' = TRUE
               /\ setup' = "start"
               /\ racyWrite' = (racyWrite \/
                                ("publishLocked" \notin Fix /\ doneClosed))
               /\ UNCHANGED result
    /\ UNCHANGED <<hsStopped, hsLoops, finished, finishedLate, protoErr,
                   timerFired, doneClosed, userClosed, sd, sdRuns, sdReadHs,
                   muxerStopped, miniStarted, miniAfterDone, startAfterDone>>

\* In English: "Start the handshake protocol: its loops run, unless it was
\* already stopped or the muxer is gone, in which case Start reports an
\* error (could not register) and stops it."
SetupStart ==
    /\ setup = "start"
    /\ setup' = "wait"
    /\ startAfterDone' = (startAfterDone \/ (sdReadHs /\ ~hsStopped))
    /\ IF hsStopped
          THEN UNCHANGED <<hsLoops, protoErr, hsStopped>>
          ELSE IF muxerStopped
               THEN /\ hsLoops' = "refused"
                    /\ protoErr' = TRUE            \* SendError
                    /\ hsStopped' = TRUE
               ELSE /\ hsLoops' = "running"
                    /\ UNCHANGED <<protoErr, hsStopped>>
    /\ UNCHANGED <<result, hsCreated, finished, finishedLate, timerFired,
                   doneClosed, userClosed, sd, sdRuns, sdReadHs, muxerStopped,
                   racyWrite, miniStarted, miniAfterDone>>

\* In English: "The select: a closed doneChan returns (or, with the fix,
\* closes and waits first); a protocol error closes and returns; a finished
\* handshake goes on; the timer closes and returns. Go picks at random
\* among the ready cases."
SetupWait ==
    /\ setup = "wait"
    /\ \/ /\ doneClosed
          /\ IF "joinOnDone" \in Fix
                THEN setup' = "closeWait" /\ result' = "shutdown"
                ELSE setup' = "returned" /\ result' = "shutdown"
          /\ UNCHANGED doneClosed
       \/ /\ protoErr
          /\ setup' = "closeWait" /\ result' = "error"
          /\ doneClosed' = TRUE
       \/ /\ finished
          /\ setup' = "lockSetup"
          /\ UNCHANGED <<result, doneClosed>>
       \/ /\ timerFired
          /\ result' = "timeout"
          /\ IF "noCloseOnTimeout" \in Mutation
                THEN setup' = "returned" /\ UNCHANGED doneClosed
                ELSE setup' = "closeWait" /\ doneClosed' = TRUE
    /\ UNCHANGED <<hsCreated, hsStopped, hsLoops, finished, finishedLate,
                   protoErr, timerFired, userClosed, sd, sdRuns, sdReadHs,
                   muxerStopped, racyWrite, miniStarted, miniAfterDone,
                   startAfterDone>>

\* In English: "Close's wait: connClosedChan is closed and the protocol
\* loops have returned; then setup returns its failure."
SetupCloseWait ==
    /\ setup = "closeWait"
    /\ sd = "done" /\ hsLoops # "running"
    /\ setup' = "returned"
    /\ UNCHANGED <<result, hsCreated, hsStopped, hsLoops, finished,
                   finishedLate, protoErr, timerFired, doneClosed, userClosed,
                   sd, sdRuns, sdReadHs, muxerStopped, racyWrite, miniStarted,
                   miniAfterDone, startAfterDone>>

\* In English: "lockProtocolSetup refuses once doneChan is closed;
\* otherwise the mini-protocols start."
SetupLock ==
    /\ setup = "lockSetup"
    /\ setup' = "returned"
    /\ IF doneClosed /\ "noSetupGuard" \notin Mutation
          THEN /\ result' = "refused"
               /\ UNCHANGED <<miniStarted, miniAfterDone>>
          ELSE /\ result' = "ok"
               /\ miniStarted' = TRUE
               /\ miniAfterDone' = (miniAfterDone \/ doneClosed)
    /\ UNCHANGED <<hsCreated, hsStopped, hsLoops, finished, finishedLate,
                   protoErr, timerFired, doneClosed, userClosed, sd, sdRuns,
                   sdReadHs, muxerStopped, racyWrite, startAfterDone>>

\* In English: "The handshake timer fires while setup waits."
TimerFires ==
    /\ setup = "wait" /\ ~timerFired
    /\ timerFired' = TRUE
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, hsLoops, finished,
                   finishedLate, protoErr, doneClosed, userClosed, sd, sdRuns,
                   sdReadHs, muxerStopped, racyWrite, miniStarted,
                   miniAfterDone, startAfterDone>>

-----------------------------------------------------------------------------
(* The handshake protocol's loops. *)

\* In English: "FinishedFunc runs on the receive loop: it writes the
\* negotiated version and closes handshakeFinishedChan."
Finish ==
    /\ hsLoops = "running" /\ ~finished /\ ~hsStopped
    /\ finished' = TRUE
    /\ finishedLate' = (finishedLate \/ (setup = "returned" /\ Failed))
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, hsLoops, protoErr,
                   timerFired, doneClosed, userClosed, sd, sdRuns, sdReadHs,
                   muxerStopped, racyWrite, miniStarted, miniAfterDone,
                   startAfterDone>>

\* In English: "The handshake protocol reports an error (refused, or
\* undecodable) and stops itself."
HsError ==
    /\ HandshakeError /\ hsLoops = "running" /\ ~finished /\ ~hsStopped
    /\ protoErr' = TRUE
    /\ hsStopped' = TRUE
    /\ UNCHANGED <<setup, result, hsCreated, hsLoops, finished, finishedLate,
                   timerFired, doneClosed, userClosed, sd, sdRuns, sdReadHs,
                   muxerStopped, racyWrite, miniStarted, miniAfterDone,
                   startAfterDone>>

\* In English: "The loops return once the protocol or the muxer stops."
HsExit ==
    /\ hsLoops = "running" /\ (hsStopped \/ muxerStopped)
    /\ hsLoops' = "exited"
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, finished, finishedLate,
                   protoErr, timerFired, doneClosed, userClosed, sd, sdRuns,
                   sdReadHs, muxerStopped, racyWrite, miniStarted,
                   miniAfterDone, startAfterDone>>

-----------------------------------------------------------------------------
(* Close and shutdown. *)

\* In English: "The user calls Close from another goroutine: doneChan
\* closes (once)."
UserClose ==
    /\ ConcurrentClose /\ ~userClosed
    /\ userClosed' = TRUE
    /\ doneClosed' = TRUE
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, hsLoops, finished,
                   finishedLate, protoErr, timerFired, sd, sdRuns, sdReadHs,
                   muxerStopped, racyWrite, miniStarted, miniAfterDone,
                   startAfterDone>>

\* In English: "The shutdown goroutine sees doneChan closed."
SdBegin ==
    /\ sd = "wait" /\ doneClosed
    /\ sd' = "stopProtocols"
    /\ sdRuns' = sdRuns + 1
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, hsLoops, finished,
                   finishedLate, protoErr, timerFired, doneClosed, userClosed,
                   sdReadHs, muxerStopped, racyWrite, miniStarted,
                   miniAfterDone, startAfterDone>>

\* In English: "stopProtocols reads c.handshake under protocolMu and
\* signals Stop on it, if there is one."
SdStopProtocols ==
    /\ sd = "stopProtocols"
    /\ sd' = "muxer"
    /\ sdReadHs' = TRUE
    /\ hsStopped' = (hsStopped \/ hsCreated)
    /\ UNCHANGED <<setup, result, hsCreated, hsLoops, finished, finishedLate,
                   protoErr, timerFired, doneClosed, userClosed, sdRuns,
                   muxerStopped, racyWrite, miniStarted, miniAfterDone,
                   startAfterDone>>

\* In English: "muxer.Stop, then CloseProtocolLoops: no loop starts after."
SdMuxer ==
    /\ sd = "muxer"
    /\ sd' = "waitLoops"
    /\ muxerStopped' = TRUE
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, hsLoops, finished,
                   finishedLate, protoErr, timerFired, doneClosed, userClosed,
                   sdRuns, sdReadHs, racyWrite, miniStarted, miniAfterDone,
                   startAfterDone>>

\* In English: "WaitProtocolLoops, then close(connClosedChan)."
SdWaitLoops ==
    /\ sd = "waitLoops" /\ hsLoops # "running"
    /\ sd' = "done"
    /\ UNCHANGED <<setup, result, hsCreated, hsStopped, hsLoops, finished,
                   finishedLate, protoErr, timerFired, doneClosed, userClosed,
                   sdRuns, sdReadHs, muxerStopped, racyWrite, miniStarted,
                   miniAfterDone, startAfterDone>>

\* In English: "Setup has returned and nothing else can move."
Quiet ==
    /\ setup = "returned"
    /\ ~ENABLED (SdBegin \/ SdStopProtocols \/ SdMuxer \/ SdWaitLoops
                 \/ Finish \/ HsError \/ HsExit \/ UserClose)
    /\ UNCHANGED vars

Next ==
    \/ SetupPublish \/ SetupStart \/ SetupWait \/ SetupCloseWait \/ SetupLock
    \/ TimerFires \/ Finish \/ HsError \/ HsExit
    \/ UserClose \/ SdBegin \/ SdStopProtocols \/ SdMuxer \/ SdWaitLoops
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every variable holds a value of the right kind."
TypeOK ==
    /\ setup \in {"publish", "start", "wait", "closeWait", "lockSetup",
                  "returned"}
    /\ result \in {"none", "ok", "shutdown", "error", "timeout", "refused"}
    /\ hsLoops \in {"none", "running", "exited", "refused"}
    /\ sd \in {"wait", "stopProtocols", "muxer", "waitLoops", "done"}

\* In English: "The connection is torn down at most once."
TornDownOnce == sdRuns <= 1

\* In English: "A handshake timeout tears the connection down."
TimeoutTearsDown == result = "timeout" => doneClosed

\* In English: "No mini-protocol starts once the connection is closing, so
\* none starts after a handshake timeout."
NoProtocolStartAfterTeardown == ~miniAfterDone /\ (result = "timeout" => ~miniStarted)

\* In English: "c.handshake is never written while a shutdown may be reading
\* it with nothing ordering the two (a data race)."
NoRacyHandshakeWrite == ~racyWrite

\* In English: "The handshake protocol is never started once shutdown has
\* read the protocol list without it: every started instance is one the
\* teardown stops."
NoHandshakeStartAfterTeardown == ~startAfterDone

\* In English: "When Dial fails, the handshake loops have returned: no
\* FinishedFunc writes handshakeVersion after it, while the caller may read
\* ProtocolVersion."
NoFinishedAfterFailedDial == ~finishedLate
=============================================================================
