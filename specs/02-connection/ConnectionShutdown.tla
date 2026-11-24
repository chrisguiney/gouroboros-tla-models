------------------------- MODULE ConnectionShutdown -------------------------
(***************************************************************************)
(* Model 02, part 4: how a gOuroboros connection carries errors and shuts  *)
(* down, while it is still being set up.                                   *)
(*                                                                         *)
(* Each step is one line or one select of connection.go, so TLC tries      *)
(* every way the goroutines can interleave:                                *)
(*                                                                         *)
(*   setup     setupConnection: wait for the handshake (or doneChan, or a  *)
(*             protocol error), start the protocol-error forwarder with    *)
(*             waitGroup.Go, then lockProtocolSetup, which refuses once    *)
(*             doneChan is closed.                                         *)
(*   muxFwd    started with waitGroup.Go at setup: waits for doneChan or a *)
(*             muxer error; forwards the error, then requestClose.         *)
(*   protoFwd  started with waitGroup.Go after the handshake: waits for    *)
(*             doneChan or a protocol error; forwards it, then            *)
(*             requestClose.                                               *)
(*   shutdown  waits for doneChan; stopProtocols; muxer.Stop;              *)
(*             waitGroup.Wait; close(errorChan) when the connection owns   *)
(*             it; close(connClosedChan).                                  *)
(*   user      calls Close (requestClose, then waits for connClosedChan).  *)
(*                                                                         *)
(* Facts from the code:                                                    *)
(*   - requestClose closes doneChan once.                                  *)
(*   - forwardError is select { errorChan <- err; <-doneChan; default }.   *)
(*     Go picks at random among ready cases, and a send on a CLOSED        *)
(*     channel is always ready - and panics.                               *)
(*   - errorChan is created and owned by the connection unless the caller  *)
(*     passed one (WithErrorChan); this model is the owned case.           *)
(*   - A protocol's SendError does nothing once the protocol is stopped.   *)
(*   - waitGroup.Wait returns once its counter is zero; a later Go starts  *)
(*     a goroutine Wait no longer waits for.                               *)
(*                                                                         *)
(* No specification source: this is gOuroboros's own Go API, and the       *)
(* property is Go's rule that sending on a closed channel panics.          *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    LateProtocolErrors  \* FALSE: errors only where the code can raise them.
                        \* TRUE: a protocol may report an error at any time, even
                        \* after the handshake finished or failed - not true of
                        \* gOuroboros today; it shows what the shutdown order
                        \* relies on.

VARIABLES
    doneChan,       \* "open" or "closed"
    errorChan,      \* "open" or "closed"
    connClosed,     \* TRUE once connClosedChan is closed
    wg,             \* the waitGroup counter
    hsDone,         \* TRUE once the handshake has finished
    hsFailed,       \* TRUE once the handshake protocol has reported an error
    protoErr,       \* TRUE while a protocol error waits on protoErrorChan
    muxErr,         \* TRUE while a muxer error waits on the muxer's error channel
    protocols,      \* "handshake", "running", or "stopped"
    setup,          \* setup's next step
    muxFwd,         \* the muxer-error forwarder's next step
    protoFwd,       \* the protocol-error forwarder's next step
    shutdown,       \* the shutdown goroutine's next step
    user,           \* the user's next step
    panicked        \* TRUE if anything sent on a closed channel

vars == <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr, muxErr,
          protocols, setup, muxFwd, protoFwd, shutdown, user, panicked>>

\* In English: "At the start, nothing is closed, the muxer-error forwarder is
\* running (counted by the waitGroup), the handshake protocol runs, setup is
\* waiting for it, and the user has not called Close."
Init ==
    /\ doneChan = "open"
    /\ errorChan = "open"
    /\ connClosed = FALSE
    /\ wg = 1                       \* muxFwd
    /\ hsDone = FALSE
    /\ hsFailed = FALSE
    /\ protoErr = FALSE
    /\ muxErr = FALSE
    /\ protocols = "handshake"
    /\ setup = "wait"
    /\ muxFwd = "select"
    /\ protoFwd = "notStarted"
    /\ shutdown = "wait"
    /\ user = "idle"
    /\ panicked = FALSE

\* forwardError, as a single step. In English: "If errorChan is closed, Go
\* may pick the send case, which panics; it may also pick doneChan if that
\* is closed. If errorChan is open, the error is delivered or dropped, and
\* nothing goes wrong."
ForwardError ==
    IF errorChan = "closed"
        THEN \/ panicked' = TRUE                            \* the send case: panic
             \/ doneChan = "closed" /\ UNCHANGED panicked   \* the doneChan case
        ELSE UNCHANGED panicked

-----------------------------------------------------------------------------
(* Things that can go wrong at any time before they are stopped. *)

\* In English: "The handshake completes, unless it has already failed: a
\* protocol that reports an error stops itself (SendError calls Stop)."
HandshakeDone ==
    /\ ~hsDone /\ (LateProtocolErrors \/ ~hsFailed) /\ protocols = "handshake"
    /\ hsDone' = TRUE
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsFailed, protoErr, muxErr,
                   protocols, setup, muxFwd, protoFwd, shutdown, user, panicked>>

\* In English: "A protocol that can still fail reports an error: the
\* handshake before it finishes, or the mini-protocols once they run."
\* Nothing else can: the handshake server sends its accept and waits for
\* the write before FinishedFunc closes handshakeFinishedChan
\* (protocol/handshake/server.go), a protocol in its Done state reports no
\* read errors, and the mini-protocols start only in lockProtocolSetup.
ProtocolError ==
    /\ \/ LateProtocolErrors /\ protocols /= "stopped"
       \/ protocols = "handshake" /\ ~hsDone
       \/ protocols = "running"
    /\ ~protoErr
    /\ protoErr' = TRUE
    /\ hsFailed' = (hsFailed \/ protocols = "handshake")
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, muxErr,
                   protocols, setup, muxFwd, protoFwd, shutdown, user, panicked>>

\* In English: "The muxer, while running, reports an error (for example the
\* peer reset the connection)."
MuxerError ==
    /\ shutdown \in {"wait", "stopProtocols", "stopMuxer"}  \* the muxer is not stopped yet
    /\ ~muxErr
    /\ muxErr' = TRUE
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   protocols, setup, muxFwd, protoFwd, shutdown, user, panicked>>

-----------------------------------------------------------------------------
(* setupConnection *)

\* In English: "Setup waits on a select with three ready-able cases:
\* doneChan closed (return an error), a protocol error (Close and return),
\* or the handshake finished (carry on). Go picks any ready one."
SetupSelect ==
    /\ setup = "wait"
    /\ \/ /\ doneChan = "closed"                    \* shutting down: return
          /\ setup' = "done"
          /\ UNCHANGED <<doneChan, protoErr>>
       \/ /\ protoErr                               \* a protocol error: Close
          /\ protoErr' = FALSE
          /\ doneChan' = "closed"
          /\ setup' = "done"
       \/ /\ hsDone                                 \* handshake done: carry on
          /\ setup' = "startFwd"
          /\ UNCHANGED <<doneChan, protoErr>>
    /\ UNCHANGED <<errorChan, connClosed, wg, hsDone, hsFailed, muxErr, protocols,
                   muxFwd, protoFwd, shutdown, user, panicked>>

\* In English: "waitGroup.Go starts the protocol-error forwarder."
SetupStartFwd ==
    /\ setup = "startFwd"
    /\ wg' = wg + 1
    /\ protoFwd' = "select"
    /\ setup' = "lock"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, hsDone, hsFailed, protoErr, muxErr,
                   protocols, muxFwd, shutdown, user, panicked>>

\* In English: "lockProtocolSetup: if doneChan is closed, give up; otherwise
\* start the mini-protocols."
SetupLock ==
    /\ setup = "lock"
    /\ protocols' = IF doneChan = "open" /\ protocols /= "stopped"
                       THEN "running" ELSE protocols
    /\ setup' = "done"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, muxFwd, protoFwd, shutdown, user, panicked>>

-----------------------------------------------------------------------------
(* The forwarders. *)

\* In English: "The muxer-error forwarder returns once doneChan is closed;
\* or it takes a muxer error, forwards it, and closes the connection."
MuxFwdStep ==
    /\ muxFwd = "select"
    /\ \/ /\ doneChan = "closed"
          /\ UNCHANGED <<muxErr, doneChan, panicked>>
       \/ /\ muxErr
          /\ muxErr' = FALSE
          /\ ForwardError
          /\ doneChan' = "closed"
    /\ muxFwd' = "exited"
    /\ wg' = wg - 1
    /\ UNCHANGED <<errorChan, connClosed, hsDone, hsFailed, protoErr, protocols, setup,
                   protoFwd, shutdown, user>>

\* In English: "The protocol-error forwarder, likewise, for protocol errors."
ProtoFwdStep ==
    /\ protoFwd = "select"
    /\ \/ /\ doneChan = "closed"
          /\ UNCHANGED <<protoErr, doneChan, panicked>>
       \/ /\ protoErr
          /\ protoErr' = FALSE
          /\ ForwardError
          /\ doneChan' = "closed"
    /\ protoFwd' = "exited"
    /\ wg' = wg - 1
    /\ UNCHANGED <<errorChan, connClosed, hsDone, hsFailed, muxErr, protocols, setup,
                   muxFwd, shutdown, user>>

-----------------------------------------------------------------------------
(* The shutdown goroutine. *)

\* In English: "When doneChan closes, shutdown begins."
ShutdownBegin ==
    /\ shutdown = "wait" /\ doneChan = "closed"
    /\ shutdown' = "stopProtocols"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "stopProtocols, then muxer.Stop."
ShutdownStopProtocols ==
    /\ shutdown = "stopProtocols"
    /\ protocols' = "stopped"
    /\ shutdown' = "stopMuxer"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, setup, muxFwd, protoFwd, user, panicked>>

ShutdownStopMuxer ==
    /\ shutdown = "stopMuxer"
    /\ shutdown' = "waitGroup"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "waitGroup.Wait returns once the counter is zero; then the
\* owned errorChan is closed, then connClosedChan."
ShutdownWait ==
    /\ shutdown = "waitGroup" /\ wg = 0
    /\ shutdown' = "closeErrorChan"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, user, panicked>>

ShutdownCloseErrorChan ==
    /\ shutdown = "closeErrorChan"
    /\ errorChan' = "closed"
    /\ shutdown' = "closeConn"
    /\ UNCHANGED <<doneChan, connClosed, wg, hsDone, hsFailed, protoErr, muxErr,
                   protocols, setup, muxFwd, protoFwd, user, panicked>>

ShutdownCloseConn ==
    /\ shutdown = "closeConn"
    /\ connClosed' = TRUE
    /\ shutdown' = "done"
    /\ UNCHANGED <<doneChan, errorChan, wg, hsDone, hsFailed, protoErr, muxErr,
                   protocols, setup, muxFwd, protoFwd, user, panicked>>

-----------------------------------------------------------------------------
(* The user. *)

\* In English: "Once New has returned (setup is done), the user may call
\* Close: it closes doneChan, then waits for connClosedChan."
UserClose ==
    /\ user = "idle" /\ setup = "done"
    /\ doneChan' = "closed"
    /\ user' = "waiting"
    /\ UNCHANGED <<errorChan, connClosed, wg, hsDone, hsFailed, protoErr, muxErr,
                   protocols, setup, muxFwd, protoFwd, shutdown, panicked>>

UserCloseReturns ==
    /\ user = "waiting" /\ connClosed
    /\ user' = "returned"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, shutdown, panicked>>

\* In English: "Nothing is left to do: shutdown finished, every goroutine
\* exited, and the user (if it called Close) got control back. Or setup and
\* the forwarders are idle on a live connection nobody closed."
Finished ==
    /\ \/ /\ shutdown = "done" /\ setup = "done"
          /\ muxFwd = "exited" /\ protoFwd \in {"notStarted", "exited"}
          /\ user /= "waiting"
       \/ /\ doneChan = "open" /\ setup = "done" /\ user = "idle"
    /\ UNCHANGED vars

Next ==
    \/ HandshakeDone \/ ProtocolError \/ MuxerError
    \/ SetupSelect \/ SetupStartFwd \/ SetupLock
    \/ MuxFwdStep \/ ProtoFwdStep
    \/ ShutdownBegin \/ ShutdownStopProtocols \/ ShutdownStopMuxer
    \/ ShutdownWait \/ ShutdownCloseErrorChan \/ ShutdownCloseConn
    \/ UserClose \/ UserCloseReturns
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Nothing ever sends on a closed channel."
NoPanic == ~panicked

\* In English: "Close only returns after shutdown has finished."
CloseWaitsForShutdown == user = "returned" => shutdown = "done"
=============================================================================
