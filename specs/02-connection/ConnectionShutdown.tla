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

\* Literally: "vars is defined as the tuple of all fifteen variables."
vars == <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr, muxErr,
          protocols, setup, muxFwd, protoFwd, shutdown, user, panicked>>

\* In English: "At the start, nothing is closed, the muxer-error forwarder is
\* running (counted by the waitGroup), the handshake protocol runs, setup is
\* waiting for it, and the user has not called Close."
\* Literally: "Init is defined as: doneChan equals "open", and errorChan equals
\*   "open", and connClosed equals FALSE, and wg equals 1, and hsDone equals
\*   FALSE, and hsFailed equals FALSE, and protoErr equals FALSE, and muxErr
\*   equals FALSE, and protocols equals "handshake", and setup equals "wait",
\*   and muxFwd equals "select", and protoFwd equals "notStarted", and shutdown
\*   equals "wait", and user equals "idle", and panicked equals FALSE."
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
\* Literally: "ForwardError is defined as: if errorChan equals "closed", then
\*   (panicked in the next state equals TRUE, or doneChan equals "closed" and
\*   panicked is unchanged), else panicked is unchanged."
ForwardError ==
    IF errorChan = "closed"
        THEN \/ panicked' = TRUE                            \* the send case: panic
             \/ doneChan = "closed" /\ UNCHANGED panicked   \* the doneChan case
        ELSE UNCHANGED panicked

-----------------------------------------------------------------------------
(* Things that can go wrong at any time before they are stopped. *)

\* In English: "The handshake completes, unless it has already failed: a
\* protocol that reports an error stops itself (SendError calls Stop)."
\* Literally: "HandshakeDone is defined as: hsDone is not true, and
\*   (LateProtocolErrors is true or hsFailed is not true), and protocols equals
\*   "handshake", and hsDone in the next state equals TRUE, and the other
\*   fourteen variables are unchanged."
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
\* Literally: "ProtocolError is defined as: (LateProtocolErrors is true and
\*   protocols does not equal "stopped", or protocols equals "handshake" and
\*   hsDone is not true, or protocols equals "running"), and protoErr is not
\*   true, and protoErr in the next state equals TRUE, and hsFailed in the next
\*   state equals (hsFailed is true or protocols equals "handshake"), and
\*   doneChan, errorChan, connClosed, wg, hsDone, muxErr, protocols, setup,
\*   muxFwd, protoFwd, shutdown, user and panicked are unchanged."
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
\* Literally: "MuxerError is defined as: shutdown is a member of the set
\*   containing "wait", "stopProtocols" and "stopMuxer", and muxErr is not
\*   true, and muxErr in the next state equals TRUE, and the other fourteen
\*   variables are unchanged."
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
\* Literally: "SetupSelect is defined as: setup equals "wait", and either
\*   (doneChan equals "closed", and setup in the next state equals "done", and
\*   doneChan and protoErr are unchanged), or (protoErr is true, and protoErr
\*   in the next state equals FALSE, and doneChan in the next state equals
\*   "closed", and setup in the next state equals "done"), or (hsDone is true,
\*   and setup in the next state equals "startFwd", and doneChan and protoErr
\*   are unchanged); and errorChan, connClosed, wg, hsDone, hsFailed, muxErr,
\*   protocols, muxFwd, protoFwd, shutdown, user and panicked are unchanged."
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
\* Literally: "SetupStartFwd is defined as: setup equals "startFwd", and wg in
\*   the next state equals wg plus 1, and protoFwd in the next state equals
\*   "select", and setup in the next state equals "lock", and the other twelve
\*   variables are unchanged."
SetupStartFwd ==
    /\ setup = "startFwd"
    /\ wg' = wg + 1
    /\ protoFwd' = "select"
    /\ setup' = "lock"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, hsDone, hsFailed, protoErr, muxErr,
                   protocols, muxFwd, shutdown, user, panicked>>

\* In English: "lockProtocolSetup: if doneChan is closed, give up; otherwise
\* start the mini-protocols."
\* Literally: "SetupLock is defined as: setup equals "lock", and protocols in
\*   the next state equals (if doneChan equals "open" and protocols does not
\*   equal "stopped", then "running", else protocols), and setup in the next
\*   state equals "done", and the other thirteen variables are unchanged."
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
\* Literally: "MuxFwdStep is defined as: muxFwd equals "select", and either
\*   (doneChan equals "closed", and muxErr, doneChan and panicked are
\*   unchanged), or (muxErr is true, and muxErr in the next state equals FALSE,
\*   and ForwardError, and doneChan in the next state equals "closed"); and
\*   muxFwd in the next state equals "exited", and wg in the next state equals
\*   wg minus 1, and errorChan, connClosed, hsDone, hsFailed, protoErr,
\*   protocols, setup, protoFwd, shutdown and user are unchanged."
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
\* Literally: "ProtoFwdStep is defined as: protoFwd equals "select", and either
\*   (doneChan equals "closed", and protoErr, doneChan and panicked are
\*   unchanged), or (protoErr is true, and protoErr in the next state equals
\*   FALSE, and ForwardError, and doneChan in the next state equals "closed");
\*   and protoFwd in the next state equals "exited", and wg in the next state
\*   equals wg minus 1, and errorChan, connClosed, hsDone, hsFailed, muxErr,
\*   protocols, setup, muxFwd, shutdown and user are unchanged."
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
\* Literally: "ShutdownBegin is defined as: shutdown equals "wait", and
\*   doneChan equals "closed", and shutdown in the next state equals
\*   "stopProtocols", and the other fourteen variables are unchanged."
ShutdownBegin ==
    /\ shutdown = "wait" /\ doneChan = "closed"
    /\ shutdown' = "stopProtocols"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "stopProtocols, then muxer.Stop."
\* Literally: "ShutdownStopProtocols is defined as: shutdown equals
\*   "stopProtocols", and protocols in the next state equals "stopped", and
\*   shutdown in the next state equals "stopMuxer", and the other thirteen
\*   variables are unchanged."
ShutdownStopProtocols ==
    /\ shutdown = "stopProtocols"
    /\ protocols' = "stopped"
    /\ shutdown' = "stopMuxer"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "muxer.Stop returns, and shutdown goes on to wait for the
\* waitGroup."
\* Literally: "ShutdownStopMuxer is defined as: shutdown equals "stopMuxer",
\*   and shutdown in the next state equals "waitGroup", and the other fourteen
\*   variables are unchanged."
ShutdownStopMuxer ==
    /\ shutdown = "stopMuxer"
    /\ shutdown' = "waitGroup"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "waitGroup.Wait returns once the counter is zero; then the
\* owned errorChan is closed, then connClosedChan."
\* Literally: "ShutdownWait is defined as: shutdown equals "waitGroup", and wg
\*   equals 0, and shutdown in the next state equals "closeErrorChan", and the
\*   other fourteen variables are unchanged."
ShutdownWait ==
    /\ shutdown = "waitGroup" /\ wg = 0
    /\ shutdown' = "closeErrorChan"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "Shutdown closes errorChan."
\* Literally: "ShutdownCloseErrorChan is defined as: shutdown equals
\*   "closeErrorChan", and errorChan in the next state equals "closed", and
\*   shutdown in the next state equals "closeConn", and the other thirteen
\*   variables are unchanged."
ShutdownCloseErrorChan ==
    /\ shutdown = "closeErrorChan"
    /\ errorChan' = "closed"
    /\ shutdown' = "closeConn"
    /\ UNCHANGED <<doneChan, connClosed, wg, hsDone, hsFailed, protoErr, muxErr,
                   protocols, setup, muxFwd, protoFwd, user, panicked>>

\* In English: "Shutdown closes connClosedChan, and is done."
\* Literally: "ShutdownCloseConn is defined as: shutdown equals "closeConn",
\*   and connClosed in the next state equals TRUE, and shutdown in the next
\*   state equals "done", and the other thirteen variables are unchanged."
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
\* Literally: "UserClose is defined as: user equals "idle", and setup equals
\*   "done", and doneChan in the next state equals "closed", and user in the
\*   next state equals "waiting", and the other thirteen variables are
\*   unchanged."
UserClose ==
    /\ user = "idle" /\ setup = "done"
    /\ doneChan' = "closed"
    /\ user' = "waiting"
    /\ UNCHANGED <<errorChan, connClosed, wg, hsDone, hsFailed, protoErr, muxErr,
                   protocols, setup, muxFwd, protoFwd, shutdown, panicked>>

\* In English: "Once connClosedChan is closed, the user's Close returns."
\* Literally: "UserCloseReturns is defined as: user equals "waiting", and
\*   connClosed is true, and user in the next state equals "returned", and the
\*   other fourteen variables are unchanged."
UserCloseReturns ==
    /\ user = "waiting" /\ connClosed
    /\ user' = "returned"
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wg, hsDone, hsFailed, protoErr,
                   muxErr, protocols, setup, muxFwd, protoFwd, shutdown, panicked>>

\* In English: "Nothing is left to do: shutdown finished, every goroutine
\* exited, and the user (if it called Close) got control back. Or setup and
\* the forwarders are idle on a live connection nobody closed."
\* Literally: "Finished is defined as: either (shutdown equals "done", and
\*   setup equals "done", and muxFwd equals "exited", and protoFwd is a member
\*   of the set containing "notStarted" and "exited", and user does not equal
\*   "waiting"), or (doneChan equals "open", and setup equals "done", and user
\*   equals "idle"); and vars is unchanged."
Finished ==
    /\ \/ /\ shutdown = "done" /\ setup = "done"
          /\ muxFwd = "exited" /\ protoFwd \in {"notStarted", "exited"}
          /\ user /= "waiting"
       \/ /\ doneChan = "open" /\ setup = "done" /\ user = "idle"
    /\ UNCHANGED vars

\* In English: "A step is any one step of any goroutine, an error being
\* reported, or staying finished."
\* Literally: "Next is defined as: HandshakeDone, or ProtocolError, or
\*   MuxerError, or SetupSelect, or SetupStartFwd, or SetupLock, or MuxFwdStep,
\*   or ProtoFwdStep, or ShutdownBegin, or ShutdownStopProtocols, or
\*   ShutdownStopMuxer, or ShutdownWait, or ShutdownCloseErrorChan, or
\*   ShutdownCloseConn, or UserClose, or UserCloseReturns, or Finished."
Next ==
    \/ HandshakeDone \/ ProtocolError \/ MuxerError
    \/ SetupSelect \/ SetupStartFwd \/ SetupLock
    \/ MuxFwdStep \/ ProtoFwdStep
    \/ ShutdownBegin \/ ShutdownStopProtocols \/ ShutdownStopMuxer
    \/ ShutdownWait \/ ShutdownCloseErrorChan \/ ShutdownCloseConn
    \/ UserClose \/ UserCloseReturns
    \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Nothing ever sends on a closed channel."
\* Literally: "NoPanic is defined as: panicked is not true."
NoPanic == ~panicked

\* In English: "Close only returns after shutdown has finished."
\* Literally: "CloseWaitsForShutdown is defined as: if user equals "returned",
\*   then shutdown equals "done"."
CloseWaitsForShutdown == user = "returned" => shutdown = "done"
=============================================================================
