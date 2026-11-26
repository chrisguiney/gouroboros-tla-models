------------------------- MODULE ConnectionLifecycle -------------------------
(***************************************************************************)
(* One gOuroboros connection end to end, from setupConnection to the end   *)
(* of shutdown, with every way it can be torn down. This is the            *)
(* integration of the per-part models: it keeps only what each part        *)
(* contributes to the lifecycle and refers to that part for the details.   *)
(*                                                                         *)
(* Goroutines (gOuroboros 7cd17437, connection.go and muxer/muxer.go):     *)
(*   setup     setupConnection (:838): handshake Start, muxer.StartOnce    *)
(*             (:1003), select (:1007) on doneChan, a protocol error,      *)
(*             handshakeFinished or the handshake timer; goTracked starts  *)
(*             the protocol-error forwarder (:1035); lockProtocolSetup     *)
(*             (:650) constructs and registers the mini-protocols, or      *)
(*             refuses once doneChan is closed; SetDiffusionMode and       *)
(*             muxer.Start (:1275-1277).                                   *)
(*   read      the muxer's readLoop (muxer.go:1516): it blocks on          *)
(*             startChan until a token arrives; StartOnce's token lets it  *)
(*             read ONE segment, Start's lets it read for good. A read     *)
(*             error calls sendError, which reports once and stops the     *)
(*             muxer unless it is already stopping.                        *)
(*   muxFwd    the muxer-error forwarder (:892): a ConnectionClosedError   *)
(*             while every protocol is idle closes without an error        *)
(*             (allProtocolsIdle, :552); anything else is forwarded with   *)
(*             forwardError (:539), then requestClose.                     *)
(*   protoFwd  the protocol-error forwarder (:1035): forwardError, then    *)
(*             requestClose.                                               *)
(*   shutdown  (:459) waits for doneChan; stopProtocols; muxer.Stop;       *)
(*             joins the protocol loops (callbacks) and both forwarders;   *)
(*             closes the owned errorChan, then connClosedChan.            *)
(*   cb        a mini-protocol callback (any protocol), joined by          *)
(*             shutdown.                                                   *)
(*   user      Close (:311): requestClose, then wait for connClosedChan    *)
(*             and the protocol loops.                                     *)
(*   peer      the remote end: sends its handshake message, then may send  *)
(*             a mini-protocol request, and may close (EOF) at any time.   *)
(*                                                                         *)
(* Facts from the code:                                                    *)
(*   - requestClose closes doneChan once (onceClose).                      *)
(*   - forwardError is select { errorChan <- err; <-doneChan; default }.   *)
(*     Go picks at random among ready cases: once doneChan is closed and   *)
(*     the owned errorChan has room, the error may still be delivered.     *)
(*   - Both forwarders run at once and each forwards at most one error.    *)
(*   - The muxer stops itself on its first error, and stopping the muxer   *)
(*     stops its error reports (sendError returns once doneChan of the     *)
(*     muxer is closed), but an error already queued stays readable.       *)
(*   - A protocol reports errors until it is stopped (SendError, :1115).   *)
(*                                                                         *)
(* What this module leaves to the per-part models:                         *)
(*   - Close during Dial, the muxer join and the late goTracked:           *)
(*     ConnectionTeardown.tla. Close from callbacks, and several closers   *)
(*     at once: ConnectionCloseConcurrent.tla. Setup's select and the      *)
(*     handshake instance: HandshakeTimeout.tla. Which close is an error   *)
(*     (agency, pipelining): ConnectionShutdownAgency.tla, summarised      *)
(*     here as one flag, busy. Errors versus the errorChan close:          *)
(*     ConnectionShutdown.tla. Protocol Start/Stop and their loops:        *)
(*     specs/engine/EngineLifecycle.tla.                                   *)
(*                                                                         *)
(* No specification source: this is gOuroboros's own Go API. The rule     *)
(* that a protocol message is read only after the handshake follows the    *)
(* network specification's handshake mini-protocol (docs/network-spec,     *)
(* section "Handshake mini-protocol": the version is negotiated before any *)
(* other mini-protocol runs).                                              *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    OneCause,   \* TRUE: the error that closes doneChan is the only one
                \* delivered (the fixed design); FALSE: forwardError as in
                \* 7cd17437, best effort from each forwarder.
    GateEarly   \* TRUE: a mutation that opens the muxer gate with Start
                \* instead of StartOnce before the handshake.

VARIABLES
    setup,        \* setupConnection's next step, or "ok" / "err" once it returned
    hsDone,       \* TRUE once the handshake has finished (FinishedFunc ran)
    wire,         \* the segments the peer sent that are not read yet
    peer,         \* "hs" (has not sent its handshake), "ready", or "closed"
    reqSent,      \* TRUE once the peer sent a mini-protocol request
    token,        \* startChan's buffered value: "none", "once" or "full"
    started,      \* readLoop's local started flag
    gateOpens,    \* how many Start tokens readLoop has taken
    registered,   \* TRUE once the mini-protocols are constructed and registered
    reqRead,      \* TRUE once readLoop has read a mini-protocol request
    busy,         \* TRUE while some protocol owes a message (not idle)
    protoErr,     \* protocol errors queued on protoErrorChan
    protoBudget,  \* how many more protocol errors the environment may raise
    muxErr,       \* the muxer's queued error: "none", "eof" or "other"
    muxStopped,   \* TRUE once the muxer's doneChan is closed
    protoStopped, \* TRUE once stopProtocols has signalled every protocol
    doneChan,     \* TRUE once the connection's doneChan is closed
    closer,       \* who closed doneChan first
    errs,         \* how many errors were delivered on ErrorChan
    muxFwd,       \* the muxer-error forwarder's next step
    protoFwd,     \* the protocol-error forwarder's next step
    cb,           \* TRUE while a mini-protocol callback runs
    shutdown,     \* the shutdown goroutine's next step
    user          \* "idle", "waiting" (in Close) or "returned"

\* Literally: "vars is defined as the tuple of all twenty-four variables."
vars == <<setup, hsDone, wire, peer, reqSent, token, started, gateOpens,
          registered, reqRead, busy, protoErr, protoBudget, muxErr, muxStopped,
          protoStopped, doneChan, closer, errs, muxFwd, protoFwd, cb, shutdown,
          user>>

\* The groups below exist only to keep the UNCHANGED lists short.
\* In English: "the variables the peer and the read loop own."
\* Literally: "wireVars is defined as the tuple of wire, peer, reqSent, token,
\*   started, gateOpens and reqRead."
wireVars == <<wire, peer, reqSent, token, started, gateOpens, reqRead>>
\* In English: "the variables that say how the connection is closing."
\* Literally: "closeVars is defined as the tuple of doneChan, closer and errs."
closeVars == <<doneChan, closer, errs>>
\* In English: "the variables of the error sources."
\* Literally: "errVars is defined as the tuple of protoErr, protoBudget and
\*   muxErr."
errVars == <<protoErr, protoBudget, muxErr>>

\* In English: "The closers whose first close carries an error."
\* Literally: "ErrorClosers is defined as the set containing "muxErr" and
\*   "protoErr"."
ErrorClosers == {"muxErr", "protoErr"}

\* In English: "At the start setup has started the handshake and called
\* StartOnce (or Start, under the mutation); the muxer-error forwarder is
\* running; nothing has been sent, raised or closed."
\* Literally: "Init is defined as: setup equals "handshake", and hsDone equals
\*   FALSE, and wire is the empty sequence, and peer equals "hs", and reqSent
\*   equals FALSE, and token equals (if GateEarly then "full" else "once"), and
\*   started equals FALSE, and gateOpens equals 0, and registered, reqRead and
\*   busy equal FALSE, and protoErr equals 0, and protoBudget equals 2, and
\*   muxErr equals "none", and muxStopped, protoStopped and doneChan equal
\*   FALSE, and closer equals "none", and errs equals 0, and muxFwd equals
\*   "select", and protoFwd equals "notStarted", and cb equals FALSE, and
\*   shutdown equals "wait", and user equals "idle"."
Init ==
    /\ setup = "handshake"
    /\ hsDone = FALSE
    /\ wire = <<>>
    /\ peer = "hs"
    /\ reqSent = FALSE
    /\ token = IF GateEarly THEN "full" ELSE "once"
    /\ started = FALSE
    /\ gateOpens = 0
    /\ registered = FALSE
    /\ reqRead = FALSE
    /\ busy = FALSE
    /\ protoErr = 0
    /\ protoBudget = 2
    /\ muxErr = "none"
    /\ muxStopped = FALSE
    /\ protoStopped = FALSE
    /\ doneChan = FALSE
    /\ closer = "none"
    /\ errs = 0
    /\ muxFwd = "select"
    /\ protoFwd = "notStarted"
    /\ cb = FALSE
    /\ shutdown = "wait"
    /\ user = "idle"

\* requestClose as a step's effect on doneChan and closer.
\* In English: "Close doneChan unless it is already closed; the first to close
\* it is recorded as the closer."
\* Literally: "RequestClose(who) is defined as: if doneChan is true then
\*   doneChan and closer are unchanged, else doneChan in the next state equals
\*   TRUE and closer in the next state equals who."
RequestClose(who) ==
    IF doneChan THEN UNCHANGED <<doneChan, closer>>
    ELSE doneChan' = TRUE /\ closer' = who

\* A forwarder delivering its error.
\* In English: "With OneCause, closeWithError closes doneChan and delivers the
\* error in one onceClose, so only the forwarder that begins the shutdown
\* delivers, and doneChan is already closed when it does. Without it
\* (7cd17437), forwardError delivers whenever doneChan is open; once doneChan
\* is closed Go may still pick the send case, or the doneChan case; the
\* forwarder's requestClose is a later step (FwdClose)."
\* Literally: "ForwardAndClose(who) is defined as: if OneCause then (if
\*   doneChan is not true then errs in the next state equals errs plus 1, and
\*   doneChan in the next state equals TRUE, and closer in the next state
\*   equals who, else doneChan, closer and errs are unchanged), else ((doneChan
\*   is not true and errs in the next state equals errs plus 1) or (doneChan
\*   is true and errs in the next state is a member of the set containing errs
\*   and errs plus 1)) and doneChan and closer are unchanged."
ForwardAndClose(who) ==
    IF OneCause
        THEN IF ~doneChan
                 THEN errs' = errs + 1 /\ doneChan' = TRUE /\ closer' = who
                 ELSE UNCHANGED <<doneChan, closer, errs>>
        ELSE /\ \/ ~doneChan /\ errs' = errs + 1
                \/ doneChan /\ errs' \in {errs, errs + 1}
             /\ UNCHANGED <<doneChan, closer>>

\* In English: "Every protocol is idle: they exist, and none owes a message."
\* allProtocolsIdle returns false until protocolsReady is set.
\* Literally: "AllIdle is defined as: registered is true and busy is not true."
AllIdle == registered /\ ~busy

-----------------------------------------------------------------------------
(* The peer and the environment. None of these is fair: the peer may stay   *)
(* silent, and nothing has to fail.                                         *)

\* In English: "The peer sends its handshake message."
\* Literally: "PeerHandshake is defined as: peer equals "hs", and wire in the
\*   next state equals wire with "hs" appended, and peer in the next state
\*   equals "ready", and the other variables are unchanged."
PeerHandshake ==
    /\ peer = "hs"
    /\ wire' = Append(wire, "hs")
    /\ peer' = "ready"
    /\ UNCHANGED <<setup, hsDone, reqSent, token, started, gateOpens,
                   registered, reqRead, busy, errVars, muxStopped,
                   protoStopped, closeVars, muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "Once its handshake is done the peer may send one request for
\* a mini-protocol on this side (a chain-sync request, say). It does not wait
\* for this side's FinishedFunc."
\* Literally: "PeerRequest is defined as: peer equals "ready", and reqSent is
\*   not true, and wire in the next state equals wire with "req" appended, and
\*   reqSent in the next state equals TRUE, and the other variables are
\*   unchanged."
PeerRequest ==
    /\ peer = "ready" /\ ~reqSent
    /\ wire' = Append(wire, "req")
    /\ reqSent' = TRUE
    /\ UNCHANGED <<setup, hsDone, peer, token, started, gateOpens, registered,
                   reqRead, busy, errVars, muxStopped, protoStopped, closeVars,
                   muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "The peer closes its end; readLoop sees EOF after the segments
\* already sent."
\* Literally: "PeerClose is defined as: peer does not equal "closed", and peer
\*   in the next state equals "closed", and the other variables are
\*   unchanged."
PeerClose ==
    /\ peer /= "closed"
    /\ peer' = "closed"
    /\ UNCHANGED <<setup, hsDone, wire, reqSent, token, started, gateOpens,
                   registered, reqRead, busy, errVars, muxStopped,
                   protoStopped, closeVars, muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "A protocol that is not stopped reports an error: a handshake
\* refusal before the handshake finishes, or later a protocol violation or a
\* keep-alive (or any state) timeout. SendError stops that protocol, so the
\* environment raises at most two."
\* Literally: "ProtocolError is defined as: protoStopped is not true, and
\*   protoBudget is greater than 0, and (hsDone is not true or registered is
\*   true), and protoErr in the next state equals protoErr plus 1, and
\*   protoBudget in the next state equals protoBudget minus 1, and the other
\*   variables are unchanged."
ProtocolError ==
    /\ ~protoStopped /\ protoBudget > 0
    /\ (~hsDone \/ registered)
    /\ protoErr' = protoErr + 1
    /\ protoBudget' = protoBudget - 1
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, muxErr,
                   muxStopped, protoStopped, closeVars, muxFwd, protoFwd, cb,
                   shutdown, user>>

\* In English: "A running protocol comes to owe a message (a client sent a
\* request and awaits the reply), or stops owing one."
\* Literally: "Agency is defined as: registered is true, and protoStopped is
\*   not true, and busy in the next state equals not busy, and the other
\*   variables are unchanged."
Agency ==
    /\ registered /\ ~protoStopped
    /\ busy' = ~busy
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, errVars, muxStopped,
                   protoStopped, closeVars, muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "A running protocol calls one of its callbacks."
\* Literally: "CallbackStart is defined as: registered is true, and
\*   protoStopped is not true, and cb is not true, and cb in the next state
\*   equals TRUE, and the other variables are unchanged."
CallbackStart ==
    /\ registered /\ ~protoStopped /\ ~cb
    /\ cb' = TRUE
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, closeVars, muxFwd, protoFwd,
                   shutdown, user>>

\* In English: "The callback returns (it watches its protocol's StopChan)."
\* Literally: "CallbackEnd is defined as: cb is true, and cb in the next state
\*   equals FALSE, and the other variables are unchanged."
CallbackEnd ==
    /\ cb
    /\ cb' = FALSE
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, closeVars, muxFwd, protoFwd,
                   shutdown, user>>

\* In English: "The user calls Close once, from any goroutine."
\* Literally: "UserClose is defined as: user equals "idle", and user in the
\*   next state equals "waiting", and RequestClose("user"), and the other
\*   variables are unchanged."
UserClose ==
    /\ user = "idle"
    /\ user' = "waiting"
    /\ RequestClose("user")
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, errs, muxFwd, protoFwd, cb,
                   shutdown>>

\* In English: "Close returns once shutdown has finished (connClosedChan) and
\* every protocol loop, and so every callback, has returned."
\* Literally: "UserReturn is defined as: user equals "waiting", and shutdown
\*   equals "done", and cb is not true, and user in the next state equals
\*   "returned", and the other variables are unchanged."
UserReturn ==
    /\ user = "waiting" /\ shutdown = "done" /\ ~cb
    /\ user' = "returned"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, closeVars, muxFwd, protoFwd, cb,
                   shutdown>>

-----------------------------------------------------------------------------
(* The muxer's read loop. *)

\* In English: "readLoop reads the next segment, if it may: it is started, or
\* a token waits in startChan, which it takes (a "once" token leaves it
\* blocked again after this segment). The handshake segment finishes the
\* handshake. A request reaches its protocol if that protocol is registered,
\* and makes it owe a reply; otherwise the muxer reports an unknown protocol
\* and stops."
\* Literally: "ReadSegment is defined as: muxStopped is not true, and wire is
\*   not the empty sequence, and (started is true or token does not equal
\*   "none"), and started in the next state equals (started is true or token
\*   equals "full"), and token in the next state equals (if started then
\*   token else "none"), and gateOpens in the next state equals gateOpens plus
\*   (1 if started is not true and token equals "full", else 0), and wire in
\*   the next state equals the tail of wire, and: if the head of wire is "hs"
\*   then hsDone in the next state equals TRUE and reqRead, busy, muxErr and
\*   muxStopped are unchanged; else reqRead in the next state equals TRUE, and
\*   if registered then busy in the next state equals TRUE and hsDone, muxErr
\*   and muxStopped are unchanged, else muxErr in the next state equals
\*   "other" and muxStopped in the next state equals TRUE and hsDone and busy
\*   are unchanged; and the other variables are unchanged."
ReadSegment ==
    /\ ~muxStopped /\ wire /= <<>>
    /\ (started \/ token /= "none")
    /\ started' = (started \/ token = "full")
    /\ token' = IF started THEN token ELSE "none"
    /\ gateOpens' = gateOpens + (IF ~started /\ token = "full" THEN 1 ELSE 0)
    /\ wire' = Tail(wire)
    /\ IF Head(wire) = "hs"
           THEN /\ hsDone' = TRUE
                /\ UNCHANGED <<reqRead, busy, muxErr, muxStopped>>
           ELSE /\ reqRead' = TRUE
                /\ IF registered
                       THEN busy' = TRUE /\ UNCHANGED <<hsDone, muxErr, muxStopped>>
                       ELSE /\ muxErr' = "other" /\ muxStopped' = TRUE
                            /\ UNCHANGED <<hsDone, busy>>
    /\ UNCHANGED <<setup, peer, reqSent, registered, protoErr, protoBudget,
                   protoStopped, closeVars, muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "With nothing left to read from a closed peer, readLoop's read
\* returns EOF: sendError queues a ConnectionClosedError and stops the muxer."
\* Literally: "ReadEOF is defined as: muxStopped is not true, and wire is the
\*   empty sequence, and peer equals "closed", and (started is true or token
\*   does not equal "none"), and muxErr in the next state equals "eof", and
\*   muxStopped in the next state equals TRUE, and the other variables are
\*   unchanged."
ReadEOF ==
    /\ ~muxStopped /\ wire = <<>> /\ peer = "closed"
    /\ (started \/ token /= "none")
    /\ muxErr' = "eof"
    /\ muxStopped' = TRUE
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, protoErr,
                   protoBudget, protoStopped, closeVars, muxFwd, protoFwd, cb,
                   shutdown, user>>

-----------------------------------------------------------------------------
(* setupConnection *)

\* In English: "Setup's select: doneChan closed (return an error); a protocol
\* error, which here is the handshake's (Close, return it); the handshake
\* finished (carry on); or the handshake timer (Close, return an error). Go
\* picks any ready case; the timer is always ready eventually."
\* Literally: "SetupSelect is defined as: setup equals "handshake", and either
\*   (doneChan is true and setup in the next state equals "err" and protoErr,
\*   doneChan and closer are unchanged), or (protoErr is greater than 0 and
\*   protoErr in the next state equals protoErr minus 1 and setup in the next
\*   state equals "closing" and RequestClose("setup")), or (hsDone is true and
\*   setup in the next state equals "fwd" and protoErr, doneChan and closer
\*   are unchanged), or (setup in the next state equals "closing" and
\*   RequestClose("setup") and protoErr is unchanged); and the other
\*   variables are unchanged."
SetupSelect ==
    /\ setup = "handshake"
    /\ \/ doneChan /\ setup' = "err" /\ UNCHANGED <<protoErr, doneChan, closer>>
       \/ /\ protoErr > 0 /\ protoErr' = protoErr - 1
          /\ setup' = "closing" /\ RequestClose("setup")
       \/ hsDone /\ setup' = "fwd" /\ UNCHANGED <<protoErr, doneChan, closer>>
       \/ setup' = "closing" /\ RequestClose("setup") /\ UNCHANGED protoErr
    /\ UNCHANGED <<hsDone, wireVars, registered, busy, protoBudget, muxErr,
                   muxStopped, protoStopped, errs, muxFwd, protoFwd, cb,
                   shutdown, user>>

\* In English: "Setup's own Close returns once shutdown has finished; setup
\* then returns the handshake's error or the timeout."
\* Literally: "SetupClosed is defined as: setup equals "closing", and
\*   shutdown equals "done", and setup in the next state equals "err", and the
\*   other variables are unchanged."
SetupClosed ==
    /\ setup = "closing" /\ shutdown = "done"
    /\ setup' = "err"
    /\ UNCHANGED <<hsDone, wireVars, registered, busy, errVars, muxStopped,
                   protoStopped, closeVars, muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "goTracked starts the protocol-error forwarder unless doneChan
\* is closed (ConnectionTeardown.tla shows the trackMu fence makes this one
\* step)."
\* Literally: "SetupStartFwd is defined as: setup equals "fwd", and protoFwd
\*   in the next state equals (if doneChan then "notStarted" else "select"),
\*   and setup in the next state equals "lock", and the other variables are
\*   unchanged."
SetupStartFwd ==
    /\ setup = "fwd"
    /\ protoFwd' = IF doneChan THEN "notStarted" ELSE "select"
    /\ setup' = "lock"
    /\ UNCHANGED <<hsDone, wireVars, registered, busy, errVars, muxStopped,
                   protoStopped, closeVars, muxFwd, cb, shutdown, user>>

\* In English: "lockProtocolSetup refuses once doneChan is closed (setup
\* returns an error); otherwise the mini-protocols are constructed for the
\* negotiated version and diffusion mode, and the servers are registered
\* with the muxer (EnsureRegistered)."
\* Literally: "SetupLock is defined as: setup equals "lock", and either
\*   (doneChan is true and setup in the next state equals "err" and
\*   registered is unchanged) or (doneChan is not true and registered in the
\*   next state equals TRUE and setup in the next state equals "start"); and
\*   the other variables are unchanged."
SetupLock ==
    /\ setup = "lock"
    /\ \/ doneChan /\ setup' = "err" /\ UNCHANGED registered
       \/ ~doneChan /\ registered' = TRUE /\ setup' = "start"
    /\ UNCHANGED <<hsDone, wireVars, busy, errVars, muxStopped, protoStopped,
                   closeVars, muxFwd, protoFwd, cb, shutdown, user>>

\* In English: "SetDiffusionMode, then muxer.Start: a non-blocking send of
\* "full" on startChan, dropped if a token is already buffered. Setup then
\* returns nil."
\* Literally: "SetupStart is defined as: setup equals "start", and token in
\*   the next state equals (if token equals "none" then "full" else token),
\*   and setup in the next state equals "ok", and the other variables are
\*   unchanged."
SetupStart ==
    /\ setup = "start"
    /\ token' = IF token = "none" THEN "full" ELSE token
    /\ setup' = "ok"
    /\ UNCHANGED <<hsDone, wire, peer, reqSent, started, gateOpens, reqRead,
                   registered, busy, errVars, muxStopped, protoStopped,
                   closeVars, muxFwd, protoFwd, cb, shutdown, user>>

-----------------------------------------------------------------------------
(* The two error forwarders. *)

\* In English: "The muxer-error forwarder's select: doneChan closed (return),
\* or an error from the muxer. Go picks either when both are ready."
\* Literally: "MuxFwdSelect is defined as: muxFwd equals "select", and either
\*   (doneChan is true and muxFwd in the next state equals "exit" and muxErr
\*   is unchanged) or (muxErr does not equal "none" and muxFwd in the next
\*   state equals (if muxErr equals "eof" then "gotEOF" else "gotErr") and
\*   muxErr in the next state equals "none"); and the other variables are
\*   unchanged."
MuxFwdSelect ==
    /\ muxFwd = "select"
    /\ \/ doneChan /\ muxFwd' = "exit" /\ UNCHANGED muxErr
       \/ /\ muxErr /= "none"
          /\ muxFwd' = IF muxErr = "eof" THEN "gotEOF" ELSE "gotErr"
          /\ muxErr' = "none"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, protoErr,
                   protoBudget, muxStopped, protoStopped, closeVars, protoFwd,
                   cb, shutdown, user>>

\* In English: "A peer EOF while every protocol is idle closes without an
\* error; any other muxer error is forwarded, then requestClose."
\* Literally: "MuxFwdForward is defined as: muxFwd is a member of the set
\*   containing "gotEOF" and "gotErr", and if muxFwd equals "gotEOF" and
\*   AllIdle then (RequestClose("clean") and errs is unchanged and muxFwd in
\*   the next state equals "exit"), else (ForwardAndClose("muxErr") and muxFwd
\*   in the next state equals (if OneCause then "exit" else "close")); and the
\*   other variables are unchanged."
MuxFwdForward ==
    /\ muxFwd \in {"gotEOF", "gotErr"}
    /\ IF muxFwd = "gotEOF" /\ AllIdle
           THEN RequestClose("clean") /\ UNCHANGED errs /\ muxFwd' = "exit"
           ELSE /\ ForwardAndClose("muxErr")
                /\ muxFwd' = IF OneCause THEN "exit" ELSE "close"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, protoFwd, cb, shutdown, user>>

\* In English: "The protocol-error forwarder's select: doneChan closed
\* (return) or a queued protocol error."
\* Literally: "ProtoFwdSelect is defined as: protoFwd equals "select", and
\*   either (doneChan is true and protoFwd in the next state equals "exit" and
\*   protoErr is unchanged) or (protoErr is greater than 0 and protoErr in the
\*   next state equals protoErr minus 1 and protoFwd in the next state equals
\*   "gotErr"); and the other variables are unchanged."
ProtoFwdSelect ==
    /\ protoFwd = "select"
    /\ \/ doneChan /\ protoFwd' = "exit" /\ UNCHANGED protoErr
       \/ protoErr > 0 /\ protoErr' = protoErr - 1 /\ protoFwd' = "gotErr"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, protoBudget,
                   muxErr, muxStopped, protoStopped, closeVars, muxFwd, cb,
                   shutdown, user>>

\* In English: "Forward the protocol error, then requestClose."
\* Literally: "ProtoFwdForward is defined as: protoFwd equals "gotErr", and
\*   ForwardAndClose("protoErr"), and protoFwd in the next state equals (if
\*   OneCause then "exit" else "close"), and the other variables are
\*   unchanged."
ProtoFwdForward ==
    /\ protoFwd = "gotErr"
    /\ ForwardAndClose("protoErr")
    /\ protoFwd' = IF OneCause THEN "exit" ELSE "close"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, muxFwd, cb, shutdown, user>>

\* In English: "7cd17437 only: after forwardError, the forwarder's
\* requestClose."
\* Literally: "FwdClose is defined as: either (muxFwd equals "close" and
\*   RequestClose("muxErr") and muxFwd in the next state equals "exit" and
\*   protoFwd is unchanged) or (protoFwd equals "close" and
\*   RequestClose("protoErr") and protoFwd in the next state equals "exit" and
\*   muxFwd is unchanged); and the other variables are unchanged."
FwdClose ==
    /\ \/ muxFwd = "close" /\ RequestClose("muxErr")
          /\ muxFwd' = "exit" /\ UNCHANGED protoFwd
       \/ protoFwd = "close" /\ RequestClose("protoErr")
          /\ protoFwd' = "exit" /\ UNCHANGED muxFwd
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, errs, cb, shutdown, user>>

-----------------------------------------------------------------------------
(* shutdown *)

\* In English: "shutdown starts once doneChan is closed, and signals every
\* protocol to stop."
\* Literally: "ShutdownStopProtocols is defined as: shutdown equals "wait",
\*   and doneChan is true, and protoStopped in the next state equals TRUE, and
\*   shutdown in the next state equals "stopMuxer", and the other variables
\*   are unchanged."
ShutdownStopProtocols ==
    /\ shutdown = "wait" /\ doneChan
    /\ protoStopped' = TRUE
    /\ shutdown' = "stopMuxer"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, closeVars, muxFwd, protoFwd, cb, user>>

\* In English: "muxer.Stop: the muxer stops reading and reporting."
\* Literally: "ShutdownStopMuxer is defined as: shutdown equals "stopMuxer",
\*   and muxStopped in the next state equals TRUE, and shutdown in the next
\*   state equals "join", and the other variables are unchanged."
ShutdownStopMuxer ==
    /\ shutdown = "stopMuxer"
    /\ muxStopped' = TRUE
    /\ shutdown' = "join"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   protoStopped, closeVars, muxFwd, protoFwd, cb, user>>

\* In English: "WaitProtocolLoops and waitGroup.Wait: every callback and both
\* forwarders have returned. Then the owned errorChan and connClosedChan are
\* closed."
\* Literally: "ShutdownJoin is defined as: shutdown equals "join", and cb is
\*   not true, and muxFwd equals "exit", and protoFwd is a member of the set
\*   containing "notStarted" and "exit", and shutdown in the next state equals
\*   "done", and the other variables are unchanged."
ShutdownJoin ==
    /\ shutdown = "join" /\ ~cb
    /\ muxFwd = "exit" /\ protoFwd \in {"notStarted", "exit"}
    /\ shutdown' = "done"
    /\ UNCHANGED <<setup, hsDone, wireVars, registered, busy, errVars,
                   muxStopped, protoStopped, closeVars, muxFwd, protoFwd, cb,
                   user>>

\* In English: "Nothing is left to do: shutdown finished, setup returned and
\* nobody waits in Close."
\* Literally: "Finished is defined as: shutdown equals "done", and setup is a
\*   member of the set containing "ok" and "err", and user does not equal
\*   "waiting", and all variables are unchanged."
Finished ==
    /\ shutdown = "done" /\ setup \in {"ok", "err"} /\ user /= "waiting"
    /\ UNCHANGED vars

\* In English: "The steps the code itself takes, which must keep happening."
\* Literally: "Internal is defined as: ReadSegment or ReadEOF or SetupSelect or
\*   SetupClosed or SetupStartFwd or SetupLock or SetupStart or MuxFwdSelect or
\*   MuxFwdForward or ProtoFwdSelect or ProtoFwdForward or FwdClose or
\*   ShutdownStopProtocols or ShutdownStopMuxer or ShutdownJoin or CallbackEnd
\*   or UserReturn."
Internal ==
    \/ ReadSegment \/ ReadEOF
    \/ SetupSelect \/ SetupClosed \/ SetupStartFwd \/ SetupLock \/ SetupStart
    \/ MuxFwdSelect \/ MuxFwdForward \/ ProtoFwdSelect \/ ProtoFwdForward
    \/ FwdClose
    \/ ShutdownStopProtocols \/ ShutdownStopMuxer \/ ShutdownJoin
    \/ CallbackEnd \/ UserReturn

\* Literally: "Next is defined as: Internal or PeerHandshake or PeerRequest or
\*   PeerClose or ProtocolError or Agency or CallbackStart or UserClose or
\*   Finished."
Next ==
    \/ Internal
    \/ PeerHandshake \/ PeerRequest \/ PeerClose \/ ProtocolError \/ Agency
    \/ CallbackStart \/ UserClose \/ Finished

\* In English: "Every internal step that stays possible eventually happens;
\* in particular setup's select cannot wait forever, because the handshake
\* timer fires."
\* Literally: "Spec is defined as: Init, and always [Next] on vars, and weak
\*   fairness on vars of each internal step."
Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(ReadSegment) /\ WF_vars(ReadEOF)
    /\ WF_vars(SetupSelect) /\ WF_vars(SetupClosed) /\ WF_vars(SetupStartFwd)
    /\ WF_vars(SetupLock) /\ WF_vars(SetupStart)
    /\ WF_vars(MuxFwdSelect) /\ WF_vars(MuxFwdForward)
    /\ WF_vars(ProtoFwdSelect) /\ WF_vars(ProtoFwdForward) /\ WF_vars(FwdClose)
    /\ WF_vars(ShutdownStopProtocols) /\ WF_vars(ShutdownStopMuxer)
    /\ WF_vars(ShutdownJoin) /\ WF_vars(CallbackEnd) /\ WF_vars(UserReturn)

-----------------------------------------------------------------------------
(* Properties *)

\* In English: "No mini-protocol message is read before the handshake has
\* finished and the mini-protocols are registered."
\* Literally: "NoMessageBeforeHandshake is defined as: reqRead implies (hsDone
\*   and registered)."
NoMessageBeforeHandshake == reqRead => hsDone /\ registered

\* In English: "The muxer gate opens at most once, and Start is never lost: a
\* setup that returned nil with the muxer still running has opened the gate
\* or left the full token for readLoop."
\* Literally: "GateOpensOnce is defined as: gateOpens is at most 1, and
\*   (setup equals "ok" and muxStopped is not true) implies (started is true
\*   or token equals "full")."
GateOpensOnce ==
    /\ gateOpens <= 1
    /\ setup = "ok" /\ ~muxStopped => started \/ token = "full"

\* In English: "Setup returns nil only after the handshake, with the
\* mini-protocols registered; a setup that returned an error had doneChan
\* closed, so the connection is torn down."
\* Literally: "SetupResult is defined as: (setup equals "ok" implies hsDone
\*   and registered) and (setup equals "err" implies doneChan)."
SetupResult ==
    /\ setup = "ok" => hsDone /\ registered
    /\ setup = "err" => doneChan

\* In English: "An error reaches ErrorChan only once doneChan is closed, so a
\* consumer woken by it knows the connection's shutdown has begun: every
\* callback's ConnectionDoneChan is closed."
\* Literally: "DoneBeforeError is defined as: errs is greater than 0 implies
\*   doneChan."
DoneBeforeError == errs > 0 => doneChan

\* In English: "No teardown puts more than one error on ErrorChan."
\* Literally: "AtMostOneError is defined as: errs is at most 1."
AtMostOneError == errs <= 1

\* In English: "Once shutdown has finished, ErrorChan carried exactly one
\* error when the first close came from a forwarded error, and none when it
\* came from Close, from setup (which returns its error to the caller), or
\* from a peer EOF with every protocol idle."
\* Literally: "OneErrorPerCause is defined as: shutdown equals "done" implies
\*   errs equals (1 if closer is a member of ErrorClosers, else 0)."
OneErrorPerCause ==
    shutdown = "done" => errs = IF closer \in ErrorClosers THEN 1 ELSE 0

\* In English: "A teardown begun by Close, by setup, or by a clean peer EOF
\* never puts an error on ErrorChan, even when an error races it."
\* Literally: "NoErrorAfterQuietClose is defined as: closer is a member of
\*   the set containing "user", "setup" and "clean" implies errs equals 0."
NoErrorAfterQuietClose == closer \in {"user", "setup", "clean"} => errs = 0

\* In English: "Once Close has returned, no callback runs, both forwarders
\* have returned and the muxer is stopped."
\* Literally: "CloseJoins is defined as: user equals "returned" implies (cb is
\*   not true, and muxFwd equals "exit", and protoFwd is a member of the set
\*   containing "notStarted" and "exit", and muxStopped)."
CloseJoins ==
    user = "returned" =>
        /\ ~cb /\ muxFwd = "exit" /\ protoFwd \in {"notStarted", "exit"}
        /\ muxStopped

\* In English: "Setup always returns."
\* Literally: "SetupReturns is defined as: eventually setup is a member of the
\*   set containing "ok" and "err"."
SetupReturns == <>(setup \in {"ok", "err"})

\* In English: "Every teardown, whatever started it, finishes."
\* Literally: "TeardownFinishes is defined as: doneChan leads to shutdown
\*   equals "done"."
TeardownFinishes == doneChan ~> (shutdown = "done")

\* In English: "Every Close returns."
\* Literally: "CloseReturns is defined as: user equals "waiting" leads to
\*   user equals "returned"."
CloseReturns == (user = "waiting") ~> (user = "returned")
=============================================================================
