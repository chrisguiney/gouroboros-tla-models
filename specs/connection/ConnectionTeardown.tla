-------------------------- MODULE ConnectionTeardown --------------------------
(***************************************************************************)
(* Model 02, part 5: a connection torn down while Dial is still setting it *)
(* up, one Go primitive per step. ConnectionShutdown.tla checks the order  *)
(* of shutdown after setup; this module adds what comes before it: the     *)
(* creation of doneChan and of the muxer, a Close from another goroutine,  *)
(* the WaitGroup at Go's own rules, and goroutines that outlive Close.     *)
(*                                                                         *)
(* Goroutines (gOuroboros 5c4f31c1, connection.go):                        *)
(*   setup  setupConnection (:670): make doneChan and start the shutdown   *)
(*          goroutine (:684-688); create the muxer (:701), which starts    *)
(*          its cleanup goroutine (muxer/muxer.go:1062); waitGroup.Go the  *)
(*          muxer-error forwarder (:704); start the handshake and          *)
(*          StartOnce (:809-815); select (:819) on doneChan, a protocol    *)
(*          error, handshakeFinishedChan or the handshake timer;           *)
(*          waitGroup.Go the protocol-error forwarder (:844);              *)
(*          lockProtocolSetup (:491), which refuses once doneChan is       *)
(*          closed; start the mini-protocols; muxer.Start (:1086).         *)
(*   user   Close (:258): nothing if doneChan is still nil (:259);         *)
(*          otherwise close doneChan once (:272) and wait for              *)
(*          connClosedChan (:265).                                         *)
(*   sd     the shutdown goroutine: <-doneChan; stopProtocols (:430);      *)
(*          muxer.Stop if c.muxer is not nil (:382); waitGroup.Wait        *)
(*          (:386); close(errorChan) (:390); close(connClosedChan) (:394). *)
(*   mf, pf the muxer-error and protocol-error forwarders (:704, :844):    *)
(*          return on doneChan, or forwardError (:400) and requestClose.   *)
(*   mc     the muxer cleanup goroutine: <-muxer doneChan; conn.Close.     *)
(*   hs     the handshake protocol: finishes once, or reports an error     *)
(*          through SendError (protocol/protocol.go:926), which checks     *)
(*          stopChan and then sends: two steps.                            *)
(*   cb     one mini-protocol callback running on that protocol's loop.    *)
(*                                                                         *)
(* Go rules used: a send on a closed channel panics, and select picks at   *)
(* random among ready cases; WaitGroup.Add with a positive delta while the *)
(* counter is zero must happen before Wait (sync.WaitGroup doc), which a   *)
(* mutex held across the doneChan check and the Add guarantees, as the     *)
(* muxer's fenceRegistrations does (muxer/muxer.go:1340).                  *)
(*                                                                         *)
(* No specification source: this is gOuroboros's own Go API.               *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    ConcurrentClose,    \* TRUE: the user may call Close while Dial runs
    LateHandshakeError, \* TRUE: the finished handshake protocol may still
                        \* report an error (bytes a hostile peer sends after
                        \* the accept fail to decode) until it is stopped
    CallbackCloseKinds, \* how the mini-protocol callback may close its own
                        \* connection, a subset of {"own", "plain"}:
                        \* "own": CloseContext with the context its
                        \*   protocol instance gave it (carrying that
                        \*   instance as marker); "plain": Close.
    UserMarker,         \* the user's Close: "none" (Close), or "foreign"
                        \* (CloseContext called from another connection's
                        \* callback, with that callback's context)
    Fix                 \* a subset of {"fence", "muxerGuard", "join",
                        \* "closeEarly", "anyMarker"}:
                        \* "fence": start a tracked goroutine only under a
                        \*   mutex, after checking doneChan; shutdown takes
                        \*   the mutex before Wait.
                        \* "muxerGuard": create the muxer under a mutex
                        \*   after checking doneChan (closing the raw conn
                        \*   instead when it is closed); shutdown reads
                        \*   c.muxer under the same mutex. Both steps are
                        \*   single steps here because the mutex makes them
                        \*   atomic with respect to each other.
                        \* "join": shutdown waits for the protocol loops
                        \*   before it closes errorChan and connClosedChan,
                        \*   skipping a loop whose callback is itself in
                        \*   Close; every Close then also waits for every
                        \*   loop but its own caller's (the reference's
                        \*   withJobPool, network-mux Mux.hs:280-287).
                        \* "anyMarker" (mutation, with "join"): any marker
                        \*   excuses this connection's callback loop, instead
                        \*   of only a marker that is one of its instances
                        \*   (compared by identity).
                        \* "closeEarly": a Close before doneChan exists
                        \*   closes the conn and makes setup give up.

ASSUME Fix \subseteq {"fence", "muxerGuard", "join", "closeEarly", "anyMarker"}
ASSUME CallbackCloseKinds \subseteq {"own", "plain"}
ASSUME UserMarker \in {"none", "foreign"}

VARIABLES
    pc,         \* next step of "setup", "user", "sd", "mf", "pf", "mc"
    doneChan,   \* "nil", "open" or "closed"
    errorChan,  \* "open" or "closed"
    connClosed, \* connClosedChan closed
    conn,       \* the net.Conn: "open" or "closed"
    muxer,      \* "none", "running" or "stopped"
    wg,         \* the waitGroup counter
    waitBegan,  \* shutdown has reached waitGroup.Wait
    lateAdd,    \* an Add happened after Wait began (Go's rule broken)
    wgMu,       \* holder of the fence mutex, or "none"
    hs,         \* handshake protocol: "none", "running", "finished", "stopped"
    hsErr,      \* its SendError: "idle", "checked" (passed the stopChan
                \* check), "sent"
    protoErr,   \* an error waits in protoErrorChan
    muxErr,     \* an error waits in the muxer's errorChan
    muxErrUsed, \* the muxer has reported its one error
    proto,      \* the mini-protocols: "none", "constructed", "running", "stopped"
    cb,         \* a mini-protocol callback: "idle", "running", "done"
    panicked,   \* something sent on a closed channel
    gaveUp,     \* setup's handshake timer fired
    hsLate,     \* the handshake finished after setup gave up
    loopCb,     \* the protocol loop that runs the callback:
                \* "none", "running" or "exited"
    loopOther,  \* the protocol's other loops, as one
    cbClose,    \* the callback's own Close: "none", "waiting", "returned"
    exempt,     \* the callback's goroutine is excused from the shutdown join
    closeReq,   \* a Close came before doneChan existed
    userExcept  \* the user's Close skips waiting for the callback's loop

chans == <<doneChan, errorChan, connClosed, conn, muxer>>
wgv   == <<wg, waitBegan, lateAdd, wgMu>>
prot  == <<hs, hsErr, protoErr, muxErr, muxErrUsed, proto, cb>>
flags == <<panicked, gaveUp, hsLate>>
joinv == <<loopCb, loopOther, cbClose, exempt, closeReq, userExcept>>
\* Literally: "vars is defined as the tuple of pc, chans, wgv, prot,
\*   flags and joinv."
vars  == <<pc, chans, wgv, prot, flags, joinv>>

\* Literally: "Procs is defined as the set containing "setup", "user",
\*   "sd", "mf", "pf" and "mc"."
Procs == {"setup", "user", "sd", "mf", "pf", "mc"}

\* In English: "Dial has begun; nothing else has."
\* Literally: "Init is defined as: pc maps "setup" to "mkDone", "user" to
\*   "idle" and every other goroutine to "notStarted", and doneChan equals
\*   "nil", and errorChan and conn equal "open", and connClosed equals
\*   FALSE, and muxer equals "none", and wg equals 0, and waitBegan and
\*   lateAdd equal FALSE, and wgMu equals "none", and hs equals "none", and
\*   hsErr equals "idle", and protoErr, muxErr and muxErrUsed equal FALSE,
\*   and proto equals "none", and cb equals "idle", and panicked, gaveUp
\*   and hsLate equal FALSE, and loopCb and loopOther equal "none", and
\*   cbClose equals "none", and exempt, closeReq and userExcept equal
\*   FALSE."
Init ==
    /\ pc = [p \in Procs |-> CASE p = "setup" -> "mkDone"
                               [] p = "user"  -> "idle"
                               [] OTHER       -> "notStarted"]
    /\ doneChan = "nil" /\ errorChan = "open" /\ connClosed = FALSE
    /\ conn = "open" /\ muxer = "none"
    /\ wg = 0 /\ waitBegan = FALSE /\ lateAdd = FALSE /\ wgMu = "none"
    /\ hs = "none" /\ hsErr = "idle" /\ protoErr = FALSE
    /\ muxErr = FALSE /\ muxErrUsed = FALSE
    /\ proto = "none" /\ cb = "idle"
    /\ panicked = FALSE /\ gaveUp = FALSE /\ hsLate = FALSE
    /\ loopCb = "none" /\ loopOther = "none" /\ cbClose = "none"
    /\ exempt = FALSE /\ closeReq = FALSE /\ userExcept = FALSE

\* In English: "Goroutine p moves to step s."
\* Literally: "Goto of p and s is defined as: pc in the next state equals pc
\*   with p mapped to s."
Goto(p, s) == pc' = [pc EXCEPT ![p] = s]

\* In English: "requestClose: close doneChan under onceClose."
\* Literally: "RequestClose is defined as: doneChan in the next state equals
\*   "closed"."
RequestClose == doneChan' = "closed"

\* In English: "forwardError: select { errorChan <- err; <-doneChan;
\* default }. If errorChan is closed, Go may pick the send, which panics."
\* Literally: "ForwardError is defined as: if errorChan equals "closed",
\*   then (panicked in the next state equals TRUE, or doneChan equals
\*   "closed" and panicked is unchanged), else panicked is unchanged."
ForwardError ==
    IF errorChan = "closed"
        THEN \/ panicked' = TRUE
             \/ doneChan = "closed" /\ UNCHANGED panicked
        ELSE UNCHANGED panicked

\* In English: "waitGroup.Go without the fence: count the goroutine, and
\* note it if shutdown's Wait has already begun."
\* Literally: "TrackedAdd is defined as: wg in the next state equals wg plus
\*   1, and lateAdd in the next state equals (lateAdd is true or waitBegan
\*   is true)."
TrackedAdd == wg' = wg + 1 /\ lateAdd' = (lateAdd \/ waitBegan)

-----------------------------------------------------------------------------
(* Things that happen on their own. *)

\* In English: "The handshake protocol finishes (FinishedFunc closes
\* handshakeFinishedChan)."
\* Literally: "HsFinish is defined as: hs equals "running", and hsErr equals
\*   "idle", and hs in the next state equals "finished", and hsLate in the
\*   next state equals (hsLate is true or gaveUp is true), and the rest is
\*   unchanged."
HsFinish ==
    /\ hs = "running" /\ hsErr = "idle"
    /\ hs' = "finished"
    /\ hsLate' = (hsLate \/ gaveUp)
    /\ UNCHANGED <<pc, chans, wgv, hsErr, protoErr, muxErr, muxErrUsed, proto, cb,
                   panicked, gaveUp>>
    /\ UNCHANGED joinv

\* In English: "SendError's check: the handshake protocol is not stopped, so
\* it goes on to report its error. After it has finished, only if a late
\* error is possible."
\* Literally: "HsErrCheck is defined as: hsErr equals "idle", and (hs equals
\*   "running", or LateHandshakeError is true and hs equals "finished"), and
\*   hsErr in the next state equals "checked", and the rest is unchanged."
HsErrCheck ==
    /\ hsErr = "idle"
    /\ \/ hs = "running"
       \/ LateHandshakeError /\ hs = "finished"
    /\ hsErr' = "checked"
    /\ UNCHANGED <<pc, chans, wgv, hs, protoErr, muxErr, muxErrUsed, proto, cb, flags>>
    /\ UNCHANGED joinv

\* In English: "SendError's send to protoErrorChan (buffered, never
\* closed), then Stop: it happens even if the protocol was stopped after
\* the check."
\* Literally: "HsErrSend is defined as: hsErr equals "checked", and
\*   protoErr in the next state equals TRUE, and hsErr in the next state
\*   equals "sent", and hs in the next state equals "stopped", and the rest
\*   is unchanged."
HsErrSend ==
    /\ hsErr = "checked"
    /\ protoErr' = TRUE
    /\ hsErr' = "sent"
    /\ hs' = "stopped"
    /\ UNCHANGED <<pc, chans, wgv, muxErr, muxErrUsed, proto, cb, flags>>
    /\ UNCHANGED joinv

\* In English: "The running muxer reports one error (a read or write
\* failure)."
\* Literally: "MuxError is defined as: muxer equals "running", and
\*   muxErrUsed is not true, and muxErr and muxErrUsed in the next state
\*   equal TRUE, and the rest is unchanged."
MuxError ==
    /\ muxer = "running" /\ ~muxErrUsed
    /\ muxErr' = TRUE /\ muxErrUsed' = TRUE
    /\ UNCHANGED <<pc, chans, wgv, hs, hsErr, protoErr, proto, cb, flags>>
    /\ UNCHANGED joinv

\* In English: "A protocol loop that is still running (even one already
\* told to stop: it may have taken its message first) calls the user
\* callback once; the callback returns when it likes, unless it is inside
\* its own Close. Protocol.Stop does not wait for it."
\* Literally: "Callback is defined as: either (loopCb equals "running" and
\*   cb equals "idle" and cb in the next state equals "running"), or (cb
\*   equals "running" and cbClose does not equal "waiting" and cb in the
\*   next state equals "done"); and the rest is unchanged."
Callback ==
    /\ \/ loopCb = "running" /\ cb = "idle" /\ cb' = "running"
       \/ cb = "running" /\ cbClose /= "waiting" /\ cb' = "done"
    /\ UNCHANGED <<pc, chans, wgv, hs, hsErr, protoErr, muxErr, muxErrUsed, proto,
                   flags, joinv>>

\* In English: "The running callback closes its connection. With
\* CloseContext and its own instance's marker, under the join, its loop is
\* excused from the shutdown join; plain Close excuses nothing."
\* Literally: "CallbackClose is defined as: there exists a k in
\*   CallbackCloseKinds such that cb equals "running", and cbClose equals
\*   "none", and RequestClose, and cbClose in the next state equals
\*   "waiting", and exempt in the next state equals ("join" is a member of
\*   Fix and k equals "own"), and the rest is unchanged."
CallbackClose ==
    \E k \in CallbackCloseKinds :
        /\ cb = "running" /\ cbClose = "none"
        /\ RequestClose
        /\ cbClose' = "waiting"
        /\ exempt' = ("join" \in Fix /\ k = "own")
        /\ UNCHANGED <<pc, errorChan, connClosed, conn, muxer, wgv, prot, flags,
                       loopCb, loopOther, closeReq, userExcept>>

\* In English: "The callback's Close returns once connClosedChan is closed,
\* without waiting for its own goroutine."
\* Literally: "CallbackCloseReturn is defined as: cbClose equals "waiting",
\*   and connClosed is true, and cbClose in the next state equals
\*   "returned", and the rest is unchanged."
CallbackCloseReturn ==
    /\ cbClose = "waiting" /\ connClosed
    /\ cbClose' = "returned"
    /\ UNCHANGED <<pc, chans, wgv, prot, flags, loopCb, loopOther, exempt, closeReq,
                   userExcept>>

\* In English: "A protocol loop exits once its protocol or the muxer is
\* stopped; the callback's loop only once the callback has returned."
\* Literally: "LoopExit is defined as: (proto equals "stopped" or muxer
\*   equals "stopped"), and either (loopOther equals "running" and loopOther
\*   in the next state equals "exited" and loopCb is unchanged), or (loopCb
\*   equals "running" and cb does not equal "running" and loopCb in the
\*   next state equals "exited" and loopOther is unchanged); and the rest
\*   is unchanged."
LoopExit ==
    /\ proto = "stopped" \/ muxer = "stopped"
    /\ \/ loopOther = "running" /\ loopOther' = "exited" /\ UNCHANGED loopCb
       \/ loopCb = "running" /\ cb /= "running" /\ loopCb' = "exited"
          /\ UNCHANGED loopOther
    /\ UNCHANGED <<pc, chans, wgv, prot, flags, cbClose, exempt, closeReq, userExcept>>

-----------------------------------------------------------------------------
(* setupConnection *)

\* In English: "Make doneChan and start the shutdown goroutine. If a Close
\* came first (closeEarly), doneChan starts closed."
\* Literally: "SetupMkDone is defined as: pc of "setup" equals "mkDone", and
\*   doneChan in the next state equals (if closeReq is true then "closed"
\*   else "open"), and pc in the next state maps
\*   "setup" to "mkMuxer" and "sd" to "wait", and the rest is unchanged."
SetupMkDone ==
    /\ pc["setup"] = "mkDone"
    /\ doneChan' = IF closeReq THEN "closed" ELSE "open"
    /\ pc' = [pc EXCEPT !["setup"] = "mkMuxer", !["sd"] = "wait"]
    /\ UNCHANGED <<errorChan, connClosed, conn, muxer, wgv, prot, flags, joinv>>

\* In English: "Create the muxer (which starts its cleanup goroutine). With
\* the guard, if doneChan is already closed, close the conn and fail
\* instead."
\* Literally: "SetupMkMuxer is defined as: pc of "setup" equals "mkMuxer",
\*   and if "muxerGuard" is a member of Fix and doneChan equals "closed",
\*   then conn in the next state equals "closed" and Goto of "setup" and
\*   "failed" and muxer is unchanged, else muxer in the next state equals
\*   "running" and pc in the next state maps "setup" to "goMuxFwd" and "mc"
\*   to "wait" and conn is unchanged; and the rest is unchanged."
SetupMkMuxer ==
    /\ pc["setup"] = "mkMuxer"
    /\ IF "muxerGuard" \in Fix /\ doneChan = "closed"
          THEN conn' = "closed" /\ Goto("setup", "failed") /\ UNCHANGED muxer
          ELSE /\ muxer' = "running"
               /\ pc' = [pc EXCEPT !["setup"] = "goMuxFwd", !["mc"] = "wait"]
               /\ UNCHANGED conn
    /\ UNCHANGED <<doneChan, errorChan, connClosed, wgv, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "waitGroup.Go(forwarder) for forwarder f, then go on to
\* step next. Without the fence it is one step. With it: take the mutex;
\* if doneChan is closed start nothing, else Go; release."
\* Literally: "SetupGo of s, f and next is defined as: pc of "setup" equals
\*   s, and either ("fence" is not a member of Fix, and TrackedAdd, and pc
\*   in the next state maps "setup" to next and f to "select", and wgMu is
\*   unchanged), or ("fence" is a member of Fix, and wgMu equals "none",
\*   and wgMu in the next state equals "setup", and Goto of "setup" and s
\*   followed by "_add", and wg, waitBegan and lateAdd are unchanged); and
\*   the rest is unchanged."
SetupGo(s, f, next) ==
    /\ pc["setup"] = s
    /\ \/ /\ "fence" \notin Fix
          /\ TrackedAdd
          /\ pc' = [pc EXCEPT !["setup"] = next, ![f] = "select"]
          /\ UNCHANGED <<wgMu, waitBegan>>
       \/ /\ "fence" \in Fix /\ wgMu = "none"
          /\ wgMu' = "setup"
          /\ Goto("setup", s \o "_add")
          /\ UNCHANGED <<wg, waitBegan, lateAdd>>
    /\ UNCHANGED <<chans, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "Under the fence mutex: Go only if doneChan is open."
\* Literally: "SetupGoAdd of s and f is defined as: pc of "setup" equals s
\*   followed by "_add", and if doneChan equals "closed" then Goto of
\*   "setup" and s followed by "_unlock" and wg and lateAdd are unchanged,
\*   else TrackedAdd and pc in the next state maps "setup" to s followed
\*   by "_unlock" and f to "select"; and the rest is unchanged."
SetupGoAdd(s, f) ==
    /\ pc["setup"] = s \o "_add"
    /\ IF doneChan = "closed"
          THEN Goto("setup", s \o "_unlock") /\ UNCHANGED <<wg, lateAdd>>
          ELSE TrackedAdd /\ pc' = [pc EXCEPT !["setup"] = s \o "_unlock", ![f] = "select"]
    /\ UNCHANGED <<waitBegan, wgMu, chans, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "Release the fence mutex and go on."
\* Literally: "SetupGoUnlock of s and next is defined as: pc of "setup"
\*   equals s followed by "_unlock", and wgMu in the next state equals
\*   "none", and Goto of "setup" and next, and the rest is unchanged."
SetupGoUnlock(s, next) ==
    /\ pc["setup"] = s \o "_unlock"
    /\ wgMu' = "none"
    /\ Goto("setup", next)
    /\ UNCHANGED <<wg, waitBegan, lateAdd, chans, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "Start the handshake protocol and StartOnce the muxer."
\* Literally: "SetupHandshake is defined as: pc of "setup" equals
\*   "mkHandshake", and hs in the next state equals "running", and Goto of
\*   "setup" and "select", and the rest is unchanged."
SetupHandshake ==
    /\ pc["setup"] = "mkHandshake"
    /\ hs' = "running"
    /\ Goto("setup", "select")
    /\ UNCHANGED <<chans, wgv, hsErr, protoErr, muxErr, muxErrUsed, proto, cb, flags>>
    /\ UNCHANGED joinv

\* In English: "The select at :819: doneChan closed (return); a protocol
\* error (Close, then return it); the handshake finished (carry on); the
\* handshake timer (Close, then return). Go picks any ready case."
\* Literally: "SetupSelect is defined as: pc of "setup" equals "select",
\*   and either (doneChan equals "closed" and Goto of "setup" and "failed"
\*   and doneChan, protoErr and gaveUp are unchanged), or (protoErr is true
\*   and protoErr in the next state equals FALSE and RequestClose and Goto
\*   of "setup" and "closeWait" and gaveUp is unchanged), or (hs equals
\*   "finished" and Goto of "setup" and "goProtoFwd" and doneChan, protoErr
\*   and gaveUp are unchanged), or (gaveUp in the next state equals TRUE
\*   and RequestClose and Goto of "setup" and "closeWait" and protoErr is
\*   unchanged); and the rest is unchanged."
SetupSelect ==
    /\ pc["setup"] = "select"
    /\ \/ doneChan = "closed" /\ Goto("setup", "failed")
          /\ UNCHANGED <<doneChan, protoErr, gaveUp>>
       \/ protoErr /\ protoErr' = FALSE /\ RequestClose /\ Goto("setup", "closeWait")
          /\ UNCHANGED gaveUp
       \/ hs = "finished" /\ Goto("setup", "goProtoFwd")
          /\ UNCHANGED <<doneChan, protoErr, gaveUp>>
       \/ gaveUp' = TRUE /\ RequestClose /\ Goto("setup", "closeWait")
          /\ UNCHANGED protoErr
    /\ UNCHANGED <<errorChan, connClosed, conn, muxer, wgv, hs, hsErr, muxErr,
                   muxErrUsed, proto, cb, panicked, hsLate>>
    /\ UNCHANGED joinv

\* In English: "setup's own Close waits for connClosedChan, then setup
\* returns its error."
\* Literally: "SetupCloseWait is defined as: pc of "setup" equals
\*   "closeWait", and connClosed is true, and Goto of "setup" and "failed",
\*   and the rest is unchanged."
SetupCloseWait ==
    /\ pc["setup"] = "closeWait" /\ connClosed
    /\ Goto("setup", "failed")
    /\ UNCHANGED <<chans, wgv, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "lockProtocolSetup refuses once doneChan is closed;
\* otherwise the mini-protocols are constructed under protocolMu."
\* Literally: "SetupLock is defined as: pc of "setup" equals "lock", and if
\*   doneChan equals "closed" then Goto of "setup" and "failed" and proto is
\*   unchanged, else proto in the next state equals "constructed" and Goto
\*   of "setup" and "start"; and the rest is unchanged."
SetupLock ==
    /\ pc["setup"] = "lock"
    /\ IF doneChan = "closed"
          THEN Goto("setup", "failed") /\ UNCHANGED proto
          ELSE proto' = "constructed" /\ Goto("setup", "start")
    /\ UNCHANGED <<chans, wgv, hs, hsErr, protoErr, muxErr, muxErrUsed, cb, flags>>
    /\ UNCHANGED joinv

\* In English: "Start the mini-protocols (a stopped one stays stopped) and
\* the muxer, and return."
\* Literally: "SetupStart is defined as: pc of "setup" equals "start", and
\*   proto in the next state equals (if proto equals "constructed" then
\*   "running" else proto), and loopCb and loopOther in the next state
\*   equal (if proto equals "constructed" then "running" else their
\*   current values), and Goto of "setup" and "returned", and the rest
\*   is unchanged."
SetupStart ==
    /\ pc["setup"] = "start"
    /\ proto' = IF proto = "constructed" THEN "running" ELSE proto
    /\ loopCb' = IF proto = "constructed" THEN "running" ELSE loopCb
    /\ loopOther' = IF proto = "constructed" THEN "running" ELSE loopOther
    /\ Goto("setup", "returned")
    /\ UNCHANGED <<chans, wgv, hs, hsErr, protoErr, muxErr, muxErrUsed, cb, flags,
                   cbClose, exempt, closeReq, userExcept>>

\* Literally: "SetupStep is defined as: SetupMkDone, or SetupMkMuxer, or
\*   SetupGo of "goMuxFwd", "mf" and "mkHandshake", or SetupGoAdd of
\*   "goMuxFwd" and "mf", or SetupGoUnlock of "goMuxFwd" and "mkHandshake",
\*   or SetupHandshake, or SetupSelect, or SetupCloseWait, or SetupGo of
\*   "goProtoFwd", "pf" and "lock", or SetupGoAdd of "goProtoFwd" and "pf",
\*   or SetupGoUnlock of "goProtoFwd" and "lock", or SetupLock, or
\*   SetupStart."
SetupStep ==
    \/ SetupMkDone \/ SetupMkMuxer
    \/ SetupGo("goMuxFwd", "mf", "mkHandshake") \/ SetupGoAdd("goMuxFwd", "mf")
    \/ SetupGoUnlock("goMuxFwd", "mkHandshake")
    \/ SetupHandshake \/ SetupSelect \/ SetupCloseWait
    \/ SetupGo("goProtoFwd", "pf", "lock") \/ SetupGoAdd("goProtoFwd", "pf")
    \/ SetupGoUnlock("goProtoFwd", "lock")
    \/ SetupLock \/ SetupStart

-----------------------------------------------------------------------------
(* The user *)

\* In English: "Close: once doneChan exists, close it, then wait. Before
\* that, gOuroboros does nothing and returns; with closeEarly it closes the
\* conn and leaves a request that setup honours. Without ConcurrentClose,
\* only after Dial has returned."
\* Literally: "UserClose is defined as: pc of "user" equals "idle", and
\*   (ConcurrentClose is true or pc of "setup" is a member of the set
\*   containing "returned" and "failed"), and if doneChan does not equal
\*   "nil" then RequestClose and Goto of "user" and "waiting" and exempt in
\*   the next state equals (exempt is true or UserMarker equals "foreign"
\*   and "anyMarker" is a member of Fix) and userExcept in the next state
\*   equals (UserMarker equals "foreign" and "anyMarker" is a member of
\*   Fix), else Goto of
\*   "user" and "returnedEarly" and (if "closeEarly" is a member of Fix
\*   then conn in the next state equals "closed" and closeReq in the next
\*   state equals TRUE); and the rest is unchanged."
UserClose ==
    /\ pc["user"] = "idle"
    /\ ConcurrentClose \/ pc["setup"] \in {"returned", "failed"}
    /\ IF doneChan /= "nil"
          THEN /\ RequestClose /\ Goto("user", "waiting")
               /\ UNCHANGED <<conn, closeReq>>
               \* A foreign marker is not one of this connection's
               \* instances, so it excuses nothing, unless the identity
               \* check is broken.
               /\ exempt' = (exempt \/ (UserMarker = "foreign" /\ "anyMarker" \in Fix))
               /\ userExcept' = (UserMarker = "foreign" /\ "anyMarker" \in Fix)
          ELSE /\ Goto("user", "returnedEarly")
               /\ IF "closeEarly" \in Fix
                     THEN conn' = "closed" /\ closeReq' = TRUE
                     ELSE UNCHANGED <<conn, closeReq>>
               /\ UNCHANGED <<doneChan, exempt, userExcept>>
    /\ UNCHANGED <<errorChan, connClosed, muxer, wgv, prot, flags, loopCb, loopOther,
                   cbClose>>

\* In English: "Close returns once connClosedChan is closed and, under the
\* join, every loop has exited (the user's goroutine runs none of them)."
\* Literally: "UserReturn is defined as: pc of "user" equals "waiting", and
\*   connClosed is true, and ("join" is not a member of Fix, or loopOther
\*   does not equal "running" and (loopCb does not equal "running" or
\*   userExcept is true)), and Goto of "user" and "returned", and the rest is
\*   unchanged."
UserReturn ==
    /\ pc["user"] = "waiting" /\ connClosed
    /\ "join" \notin Fix \/ (loopOther /= "running" /\ (loopCb /= "running" \/ userExcept))
    /\ Goto("user", "returned")
    /\ UNCHANGED <<chans, wgv, prot, flags>>
    /\ UNCHANGED joinv

-----------------------------------------------------------------------------
(* The shutdown goroutine *)

\* In English: "Wait for doneChan, then stopProtocols: the handshake and
\* the mini-protocols, if they exist. Protocol.Stop waits for no loop."
\* Literally: "SdBegin is defined as: pc of "sd" equals "wait", and doneChan
\*   equals "closed", and hs in the next state equals (if hs is a member of
\*   the set containing "running" and "finished" then "stopped" else hs),
\*   and proto in the next state equals (if proto is a member of the set
\*   containing "constructed" and "running" then "stopped" else proto), and
\*   Goto of "sd" and "readMuxer", and the rest is unchanged."
SdBegin ==
    /\ pc["sd"] = "wait" /\ doneChan = "closed"
    /\ hs' = IF hs \in {"running", "finished"} THEN "stopped" ELSE hs
    /\ proto' = IF proto \in {"constructed", "running"} THEN "stopped" ELSE proto
    /\ Goto("sd", "readMuxer")
    /\ UNCHANGED <<chans, wgv, hsErr, protoErr, muxErr, muxErrUsed, cb, flags>>
    /\ UNCHANGED joinv

\* In English: "Where shutdown goes after muxer.Stop and the join: the
\* fence, or Wait at once."
\* Literally: "AfterJoin is defined as: if "fence" is a member of Fix then
\*   Goto of "sd" and "fenceLock" and waitBegan is unchanged, else Goto of
\*   "sd" and "wgWait" and waitBegan in the next state equals TRUE."
AfterJoin ==
    IF "fence" \in Fix
        THEN Goto("sd", "fenceLock") /\ UNCHANGED waitBegan
        ELSE Goto("sd", "wgWait") /\ waitBegan' = TRUE

\* In English: "If c.muxer is set, muxer.Stop (which only closes the
\* muxer's doneChan). Then the join, or what follows it."
\* Literally: "SdMuxer is defined as: pc of "sd" equals "readMuxer", and
\*   muxer in the next state equals (if muxer equals "running" then
\*   "stopped" else muxer), and if "join" is a member of Fix then Goto of
\*   "sd" and "join" and waitBegan is unchanged, else AfterJoin; and the
\*   rest is unchanged."
SdMuxer ==
    /\ pc["sd"] = "readMuxer"
    /\ muxer' = IF muxer = "running" THEN "stopped" ELSE muxer
    /\ IF "join" \in Fix
          THEN Goto("sd", "join") /\ UNCHANGED waitBegan
          ELSE AfterJoin
    /\ UNCHANGED <<doneChan, errorChan, connClosed, conn, wg, lateAdd, wgMu, prot,
                   flags, joinv>>

\* In English: "The join: wait until every protocol loop has exited, except
\* the goroutine of a callback that is itself in Close."
\* Literally: "SdJoin is defined as: pc of "sd" equals "join", and loopOther
\*   does not equal "running", and (loopCb does not equal "running" or
\*   exempt is true), and AfterJoin, and the rest is unchanged."
SdJoin ==
    /\ pc["sd"] = "join"
    /\ loopOther /= "running"
    /\ loopCb /= "running" \/ exempt
    /\ AfterJoin
    /\ UNCHANGED <<doneChan, errorChan, connClosed, conn, muxer, wg, lateAdd, wgMu,
                   prot, flags, joinv>>

\* In English: "The fence: take the mutex..."
\* Literally: "SdFenceLock is defined as: pc of "sd" equals "fenceLock", and
\*   wgMu equals "none", and wgMu in the next state equals "sd", and Goto of
\*   "sd" and "fenceUnlock", and the rest is unchanged."
SdFenceLock ==
    /\ pc["sd"] = "fenceLock" /\ wgMu = "none"
    /\ wgMu' = "sd"
    /\ Goto("sd", "fenceUnlock")
    /\ UNCHANGED <<chans, wg, waitBegan, lateAdd, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "... and release it, then Wait."
\* Literally: "SdFenceUnlock is defined as: pc of "sd" equals "fenceUnlock",
\*   and wgMu in the next state equals "none", and waitBegan in the next
\*   state equals TRUE, and Goto of "sd" and "wgWait", and the rest is
\*   unchanged."
SdFenceUnlock ==
    /\ pc["sd"] = "fenceUnlock"
    /\ wgMu' = "none" /\ waitBegan' = TRUE
    /\ Goto("sd", "wgWait")
    /\ UNCHANGED <<chans, wg, lateAdd, prot, flags>>
    /\ UNCHANGED joinv

\* In English: "waitGroup.Wait returns once the counter is zero; then close
\* errorChan, then connClosedChan."
\* Literally: "SdRest is defined as: either (pc of "sd" equals "wgWait" and
\*   wg equals 0 and Goto of "sd" and "closeErr" and errorChan and
\*   connClosed are unchanged), or (pc of "sd" equals "closeErr" and
\*   errorChan in the next state equals "closed" and Goto of "sd" and
\*   "closeConn" and connClosed is unchanged), or (pc of "sd" equals
\*   "closeConn" and connClosed in the next state equals TRUE and Goto of
\*   "sd" and "done" and errorChan is unchanged); and the rest is
\*   unchanged."
SdRest ==
    /\ \/ pc["sd"] = "wgWait" /\ wg = 0 /\ Goto("sd", "closeErr")
          /\ UNCHANGED <<errorChan, connClosed>>
       \/ pc["sd"] = "closeErr" /\ errorChan' = "closed" /\ Goto("sd", "closeConn")
          /\ UNCHANGED connClosed
       \/ pc["sd"] = "closeConn" /\ connClosed' = TRUE /\ Goto("sd", "done")
          /\ UNCHANGED errorChan
    /\ UNCHANGED <<doneChan, conn, muxer, wgv, prot, flags>>
    /\ UNCHANGED joinv

-----------------------------------------------------------------------------
(* The forwarders and the muxer cleanup goroutine *)

\* In English: "A forwarder f with pending-error flag e: return on doneChan,
\* or take the error, forwardError, requestClose; waitGroup.Done either
\* way."
\* Literally: "MuxFwd is defined as: pc of "mf" equals "select", and either
\*   (doneChan equals "closed" and muxErr, doneChan and panicked are
\*   unchanged), or (muxErr is true and muxErr in the next state equals
\*   FALSE and ForwardError and RequestClose); and wg in the next state
\*   equals wg minus 1, and Goto of "mf" and "exited", and the rest is
\*   unchanged."
MuxFwd ==
    /\ pc["mf"] = "select"
    /\ \/ doneChan = "closed" /\ UNCHANGED <<muxErr, doneChan, panicked>>
       \/ muxErr /\ muxErr' = FALSE /\ ForwardError /\ RequestClose
    /\ wg' = wg - 1
    /\ Goto("mf", "exited")
    /\ UNCHANGED <<errorChan, connClosed, conn, muxer, waitBegan, lateAdd, wgMu,
                   hs, hsErr, protoErr, muxErrUsed, proto, cb, gaveUp, hsLate>>
    /\ UNCHANGED joinv

\* In English: "The protocol-error forwarder, likewise."
\* Literally: "ProtoFwd is defined as: pc of "pf" equals "select", and
\*   either (doneChan equals "closed" and protoErr, doneChan and panicked
\*   are unchanged), or (protoErr is true and protoErr in the next state
\*   equals FALSE and ForwardError and RequestClose); and wg in the next
\*   state equals wg minus 1, and Goto of "pf" and "exited", and the rest
\*   is unchanged."
ProtoFwd ==
    /\ pc["pf"] = "select"
    /\ \/ doneChan = "closed" /\ UNCHANGED <<protoErr, doneChan, panicked>>
       \/ protoErr /\ protoErr' = FALSE /\ ForwardError /\ RequestClose
    /\ wg' = wg - 1
    /\ Goto("pf", "exited")
    /\ UNCHANGED <<errorChan, connClosed, conn, muxer, waitBegan, lateAdd, wgMu,
                   hs, hsErr, muxErr, muxErrUsed, proto, cb, gaveUp, hsLate>>
    /\ UNCHANGED joinv

\* In English: "The muxer cleanup goroutine closes the conn once the muxer
\* is stopped. Nothing waits for it."
\* Literally: "MuxCleanup is defined as: pc of "mc" equals "wait", and muxer
\*   equals "stopped", and conn in the next state equals "closed", and Goto
\*   of "mc" and "exited", and the rest is unchanged."
MuxCleanup ==
    /\ pc["mc"] = "wait" /\ muxer = "stopped"
    /\ conn' = "closed"
    /\ Goto("mc", "exited")
    /\ UNCHANGED <<doneChan, errorChan, connClosed, muxer, wgv, prot, flags>>
    /\ UNCHANGED joinv

-----------------------------------------------------------------------------

\* In English: "Everything is over: Dial and Close returned, shutdown and
\* every goroutine finished, no callback runs, no SendError is half done."
\* Literally: "Finished is defined as: pc of "setup" is a member of the set
\*   containing "returned" and "failed", and pc of "user" is a member of
\*   the set containing "returned" and "returnedEarly", and pc of "sd"
\*   equals "done", and pc of "mf", "pf" and "mc" are members of the set
\*   containing "notStarted" and "exited", and cb does not equal "running",
\*   and hsErr does not equal "checked", and loopCb and loopOther do not
\*   equal "running", and cbClose does not equal "waiting"."
Finished ==
    /\ pc["setup"] \in {"returned", "failed"} /\ pc["user"] \in {"returned", "returnedEarly"}
    /\ pc["sd"] = "done"
    /\ \A p \in {"mf", "pf", "mc"} : pc[p] \in {"notStarted", "exited"}
    /\ cb /= "running" /\ hsErr /= "checked"
    /\ loopCb /= "running" /\ loopOther /= "running" /\ cbClose /= "waiting"

\* In English: "A step is one step of one goroutine or one event; once
\* everything is over, nothing changes. Any other state with no step is a
\* deadlock (a goroutine stuck for good), which TLC reports."
\* Literally: "Next is defined as: HsFinish, or HsErrCheck, or HsErrSend,
\*   or MuxError, or Callback, or CallbackClose, or CallbackCloseReturn, or
\*   LoopExit, or SdJoin, or SetupStep, or UserClose, or UserReturn,
\*   or SdBegin, or SdMuxer, or SdFenceLock, or SdFenceUnlock, or SdRest,
\*   or MuxFwd, or ProtoFwd, or MuxCleanup, or (Finished and vars is
\*   unchanged)."
Next ==
    \/ HsFinish \/ HsErrCheck \/ HsErrSend \/ MuxError \/ Callback
    \/ CallbackClose \/ CallbackCloseReturn \/ LoopExit \/ SdJoin
    \/ SetupStep
    \/ UserClose \/ UserReturn
    \/ SdBegin \/ SdMuxer \/ SdFenceLock \/ SdFenceUnlock \/ SdRest
    \/ MuxFwd \/ ProtoFwd \/ MuxCleanup
    \/ Finished /\ UNCHANGED vars

\* Literally: "Spec is defined as: Init holds at the start, and always,
\*   every step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

\* In English: "Nothing sends on a closed channel."
\* Literally: "NoPanic is defined as: panicked is not true."
NoPanic == ~panicked

\* In English: "Close returns only after shutdown has finished."
\* Literally: "CloseWaitsForShutdown is defined as: if pc of "user" equals
\*   "returned", then pc of "sd" equals "done"."
CloseWaitsForShutdown == pc["user"] = "returned" => pc["sd"] = "done"

\* In English: "No waitGroup.Add happens after shutdown's Wait has begun
\* (Go's rule for a WaitGroup: an Add from zero must happen before Wait)."
\* Literally: "NoAddAfterWaitBegan is defined as: lateAdd is not true."
NoAddAfterWaitBegan == ~lateAdd

\* In English: "Once shutdown has finished and Dial has returned, no muxer
\* is left running (so its conn and goroutines are not leaked)."
\* Literally: "MuxerStoppedWhenClosed is defined as: if pc of "sd" equals
\*   "done" and pc of "setup" is a member of the set containing "returned"
\*   and "failed", then muxer does not equal "running"."
MuxerStoppedWhenClosed ==
    pc["sd"] = "done" /\ pc["setup"] \in {"returned", "failed"} => muxer /= "running"

\* In English: "After Close returns, no protocol callback is running and
\* no protocol loop is left to start one (what the comment at :263
\* claims)."
\* Literally: "NoCallbackAfterClose is defined as: if pc of "user" equals
\*   "returned", then cb does not equal "running", and loopCb and loopOther
\*   do not equal "running"."
NoCallbackAfterClose ==
    pc["user"] = "returned" =>
        cb /= "running" /\ loopCb /= "running" /\ loopOther /= "running"

\* In English: "A Close, even one made before setup got far, leaves no
\* muxer or protocol running once Dial has returned."
\* Literally: "CloseTearsDown is defined as: if pc of "user" is a member of
\*   the set containing "returned" and "returnedEarly", and pc of "setup"
\*   is a member of the set containing "returned" and "failed", then muxer
\*   does not equal "running" and proto does not equal "running"."
CloseTearsDown ==
    pc["user"] \in {"returned", "returnedEarly"} /\ pc["setup"] \in {"returned", "failed"}
        => muxer /= "running" /\ proto /= "running"

(* Reachability probes: each is expected to be violated. *)

\* In English: "Probe: the handshake never finishes after setup's timer
\* fired (FinishedFunc then writes handshakeVersion with no
\* synchronisation)."
\* Literally: "ProbeNoHandshakeAfterGiveUp is defined as: hsLate is not
\*   true."
ProbeNoHandshakeAfterGiveUp == ~hsLate

\* In English: "Probe: Close never closes doneChan before the muxer
\* exists."
\* Literally: "ProbeNoCloseBeforeMuxer is defined as: not (doneChan equals
\*   "closed" and muxer equals "none" and pc of "setup" equals "mkMuxer")."
ProbeNoCloseBeforeMuxer ==
    ~(doneChan = "closed" /\ muxer = "none" /\ pc["setup"] = "mkMuxer")
=============================================================================
