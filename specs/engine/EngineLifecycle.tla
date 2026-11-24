--------------------------- MODULE EngineLifecycle ---------------------------
(***************************************************************************)
(* Model 03, slice 4: how the protocol engine starts, stops and restarts,  *)
(* one Go primitive per step.                                              *)
(*                                                                         *)
(* Goroutines (gOuroboros 5c4f31c1, protocol/protocol.go):                 *)
(*   owner   Start (:421): lifecycleMu, check stopped, start the five      *)
(*           goroutines below, set started, unlock.                        *)
(*   user    calls Stop (:465) once, from outside the engine.              *)
(*   rd      readLoop (:1849): take a segment, decode it                   *)
(*           (MessageFromCborFunc), run MessageReceivedFunc (:2172), then  *)
(*           queue it on recvQueueChan (:2183). A server's readLoop stops  *)
(*           after queueing a message that ends the protocol (:2199).      *)
(*           Its deferred close(readDoneChan) is at :1854.                 *)
(*   rv      recvLoop (:2207): take a queued message, ask stateLoop for    *)
(*           the transition (requestStateTransition :2466), then run       *)
(*           MessageHandlerFunc (:2260). A server's handler for MsgDone    *)
(*           calls StopForRestart and starts a new instance                *)
(*           (keepalive/server.go:145, chainsync/server.go:335, ...).      *)
(*           close(recvDoneChan) at :2209.                                 *)
(*   sd      sendLoop (:1195): leaves on stopChan or recvDoneChan; closes  *)
(*           muxerSendChan and sendDoneChan (:1200-1201).                  *)
(*   st      stateLoop (:2279): select over stopChan, a transition         *)
(*           request, the state timer and doneChan (:2376-2416). A timer   *)
(*           firing calls SendError (:2408).                               *)
(*   w       the done watcher (:448-452): recvDoneChan, then              *)
(*           sendDoneChan, then closeDone.                                 *)
(*                                                                         *)
(* stop(restart) (:496) runs inline in whichever goroutine calls it:       *)
(* onceStop.Do; lifecycleMu: stopped := TRUE, read started; unlock;        *)
(* close(stopChan); closeDone if never started; if restarting and started, *)
(* <-readDoneChan (:521); then SuspendProtocol or UnregisterProtocol.      *)
(* sync.Once blocks a second caller until the first call returns.          *)
(* SendError (:926) checks stopChan and doneChan, sends to ErrorChan       *)
(* without blocking, then calls Stop: the check and the Stop are separate  *)
(* steps.                                                                  *)
(*                                                                         *)
(* User callbacks are steps that may return, call Stop or                  *)
(* StopForRestart, wait for StopChan (what the StopChan doc at :567 asks   *)
(* of a callback), or wait for the user's Stop call to return (a callback  *)
(* blocked on a lock the Stop caller holds).                               *)
(*                                                                         *)
(* No specification source: this is gOuroboros's own Go API. The rules     *)
(* checked are Go's (sync.Once, closing a channel once) and the engine's  *)
(* own contracts (DoneChan doc :562, StopForRestart doc :469).            *)
(* EngineTimer.tla covers when the state timer is armed; here it only      *)
(* fires once, at any time, as one more way to reach SendError.            *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Role,              \* "client" or "server": a server restarts after MsgDone
    Msgs,              \* the peer's messages, in order: "msg", "bad"
                       \* (fails to decode) or "done" (MsgDone, server only)
    ReceivedCallbacks, \* what MessageReceivedFunc may do, chosen per message:
                       \* "returns", "callsStop", "callsStopForRestart",
                       \* "waitsForStopChan"
    HandlerCallbacks,  \* what MessageHandlerFunc may do for a "msg":
                       \* "returns", "callsStop", "waitsForStopChan",
                       \* "waitsForCaller" (until the user's Stop returns)
    TimerFires,        \* TRUE: the state timer may fire once
    MuxerMayStop,      \* TRUE: the muxer may shut down under the engine
    RestartOn,         \* "terminal": a server restarts from the MsgDone
                       \* handler (gOuroboros); "anyMessage": a mutation
                       \* that also restarts from an ordinary message
    StopJoins,         \* "none": Stop waits for no loop (gOuroboros);
                       \* "loops": a candidate fix where a Stop called from
                       \* outside the engine waits for every loop to exit
    Mutation           \* "none", or one deliberate break of the code:
                       \* "watcherRecvOnly", "startIgnoresStopped",
                       \* "noOnces", "noWaitRead", "waitReadUnderLock"

ASSUME Role \in {"client", "server"}
ASSUME RestartOn \in {"terminal", "anyMessage"}
ASSUME StopJoins \in {"none", "loops"}
ASSUME Mutation \in {"none", "watcherRecvOnly", "startIgnoresStopped",
                     "noOnces", "noWaitRead", "waitReadUnderLock"}

(* The peer's message sequences the configs choose from (a .cfg file cannot
   write a sequence, so it names one of these with Msgs <- Name). *)
\* Literally: "MsgThenDone is defined as the sequence of "msg" then "done"."
MsgThenDone == <<"msg", "done">>
\* Literally: "MsgThenBad is defined as the sequence of "msg" then "bad"."
MsgThenBad == <<"msg", "bad">>
\* Literally: "TwoMsgs is defined as the sequence of "msg" then "msg"."
TwoMsgs == <<"msg", "msg">>
\* Literally: "OneMsg is defined as the sequence of one "msg"."
OneMsg == <<"msg">>
\* Literally: "OnlyDone is defined as the sequence of one "done"."
OnlyDone == <<"done">>
\* Literally: "NoMsgs is defined as the empty sequence."
NoMsgs == <<>>

VARIABLES
    pc,          \* each goroutine's next step
    ret,         \* where a goroutine goes when its inline Stop/SendError returns
    smode,       \* TRUE while a goroutine runs stop(true), StopForRestart
    saw,         \* the value of started that each goroutine's stop read
    lifeMu,      \* who holds lifecycleMu, or "none"
    started,     \* Protocol.started
    stopped,     \* Protocol.stopped
    once,        \* onceStop: "idle", "running" or "done"
    startedAfterStop, \* TRUE if Start started loops after stopped was set
    stopChan, readDone, recvDone, sendDone, doneChan, muxDone, \* closed?
    doneCloses,  \* how many times doneChan was closed
    sent,        \* how many of Msgs the peer has sent
    wire,        \* segments the muxer holds for readLoop
    rq,          \* recvQueueChan (one slot in the model)
    cur,         \* the message readLoop is handling
    hmsg,        \* the message recvLoop is handling
    reply,       \* stateLoop's answer waits in the request's errorChan
    restarted,   \* a server started its next instance
    badCarry,    \* a restart suspended the role while readLoop still read
    timerFired   \* the state timer has fired

pcs   == <<pc, ret, smode, saw>>
life  == <<lifeMu, started, stopped, once, startedAfterStop>>
chans == <<stopChan, readDone, recvDone, sendDone, doneChan, muxDone, doneCloses>>
data  == <<sent, wire, rq, cur, hmsg, reply, restarted, badCarry, timerFired>>
\* Literally: "vars is defined as the tuple of pcs, life, chans and data."
vars  == <<pcs, life, chans, data>>

\* Literally: "Procs is defined as the set containing "owner", "user", "rd",
\*   "rv", "sd", "st" and "w"."
Procs == {"owner", "user", "rd", "rv", "sd", "st", "w"}
\* Literally: "Loops is defined as the set containing "rd", "rv", "sd", "st"
\*   and "w"."
Loops == {"rd", "rv", "sd", "st", "w"}

\* In English: "Steps at which a goroutine is blocked until something else
\* happens: a lock must never be held at one of them."
\* Literally: "Blocking is defined as the set of these step names."
Blocking == {"s_onceWait", "s_waitRead", "s_join", "cbWait", "hWait",
             "hWaitCaller", "wait", "queue", "req", "reply", "select",
             "w1", "w2"}

\* In English: "Every goroutine starts at its first step; the loops have not
\* been started; every channel is open; nothing has happened."
\* Literally: "Init is defined as: pc equals the function that maps "owner"
\*   to "start", "user" to "idle" and every other goroutine to "notStarted",
\*   and ret maps every goroutine to "none", and smode and saw map every
\*   goroutine to FALSE, and lifeMu equals "none", and started, stopped and
\*   startedAfterStop equal FALSE, and once equals "idle", and every channel
\*   is open (FALSE), and doneCloses equals 0, and sent equals 0, and wire
\*   and rq are empty, and cur and hmsg equal "none", and reply, restarted,
\*   badCarry and timerFired equal FALSE."
Init ==
    /\ pc = [p \in Procs |-> IF p = "owner" THEN "start"
                             ELSE IF p = "user" THEN "idle" ELSE "notStarted"]
    /\ ret = [p \in Procs |-> "none"]
    /\ smode = [p \in Procs |-> FALSE]
    /\ saw = [p \in Procs |-> FALSE]
    /\ lifeMu = "none"
    /\ started = FALSE /\ stopped = FALSE /\ startedAfterStop = FALSE
    /\ once = "idle"
    /\ stopChan = FALSE /\ readDone = FALSE /\ recvDone = FALSE
    /\ sendDone = FALSE /\ doneChan = FALSE /\ muxDone = FALSE
    /\ doneCloses = 0
    /\ sent = 0 /\ wire = <<>> /\ rq = <<>>
    /\ cur = "none" /\ hmsg = "none"
    /\ reply = FALSE /\ restarted = FALSE /\ badCarry = FALSE
    /\ timerFired = FALSE

\* In English: "Goroutine p moves to step s; nothing else about the
\* goroutines changes."
\* Literally: "Goto of p and s is defined as: pc in the next state equals pc
\*   with p mapped to s, and ret, smode and saw are unchanged."
Goto(p, s) == pc' = [pc EXCEPT ![p] = s] /\ UNCHANGED <<ret, smode, saw>>

\* In English: "Goroutine p starts an inline stop(restart) and returns to
\* step r when it is done."
\* Literally: "CallStop of p, restart and r is defined as: pc in the next
\*   state equals pc with p mapped to "s_once", and ret in the next state
\*   equals ret with p mapped to r, and smode in the next state equals smode
\*   with p mapped to restart, and saw is unchanged."
CallStop(p, restart, r) ==
    /\ pc' = [pc EXCEPT ![p] = "s_once"]
    /\ ret' = [ret EXCEPT ![p] = r]
    /\ smode' = [smode EXCEPT ![p] = restart]
    /\ UNCHANGED saw

\* In English: "Goroutine p calls SendError and goes to step r after it."
\* Literally: "CallSendError of p and r is defined as: pc in the next state
\*   equals pc with p mapped to "se_check", and ret in the next state equals
\*   ret with p mapped to r, and smode and saw are unchanged."
CallSendError(p, r) ==
    /\ pc' = [pc EXCEPT ![p] = "se_check"]
    /\ ret' = [ret EXCEPT ![p] = r]
    /\ UNCHANGED <<smode, saw>>

\* In English: "closeDone: close doneChan under doneOnce. The noOnces
\* mutation drops the Once and closes it again."
\* Literally: "CloseDone is defined as: if Mutation does not equal "noOnces"
\*   and doneChan is true, then doneChan and doneCloses are unchanged; else
\*   doneChan in the next state equals TRUE and doneCloses in the next state
\*   equals doneCloses plus 1."
CloseDone ==
    IF Mutation /= "noOnces" /\ doneChan
        THEN UNCHANGED <<doneChan, doneCloses>>
        ELSE doneChan' = TRUE /\ doneCloses' = doneCloses + 1

\* In English: "Where a stop call goes when its Once part is over. Under the
\* "loops" candidate fix, every Stop from outside the engine, first or not,
\* then waits for the loops; a Stop from inside a loop never does, since it
\* would wait for itself."
\* Literally: "AfterStop of p is defined as: if StopJoins equals "loops" and
\*   p equals "user", then "s_join", else ret of p."
AfterStop(p) == IF StopJoins = "loops" /\ p = "user" THEN "s_join" ELSE ret[p]

-----------------------------------------------------------------------------
(* The environment: the peer and the muxer act only until the user calls  *)
(* Stop, so every run after that shows Stop finishing without their help. *)

\* In English: "The peer sends its next message."
\* Literally: "PeerSend is defined as: pc of "user" equals "idle", and sent
\*   is less than the length of Msgs, and wire in the next state equals wire
\*   with element sent plus 1 of Msgs appended, and sent in the next state
\*   equals sent plus 1, and everything else is unchanged."
PeerSend ==
    /\ pc["user"] = "idle" /\ sent < Len(Msgs)
    /\ wire' = Append(wire, Msgs[sent + 1])
    /\ sent' = sent + 1
    /\ UNCHANGED <<pcs, life, chans, rq, cur, hmsg, reply, restarted, badCarry,
                   timerFired>>

\* In English: "The muxer shuts down (its doneChan closes)."
\* Literally: "MuxerStop is defined as: MuxerMayStop is true, and pc of
\*   "user" equals "idle", and muxDone is not true, and muxDone in the next
\*   state equals TRUE, and everything else is unchanged."
MuxerStop ==
    /\ MuxerMayStop /\ pc["user"] = "idle" /\ ~muxDone
    /\ muxDone' = TRUE
    /\ UNCHANGED <<pcs, life, stopChan, readDone, recvDone, sendDone, doneChan,
                   doneCloses, data>>

-----------------------------------------------------------------------------
(* Start, by its owner. *)

\* In English: "Start takes lifecycleMu."
\* Literally: "OwnerLock is defined as: pc of "owner" equals "start", and
\*   lifeMu equals "none", and lifeMu in the next state equals "owner", and
\*   Goto of "owner" and "startCheck", and everything else is unchanged."
OwnerLock ==
    /\ pc["owner"] = "start" /\ lifeMu = "none"
    /\ lifeMu' = "owner"
    /\ Goto("owner", "startCheck")
    /\ UNCHANGED <<started, stopped, once, startedAfterStop, chans, data>>

\* In English: "If the protocol was stopped, start nothing. Otherwise start
\* the done watcher and the four loops, and set started."
\* Literally: "OwnerCheck is defined as: pc of "owner" equals "startCheck",
\*   and if stopped is true and Mutation is not a member of the set
\*   containing "startIgnoresStopped" and "noOnces", then Goto of "owner"
\*   and "startUnlock" and started and startedAfterStop are unchanged; else
\*   pc in the next state maps "owner" to "startUnlock", "rd", "rv" and
\*   "sd" to "wait", "st" to "select" and "w" to "w1", and started in the
\*   next state equals TRUE, and startedAfterStop in the next state equals
\*   stopped; and lifeMu, stopped, once, chans and data are unchanged."
OwnerCheck ==
    /\ pc["owner"] = "startCheck"
    /\ IF stopped /\ Mutation \notin {"startIgnoresStopped", "noOnces"}
          THEN Goto("owner", "startUnlock") /\ UNCHANGED <<started, startedAfterStop>>
          ELSE /\ pc' = [pc EXCEPT !["owner"] = "startUnlock", !["rd"] = "wait",
                                   !["rv"] = "wait", !["sd"] = "wait",
                                   !["st"] = "select", !["w"] = "w1"]
               /\ UNCHANGED <<ret, smode, saw>>
               /\ started' = TRUE
               /\ startedAfterStop' = stopped
    /\ UNCHANGED <<lifeMu, stopped, once, chans, data>>

\* In English: "Start releases lifecycleMu and returns."
\* Literally: "OwnerUnlock is defined as: pc of "owner" equals "startUnlock",
\*   and lifeMu in the next state equals "none", and Goto of "owner" and
\*   "done", and everything else is unchanged."
OwnerUnlock ==
    /\ pc["owner"] = "startUnlock"
    /\ lifeMu' = "none"
    /\ Goto("owner", "done")
    /\ UNCHANGED <<started, stopped, once, startedAfterStop, chans, data>>

-----------------------------------------------------------------------------
(* The user. *)

\* In English: "The user calls Stop once, and is "returned" after it."
\* Literally: "UserStop is defined as: pc of "user" equals "idle", and
\*   CallStop of "user", FALSE and "returned", and everything else is
\*   unchanged."
UserStop ==
    /\ pc["user"] = "idle"
    /\ CallStop("user", FALSE, "returned")
    /\ UNCHANGED <<life, chans, data>>

-----------------------------------------------------------------------------
(* stop(restart) and SendError, inline in the calling goroutine p. *)

\* In English: "onceStop.Do: the first caller runs the body; a caller that
\* comes while the body runs waits for it; a later caller returns at once."
\* Literally: "StopOnce of p is defined as: pc of p equals "s_once", and
\*   either (once equals "idle" and once in the next state equals "running"
\*   and Goto of p and "s_lock"), or (once equals "running" and Goto of p
\*   and "s_onceWait" and once is unchanged), or (once equals "done" and
\*   Goto of p and AfterStop of p and once is unchanged); and the rest of life,
\*   chans and data are unchanged."
StopOnce(p) ==
    /\ pc[p] = "s_once"
    /\ \/ once = "idle" /\ once' = "running" /\ Goto(p, "s_lock")
       \/ once = "running" /\ Goto(p, "s_onceWait") /\ UNCHANGED once
       \/ once = "done" /\ Goto(p, AfterStop(p)) /\ UNCHANGED once
    /\ UNCHANGED <<lifeMu, started, stopped, startedAfterStop, chans, data>>

\* In English: "A second caller of Do returns once the first call's body
\* has returned."
\* Literally: "StopOnceWait of p is defined as: pc of p equals "s_onceWait",
\*   and once equals "done", and Goto of p and AfterStop of p, and
\*   everything else is unchanged."
StopOnceWait(p) ==
    /\ pc[p] = "s_onceWait" /\ once = "done"
    /\ Goto(p, AfterStop(p))
    /\ UNCHANGED <<life, chans, data>>

\* In English: "Take lifecycleMu, set stopped, and read started."
\* Literally: "StopLock of p is defined as: pc of p equals "s_lock", and
\*   lifeMu equals "none", and lifeMu in the next state equals p, and
\*   stopped in the next state equals TRUE, and saw in the next state equals
\*   saw with p mapped to started, and pc in the next state equals pc with p
\*   mapped to (if Mutation equals "waitReadUnderLock" then "s_close" else
\*   "s_unlock"), and the rest is unchanged."
StopLock(p) ==
    /\ pc[p] = "s_lock" /\ lifeMu = "none"
    /\ lifeMu' = p
    /\ stopped' = TRUE
    /\ saw' = [saw EXCEPT ![p] = started]
    /\ pc' = [pc EXCEPT ![p] = IF Mutation = "waitReadUnderLock"
                               THEN "s_close" ELSE "s_unlock"]
    /\ UNCHANGED <<ret, smode, started, once, startedAfterStop, chans, data>>

\* In English: "Release lifecycleMu."
\* Literally: "StopUnlock of p is defined as: pc of p equals "s_unlock", and
\*   lifeMu in the next state equals "none", and Goto of p and "s_close",
\*   and the rest is unchanged."
StopUnlock(p) ==
    /\ pc[p] = "s_unlock"
    /\ lifeMu' = "none"
    /\ Goto(p, "s_close")
    /\ UNCHANGED <<started, stopped, once, startedAfterStop, chans, data>>

\* In English: "Close stopChan; if the loops never started, close doneChan
\* too. A restart of a started protocol then waits for readLoop."
\* Literally: "StopClose of p is defined as: pc of p equals "s_close", and
\*   stopChan in the next state equals TRUE, and (if saw of p is not true
\*   then CloseDone else doneChan and doneCloses are unchanged), and pc in
\*   the next state equals pc with p mapped to (if smode of p and saw of p
\*   are true and Mutation does not equal "noWaitRead" then "s_waitRead"
\*   else "s_unreg"), and the rest is unchanged."
StopClose(p) ==
    /\ pc[p] = "s_close"
    /\ stopChan' = TRUE
    /\ IF ~saw[p] THEN CloseDone ELSE UNCHANGED <<doneChan, doneCloses>>
    /\ pc' = [pc EXCEPT ![p] = IF smode[p] /\ saw[p] /\ Mutation /= "noWaitRead"
                               THEN "s_waitRead" ELSE "s_unreg"]
    /\ UNCHANGED <<ret, smode, saw, life, readDone, recvDone, sendDone, muxDone,
                   data>>

\* In English: "StopForRestart waits on readDoneChan, with no other case."
\* Literally: "StopWaitRead of p is defined as: pc of p equals
\*   "s_waitRead", and readDone is true, and Goto of p and "s_unreg", and
\*   everything else is unchanged."
StopWaitRead(p) ==
    /\ pc[p] = "s_waitRead" /\ readDone
    /\ Goto(p, "s_unreg")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "Suspend (restart) or unregister the role, and leave the
\* Once body. A suspend while readLoop still reads loses its unread data.
\* Under the "loops" fix, a Stop from outside the engine then waits for
\* every loop."
\* Literally: "StopUnreg of p is defined as: pc of p equals "s_unreg", and
\*   once in the next state equals "done", and badCarry in the next state
\*   equals (badCarry is true, or smode of p and saw of p are true and
\*   readDone is not true), and lifeMu in the next state equals (if
\*   Mutation equals "waitReadUnderLock" then "none" else lifeMu), and Goto
\*   of p and AfterStop of p, and the rest is unchanged."
StopUnreg(p) ==
    /\ pc[p] = "s_unreg"
    /\ once' = "done"
    /\ badCarry' = (badCarry \/ (smode[p] /\ saw[p] /\ ~readDone))
    /\ lifeMu' = IF Mutation = "waitReadUnderLock" THEN "none" ELSE lifeMu
    /\ Goto(p, AfterStop(p))
    /\ UNCHANGED <<started, stopped, startedAfterStop, chans, sent, wire, rq, cur,
                   hmsg, reply, restarted, timerFired>>

\* In English: "The candidate fix: wait until every loop has exited."
\* Literally: "StopJoin of p is defined as: pc of p equals "s_join", and for
\*   all l in Loops, pc of l is a member of the set containing "notStarted"
\*   and "exited", and Goto of p and ret of p, and everything else is
\*   unchanged."
StopJoin(p) ==
    /\ pc[p] = "s_join"
    /\ \A l \in Loops : pc[l] \in {"notStarted", "exited"}
    /\ Goto(p, ret[p])
    /\ UNCHANGED <<life, chans, data>>

\* In English: "SendError returns at once if stopChan or doneChan is
\* closed; otherwise it goes on to report the error."
\* Literally: "SeCheck of p is defined as: pc of p equals "se_check", and if
\*   stopChan is true or doneChan is true then Goto of p and ret of p else
\*   Goto of p and "se_send", and everything else is unchanged."
SeCheck(p) ==
    /\ pc[p] = "se_check"
    /\ IF stopChan \/ doneChan THEN Goto(p, ret[p]) ELSE Goto(p, "se_send")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "The non-blocking send to ErrorChan, then Stop."
\* Literally: "SeSend of p is defined as: pc of p equals "se_send", and
\*   CallStop of p, FALSE and ret of p, and everything else is unchanged."
SeSend(p) ==
    /\ pc[p] = "se_send"
    /\ CallStop(p, FALSE, ret[p])
    /\ UNCHANGED <<life, chans, data>>

\* Literally: "StopStep of p is defined as: StopOnce of p, or StopOnceWait
\*   of p, or StopLock of p, or StopUnlock of p, or StopClose of p, or
\*   StopWaitRead of p, or StopUnreg of p, or StopJoin of p, or SeCheck of
\*   p, or SeSend of p."
StopStep(p) ==
    \/ StopOnce(p) \/ StopOnceWait(p) \/ StopLock(p) \/ StopUnlock(p)
    \/ StopClose(p) \/ StopWaitRead(p) \/ StopUnreg(p) \/ StopJoin(p)
    \/ SeCheck(p) \/ SeSend(p)

-----------------------------------------------------------------------------
(* readLoop *)

\* In English: "readLoop's select: leave on stopChan, sendDoneChan or the
\* muxer's doneChan, or take the next segment."
\* Literally: "RdWait is defined as: pc of "rd" equals "wait", and either
\*   (stopChan or sendDone or muxDone is true, and Goto of "rd" and "exit",
\*   and wire and cur are unchanged), or (wire is not empty, and cur in the
\*   next state equals the head of wire, and wire in the next state equals
\*   the tail of wire, and Goto of "rd" and "decode"); and the rest is
\*   unchanged."
RdWait ==
    /\ pc["rd"] = "wait"
    /\ \/ (stopChan \/ sendDone \/ muxDone) /\ Goto("rd", "exit") /\ UNCHANGED <<wire, cur>>
       \/ wire /= <<>> /\ cur' = Head(wire) /\ wire' = Tail(wire) /\ Goto("rd", "decode")
    /\ UNCHANGED <<life, chans, sent, rq, hmsg, reply, restarted, badCarry, timerFired>>

\* In English: "MessageFromCborFunc: a message that fails to decode goes to
\* SendError and readLoop returns. Otherwise MessageReceivedFunc runs and
\* does one of the things it may do."
\* Literally: "RdDecode is defined as: pc of "rd" equals "decode", and if
\*   cur equals "bad" then CallSendError of "rd" and "exit", else there
\*   exists a c in ReceivedCallbacks such that (c equals "returns" and Goto
\*   of "rd" and "queueCheck"), or (c equals "waitsForStopChan" and Goto of
\*   "rd" and "cbWait"), or (c equals "callsStop" and CallStop of "rd",
\*   FALSE and "queueCheck"), or (c equals "callsStopForRestart" and
\*   CallStop of "rd", TRUE and "queueCheck"); and the rest is unchanged."
RdDecode ==
    /\ pc["rd"] = "decode"
    /\ IF cur = "bad"
          THEN CallSendError("rd", "exit")
          ELSE \E c \in ReceivedCallbacks :
                 \/ c = "returns" /\ Goto("rd", "queueCheck")
                 \/ c = "waitsForStopChan" /\ Goto("rd", "cbWait")
                 \/ c = "callsStop" /\ CallStop("rd", FALSE, "queueCheck")
                 \/ c = "callsStopForRestart" /\ CallStop("rd", TRUE, "queueCheck")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "A MessageReceivedFunc that waits for StopChan returns once
\* it closes."
\* Literally: "RdCbWait is defined as: pc of "rd" equals "cbWait", and
\*   stopChan is true, and Goto of "rd" and "queueCheck", and everything
\*   else is unchanged."
RdCbWait ==
    /\ pc["rd"] = "cbWait" /\ stopChan
    /\ Goto("rd", "queueCheck")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "select { case <-stopChan: return; default: } (:2177)."
\* Literally: "RdQueueCheck is defined as: pc of "rd" equals "queueCheck",
\*   and if stopChan is true then Goto of "rd" and "exit" else Goto of "rd"
\*   and "queue", and everything else is unchanged."
RdQueueCheck ==
    /\ pc["rd"] = "queueCheck"
    /\ IF stopChan THEN Goto("rd", "exit") ELSE Goto("rd", "queue")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "Queue the message, or leave on stopChan or the muxer's
\* doneChan. A server leaves after queueing MsgDone, which ends the
\* protocol (:2199)."
\* Literally: "RdQueue is defined as: pc of "rd" equals "queue", and either
\*   (stopChan or muxDone is true, and Goto of "rd" and "exit", and rq is
\*   unchanged), or (the length of rq is less than 1, and rq in the next
\*   state equals rq with cur appended, and Goto of "rd" and (if Role
\*   equals "server" and cur equals "done" then "exit" else "wait")); and
\*   the rest is unchanged."
RdQueue ==
    /\ pc["rd"] = "queue"
    /\ \/ (stopChan \/ muxDone) /\ Goto("rd", "exit") /\ UNCHANGED rq
       \/ /\ Len(rq) < 1
          /\ rq' = Append(rq, cur)
          /\ Goto("rd", IF Role = "server" /\ cur = "done" THEN "exit" ELSE "wait")
    /\ UNCHANGED <<life, chans, sent, wire, cur, hmsg, reply, restarted, badCarry,
                   timerFired>>

\* In English: "readLoop's deferred close(readDoneChan)."
\* Literally: "RdExit is defined as: pc of "rd" equals "exit", and readDone
\*   in the next state equals TRUE, and Goto of "rd" and "exited", and the
\*   rest is unchanged."
RdExit ==
    /\ pc["rd"] = "exit"
    /\ readDone' = TRUE
    /\ Goto("rd", "exited")
    /\ UNCHANGED <<life, stopChan, recvDone, sendDone, doneChan, muxDone,
                   doneCloses, data>>

-----------------------------------------------------------------------------
(* recvLoop *)

\* In English: "recvLoop's select: leave on stopChan, sendDoneChan or the
\* muxer's doneChan, or take a queued message."
\* Literally: "RvWait is defined as: pc of "rv" equals "wait", and either
\*   (stopChan or sendDone or muxDone is true, and Goto of "rv" and "exit",
\*   and rq and hmsg are unchanged), or (rq is not empty, and hmsg in the
\*   next state equals the head of rq, and rq in the next state equals the
\*   tail of rq, and Goto of "rv" and "req"); and the rest is unchanged."
RvWait ==
    /\ pc["rv"] = "wait"
    /\ \/ (stopChan \/ sendDone \/ muxDone) /\ Goto("rv", "exit") /\ UNCHANGED <<rq, hmsg>>
       \/ rq /= <<>> /\ hmsg' = Head(rq) /\ rq' = Tail(rq) /\ Goto("rv", "req")
    /\ UNCHANGED <<life, chans, sent, wire, cur, reply, restarted, badCarry, timerFired>>

\* In English: "requestStateTransition: hand the transition to stateLoop
\* (an unbuffered send, so stateLoop must be at its select), or leave on
\* stopChan or doneChan."
\* Literally: "RvReq is defined as: pc of "rv" equals "req", and either
\*   (stopChan or doneChan is true, and Goto of "rv" and "exit"), or (pc of
\*   "st" equals "select", and pc in the next state equals pc with "rv"
\*   mapped to "reply" and "st" mapped to "reply", and ret, smode and saw
\*   are unchanged); and everything else is unchanged."
RvReq ==
    /\ pc["rv"] = "req"
    /\ \/ (stopChan \/ doneChan) /\ Goto("rv", "exit")
       \/ /\ pc["st"] = "select"
          /\ pc' = [pc EXCEPT !["rv"] = "reply", !["st"] = "reply"]
          /\ UNCHANGED <<ret, smode, saw>>
    /\ UNCHANGED <<life, chans, data>>

\* In English: "Wait for stateLoop's answer, or leave on stopChan or
\* doneChan."
\* Literally: "RvReply is defined as: pc of "rv" equals "reply", and either
\*   (reply is true, and reply in the next state equals FALSE, and Goto of
\*   "rv" and "handler"), or (stopChan or doneChan is true, and Goto of "rv"
\*   and "exit", and reply is unchanged); and the rest is unchanged."
RvReply ==
    /\ pc["rv"] = "reply"
    /\ \/ reply /\ reply' = FALSE /\ Goto("rv", "handler")
       \/ (stopChan \/ doneChan) /\ Goto("rv", "exit") /\ UNCHANGED reply
    /\ UNCHANGED <<life, chans, sent, wire, rq, cur, hmsg, restarted, badCarry,
                   timerFired>>

\* In English: "MessageHandlerFunc. A server's MsgDone handler calls
\* StopForRestart, then starts the next instance. For any other message
\* the handler does one of the things it may do; under the "anyMessage"
\* mutation a server may also restart from it."
\* Literally: "RvHandler is defined as: pc of "rv" equals "handler", and if
\*   hmsg equals "done" then CallStop of "rv", TRUE and "restart", else
\*   either there exists a c in HandlerCallbacks such that (c equals
\*   "returns" and Goto of "rv" and "wait") or (c equals "callsStop" and
\*   CallStop of "rv", FALSE and "wait") or (c equals "waitsForStopChan" and
\*   Goto of "rv" and "hWait") or (c equals "waitsForCaller" and Goto of
\*   "rv" and "hWaitCaller"), or (RestartOn equals "anyMessage" and Role
\*   equals "server" and CallStop of "rv", TRUE and "restart"); and the
\*   rest is unchanged."
RvHandler ==
    /\ pc["rv"] = "handler"
    /\ IF hmsg = "done"
          THEN CallStop("rv", TRUE, "restart")
          ELSE \/ \E c \in HandlerCallbacks :
                    \/ c = "returns" /\ Goto("rv", "wait")
                    \/ c = "callsStop" /\ CallStop("rv", FALSE, "wait")
                    \/ c = "waitsForStopChan" /\ Goto("rv", "hWait")
                    \/ c = "waitsForCaller" /\ Goto("rv", "hWaitCaller")
               \/ RestartOn = "anyMessage" /\ Role = "server"
                  /\ CallStop("rv", TRUE, "restart")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "A handler waiting for StopChan returns once it closes."
\* Literally: "RvHWait is defined as: pc of "rv" equals "hWait", and
\*   stopChan is true, and Goto of "rv" and "wait", and everything else is
\*   unchanged."
RvHWait ==
    /\ pc["rv"] = "hWait" /\ stopChan
    /\ Goto("rv", "wait")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "A handler waiting for the user's Stop call returns once it
\* has returned."
\* Literally: "RvHWaitCaller is defined as: pc of "rv" equals "hWaitCaller",
\*   and pc of "user" equals "returned", and Goto of "rv" and "wait", and
\*   everything else is unchanged."
RvHWaitCaller ==
    /\ pc["rv"] = "hWaitCaller" /\ pc["user"] = "returned"
    /\ Goto("rv", "wait")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "The server installs and starts its next instance."
\* Literally: "RvRestart is defined as: pc of "rv" equals "restart", and
\*   restarted in the next state equals TRUE, and Goto of "rv" and "wait",
\*   and the rest is unchanged."
RvRestart ==
    /\ pc["rv"] = "restart"
    /\ restarted' = TRUE
    /\ Goto("rv", "wait")
    /\ UNCHANGED <<life, chans, sent, wire, rq, cur, hmsg, reply, badCarry,
                   timerFired>>

\* In English: "recvLoop's deferred close(recvDoneChan)."
\* Literally: "RvExit is defined as: pc of "rv" equals "exit", and recvDone
\*   in the next state equals TRUE, and Goto of "rv" and "exited", and the
\*   rest is unchanged."
RvExit ==
    /\ pc["rv"] = "exit"
    /\ recvDone' = TRUE
    /\ Goto("rv", "exited")
    /\ UNCHANGED <<life, stopChan, readDone, sendDone, doneChan, muxDone,
                   doneCloses, data>>

-----------------------------------------------------------------------------
(* sendLoop, stateLoop and the done watcher *)

\* In English: "sendLoop leaves on stopChan or recvDoneChan."
\* Literally: "SdWait is defined as: pc of "sd" equals "wait", and stopChan
\*   or recvDone is true, and Goto of "sd" and "exit", and everything else
\*   is unchanged."
SdWait ==
    /\ pc["sd"] = "wait" /\ (stopChan \/ recvDone)
    /\ Goto("sd", "exit")
    /\ UNCHANGED <<life, chans, data>>

\* In English: "sendLoop closes muxerSendChan (it is the only sender) and
\* sendDoneChan."
\* Literally: "SdExit is defined as: pc of "sd" equals "exit", and sendDone
\*   in the next state equals TRUE, and Goto of "sd" and "exited", and the
\*   rest is unchanged."
SdExit ==
    /\ pc["sd"] = "exit"
    /\ sendDone' = TRUE
    /\ Goto("sd", "exited")
    /\ UNCHANGED <<life, stopChan, readDone, recvDone, doneChan, muxDone,
                   doneCloses, data>>

\* In English: "stateLoop's select: leave on stopChan or doneChan, or the
\* timer fires and SendError runs. (A transition request is taken by
\* RvReq.)"
\* Literally: "StSelect is defined as: pc of "st" equals "select", and
\*   either (stopChan or doneChan is true, and Goto of "st" and "exited",
\*   and timerFired is unchanged), or (TimerFires is true, and timerFired is
\*   not true, and timerFired in the next state equals TRUE, and
\*   CallSendError of "st" and "select"); and the rest is unchanged."
StSelect ==
    /\ pc["st"] = "select"
    /\ \/ (stopChan \/ doneChan) /\ Goto("st", "exited") /\ UNCHANGED timerFired
       \/ TimerFires /\ ~timerFired /\ timerFired' = TRUE
          /\ CallSendError("st", "select")
    /\ UNCHANGED <<life, chans, sent, wire, rq, cur, hmsg, reply, restarted, badCarry>>

\* In English: "setState (TimeoutFunc runs here, and returns), then the
\* answer goes into the request's one-slot errorChan."
\* Literally: "StReply is defined as: pc of "st" equals "reply", and reply in
\*   the next state equals TRUE, and Goto of "st" and "select", and the
\*   rest is unchanged."
StReply ==
    /\ pc["st"] = "reply"
    /\ reply' = TRUE
    /\ Goto("st", "select")
    /\ UNCHANGED <<life, chans, sent, wire, rq, cur, hmsg, restarted, badCarry,
                   timerFired>>

\* In English: "The done watcher waits for recvDoneChan, then sendDoneChan
\* (the watcherRecvOnly mutation skips the second), then closes doneChan."
\* Literally: "Watcher is defined as: either (pc of "w" equals "w1", and
\*   recvDone is true, and Goto of "w" and (if Mutation equals
\*   "watcherRecvOnly" then "w3" else "w2"), and doneChan and doneCloses
\*   are unchanged), or (pc of "w" equals "w2", and sendDone is true, and
\*   Goto of "w" and "w3", and doneChan and doneCloses are unchanged), or
\*   (pc of "w" equals "w3", and CloseDone, and Goto of "w" and "exited");
\*   and the rest is unchanged."
Watcher ==
    /\ \/ pc["w"] = "w1" /\ recvDone
          /\ Goto("w", IF Mutation = "watcherRecvOnly" THEN "w3" ELSE "w2")
          /\ UNCHANGED <<doneChan, doneCloses>>
       \/ pc["w"] = "w2" /\ sendDone /\ Goto("w", "w3")
          /\ UNCHANGED <<doneChan, doneCloses>>
       \/ pc["w"] = "w3" /\ CloseDone /\ Goto("w", "exited")
    /\ UNCHANGED <<life, stopChan, readDone, recvDone, sendDone, muxDone, data>>

-----------------------------------------------------------------------------

\* In English: "Everything is over: Start and Stop have returned and every
\* loop has exited or never started."
\* Literally: "Finished is defined as: pc of "owner" equals "done", and pc
\*   of "user" equals "returned", and for all l in Loops, pc of l is a
\*   member of the set containing "notStarted" and "exited"."
Finished ==
    /\ pc["owner"] = "done" /\ pc["user"] = "returned"
    /\ \A l \in Loops : pc[l] \in {"notStarted", "exited"}

\* In English: "A step is one step of one goroutine, the peer or the muxer;
\* once everything is over, nothing changes. A state with no step that is
\* not Finished is a deadlock, which TLC reports."
\* Literally: "Next is defined as: PeerSend, or MuxerStop, or OwnerLock, or
\*   OwnerCheck, or OwnerUnlock, or UserStop, or there exists a p in Procs
\*   such that StopStep of p, or RdWait, or RdDecode, or RdCbWait, or
\*   RdQueueCheck, or RdQueue, or RdExit, or RvWait, or RvReq, or RvReply,
\*   or RvHandler, or RvHWait, or RvHWaitCaller, or RvRestart, or RvExit,
\*   or SdWait, or SdExit, or StSelect, or StReply, or Watcher, or
\*   (Finished and vars is unchanged)."
Next ==
    \/ PeerSend \/ MuxerStop
    \/ OwnerLock \/ OwnerCheck \/ OwnerUnlock \/ UserStop
    \/ \E p \in Procs : StopStep(p)
    \/ RdWait \/ RdDecode \/ RdCbWait \/ RdQueueCheck \/ RdQueue \/ RdExit
    \/ RvWait \/ RvReq \/ RvReply \/ RvHandler \/ RvHWait \/ RvHWaitCaller
    \/ RvRestart \/ RvExit
    \/ SdWait \/ SdExit \/ StSelect \/ StReply \/ Watcher
    \/ Finished /\ UNCHANGED vars

\* Literally: "Spec is defined as: Init holds at the start, and always,
\*   every step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

\* In English: "DoneChan is closed only after recvLoop and sendLoop have
\* exited (when the loops started): the DoneChan doc and the rule that a
\* handler never sees DoneChan close."
\* Literally: "DoneImpliesRecvSendExited is defined as: if doneChan and
\*   started are true, then pc of "rv" equals "exited" and pc of "sd"
\*   equals "exited"."
DoneImpliesRecvSendExited ==
    doneChan /\ started => pc["rv"] = "exited" /\ pc["sd"] = "exited"

\* In English: "A Start after Stop starts nothing."
\* Literally: "NoLoopAfterStopStart is defined as: startedAfterStop is not
\*   true."
NoLoopAfterStopStart == ~startedAfterStop

\* In English: "doneChan is closed at most once (a second close panics)."
\* Literally: "DoneClosedOnce is defined as: doneCloses is less than or
\*   equal to 1."
DoneClosedOnce == doneCloses <= 1

\* In English: "A restart suspends the role only after readLoop has stopped
\* reading, so everything it read and did not process is carried to the
\* next instance."
\* Literally: "CarryCompleteBeforeNewInstance is defined as: badCarry is not
\*   true."
CarryCompleteBeforeNewInstance == ~badCarry

\* In English: "lifecycleMu is never held by a goroutine that is blocked."
\* Literally: "NoLockAcrossWait is defined as: if lifeMu does not equal
\*   "none", then pc of lifeMu is not a member of Blocking."
NoLockAcrossWait == lifeMu /= "none" => pc[lifeMu] \notin Blocking

\* In English: "StopForRestart never waits on readLoop while readLoop is
\* inside MessageReceivedFunc."
\* Literally: "RestartNeverWaitsOnCallback is defined as: if there exists a
\*   p in Procs such that pc of p equals "s_waitRead", then pc of "rd" does
\*   not equal "cbWait", and not (pc of "rd" is a member of the set
\*   containing "s_once", "s_onceWait", "s_lock", "s_unlock", "s_close",
\*   "s_waitRead" and "s_unreg", and ret of "rd" equals "queueCheck")."
RestartNeverWaitsOnCallback ==
    (\E p \in Procs : pc[p] = "s_waitRead") =>
        /\ pc["rd"] /= "cbWait"
        /\ ~(pc["rd"] \in {"s_once", "s_onceWait", "s_lock", "s_unlock",
                           "s_close", "s_waitRead", "s_unreg"}
             /\ ret["rd"] = "queueCheck")

\* In English: "Once the user's Stop has returned, every goroutine the
\* engine started has exited (the join)."
\* Literally: "JoinedAfterStop is defined as: if pc of "user" equals
\*   "returned", then for all l in Loops, pc of l is a member of the set
\*   containing "notStarted" and "exited"."
JoinedAfterStop ==
    pc["user"] = "returned" => \A l \in Loops : pc[l] \in {"notStarted", "exited"}

(* Reachability probes: each is expected to be violated. *)

\* In English: "Probe: a server never restarts."
\* Literally: "ProbeNeverRestarts is defined as: restarted is not true."
ProbeNeverRestarts == ~restarted

\* In English: "Probe: no loop runs after doneChan closed."
\* Literally: "ProbeNoLoopAfterDone is defined as: if doneChan is true, then
\*   pc of "st" and pc of "rd" are members of the set containing
\*   "notStarted" and "exited"."
ProbeNoLoopAfterDone ==
    doneChan => pc["st"] \in {"notStarted", "exited"} /\ pc["rd"] \in {"notStarted", "exited"}

\* In English: "Probe: Stop never runs before Start, leaving Start to start
\* nothing."
\* Literally: "ProbeNoStopBeforeStart is defined as: not (pc of "owner"
\*   equals "done", and stopped is true, and started is not true)."
ProbeNoStopBeforeStart == ~(pc["owner"] = "done" /\ stopped /\ ~started)
=============================================================================
