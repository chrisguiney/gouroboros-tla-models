---------------------- MODULE LeiosNotifyServerRestart ----------------------
(***************************************************************************)
(* The gOuroboros LeiosNotify server's goroutines across a restart, and    *)
(* what Server.Stop waits for (protocol/leiosnotify/server.go:             *)
(* messageHandler, serveRequestNext, releaseLateNotification,              *)
(* deliverNotification, handleQuit, Stop; protocol/protocol.go: RunLoop,   *)
(* StopForRestart, join).                                                   *)
(*                                                                         *)
(* One request of the first run. The server runs the user's               *)
(* RequestNextFunc (the "source") on a RunLoop goroutine of the instance   *)
(* that read the request, and a second RunLoop goroutine (the "request")   *)
(* waits for the source's answer, the client's MsgQuit, or the instance's  *)
(* DoneChan:                                                               *)
(*   - answer first: send it, then call ResponseSentFunc with the send's   *)
(*     result;                                                             *)
(*   - quit first: send MsgCanceled and leave a third RunLoop goroutine    *)
(*     (the "late" one) waiting for the source, which hands a notification *)
(*     it returns later to ResponseSentFunc with ErrRequestCanceled;       *)
(*   - DoneChan first: leave the late goroutine, send nothing.             *)
(* MsgQuit is read at once (MessageReceivedFunc fires QuitChan) but        *)
(* handled only once the request is answered, since the protocol holds a   *)
(* message back until the state allows it [G3]. handleQuit sends MsgDone,  *)
(* stops the instance with StopForRestart, and installs a second instance  *)
(* unless Stop has run. The first instance's goroutines may still be       *)
(* running then: a source that ignores QuitChan, the late goroutine, or    *)
(* the request goroutine's ResponseSentFunc call.                          *)
(*                                                                         *)
(* Server.Stop(ctx) marks the server stopped, stops the current instance   *)
(* and waits for its goroutines.                                           *)
(*   7cd17437:  it waits for the current instance only, so a callback of   *)
(*              the retired first instance can run after Stop returned     *)
(*              (LeiosNotifyServerRestartRetiredBug.cfg).                  *)
(*   fix:       handleQuit records the retired instance and Stop waits for *)
(*              it too (LeiosNotifyServerRestart.cfg).                     *)
(*                                                                         *)
(* Stop from a callback. Stop's doc says that with the Context of a        *)
(* CallbackContext it returns without waiting, since it would wait for the *)
(* goroutine running the callback. CallbackStop lets two callbacks call    *)
(* Stop with their own context: the first run's ResponseSentFunc (request  *)
(* or late goroutine, on the retired instance once the restart happened)   *)
(* and the second run's RequestNextFunc (on the second instance).          *)
(*   bf0d7a47:  Protocol.join skips only the instance whose callback       *)
(*              context it gets, so a callback's Stop waits for every      *)
(*              other instance, current and retired. Each of the two       *)
(*              callbacks then waits for the other's instance: deadlock    *)
(*              (LeiosNotifyServerRestartCallbackStopWaitsBug.cfg,         *)
(*              LeiosNotifyServerRestartCallbackStopDeadlockBug.cfg). Two  *)
(*              retired runs whose callbacks call Stop form the same cycle.*)
(*   97045bac:  a callback context of the current or a retired instance    *)
(*              only signals stop (LeiosNotifyServerRestartCallbackStop.cfg).*)
(*                                                                         *)
(* Granularity: one step per select choice, per send, per user callback    *)
(* start and return, per lock-protected update.                            *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoCallbackAfterStop  once Stop has returned nil, no goroutine of any  *)
(*                        instance runs a user callback or is still alive. *)
(*   ReplyOnOwnInstance   the answer to the request goes out on the first  *)
(*                        instance, the one that read it.                  *)
(*   ResponseSentOnce     ResponseSentFunc sees the notification at most   *)
(*                        once.                                            *)
(*   CallbackStopDoesNotWait  Stop called from a callback waits for no      *)
(*                        instance.                                        *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [G3] gOuroboros 7cd17437, protocol/protocol.go: a message whose state *)
(*        does not allow it yet is held back; RunLoop goroutines are in    *)
(*        the instance's join; join skips only the instance whose          *)
(*        callback context it is given.                                    *)
(*   [R5] ouroboros-consensus ec239d57f618, LeiosNotify/Server.hs 51-134:  *)
(*        after MsgQuit every outstanding request is answered with         *)
(*        MsgCanceled, then MsgDone.                                       *)
(*   [R11] ouroboros-network 5f356486ab3e, InboundGovernor.hs 455-470: a   *)
(*        responder that ended cleanly is run again, as a new thread.      *)
(*   [R14] ouroboros-network 5f356486ab3e, network-mux Network/Mux.hs      *)
(*        280-287: the mux waits for a mini-protocol's threads before it   *)
(*        returns.                                                         *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `src`, `req`, `late`, `quitter` and `stopper` are program      *)
(*   counters.                                                             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    JoinRetired,    \* TRUE: Stop also waits for instances retired by a
                    \*   restart (the fix); FALSE: 7cd17437
    HoldQuit,       \* TRUE: MsgQuit is handled only once the request is
                    \*   answered [G3]; FALSE: a mutation that handles it at once
    CallbackStop    \* "none": no callback calls Stop; "skipOwn": a callback's
                    \*   Stop waits for every instance but its own (bf0d7a47);
                    \*   "signal": a callback's Stop only signals (97045bac)

\* In English: "The two protocol instances: the first run's and the one the
\* restart installs."
\* Literally: "Instances is defined as the set containing 1 and 2."
Instances == {1, 2}

VARIABLES
    cur,        \* the instance Server.ProtocolInstance returns
    inst,       \* inst[i]: "unborn", "running" or "stopped"
    retired,    \* the instances handleQuit has recorded for Stop
    stopped,    \* Server.stopped
    src,        \* the source: "running" or "returned" (with a notification)
    req,        \* the request goroutine: "wait", "send", "callback",
                \*   "cancel" or "done"
    late,       \* the late-notification goroutine: "none", "wait",
                \*   "callback" or "done"
    quitRead,   \* the client's MsgQuit has been read (QuitChan closed)
    quitter,    \* handleQuit: "idle", "restarting" or "done"
    replyOn,    \* the instance the answer went out on, 0 before it does
    sentCalls,  \* how many times ResponseSentFunc has been called
    stopper,    \* Server.Stop: "idle", "joining" or "returned"
    joinSet,    \* the instances Stop waits for
    src2,       \* the second run's RequestNextFunc: "none", "running" or
                \*   "done"
    cbStop,     \* cbStop[o]: Stop called by a callback of instance o:
                \*   "idle", "joining" or "returned"
    cbJoin,     \* cbJoin[o]: the instances that Stop waits for
    cbAt        \* cbAt[o]: the current instance when that Stop was called,
                \*   0 before

\* Literally: "vars is defined as the tuple of all seventeen variables."
vars == <<cur, inst, retired, stopped, src, req, late, quitRead, quitter,
          replyOn, sentCalls, stopper, joinSet, src2, cbStop, cbJoin, cbAt>>

\* Literally: "others is defined as the tuple of src2, cbStop, cbJoin and
\*   cbAt", the variables only the callback Stop steps change.
others == <<src2, cbStop, cbJoin, cbAt>>

\* In English: "The request has been read on the first instance, whose
\* source and request goroutines are running; nothing else has happened."
\* Literally: "Init is defined as: cur equals 1, inst maps 1 to "running"
\*   and 2 to "unborn", retired is empty, stopped is false, src equals
\*   "running", req equals "wait", late equals "none", quitRead is false,
\*   quitter equals "idle", replyOn equals 0, sentCalls equals 0, stopper
\*   equals "idle", joinSet is empty, src2 equals "none", and no callback
\*   has called Stop."
Init ==
    /\ cur = 1
    /\ inst = [i \in Instances |-> IF i = 1 THEN "running" ELSE "unborn"]
    /\ retired = {}
    /\ stopped = FALSE
    /\ src = "running"
    /\ req = "wait"
    /\ late = "none"
    /\ quitRead = FALSE
    /\ quitter = "idle"
    /\ replyOn = 0
    /\ sentCalls = 0
    /\ stopper = "idle"
    /\ joinSet = {}
    /\ src2 = "none"
    /\ cbStop = [o \in Instances |-> "idle"]
    /\ cbJoin = [o \in Instances |-> {}]
    /\ cbAt = [o \in Instances |-> 0]

-----------------------------------------------------------------------------
(* The first instance's goroutines. *)

\* In English: "The source returns a notification, whenever it likes: one
\* that ignores QuitChan may do so long after the run is over."
\* Literally: "SourceReturns is defined as: src equals "running", and src
\*   becomes "returned"."
SourceReturns ==
    /\ src = "running"
    /\ src' = "returned"
    /\ UNCHANGED <<cur, inst, retired, stopped, req, late, quitRead, quitter,
                   replyOn, sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "The request goroutine takes the answer and sends it on the
\* instance ProtocolInstance returns now. If the answer is ready the select
\* takes it even when QuitChan is closed too: the inner select prefers it."
\* Literally: "ReqAnswer is defined as: req equals "wait", src equals
\*   "returned", replyOn becomes cur, and req becomes "send"."
ReqAnswer ==
    /\ req = "wait" /\ src = "returned"
    /\ replyOn' = cur                                  \* SendMessageAndWait(resp)
    /\ req' = "send"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, late, quitRead, quitter,
                   sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "The send has returned; the goroutine calls ResponseSentFunc."
\* Literally: "ReqCallback is defined as: req equals "send", and req
\*   becomes "callback"."
ReqCallback ==
    /\ req = "send"
    /\ req' = "callback"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, late, quitRead, quitter,
                   replyOn, sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "ResponseSentFunc returns and the request goroutine ends."
\* Literally: "ReqCallbackEnds is defined as: req equals "callback",
\*   sentCalls goes up by one, and req becomes "done"."
ReqCallbackEnds ==
    /\ req = "callback"
    /\ cbStop[1] # "joining"
    /\ sentCalls' = sentCalls + 1
    /\ req' = "done"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, late, quitRead, quitter,
                   replyOn, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "QuitChan closed while the source still runs: the request
\* goroutine starts the late goroutine on the instance ProtocolInstance
\* returns, then sends MsgCanceled."
\* Literally: "ReqQuit is defined as: req equals "wait", quitRead is true,
\*   src equals "running", late becomes "wait", and req becomes "cancel"."
ReqQuit ==
    /\ req = "wait" /\ quitRead /\ src = "running"
    /\ late' = "wait"                                  \* releaseLateNotification
    /\ req' = "cancel"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, quitRead, quitter,
                   replyOn, sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "MsgCanceled goes out, and the request goroutine ends."
\* Literally: "ReqCancelSent is defined as: req equals "cancel", replyOn
\*   becomes cur, and req becomes "done"."
ReqCancelSent ==
    /\ req = "cancel"
    /\ replyOn' = cur                                  \* SendMessageAndWait(MsgCanceled)
    /\ req' = "done"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, late, quitRead, quitter,
                   sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "The first instance is stopped while the request waits: the
\* goroutine leaves the late goroutine to release the notification and
\* ends without sending."
\* Literally: "ReqDone is defined as: req equals "wait", inst of 1 equals
\*   "stopped", src equals "running", late becomes "wait", and req becomes
\*   "done"."
ReqDone ==
    /\ req = "wait" /\ inst[1] = "stopped" /\ src = "running"
    /\ late' = "wait"
    /\ req' = "done"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, quitRead, quitter,
                   replyOn, sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "The late goroutine gets the notification and calls
\* ResponseSentFunc with the reason it was not sent."
\* Literally: "LateCallback is defined as: late equals "wait", src equals
\*   "returned", and late becomes "callback"."
LateCallback ==
    /\ late = "wait" /\ src = "returned"
    /\ late' = "callback"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, quitRead, quitter,
                   replyOn, sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "ResponseSentFunc returns and the late goroutine ends."
\* Literally: "LateEnds is defined as: late equals "callback", sentCalls
\*   goes up by one, and late becomes "done"."
LateEnds ==
    /\ late = "callback"
    /\ cbStop[1] # "joining"
    /\ sentCalls' = sentCalls + 1
    /\ late' = "done"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, quitRead, quitter,
                   replyOn, stopper, joinSet>>
    /\ UNCHANGED others

-----------------------------------------------------------------------------
(* The client's MsgQuit and the restart. *)

\* In English: "The client's MsgQuit is read: MessageReceivedFunc closes
\* QuitChan at once."
\* Literally: "QuitRead is defined as: quitRead is false, inst of 1 equals
\*   "running", and quitRead becomes true."
QuitRead ==
    /\ ~quitRead /\ inst[1] = "running"
    /\ quitRead' = TRUE
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, late, quitter,
                   replyOn, sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "handleQuit runs once the request is answered (or at once,
\* in the mutation): it sends MsgDone, stops the first instance with
\* StopForRestart, which does not wait for it, and, with the fix, records
\* it for Stop."
\* Literally: "QuitHandled is defined as: quitRead is true, quitter equals
\*   "idle", inst of 1 equals "running", HoldQuit implies replyOn is not 0,
\*   inst of 1 becomes "stopped", retired gains 1 if JoinRetired, and
\*   quitter becomes "restarting"."
QuitHandled ==
    /\ quitRead /\ quitter = "idle" /\ inst[1] = "running"
    /\ HoldQuit => replyOn # 0                         \* held back until Idle [G3]
    /\ inst' = [inst EXCEPT ![1] = "stopped"]          \* StopForRestart
    /\ retired' = IF JoinRetired THEN retired \cup {1} ELSE retired
    /\ quitter' = "restarting"
    /\ UNCHANGED <<cur, stopped, src, req, late, quitRead, replyOn,
                   sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

\* In English: "initProtocol, under the server's lock: unless Stop has run,
\* the second instance becomes current and starts."
\* Literally: "Restart is defined as: quitter equals "restarting", quitter
\*   becomes "done", and if stopped then nothing else changes, else cur
\*   becomes 2 and inst of 2 becomes "running"."
Restart ==
    /\ quitter = "restarting"
    /\ quitter' = "done"
    /\ IF stopped
          THEN UNCHANGED <<cur, inst>>                 \* CancelRestart
          ELSE /\ cur' = 2
               /\ inst' = [inst EXCEPT ![2] = "running"]
    /\ UNCHANGED <<retired, stopped, src, req, late, quitRead, replyOn,
                   sentCalls, stopper, joinSet>>
    /\ UNCHANGED others

-----------------------------------------------------------------------------
(* Server.Stop, called by the user with a context that does not end. *)

\* In English: "Stop marks the server stopped and, under the same lock,
\* takes the current instance and the retired ones; it stops the current
\* one."
\* Literally: "StopStarts is defined as: stopper equals "idle", stopped
\*   becomes true, joinSet becomes the set containing cur, joined with
\*   retired, inst of cur becomes "stopped", and stopper becomes "joining"."
StopStarts ==
    /\ stopper = "idle"
    /\ stopped' = TRUE
    /\ joinSet' = {cur} \cup retired
    /\ inst' = [inst EXCEPT ![cur] = "stopped"]
    /\ stopper' = "joining"
    /\ UNCHANGED <<cur, retired, src, req, late, quitRead, quitter, replyOn,
                   sentCalls>>
    /\ UNCHANGED others

\* In English: "Instance i has no goroutine left: the first instance's
\* source, request and late goroutines have ended, or the second
\* instance's source has. The engine loops end once an instance is
\* stopped, so they are not modelled."
\* Literally: "Quiet of i is defined as: i equals 2 and src2 is "none" or
\*   "done"; or i equals 1 and src does not equal "running" and req equals
\*   "done" and late is "none" or "done"."
Quiet(i) ==
    \/ i = 2 /\ src2 \in {"none", "done"}
    \/ /\ i = 1
       /\ src # "running"
       /\ req = "done"
       /\ late \in {"none", "done"}

\* In English: "Stop returns nil once every instance it waits for is
\* quiet."
\* Literally: "StopReturns is defined as: stopper equals "joining", every i
\*   in joinSet is Quiet, and stopper becomes "returned"."
StopReturns ==
    /\ stopper = "joining"
    /\ \A i \in joinSet : Quiet(i)
    /\ stopper' = "returned"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, late, quitRead,
                   quitter, replyOn, sentCalls, joinSet>>
    /\ UNCHANGED others

-----------------------------------------------------------------------------
(* The second run's source, and Stop called from a callback. *)

\* In English: "The second instance reads the client's next request and
\* runs RequestNextFunc on one of its RunLoop goroutines."
\* Literally: "Src2Starts is defined as: CallbackStop does not equal
\*   "none", cur equals 2, inst of 2 equals "running", src2 equals "none",
\*   and src2 becomes "running"."
Src2Starts ==
    /\ CallbackStop # "none"
    /\ cur = 2 /\ inst[2] = "running" /\ src2 = "none"
    /\ src2' = "running"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, late, quitRead,
                   quitter, replyOn, sentCalls, stopper, joinSet, cbStop,
                   cbJoin, cbAt>>

\* In English: "The second run's source returns, unless it is inside Stop."
\* Literally: "Src2Returns is defined as: src2 equals "running", cbStop of
\*   2 does not equal "joining", and src2 becomes "done"."
Src2Returns ==
    /\ src2 = "running" /\ cbStop[2] # "joining"
    /\ src2' = "done"
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, late, quitRead,
                   quitter, replyOn, sentCalls, stopper, joinSet, cbStop,
                   cbJoin, cbAt>>

\* In English: "A user callback of instance o is running: ResponseSentFunc
\* on the first instance, RequestNextFunc on the second."
\* Literally: "InCallback of o is defined as: o equals 1 and req or late
\*   equals "callback"; or o equals 2 and src2 equals "running"."
InCallback(o) ==
    \/ o = 1 /\ (req = "callback" \/ late = "callback")
    \/ o = 2 /\ src2 = "running"

\* In English: "A callback of instance o calls Stop with its
\* CallbackContext's Context. Stop marks the server stopped and stops the
\* current instance, as from the user. bf0d7a47 then waits for every
\* instance it would join but the callback's own; 97045bac waits for none."
\* Literally: "CallbackStopStarts of o is defined as: CallbackStop does not
\*   equal "none", InCallback of o, cbStop of o equals "idle", stopped
\*   becomes true, inst of cur becomes "stopped", cbJoin of o becomes (if
\*   CallbackStop equals "skipOwn" then the set containing cur joined with
\*   retired, without o, else empty), cbAt of o becomes cur, and cbStop of
\*   o becomes "joining"."
CallbackStopStarts(o) ==
    /\ CallbackStop # "none"
    /\ InCallback(o) /\ cbStop[o] = "idle"
    /\ stopped' = TRUE
    /\ inst' = [inst EXCEPT ![cur] = "stopped"]
    /\ cbJoin' = [cbJoin EXCEPT ![o] = IF CallbackStop = "skipOwn"
                                          THEN ({cur} \cup retired) \ {o}
                                          ELSE {}]
    /\ cbAt' = [cbAt EXCEPT ![o] = cur]
    /\ cbStop' = [cbStop EXCEPT ![o] = "joining"]
    /\ UNCHANGED <<cur, retired, src, req, late, quitRead, quitter, replyOn,
                   sentCalls, stopper, joinSet, src2>>

\* In English: "That Stop returns once every instance it waits for is
\* quiet, at once when it waits for none."
\* Literally: "CallbackStopReturns of o is defined as: cbStop of o equals
\*   "joining", every i in cbJoin of o is Quiet, and cbStop of o becomes
\*   "returned"."
CallbackStopReturns(o) ==
    /\ cbStop[o] = "joining"
    /\ \A i \in cbJoin[o] : Quiet(i)
    /\ cbStop' = [cbStop EXCEPT ![o] = "returned"]
    /\ UNCHANGED <<cur, inst, retired, stopped, src, req, late, quitRead,
                   quitter, replyOn, sentCalls, stopper, joinSet, src2,
                   cbJoin, cbAt>>

\* In English: "Everything that can happen has happened."
\* Literally: "Finished is defined as: stopper equals "returned", and Quiet
\*   of 1 and of 2, and quitter is "idle" or "done"."
Finished ==
    /\ stopper = "returned"
    /\ Quiet(1) /\ Quiet(2)
    /\ quitter \in {"idle", "done"}

\* In English: "A step is one of the steps above, or nothing once finished."
\* Literally: "Next is defined as the disjunction of every action above, or
\*   Finished and vars unchanged."
Next ==
    \/ SourceReturns
    \/ ReqAnswer \/ ReqCallback \/ ReqCallbackEnds
    \/ ReqQuit \/ ReqCancelSent \/ ReqDone
    \/ LateCallback \/ LateEnds
    \/ QuitRead \/ QuitHandled \/ Restart
    \/ StopStarts \/ StopReturns
    \/ Src2Starts \/ Src2Returns
    \/ \E o \in Instances : CallbackStopStarts(o) \/ CallbackStopReturns(o)
    \/ Finished /\ UNCHANGED vars

\* Literally: "Spec is defined as: Init holds at the start, and always,
\*   every step is a Next step or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Every variable holds the kind of value it should."
TypeOK ==
    /\ cur \in Instances
    /\ inst \in [Instances -> {"unborn", "running", "stopped"}]
    /\ retired \subseteq Instances
    /\ stopped \in BOOLEAN
    /\ src \in {"running", "returned"}
    /\ req \in {"wait", "send", "callback", "cancel", "done"}
    /\ late \in {"none", "wait", "callback", "done"}
    /\ quitRead \in BOOLEAN
    /\ quitter \in {"idle", "restarting", "done"}
    /\ replyOn \in {0} \cup Instances
    /\ sentCalls \in 0..2
    /\ stopper \in {"idle", "joining", "returned"}
    /\ joinSet \subseteq Instances
    /\ src2 \in {"none", "running", "done"}
    /\ cbStop \in [Instances -> {"idle", "joining", "returned"}]
    /\ cbJoin \in [Instances -> SUBSET Instances]
    /\ cbAt \in [Instances -> {0} \cup Instances]

\* In English: "Once the user's Stop has returned nil, no goroutine of
\* either instance is left: no user callback runs or can still start."
\* Literally: "NoCallbackAfterStop is defined as: stopper equals "returned"
\*   implies Quiet of 1 and Quiet of 2."
NoCallbackAfterStop == stopper = "returned" => Quiet(1) /\ Quiet(2)

\* In English: "Stop called from a callback waits for no instance, as its
\* doc says." It fails when a callback's Stop joins another instance,
\* which may be running a callback that is itself in Stop.
\* Literally: "CallbackStopDoesNotWait is defined as: for every o in
\*   Instances, cbJoin of o is empty."
CallbackStopDoesNotWait == \A o \in Instances : cbJoin[o] = {}

\* In English: "The answer goes out on the instance that read the request."
\* Literally: "ReplyOnOwnInstance is defined as: replyOn is 0 or 1."
ReplyOnOwnInstance == replyOn \in {0, 1}

\* In English: "ResponseSentFunc sees the one notification at most once."
\* Literally: "ResponseSentOnce is defined as: sentCalls is at most 1."
ResponseSentOnce == sentCalls <= 1

\* Probe, EXPECTED to be violated: "Stop is never called after the restart
\* while the retired instance's source still runs."
ProbeStopAfterRestartWhileSourceRuns ==
    ~(stopper = "joining" /\ cur = 2 /\ src = "running")

\* Probe, EXPECTED to be violated: "The retired run's callback and the
\* second run's source never both call Stop after the restart", the
\* interleaving that deadlocks at bf0d7a47.
ProbeCallbacksStopAfterRestart ==
    ~(cbAt[1] = 2 /\ cbAt[2] = 2)
=============================================================================
