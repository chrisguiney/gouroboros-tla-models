-------------------------- MODULE ChainSyncTipWorker --------------------------
(***************************************************************************)
(* Model `chainsync`, slice 5: the GetCurrentTip worker, Stop's wait for   *)
(* busyMutex, and GetAvailableBlockRange, as the code is now.              *)
(*                                                                         *)
(* Based on protocol/chainsync/client.go (gOuroboros 7cd17437):            *)
(*   GetCurrentTip   takes an operation slot, starts a worker goroutine    *)
(*                   and waits for the worker's answer or DoneChan, then   *)
(*                   joins the worker. The worker locks busyMutex          *)
(*                   (Lock, or lockBusy ending on StopChan with the fix),  *)
(*                   returns if the client stopped, registers              *)
(*                   for an intersect answer, sends MsgFindIntersect with  *)
(*                   no points and waits for its own answer or DoneChan.   *)
(*                   It does not check that the protocol is idle: the      *)
(*                   engine holds the message until agency returns.        *)
(*   GetAvailableBlockRange  locks busyMutex, takes a slot, refuses if a   *)
(*                   MsgRequestNext is unanswered, sends MsgFindIntersect, *)
(*                   then MsgRequestNext until the first block after the   *)
(*                   intersection arrives, and waits until every request   *)
(*                   is retired before it releases busyMutex.              *)
(*   Jump            locks busyMutex (blocking), takes a slot, refuses if  *)
(*                   a MsgRequestNext is unanswered, sends                 *)
(*                   MsgFindIntersect and waits for its answer or          *)
(*                   DoneChan. The handler runs IntersectFoundFunc before  *)
(*                   it hands Jump the answer, so Jump holds busyMutex     *)
(*                   until that callback returns.                          *)
(*   Stop            marks the client Stopping, then polls TryLock on      *)
(*                   busyMutex every 10 ms for up to 5 s (stopRunning),    *)
(*                   then sends MsgDone if it can (finishStop), signals    *)
(*                   the protocol to stop, and waits for DoneChan and the  *)
(*                   operation slots, or for ctx. DoneChan closes only     *)
(*                   once the receive loop, which runs every callback,     *)
(*                   has returned.                                         *)
(*                                                                         *)
(* Questions:                                                              *)
(*   - Does every answer reach the call that asked, and does               *)
(*     GetAvailableBlockRange build its range only from its own replies    *)
(*     and leave nothing unretired?                                        *)
(*   - Does GetCurrentTip join its worker before returning?                *)
(*   - Does Stop honour its ctx and the callback marker while it waits for *)
(*     busyMutex, as its doc comment says?                                 *)
(*   - Does Stop always return, including when a callback is the caller   *)
(*     of GetCurrentTip, and when that callback is IntersectFoundFunc, so  *)
(*     the worker waits for busyMutex held by the Jump the callback        *)
(*     blocks?                                                             *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex:                                  *)
(*   [C1] 838-848, 893-908: MsgFindIntersect and MsgDone only from         *)
(*        StIdle; StIntersect is answered by exactly one                   *)
(*        MsgIntersectFound or MsgIntersectNotFound.                       *)
(*   [P1] 2180-2208: replies come back in request order.                   *)
(*   gOuroboros, blinklabs-io/gouroboros 7cd17437:                         *)
(*   [G1] protocol/chainsync/client.go: GetCurrentTip (worker),            *)
(*        GetAvailableBlockRange, Jump, findIntersect, lockBusy,           *)
(*        prepareIdleProtocol, handleIntersectFound,                       *)
(*        waitRequestNextRetired, Stop, stopRunning, finishStop,           *)
(*        abandonIfOwed, messageHandler and its handlers.                  *)
(*   [G2] protocol/protocol.go: a queued message waits for agency          *)
(*        (sendLoop); DoneChan closes after recvLoop and sendLoop return   *)
(*        (Start); StopChan closes at once (stop).                         *)
(*   Lock, ctx and goroutine rules are gOuroboros implementation choices;  *)
(*   the network specification does not describe them, so [G1]/[G2] are   *)
(*   their only source.                                                    *)
(*                                                                         *)
(* Abstractions: one sync MsgRequestNext may be outstanding when the calls *)
(* start (its loop sends nothing more); the server rolls back at most     *)
(* once for GetAvailableBlockRange; the 5 s deadline is Deadline polls;    *)
(* MsgDone's 250 ms send window is one atomic step that succeeds only      *)
(* when nothing is outstanding.                                            *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    SyncOutstanding,   \* TRUE: one sync MsgRequestNext is unanswered at the start
    AtTip,             \* TRUE: the server may withhold that reply for ever
                       \* (MsgAwaitReply at the tip; node-to-client has no timeout)
    WithTip,           \* TRUE: a goroutine calls GetCurrentTip
    WithRange,         \* TRUE: a goroutine calls GetAvailableBlockRange
    CallbackCallsTip,  \* TRUE: the callback for the sync's roll calls GetCurrentTip
    StopFrom,          \* "none", "outside" (a goroutine) or "callback" (the
                       \* sync's roll callback, with its CallbackContext)
    StopCtxExpires,    \* TRUE: the outside Stop's ctx may expire
    Deadline,          \* TryLock polls before Stop gives up on busyMutex
    StopHonoursCtx,    \* FALSE today. TRUE: Stop's wait for busyMutex also
                       \* ends on ctx and does not wait at all in a callback
    TipWatchesStop,    \* FALSE today. TRUE: GetCurrentTip and its worker also
                       \* return on StopChan, not only DoneChan
    WorkerLockWatchesStop, \* FALSE today. TRUE: the worker takes busyMutex
                       \* with lockBusy, which also ends on StopChan
    WithJump,          \* TRUE: a goroutine calls Jump, and its
                       \* IntersectFoundFunc calls GetCurrentTip
    RangeWaitsRetired, \* TRUE in the code; FALSE is a mutation
    TipJoinsWorker     \* TRUE in the code; FALSE is a mutation

\* In English: "At most one GetCurrentTip, and at most one thing runs in the
\* sync's roll callback."
ASSUME /\ ~(WithTip /\ CallbackCallsTip)
       /\ ~(CallbackCallsTip /\ StopFrom = "callback")
       /\ WithJump => ~WithTip /\ ~CallbackCallsTip /\ ~WithRange
       /\ StopFrom \in {"none", "outside", "callback"}
       /\ Deadline \in Nat

\* In English: "The value of busyMutex or a want slot when it is empty."
None == "none"

\* In English: "A message is a record of its kind and the call it belongs to."
Msg(k, f) == [k |-> k, f |-> f]

VARIABLES
    busy,          \* who holds busyMutex: None, "worker", "range", "jump"
                   \* or "stop"
    life,          \* lifecycleState: "running", "stopping", "stopped"
    ops,           \* operation slots held (activeOperations)
    opc,           \* GetCurrentTip's next step
    wpc,           \* its worker's next step
    wAns,          \* TRUE once the worker's own answer was handed to it
    wres,          \* what the worker reported: "none", "own" or "err"
    tres,          \* what GetCurrentTip returned: "none", "own" or "err"
    gpc,           \* GetAvailableBlockRange's next step
    gIF,           \* the intersect answer it received: "none", "Found", "FoundAtTip"
    gTip,          \* who sent the tip it received: "none", "range", "sync", "worker"
    gFirst,        \* who sent the first block it received: "none", "range", "sync"
    gres,          \* what it returned: "none", "ok", "empty", "inprogress", "err"
    backed,        \* TRUE once the server rolled back for it
    wantIF,        \* wantIntersectFoundChan's slot: None, "worker" or "range"
    wantTip,       \* TRUE while wantCurrentTipChan holds a channel
    wantFB,        \* TRUE while wantFirstBlockChan holds a channel
    ready,         \* signals waiting in readyForNextBlockChan
    outstanding,   \* outstandingRequestNext
    sendQ,         \* client messages queued in the engine
    inflight,      \* client messages the server has not answered, in order
    toClient,      \* server replies not yet taken by the handler, in order
    hpc,           \* the handler (recvLoop): "idle", or its next step
    hmsg,          \* the reply the handler is working on
    misrouted,     \* TRUE once an answer went to a call that did not ask
    orphan,        \* TRUE once a MsgIntersectFound arrived with nobody registered
    spc,           \* Stop's next step
    stopHeld,      \* TRUE if Stop got busyMutex
    ticks,         \* TryLock polls Stop has made
    ticksAfterCtx, \* polls made after Stop's ctx was done
    ctxDone,       \* TRUE once the outside Stop's ctx is done
    doneSent,      \* TRUE once MsgDone is on the wire
    closed,        \* TRUE once abandonIfOwed closed the connection
    stopSig,       \* TRUE once StopChan is closed
    recvExited,    \* TRUE once recvLoop returned (DoneChan closes)
    jpc,           \* Jump's next step
    jAns,          \* TRUE once Jump's own answer was handed to it
    jres           \* what Jump returned: "none", "ok", "inprogress", "err"

vars == <<busy, life, ops, opc, wpc, wAns, wres, tres, gpc, gIF, gTip, gFirst,
          gres, backed, wantIF, wantTip, wantFB, ready, outstanding, sendQ,
          inflight, toClient, hpc, hmsg, misrouted, orphan, spc, stopHeld,
          ticks, ticksAfterCtx, ctxDone, doneSent, closed, stopSig,
          recvExited, jpc, jAns, jres>>

\* In English: "Variables grouped by owner, so each action can say which
\* groups it leaves alone."
tipVars   == <<opc, wpc, wAns, wres, tres>>
rangeVars == <<gpc, gIF, gTip, gFirst, gres, backed>>
wantVars  == <<wantIF, wantTip, wantFB>>
wireVars  == <<sendQ, inflight, toClient>>
stopVars  == <<spc, stopHeld, ticks, ticksAfterCtx, ctxDone, doneSent, closed,
               stopSig>>
handVars  == <<hpc, hmsg, misrouted, orphan, recvExited>>
jumpVars  == <<jpc, jAns, jres>>

\* In English: "Is this Stop called from the sync's roll callback?"
CallbackStop == StopFrom = "callback"

\* In English: "DoneChan is closed once recvLoop has returned [G2]."
DoneClosed == recvExited

\* In English: "The calls are about to start. If a sync is running, its one
\* MsgRequestNext is on the wire and counted."
Init ==
    /\ busy = None /\ life = "running"
    /\ ops = 0
    /\ opc = IF WithTip THEN "begin" ELSE "off"  \* a goroutine calls it, or nobody yet
    /\ wpc = "off" /\ wAns = FALSE /\ wres = "none" /\ tres = "none"
    /\ gpc = IF WithRange THEN "lock" ELSE "off"
    /\ gIF = "none" /\ gTip = "none" /\ gFirst = "none" /\ gres = "none"
    /\ backed = FALSE
    /\ wantIF = None /\ wantTip = FALSE /\ wantFB = FALSE
    /\ ready = 0
    /\ outstanding = IF SyncOutstanding THEN 1 ELSE 0
    /\ sendQ = <<>>
    /\ inflight = IF SyncOutstanding THEN <<Msg("RN", "sync")>> ELSE <<>>
    /\ toClient = <<>>
    /\ hpc = "idle" /\ hmsg = Msg("none", "none")
    /\ misrouted = FALSE /\ orphan = FALSE
    /\ spc = IF StopFrom = "outside" THEN "begin" ELSE "off"
    /\ stopHeld = FALSE /\ ticks = 0 /\ ticksAfterCtx = 0 /\ ctxDone = FALSE
    /\ doneSent = FALSE /\ closed = FALSE /\ stopSig = FALSE
    /\ recvExited = FALSE
    /\ jpc = IF WithJump THEN "lock" ELSE "off"
    /\ jAns = FALSE /\ jres = "none"

-----------------------------------------------------------------------------
(* GetCurrentTip, the calling goroutine [G1]. *)

\* In English: "GetCurrentTip takes an operation slot and starts its worker,
\* or returns an error if the client is not running (beginOperation)."
TipBegin ==
    /\ opc = "begin"
    /\ IF life = "running"
          THEN /\ ops' = ops + 1        \* beginOperation
               /\ opc' = "wait"
               /\ wpc' = "lock"         \* go func() { ... }
               /\ UNCHANGED tres
          ELSE /\ tres' = "err"         \* ErrProtocolShuttingDown
               /\ opc' = "returned"
               /\ UNCHANGED <<ops, wpc>>
    /\ UNCHANGED <<busy, life, wAns, wres>>
    /\ UNCHANGED <<rangeVars, wantVars, ready, outstanding, wireVars,
                   stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "GetCurrentTip takes the worker's result, or gives up when
\* DoneChan closes (or, with the fix, StopChan)."
TipWait ==
    /\ opc = "wait"
    /\ \/ /\ wres /= "none"                       \* requestResultChan / requestErrorChan
          /\ tres' = wres
       \/ /\ DoneClosed \/ (TipWatchesStop /\ stopSig)
          /\ tres' = "err"
    /\ opc' = "join"
    /\ UNCHANGED <<busy, life, ops, wpc, wAns, wres>>
    /\ UNCHANGED <<rangeVars, wantVars, ready, outstanding, wireVars,
                   stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "GetCurrentTip waits for its worker to exit (the deferred
\* <-requestWorkerDone), then releases its slot and returns."
TipJoin ==
    /\ opc = "join"
    /\ wpc = "exited" \/ ~TipJoinsWorker         \* the join
    /\ opc' = "returned"
    /\ ops' = ops - 1                            \* endOperation
    /\ UNCHANGED <<busy, life, wpc, wAns, wres, tres>>
    /\ UNCHANGED <<rangeVars, wantVars, ready, outstanding, wireVars,
                   stopVars, handVars>>
    /\ UNCHANGED jumpVars

(* GetCurrentTip's worker goroutine [G1]. *)

\* In English: "The worker takes busyMutex once it is free (Lock, or
\* lockBusy's TryLock)."
WorkerLock ==
    /\ wpc = "lock" /\ busy = None
    /\ busy' = "worker"
    /\ wpc' = "check"
    /\ UNCHANGED <<life, ops, opc, wAns, wres, tres>>
    /\ UNCHANGED <<rangeVars, wantVars, ready, outstanding, wireVars,
                   stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "With the fix, the worker's wait for busyMutex also ends on
\* StopChan and it reports ErrProtocolShuttingDown. Without it, Lock()
\* waits for whoever holds busyMutex, however long that is."
WorkerLockGiveUp ==
    /\ wpc = "lock" /\ WorkerLockWatchesStop /\ stopSig
    /\ wres' = "err"
    /\ wpc' = "exited"
    /\ UNCHANGED <<busy, life, ops, opc, wAns, tres>>
    /\ UNCHANGED <<rangeVars, wantVars, ready, outstanding, wireVars,
                   stopVars, handVars, jumpVars>>

\* In English: "Holding busyMutex, the worker returns if the client is no
\* longer running or the protocol is stopping (SendMessage fails);
\* otherwise it registers for an intersect answer and queues
\* MsgFindIntersect."
WorkerSend ==
    /\ wpc = "check"
    /\ IF life /= "running" \/ stopSig
          THEN /\ wres' = "err"
               /\ busy' = None                      \* deferred Unlock
               /\ wpc' = "exited"
               /\ UNCHANGED <<wantIF, sendQ>>
          ELSE /\ wantIF' = "worker"                \* wantIntersectFound
               /\ sendQ' = Append(sendQ, Msg("FI", "worker"))
               /\ wpc' = "wait"
               /\ UNCHANGED <<wres, busy>>
    /\ UNCHANGED <<life, ops, opc, wAns, tres, wantTip, wantFB>>
    /\ UNCHANGED <<rangeVars, ready, outstanding, inflight, toClient,
                   stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "The worker reports its own answer, or exits when DoneChan
\* closes (or, with the fix, StopChan), and releases busyMutex."
WorkerWait ==
    /\ wpc = "wait"
    /\ \/ /\ wAns
          /\ wres' = "own"
       \/ /\ DoneClosed \/ (TipWatchesStop /\ stopSig)
          /\ UNCHANGED wres
    /\ busy' = None                                 \* deferred Unlock
    /\ wpc' = "exited"
    /\ UNCHANGED <<life, ops, opc, wAns, tres>>
    /\ UNCHANGED <<rangeVars, wantVars, ready, outstanding, wireVars,
                   stopVars, handVars>>
    /\ UNCHANGED jumpVars

-----------------------------------------------------------------------------
(* GetAvailableBlockRange [G1]. *)

\* In English: "Return with result r: release busyMutex and the slot, and
\* cancel any want registration still pending (the deferred cancels)."
RangeReturn(r) ==
    /\ gres' = r
    /\ gpc' = "returned"
    /\ busy' = None
    /\ ops' = ops - 1
    /\ wantTip' = FALSE
    /\ wantFB' = FALSE

\* In English: "GetAvailableBlockRange blocks on busyMutex until it is free."
RangeLock ==
    /\ gpc = "lock" /\ busy = None
    /\ busy' = "range"
    /\ gpc' = "begin"
    /\ UNCHANGED <<life, ops, tipVars, gIF, gTip, gFirst, gres, backed,
                   wantVars, ready, outstanding, wireVars, stopVars,
                   handVars>>
    /\ UNCHANGED jumpVars

\* In English: "It takes an operation slot, or returns an error if the client
\* is not running."
RangeBegin ==
    /\ gpc = "begin"
    /\ IF life = "running"
          THEN /\ ops' = ops + 1
               /\ gpc' = "idle"
               /\ UNCHANGED <<busy, gres>>
          ELSE /\ busy' = None
               /\ gres' = "err"
               /\ gpc' = "returned"
               /\ UNCHANGED ops
    /\ UNCHANGED <<life, tipVars, gIF, gTip, gFirst, backed, wantVars, ready,
                   outstanding, wireVars, stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "prepareIdleProtocol: with a MsgRequestNext unanswered it
\* returns ErrSyncInProgress; otherwise it discards stale ready signals,
\* registers for the intersect answer and queues MsgFindIntersect."
RangeFind ==
    /\ gpc = "idle"
    /\ IF outstanding > 0
          THEN /\ RangeReturn("inprogress")
               /\ UNCHANGED <<wantIF, ready, sendQ>>
          ELSE IF stopSig
          THEN /\ RangeReturn("err")                \* SendMessage fails
               /\ UNCHANGED <<wantIF, ready, sendQ>>
          ELSE /\ ready' = 0                        \* discardReadySignals
               /\ wantIF' = "range"
               /\ sendQ' = Append(sendQ, Msg("FI", "range"))
               /\ gpc' = "fiwait"
               /\ UNCHANGED <<busy, ops, gres, wantTip, wantFB>>
    /\ UNCHANGED <<life, tipVars, gIF, gTip, gFirst, backed, outstanding,
                   inflight, toClient, stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "It takes the intersect answer. At the tip it returns an
\* empty range; otherwise it registers for the tip and the first block and
\* queues MsgRequestNext. DoneChan ends the wait with an error."
RangeAfterFind ==
    /\ gpc = "fiwait"
    /\ \/ /\ gIF = "FoundAtTip"
          /\ RangeReturn("empty")
          /\ UNCHANGED <<outstanding, sendQ>>
       \/ /\ gIF = "Found"
          /\ IF stopSig
                THEN /\ RangeReturn("err")
                     /\ UNCHANGED <<outstanding, sendQ>>
                ELSE /\ wantTip' = TRUE             \* wantCurrentTip
                     /\ wantFB' = TRUE              \* wantFirstBlock
                     /\ outstanding' = outstanding + 1   \* sendRequestNext
                     /\ sendQ' = Append(sendQ, Msg("RN", "range"))
                     /\ gpc' = "rnwait"
                     /\ UNCHANGED <<busy, ops, gres>>
       \/ /\ gIF = "none" /\ DoneClosed
          /\ RangeReturn("err")
          /\ UNCHANGED <<outstanding, sendQ>>
    /\ UNCHANGED <<life, tipVars, gIF, gTip, gFirst, backed, wantIF, ready,
                   inflight, toClient, stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "The receive loop: once both the tip and the first block
\* arrived it moves on; a ready signal (from a roll back) makes it send the
\* next MsgRequestNext; DoneChan ends it with an error."
RangeLoop ==
    /\ gpc = "rnwait"
    /\ \/ /\ gTip /= "none" /\ gFirst /= "none"
          /\ gpc' = "retire"
          /\ UNCHANGED <<busy, ops, gres, wantTip, wantFB, ready, outstanding,
                         sendQ>>
       \/ /\ ~(gTip /= "none" /\ gFirst /= "none")
          /\ ready > 0
          /\ ready' = ready - 1
          /\ IF stopSig
                THEN /\ RangeReturn("err")
                     /\ UNCHANGED <<outstanding, sendQ>>
                ELSE /\ outstanding' = outstanding + 1
                     /\ sendQ' = Append(sendQ, Msg("RN", "range"))
                     /\ UNCHANGED <<busy, ops, gres, gpc, wantTip, wantFB>>
       \/ /\ ~(gTip /= "none" /\ gFirst /= "none")
          /\ DoneClosed
          /\ RangeReturn("err")
          /\ UNCHANGED <<ready, outstanding, sendQ>>
    /\ UNCHANGED <<life, tipVars, gIF, gTip, gFirst, backed, wantIF,
                   inflight, toClient, stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "waitRequestNextRetired: it returns its range only once every
\* MsgRequestNext it sent has been retired."
RangeRetire ==
    /\ gpc = "retire"
    /\ \/ /\ outstanding = 0 \/ ~RangeWaitsRetired
          /\ RangeReturn("ok")
       \/ /\ outstanding > 0 /\ DoneClosed
          /\ RangeReturn("err")
    /\ UNCHANGED <<life, tipVars, gIF, gTip, gFirst, backed, wantIF, ready,
                   outstanding, wireVars, stopVars, handVars>>
    /\ UNCHANGED jumpVars

-----------------------------------------------------------------------------
(* Jump [G1]. *)

\* In English: "Jump returns with result r: it releases busyMutex and its
\* slot (the deferred function)."
JumpReturn(r) ==
    /\ jres' = r
    /\ jpc' = "returned"
    /\ busy' = None
    /\ ops' = ops - 1

\* In English: "Jump blocks on busyMutex until it is free."
JumpLock ==
    /\ jpc = "lock" /\ busy = None
    /\ busy' = "jump"
    /\ jpc' = "begin"
    /\ UNCHANGED <<life, ops, jAns, jres, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, stopVars, handVars>>

\* In English: "Jump takes an operation slot, or unlocks and returns an
\* error if the client is not running."
JumpBegin ==
    /\ jpc = "begin"
    /\ IF life = "running"
          THEN /\ ops' = ops + 1
               /\ jpc' = "find"
               /\ UNCHANGED <<busy, jres>>
          ELSE /\ busy' = None
               /\ jres' = "err"
               /\ jpc' = "returned"
               /\ UNCHANGED ops
    /\ UNCHANGED <<life, jAns, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, stopVars, handVars>>

\* In English: "prepareIdleProtocol, then findIntersect: with a
\* MsgRequestNext unanswered Jump returns ErrSyncInProgress; otherwise it
\* registers for the intersect answer and queues MsgFindIntersect."
JumpFind ==
    /\ jpc = "find"
    /\ IF outstanding > 0
          THEN /\ JumpReturn("inprogress")
               /\ UNCHANGED <<wantIF, sendQ>>
          ELSE IF stopSig
          THEN /\ JumpReturn("err")                 \* SendMessage fails
               /\ UNCHANGED <<wantIF, sendQ>>
          ELSE /\ wantIF' = "jump"
               /\ sendQ' = Append(sendQ, Msg("FI", "jump"))
               /\ jpc' = "wait"
               /\ UNCHANGED <<busy, ops, jres>>
    /\ UNCHANGED <<life, jAns, tipVars, rangeVars, wantTip, wantFB, ready,
                   outstanding, inflight, toClient, stopVars, handVars>>

\* In English: "findIntersect waits for Jump's own answer or DoneChan; it
\* does not watch StopChan."
JumpWait ==
    /\ jpc = "wait"
    /\ \/ jAns /\ JumpReturn("ok")
       \/ ~jAns /\ DoneClosed /\ JumpReturn("err")
    /\ UNCHANGED <<life, jAns, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, stopVars, handVars>>

-----------------------------------------------------------------------------
(* The engine and the server [G2], [C1], [P1]. *)

\* In English: "The engine puts the next queued message on the wire. A
\* MsgRequestNext may be pipelined; MsgFindIntersect needs StIdle: nothing
\* in flight and no reply waiting for the handler. After MsgDone, or once
\* stopped or closed, nothing more is sent."
EngineSend ==
    /\ sendQ /= <<>>
    /\ ~doneSent /\ ~closed /\ ~stopSig
    /\ Head(sendQ).k = "RN" \/ (inflight = <<>> /\ toClient = <<>>)   \* [C1]
    /\ inflight' = Append(inflight, Head(sendQ))
    /\ sendQ' = Tail(sendQ)
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, toClient, stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "The server's reply to message m."
Reply(m) ==
    CASE m.k = "RN" /\ m.f = "sync"   -> {Msg("Roll", "sync")}
      [] m.k = "FI" /\ m.f = "worker" -> {Msg("NotFound", "worker")}
      [] m.k = "FI" /\ m.f = "jump"   -> {Msg("Found", "jump")}
      [] m.k = "FI" /\ m.f = "range"  -> {Msg("Found", "range"),
                                          Msg("FoundAtTip", "range")}
      [] m.k = "RN" /\ m.f = "range"  ->
            IF backed THEN {Msg("Roll", "range")}
                      ELSE {Msg("Back", "range"), Msg("Roll", "range")}

\* In English: "The server answers the oldest request in flight [P1]."
ServerReply ==
    /\ inflight /= <<>> /\ ~closed
    /\ \E r \in Reply(Head(inflight)):
          /\ toClient' = Append(toClient, r)
          /\ backed' = (backed \/ r.k = "Back")
    /\ inflight' = Tail(inflight)
    /\ UNCHANGED <<busy, life, ops, tipVars, gpc, gIF, gTip, gFirst, gres,
                   wantVars, ready, outstanding, sendQ, stopVars, handVars>>
    /\ UNCHANGED jumpVars

\* In English: "ServerReply for anything but the sync's request at the tip,
\* which may never come (used only for fairness)."
ServerReplyPrompt ==
    /\ ~(AtTip /\ inflight /= <<>> /\ Head(inflight) = Msg("RN", "sync"))
    /\ ServerReply

-----------------------------------------------------------------------------
(* The handler: recvLoop running messageHandler [G1], [G2]. *)

\* In English: "recvLoop takes the next reply."
HandleTake ==
    /\ hpc = "idle" /\ ~recvExited /\ toClient /= <<>>
    /\ hmsg' = Head(toClient)
    /\ toClient' = Tail(toClient)
    /\ hpc' = "run"
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, sendQ, inflight, stopVars, misrouted, orphan,
                   recvExited>>
    /\ UNCHANGED jumpVars

\* In English: "sendCurrentTip: if a channel is registered, it takes the tip
\* and the slot empties."
GiveTip(from) ==
    IF wantTip THEN /\ wantTip' = FALSE /\ gTip' = from
               ELSE UNCHANGED <<wantTip, gTip>>

\* In English: "The sync's roll: its callback may call GetCurrentTip or
\* Stop, and the handler waits for that call to return; otherwise the roll
\* is delivered."
HandleSyncRoll ==
    /\ hpc = "run" /\ hmsg = Msg("Roll", "sync")
    /\ IF CallbackCallsTip /\ opc = "off"
          THEN /\ opc' = "begin" /\ hpc' = "cbtip"
               /\ UNCHANGED spc
          ELSE IF CallbackStop /\ spc = "off"
          THEN /\ spc' = "begin" /\ hpc' = "cbstop"
               /\ UNCHANGED opc
          ELSE /\ hpc' = "deliver"
               /\ UNCHANGED <<opc, spc>>
    /\ UNCHANGED <<busy, life, ops, wpc, wAns, wres, tres, rangeVars, wantVars,
                   ready, outstanding, wireVars, hmsg, misrouted, orphan,
                   recvExited, stopHeld, ticks, ticksAfterCtx, ctxDone,
                   doneSent, closed, stopSig>>
    /\ UNCHANGED jumpVars

\* In English: "The callback's call returned; the handler goes on."
HandleCallbackDone ==
    /\ \/ hpc = "cbtip" /\ opc = "returned"
       \/ hpc = "cbstop" /\ spc = "returned"
    /\ hpc' = "deliver"
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, stopVars, hmsg, misrouted, orphan,
                   recvExited>>
    /\ UNCHANGED jumpVars

\* In English: "A roll forward or back: the tip goes to sendCurrentTip; a
\* roll forward also goes to a registered first-block channel; a roll back
\* for GetAvailableBlockRange sends a ready signal. The sync's ready signal
\* goes to its loop and is not modelled. Then the request is retired."
HandleDeliver ==
    /\ \/ hpc = "deliver"
       \/ hpc = "run" /\ hmsg \in {Msg("Roll", "range"), Msg("Back", "range")}
    /\ GiveTip(hmsg.f)
    /\ IF hmsg.k = "Roll" /\ wantFB
          THEN /\ wantFB' = FALSE /\ gFirst' = hmsg.f
          ELSE UNCHANGED <<wantFB, gFirst>>
    /\ ready' = IF hmsg = Msg("Back", "range") THEN ready + 1 ELSE ready
    /\ hpc' = "retire"
    /\ UNCHANGED <<busy, life, ops, tipVars, gpc, gIF, gres, backed, wantIF,
                   outstanding, wireVars, stopVars, hmsg, misrouted, orphan,
                   recvExited>>
    /\ UNCHANGED jumpVars

\* In English: "requestNextAnswered, after the handler returned."
HandleRetire ==
    /\ hpc = "retire"
    /\ outstanding' = outstanding - 1
    /\ hpc' = "idle"
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   wireVars, stopVars, hmsg, misrouted, orphan, recvExited>>
    /\ UNCHANGED jumpVars

\* In English: "An intersect answer: MsgIntersectNotFound gives its tip to
\* sendCurrentTip, then fails the registered request (ignored if none);
\* MsgIntersectFound takes the registered request first (an error if none).
\* The request registered should be the one that asked."
HandleIntersect ==
    /\ hpc = "run" /\ hmsg.k \in {"NotFound", "Found", "FoundAtTip"}
    /\ hmsg.f /= "jump"
    /\ IF hmsg.k = "NotFound" THEN GiveTip(hmsg.f)
                              ELSE UNCHANGED <<wantTip, gTip>>
    /\ IF wantIF = None
          THEN /\ orphan' = (orphan \/ hmsg.k /= "NotFound")
               /\ UNCHANGED <<wantIF, misrouted, wAns, gIF>>
          ELSE /\ wantIF' = None
               /\ misrouted' = (misrouted \/ wantIF /= hmsg.f)
               /\ IF wantIF = "worker" THEN /\ wAns' = TRUE
                                            /\ UNCHANGED gIF
                                       ELSE /\ gIF' = hmsg.k
                                            /\ UNCHANGED wAns
               /\ UNCHANGED orphan
    /\ hpc' = "idle"
    /\ UNCHANGED <<busy, life, ops, opc, wpc, wres, tres, gpc, gFirst, gres,
                   backed, wantFB, ready, outstanding, wireVars, stopVars,
                   hmsg, recvExited>>
    /\ UNCHANGED jumpVars

\* In English: "Jump's MsgIntersectFound: handleIntersectFound takes the
\* registered request, then runs IntersectFoundFunc, which calls
\* GetCurrentTip; the handler waits for that call to return before it
\* hands Jump its answer."
HandleJumpFound ==
    /\ hpc = "run" /\ hmsg = Msg("Found", "jump")
    /\ IF wantIF = None
          THEN /\ orphan' = TRUE
               /\ hpc' = "idle"
               /\ UNCHANGED <<wantIF, misrouted, opc>>
          ELSE /\ wantIF' = None
               /\ misrouted' = (misrouted \/ wantIF /= "jump")
               /\ hpc' = "cbjump"
               /\ opc' = "begin"
               /\ UNCHANGED orphan
    /\ UNCHANGED <<busy, life, ops, wpc, wAns, wres, tres, rangeVars, wantTip,
                   wantFB, ready, outstanding, wireVars, stopVars, hmsg,
                   recvExited, jumpVars>>

\* In English: "IntersectFoundFunc returned: request.resultChan gets Jump's
\* answer."
HandleJumpAnswer ==
    /\ hpc = "cbjump" /\ opc = "returned"
    /\ jAns' = TRUE
    /\ hpc' = "idle"
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, stopVars, hmsg, misrouted, orphan,
                   recvExited, jpc, jres>>

\* In English: "recvLoop sees StopChan between messages and returns, so
\* DoneChan closes [G2]."
HandleExit ==
    /\ hpc = "idle" /\ stopSig /\ ~recvExited
    /\ recvExited' = TRUE
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, stopVars, hpc, hmsg, misrouted,
                   orphan>>
    /\ UNCHANGED jumpVars

-----------------------------------------------------------------------------
(* Stop [G1]. *)

\* In English: "Stop marks the client Stopping and starts waiting for
\* busyMutex."
StopBegin ==
    /\ spc = "begin"
    /\ IF life = "running"
          THEN /\ life' = "stopping" /\ spc' = "spin"
          ELSE /\ spc' = "returned" /\ UNCHANGED life
    /\ UNCHANGED <<busy, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, handVars, stopHeld, ticks,
                   ticksAfterCtx, ctxDone, doneSent, closed, stopSig>>
    /\ UNCHANGED jumpVars

\* In English: "With the fix, Stop stops waiting for busyMutex once its ctx
\* is done, and does not wait at all when called from a callback."
GiveUpEarly == StopHonoursCtx /\ (ctxDone \/ CallbackStop)

\* In English: "One poll of stopRunning: TryLock succeeds; or the deadline
\* (or, with the fix, ctx or the callback marker) ends the wait; or it
\* sleeps 10 ms and tries again."
StopSpin ==
    /\ spc = "spin"
    /\ IF busy = None
          THEN /\ busy' = "stop" /\ stopHeld' = TRUE /\ spc' = "finish"
               /\ UNCHANGED <<ticks, ticksAfterCtx>>
          ELSE IF ticks = Deadline \/ GiveUpEarly
          THEN /\ spc' = "finish"
               /\ UNCHANGED <<busy, stopHeld, ticks, ticksAfterCtx>>
          ELSE /\ ticks' = ticks + 1
               /\ ticksAfterCtx' = IF ctxDone THEN ticksAfterCtx + 1
                                              ELSE ticksAfterCtx
               /\ UNCHANGED <<busy, stopHeld, spc>>
    /\ UNCHANGED <<life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, handVars, ctxDone, doneSent, closed,
                   stopSig>>
    /\ UNCHANGED jumpVars

\* In English: "The protocol is not in StIdle: something is queued, on the
\* wire, or received but not yet taken by recvLoop, which applies a
\* reply's transition before its handler runs [G2]."
NotIdle == sendQ /= <<>> \/ inflight /= <<>> \/ toClient /= <<>>

\* In English: "finishStop: MsgDone goes out only from StIdle, and never
\* with a done ctx. If it cannot go out and a request is unanswered or the
\* state is not StIdle, abandonIfOwed closes the connection. Then
\* busyMutex is released if held and StopChan closes."
StopFinish ==
    /\ spc = "finish"
    /\ IF ~ctxDone /\ ~NotIdle
          THEN /\ doneSent' = TRUE /\ UNCHANGED <<closed, sendQ, inflight>>
          ELSE IF outstanding > 0 \/ NotIdle
          THEN /\ closed' = TRUE               \* muxer stopped
               /\ sendQ' = <<>> /\ inflight' = <<>>
               /\ UNCHANGED doneSent
          ELSE UNCHANGED <<doneSent, closed, sendQ, inflight>>
    /\ busy' = IF stopHeld THEN None ELSE busy
    /\ stopSig' = TRUE                         \* proto.Stop: StopChan closes
    /\ spc' = "wait"
    /\ UNCHANGED <<life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, toClient, handVars, stopHeld, ticks,
                   ticksAfterCtx, ctxDone>>
    /\ UNCHANGED jumpVars

\* In English: "Stop returns: at once in a callback (waitStopped), once the
\* client is Stopped, or once ctx is done."
StopReturn ==
    /\ spc = "wait"
    /\ CallbackStop \/ life = "stopped" \/ ctxDone
    /\ spc' = "returned"
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, handVars, stopHeld, ticks,
                   ticksAfterCtx, ctxDone, doneSent, closed, stopSig>>
    /\ UNCHANGED jumpVars

\* In English: "The goroutine finishStop starts: after DoneChan, and once
\* every operation slot is released, the client is Stopped."
StopComplete ==
    /\ life = "stopping" /\ stopSig /\ DoneClosed /\ ops = 0
    /\ life' = "stopped"
    /\ UNCHANGED <<busy, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, handVars, stopVars>>
    /\ UNCHANGED jumpVars

\* In English: "The outside Stop's ctx may expire at any time while Stop
\* runs."
CtxExpire ==
    /\ StopCtxExpires /\ StopFrom = "outside" /\ ~ctxDone
    /\ spc \in {"begin", "spin", "finish", "wait"}
    /\ ctxDone' = TRUE
    /\ UNCHANGED <<busy, life, ops, tipVars, rangeVars, wantVars, ready,
                   outstanding, wireVars, handVars, spc, stopHeld, ticks,
                   ticksAfterCtx, doneSent, closed, stopSig>>
    /\ UNCHANGED jumpVars

-----------------------------------------------------------------------------

\* In English: "Every call has returned and the handler is idle."
AllDone ==
    /\ opc \in {"off", "returned"} /\ wpc \in {"off", "exited"}
    /\ gpc \in {"off", "returned"} /\ spc \in {"off", "returned"}
    /\ jpc \in {"off", "returned"}
    /\ hpc = "idle"

\* In English: "Once everything has returned, the system may stay as it is."
Finished == AllDone /\ UNCHANGED vars

\* In English: "The steps of the calls and the handler: the ones that run
\* on their own goroutines and must not stall for ever."
TipSteps     == TipBegin \/ TipWait \/ TipJoin
WorkerSteps  == WorkerLock \/ WorkerLockGiveUp \/ WorkerSend \/ WorkerWait
RangeSteps   == RangeLock \/ RangeBegin \/ RangeFind \/ RangeAfterFind
                \/ RangeLoop \/ RangeRetire
HandlerSteps == HandleTake \/ HandleSyncRoll \/ HandleCallbackDone
                \/ HandleDeliver \/ HandleRetire \/ HandleIntersect
                \/ HandleJumpFound \/ HandleJumpAnswer \/ HandleExit
JumpSteps    == JumpLock \/ JumpBegin \/ JumpFind \/ JumpWait
StopSteps    == StopBegin \/ StopSpin \/ StopFinish \/ StopReturn
                \/ StopComplete

Next ==
    \/ TipSteps \/ WorkerSteps \/ RangeSteps \/ HandlerSteps \/ StopSteps
    \/ JumpSteps
    \/ EngineSend \/ ServerReply \/ CtxExpire
    \/ Finished

\* In English: "Each goroutine keeps running while it can; the server
\* answers every request except, at the tip, the sync's."
Fairness ==
    /\ WF_vars(TipSteps) /\ WF_vars(WorkerSteps) /\ WF_vars(RangeSteps)
    /\ WF_vars(HandlerSteps) /\ WF_vars(StopSteps) /\ WF_vars(JumpSteps)
    /\ WF_vars(EngineSend) /\ WF_vars(ServerReplyPrompt)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "A call runs its critical section only while it holds
\* busyMutex."
BusyHeldInCriticalSection ==
    /\ wpc \in {"check", "wait"} => busy = "worker"
    /\ gpc \in {"begin", "idle", "fiwait", "rnwait", "retire"} => busy = "range"
    /\ jpc \in {"begin", "find", "wait"} => busy = "jump"

\* In English: "GetCurrentTip has joined its worker when it returns."
WorkerJoinedBeforeReturn ==
    opc = "returned" /\ wpc /= "off" => wpc = "exited"

\* In English: "Every intersect answer goes to the call that asked, and a
\* MsgIntersectFound never arrives with nobody registered."
AnswersReachTheirCall == ~misrouted /\ ~orphan

\* In English: "GetAvailableBlockRange builds its range only from replies to
\* its own requests."
RangeFromOwnReplies ==
    /\ gTip \in {"none", "range"}
    /\ gFirst \in {"none", "range"}

\* In English: "When GetAvailableBlockRange returns a range, every request
\* has been retired and no ready signal is left for the next sync."
RangeLeavesIdle ==
    gpc = "returned" /\ gres = "ok" => outstanding = 0 /\ ready = 0

\* In English: "MsgFindIntersect is on the wire only on its own (StIdle)."
FindOnlyWhenIdle ==
    \A i \in 1..Len(inflight):
        inflight[i].k = "FI" => Len(inflight) = 1

\* In English: "Stop does not poll for busyMutex after its ctx is done."
StopHonoursCtxInvariant == ticksAfterCtx = 0

\* In English: "A Stop called from a callback does not wait for busyMutex."
CallbackStopDoesNotWait == CallbackStop => ticks = 0

(* Properties (liveness). *)

\* In English: "Once Stop has been called, it returns."
StopReturns == (spc /= "off") ~> (spc = "returned")

\* In English: "Once GetCurrentTip has been called, it returns."
TipReturns == (opc /= "off") ~> (opc = "returned")

\* In English: "Once Jump has been called, it returns."
JumpReturns == (jpc /= "off") ~> (jpc = "returned")

(* Probes: each is EXPECTED to be violated, showing the state is reached. *)

\* "GetCurrentTip's worker never waits on busyMutex held by the range call."
ProbeTipWaitsBehindRange == ~(wpc = "lock" /\ busy = "range")

\* "GetAvailableBlockRange never returns a range."
ProbeRangeOk == gres /= "ok"

\* "Stop never proceeds without busyMutex."
ProbeStopWithoutBusy == ~(spc = "wait" /\ ~stopHeld)
=============================================================================
