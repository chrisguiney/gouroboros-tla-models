---------------------- MODULE TxSubmissionServerLocks ----------------------
(***************************************************************************)
(* The gOuroboros tx-submission SERVER at the level of its locks and      *)
(* goroutines (protocol/txsubmission/server.go). TxSubmission.tla says    *)
(* WHICH requests and replies are legal; this module checks HOW the       *)
(* server hands a reply from its receive loop to the goroutine that asked *)
(* for it, and how it restarts after MsgDone while something may be       *)
(* stopping it.                                                           *)
(*                                                                         *)
(* The server has three locks:                                            *)
(*   requestMu  (Mutex)   one RequestTxIds/RequestTxs caller at a time,   *)
(*                        held across the wait for the peer's reply;     *)
(*   protocolMu (RWMutex) the current protocol instance and `stopped`;    *)
(*   stateMu    (Mutex)   stopping, the pending request, the result       *)
(*                        channel of the current instance.               *)
(* The documented order is requestMu -> protocolMu -> stateMu. A reply    *)
(* travels through a one-slot channel, remade for every instance.        *)
(*                                                                         *)
(* Goroutines:                                                            *)
(*   Callers  RequestTxIds(blocking): requestMu, protocolMu (read),       *)
(*            stateMu; record the pending request; unlock both; send;    *)
(*            wait for the slot or the instance's DoneChan. A caller that *)
(*            gets MsgDone's ErrStopServerProcess may call again, on the *)
(*            restarted instance.                                        *)
(*   Handler  the receive loop of the current instance, running          *)
(*            handleInit, handleReplyTxIds and handleDone. handleDone    *)
(*            restarts: StopForRestart, initProtocol (protocolMu write,  *)
(*            then stateMu), Start.                                      *)
(*   Stopper  Server.Stop: protocolMu write, set `stopped`, read the     *)
(*            instance; unlock; stop it and wait for its loops.          *)
(*                                                                         *)
(* sync.RWMutex (Go standard library, sync/rwmutex.go): once a writer    *)
(* waits in Lock, a new RLock blocks until that writer has had the lock. *)
(* This is what turns a lock-order inversion into a deadlock.            *)
(*                                                                         *)
(* Facts about instances (protocol/protocol.go): the message handler     *)
(* runs on recvLoop, and DoneChan closes only after recvLoop returns, so *)
(* DoneChan never closes while a handler is mid-message. Stop on an      *)
(* instance that never started closes its DoneChan at once. Start on a   *)
(* stopped instance does nothing.                                        *)
(*                                                                         *)
(* Message-level rules (window, acknowledgement, blocking style) are in  *)
(* TxSubmission.tla and are not repeated: every request here is the      *)
(* blocking request the server always sends, which the peer answers      *)
(* with MsgReplyTxIds or MsgDone. The muxer slot during a restart is in  *)
(* specs/keepalive/KeepAliveLifecycle.tla, which stands for this server  *)
(* too.                                                                   *)
(*                                                                         *)
(* HOW TO READ IT                                                         *)
(*   Each goroutine has a program counter (cpc, hpc, spc) naming the step *)
(*   it runs next, like a line number. A step whose first clause is a    *)
(*   lock test waits there until the lock is free. Symbols are explained *)
(*   in specs/keepalive/KeepAlive.tla's header.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    NCallers,       \* 1 or 2 goroutines calling RequestTxIds
    MaxCalls,       \* calls each caller makes
    MaxDones,       \* MsgDone the peer may send (each restarts the server)
    WithStop,       \* TRUE: Server.Stop runs concurrently
    ReadUnderState, \* TRUE (gOuroboros at 7cd17437): handleInit and handleDone read
                    \* the instance through ProtocolInstance (protocolMu read) while
                    \* holding stateMu. FALSE: they use the instance read before.
    StopGuard,      \* TRUE (gOuroboros): initProtocol installs nothing once Stop set
                    \* `stopped`. FALSE: a mutation without that check.
    Drain           \* TRUE (gOuroboros): a caller woken by DoneChan still takes a
                    \* result already in the slot. FALSE: a mutation that drops it.

\* In English: "the callers are c1, or c1 and c2."
Callers == IF NCallers = 1 THEN {"c1"} ELSE {"c1", "c2"}

\* In English: "the instances are the first one plus one per restart."
Instances == 1..(MaxDones + 1)

\* In English: "nobody", a value distinct from every goroutine name.
None == "none"

VARIABLES
    status,     \* status[i]: "unused", "new", "running" or "stopped"
    done,       \* done[i]: instance i's DoneChan is closed
    current,    \* s.proto
    stopped,    \* s.stopped, set by Stop under protocolMu
    stopping,   \* s.stopping, under stateMu
    pending,    \* s.pendingTxIds: the caller whose request is pending, or None
    slot,       \* slot[i]: instance i's result channel, "empty", "reply" or "stop"
    initSeen,   \* initSeen[i]: instance i has handled MsgInit
    sent,       \* sent[i]: a request on instance i awaits the peer's answer
    reqMu,      \* requestMu holder, or None
    readers,    \* protocolMu readers
    writer,     \* protocolMu writer, or None
    wWait,      \* goroutines waiting in protocolMu.Lock
    stMu,       \* stateMu holder, or None
    cpc,        \* cpc[c]: caller c's next step
    cinst,      \* cinst[c]: the instance caller c sent on
    calls,      \* calls[c]: calls caller c has finished
    hpc,        \* the handler's next step
    hinst,      \* the instance whose receive loop the handler is
    dones,      \* MsgDone received so far
    spc,        \* the stopper's next step
    snap,       \* the instance the stopper read
    installedAfterStop, \* initProtocol installed an instance after Stop set `stopped`
    lostResult  \* a caller returned ErrProtocolShuttingDown with a result in its slot

vars == <<status, done, current, stopped, stopping, pending, slot, initSeen,
          sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls, hpc,
          hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "instance 1 is running; every lock is free; every goroutine
\* is at its first step."
Init ==
    /\ status = [i \in Instances |-> IF i = 1 THEN "running" ELSE "unused"]
    /\ done = [i \in Instances |-> FALSE]
    /\ current = 1
    /\ stopped = FALSE
    /\ stopping = FALSE
    /\ pending = None
    /\ slot = [i \in Instances |-> "empty"]
    /\ initSeen = [i \in Instances |-> FALSE]
    /\ sent = [i \in Instances |-> FALSE]
    /\ reqMu = None
    /\ readers = {}
    /\ writer = None
    /\ wWait = {}
    /\ stMu = None
    /\ cpc = [c \in Callers |-> "idle"]
    /\ cinst = [c \in Callers |-> 1]
    /\ calls = [c \in Callers |-> 0]
    /\ hpc = "idle"
    /\ hinst = 1
    /\ dones = 0
    /\ spc = IF WithStop THEN "idle" ELSE "done"
    /\ snap = 1
    /\ installedAfterStop = FALSE
    /\ lostResult = FALSE

\* In English: "a new reader can take protocolMu: no writer holds it and
\* none is waiting for it" (sync.RWMutex's writer preference).
CanRLock == writer = None /\ wWait = {}

\* In English: "a writer can take protocolMu: nobody holds it."
CanLock == writer = None /\ readers = {}

-----------------------------------------------------------------------------
(* Callers: Server.RequestTxIds. *)

\* In English: "an idle caller with calls left takes requestMu."
CallReqMu(c) ==
    /\ cpc[c] = "idle"
    /\ calls[c] < MaxCalls
    /\ reqMu = None                          \* wait for requestMu
    /\ reqMu' = c
    /\ cpc' = [cpc EXCEPT ![c] = "rlock"]
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, sent, readers, writer, wWait, stMu, cinst, calls,
                   hpc, hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "it takes protocolMu for reading" (server.go s.protocolMu.RLock).
CallRLock(c) ==
    /\ cpc[c] = "rlock"
    /\ CanRLock                              \* wait while a writer holds or waits
    /\ readers' = readers \cup {c}
    /\ cpc' = [cpc EXCEPT ![c] = "state"]
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, sent, reqMu, writer, wWait, stMu, cinst, calls,
                   hpc, hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "it takes stateMu. If the server is stopping it returns
\* ErrProtocolShuttingDown; otherwise it records its pending request on the
\* current instance. Either way it releases stateMu and protocolMu." Nothing
\* inside this critical section blocks, so it is one step.
CallState(c) ==
    /\ cpc[c] = "state"
    /\ stMu = None                           \* wait for stateMu
    /\ IF stopping \/ pending /= None        \* refused before sending
          THEN /\ cpc' = [cpc EXCEPT ![c] = "ret"]
               /\ UNCHANGED <<pending, cinst>>
          ELSE /\ pending' = c               \* s.pendingTxIds = pending
               /\ cinst' = [cinst EXCEPT ![c] = current]  \* p := s.proto
               /\ cpc' = [cpc EXCEPT ![c] = "send"]
    /\ readers' = readers \ {c}              \* RUnlock
    /\ UNCHANGED <<status, done, current, stopped, stopping, slot, initSeen,
                   sent, reqMu, writer, wWait, stMu, calls, hpc, hinst, dones,
                   spc, snap, installedAfterStop, lostResult>>

\* In English: "it sends the request on its instance. A stopped instance
\* refuses it, and the caller clears its own pending request; a new
\* instance queues it until it starts."
CallSend(c) ==
    /\ cpc[c] = "send"
    /\ IF status[cinst[c]] = "stopped"
          THEN /\ stMu = None                \* SendMessage failed: clear under stateMu
               /\ pending' = IF pending = c THEN None ELSE pending
               /\ cpc' = [cpc EXCEPT ![c] = "ret"]
               /\ UNCHANGED sent
          ELSE /\ sent' = [sent EXCEPT ![cinst[c]] = TRUE]
               /\ cpc' = [cpc EXCEPT ![c] = "wait"]
               /\ UNCHANGED pending
    /\ UNCHANGED <<status, done, current, stopped, stopping, slot, initSeen,
                   reqMu, readers, writer, wWait, stMu, cinst, calls, hpc,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "it takes the result from its slot."
CallTake(c) ==
    /\ cpc[c] = "wait"
    /\ slot[cinst[c]] /= "empty"
    /\ slot' = [slot EXCEPT ![cinst[c]] = "empty"]
    /\ cpc' = [cpc EXCEPT ![c] = "ret"]
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, initSeen,
                   sent, reqMu, readers, writer, wWait, stMu, cinst, calls, hpc,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "or its instance's DoneChan closes: under stateMu it clears
\* its own pending request and marks the server stopping, then takes a
\* result already in the slot (with Drain), or returns
\* ErrProtocolShuttingDown." Go's select may take this branch even when the
\* slot is full.
CallDone(c) ==
    /\ cpc[c] = "wait"
    /\ done[cinst[c]]
    /\ stMu = None                           \* wait for stateMu
    /\ pending' = IF pending = c THEN None ELSE pending
    /\ stopping' = IF pending = c THEN TRUE ELSE stopping
    /\ IF Drain /\ slot[cinst[c]] /= "empty"
          THEN /\ slot' = [slot EXCEPT ![cinst[c]] = "empty"]  \* nested select
               /\ UNCHANGED lostResult
          ELSE /\ lostResult' = (lostResult \/ slot[cinst[c]] /= "empty")
               /\ UNCHANGED slot
    /\ cpc' = [cpc EXCEPT ![c] = "ret"]
    /\ UNCHANGED <<status, done, current, stopped, initSeen, sent, reqMu,
                   readers, writer, wWait, stMu, cinst, calls, hpc, hinst,
                   dones, spc, snap, installedAfterStop>>

\* In English: "it returns, releasing requestMu."
CallReturn(c) ==
    /\ cpc[c] = "ret"
    /\ reqMu' = None
    /\ calls' = [calls EXCEPT ![c] = calls[c] + 1]
    /\ cpc' = [cpc EXCEPT ![c] = "idle"]
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, sent, readers, writer, wWait, stMu, cinst, hpc,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

Caller(c) ==
    \/ CallReqMu(c) \/ CallRLock(c) \/ CallState(c) \/ CallSend(c)
    \/ CallTake(c) \/ CallDone(c) \/ CallReturn(c)

-----------------------------------------------------------------------------
(* The handler: the current instance's receive loop. *)

\* The variables a handler step that only moves its program counter leaves
\* alone.
hOnly == <<status, done, current, stopped, stopping, pending, slot, initSeen,
           sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
           hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "a running instance's handler reads MsgInit once."
RecvInit ==
    /\ hpc = "idle"
    /\ status[hinst] = "running"
    /\ ~initSeen[hinst]
    /\ initSeen' = [initSeen EXCEPT ![hinst] = TRUE]
    /\ hpc' = "initRead"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "after MsgInit, the peer answers a request it has received
\* with MsgReplyTxIds."
RecvReply ==
    /\ hpc = "idle"
    /\ status[hinst] = "running"
    /\ initSeen[hinst] /\ sent[hinst]
    /\ sent' = [sent EXCEPT ![hinst] = FALSE]
    /\ hpc' = "replyRead"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, reqMu, readers, writer, wWait, stMu, cpc, cinst,
                   calls, hinst, dones, spc, snap, installedAfterStop,
                   lostResult>>

\* In English: "...or, while it has MsgDone left to send, with MsgDone."
RecvDone ==
    /\ hpc = "idle"
    /\ status[hinst] = "running"
    /\ initSeen[hinst] /\ sent[hinst]
    /\ dones < MaxDones
    /\ sent' = [sent EXCEPT ![hinst] = FALSE]
    /\ dones' = dones + 1
    /\ hpc' = "doneRead"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, reqMu, readers, writer, wWait, stMu, cpc, cinst,
                   calls, hinst, spc, snap, installedAfterStop, lostResult>>

\* In English: "once its instance is stopped, an idle receive loop
\* returns, and the instance's DoneChan closes."
Halt ==
    /\ hpc = "idle"
    /\ status[hinst] = "stopped"
    /\ done' = [done EXCEPT ![hinst] = TRUE]
    /\ hpc' = "exit"
    /\ UNCHANGED <<status, current, stopped, stopping, pending, slot, initSeen,
                   sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "each handler first reads the instance through
\* ProtocolInstance, taking and releasing protocolMu for reading."
\* (`p := s.ProtocolInstance()` at the top of handleInit, handleReplyTxIds
\* and handleDone.)
HRead(from, to) ==
    /\ hpc = from
    /\ CanRLock
    /\ hpc' = to
    /\ UNCHANGED hOnly

\* handleInit: stateMu around building the callback context.
\* In English: "it takes stateMu. With ReadUnderState it keeps it while it
\* reads the instance again; otherwise it releases it at once."
InitLock ==
    /\ hpc = "initLock"
    /\ stMu = None
    /\ IF ReadUnderState
          THEN /\ stMu' = "H"
               /\ hpc' = "initReadUnder"
          ELSE /\ hpc' = "idle"
               /\ UNCHANGED stMu
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, sent, reqMu, readers, writer, wWait, cpc, cinst,
                   calls, hinst, dones, spc, snap, installedAfterStop,
                   lostResult>>

\* In English: "holding stateMu, it reads the instance through
\* ProtocolInstance, then releases stateMu." Lock order: stateMu ->
\* protocolMu, the reverse of every other path.
InitReadUnder ==
    /\ hpc = "initReadUnder"
    /\ CanRLock                              \* blocked while Stop waits for protocolMu
    /\ stMu' = None
    /\ hpc' = "idle"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, sent, reqMu, readers, writer, wWait, cpc, cinst,
                   calls, hinst, dones, spc, snap, installedAfterStop,
                   lostResult>>

\* handleReplyTxIds.
\* In English: "under stateMu it clears the pending request it answers;
\* if there is none (the caller gave up when DoneChan closed) it returns
\* without a result." The two stateMu blocks of the Go code are one step:
\* nothing else clears `pending` while the instance runs.
ReplyLock ==
    /\ hpc = "replyLock"
    /\ stMu = None
    /\ IF pending /= None
          THEN /\ pending' = None
               /\ hpc' = "replySend"
          ELSE /\ hpc' = "idle"
               /\ UNCHANGED pending
    /\ UNCHANGED <<status, done, current, stopped, stopping, slot, initSeen,
                   sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "it puts the reply in its instance's slot, waiting while
\* the slot is full."
ReplySend ==
    /\ hpc = "replySend"
    /\ slot[hinst] = "empty"
    /\ slot' = [slot EXCEPT ![hinst] = "reply"]
    /\ hpc' = "idle"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, initSeen,
                   sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* handleDone.
\* In English: "under stateMu it marks the server stopping and clears the
\* pending blocking request. With ReadUnderState it then reads the
\* instance while still holding stateMu."
DoneLock ==
    /\ hpc = "doneLock"
    /\ stMu = None
    /\ pending /= None                       \* else: a protocol error, not modelled
    /\ stopping' = TRUE
    /\ pending' = None
    /\ IF ReadUnderState
          THEN /\ stMu' = "H"
               /\ hpc' = "doneReadUnder"
          ELSE /\ hpc' = "doneSend"
               /\ UNCHANGED stMu
    /\ UNCHANGED <<status, done, current, stopped, slot, initSeen, sent, reqMu,
                   readers, writer, wWait, cpc, cinst, calls, hinst, dones,
                   spc, snap, installedAfterStop, lostResult>>

\* In English: "holding stateMu, it reads the instance, then releases
\* stateMu."
DoneReadUnder ==
    /\ hpc = "doneReadUnder"
    /\ CanRLock
    /\ stMu' = None
    /\ hpc' = "doneSend"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, slot,
                   initSeen, sent, reqMu, readers, writer, wWait, cpc, cinst,
                   calls, hinst, dones, spc, snap, installedAfterStop,
                   lostResult>>

\* In English: "it puts ErrStopServerProcess in the slot, waiting while
\* the slot is full."
DoneSend ==
    /\ hpc = "doneSend"
    /\ slot[hinst] = "empty"
    /\ slot' = [slot EXCEPT ![hinst] = "stop"]
    /\ hpc' = "doneStopOld"
    /\ UNCHANGED <<status, done, current, stopped, stopping, pending, initSeen,
                   sent, reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
                   hinst, dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "StopForRestart stops its own instance; its DoneChan closes
\* when this handler returns."
DoneStopOld ==
    /\ hpc = "doneStopOld"
    /\ status' = [status EXCEPT ![hinst] = "stopped"]
    /\ wWait' = wWait \cup {"H"}             \* initProtocol: protocolMu.Lock
    /\ hpc' = "doneLockW"
    /\ UNCHANGED <<done, current, stopped, stopping, pending, slot, initSeen,
                   sent, reqMu, readers, writer, stMu, cpc, cinst, calls, hinst,
                   dones, spc, snap, installedAfterStop, lostResult>>

\* In English: "initProtocol takes protocolMu for writing. If Stop set
\* `stopped` (and StopGuard is on) it installs nothing, and the handler
\* returns."
DoneLockW ==
    /\ hpc = "doneLockW"
    /\ CanLock
    /\ wWait' = wWait \ {"H"}
    /\ IF StopGuard /\ stopped
          THEN /\ hpc' = "exit"              \* CancelRestart, return
               /\ done' = [done EXCEPT ![hinst] = TRUE]
               /\ UNCHANGED writer
          ELSE /\ writer' = "H"
               /\ hpc' = "doneInstall"
               /\ UNCHANGED done
    /\ UNCHANGED <<status, current, stopped, stopping, pending, slot, initSeen,
                   sent, reqMu, readers, stMu, cpc, cinst, calls, hinst, dones,
                   spc, snap, installedAfterStop, lostResult>>

\* In English: "still holding protocolMu, it takes stateMu, installs a new
\* instance with an empty slot and a clear request state, and releases
\* both locks."
DoneInstall ==
    /\ hpc = "doneInstall"
    /\ stMu = None
    /\ LET n == current + 1 IN
         /\ status' = [status EXCEPT ![n] = "new"]
         /\ current' = n
    /\ stopping' = FALSE
    /\ pending' = None
    /\ installedAfterStop' = (installedAfterStop \/ stopped)
    /\ writer' = None
    /\ hpc' = "doneStart"
    /\ UNCHANGED <<done, stopped, slot, initSeen, sent, reqMu, readers, wWait,
                   stMu, cpc, cinst, calls, hinst, dones, spc, snap, lostResult>>

\* In English: "it starts the new instance (a no-op if Stop already
\* stopped it) and returns; the old instance's DoneChan closes and the new
\* instance's receive loop takes over."
DoneStart ==
    /\ hpc = "doneStart"
    /\ CanRLock                              \* s.Start reads ProtocolInstance
    /\ status' = IF status[current] = "new"
                    THEN [status EXCEPT ![current] = "running"]
                    ELSE status
    /\ done' = [done EXCEPT ![hinst] = TRUE]
    /\ hinst' = current
    /\ hpc' = IF status[current] = "new" THEN "idle" ELSE "exit"
    /\ UNCHANGED <<current, stopped, stopping, pending, slot, initSeen, sent,
                   reqMu, readers, writer, wWait, stMu, cpc, cinst, calls,
                   dones, spc, snap, installedAfterStop, lostResult>>

Handler ==
    \/ RecvInit \/ RecvReply \/ RecvDone \/ Halt
    \/ HRead("initRead", "initLock") \/ InitLock \/ InitReadUnder
    \/ HRead("replyRead", "replyLock") \/ ReplyLock \/ ReplySend
    \/ HRead("doneRead", "doneLock") \/ DoneLock \/ DoneReadUnder
    \/ DoneSend \/ DoneStopOld \/ DoneLockW \/ DoneInstall \/ DoneStart

-----------------------------------------------------------------------------
(* The stopper: Server.Stop(context.Background()). *)

sOnly == <<status, done, current, stopping, pending, slot, initSeen, sent,
           reqMu, readers, writer, stMu, cpc, cinst, calls, hpc, hinst, dones,
           installedAfterStop, lostResult>>

\* In English: "Stop calls protocolMu.Lock and waits for it."
StopWait ==
    /\ spc = "idle"
    /\ wWait' = wWait \cup {"S"}
    /\ spc' = "lock"
    /\ UNCHANGED <<stopped, snap>>
    /\ UNCHANGED sOnly

\* In English: "with protocolMu held it sets `stopped` and reads the
\* instance, then releases the lock." Nothing inside blocks.
StopLock ==
    /\ spc = "lock"
    /\ CanLock
    /\ wWait' = wWait \ {"S"}
    /\ stopped' = TRUE
    /\ snap' = current
    /\ spc' = "stop"
    /\ UNCHANGED sOnly

\* In English: "it stops that instance. One that never started closes its
\* DoneChan at once; a running one closes it when its receive loop
\* returns."
StopInstance ==
    /\ spc = "stop"
    /\ status' = IF status[snap] \in {"new", "running"}
                    THEN [status EXCEPT ![snap] = "stopped"]
                    ELSE status
    /\ done' = IF status[snap] = "new"
                  THEN [done EXCEPT ![snap] = TRUE]
                  ELSE done
    /\ spc' = "join"
    /\ UNCHANGED <<current, stopped, stopping, pending, slot, initSeen, sent,
                   reqMu, readers, writer, wWait, stMu, cpc, cinst, calls, hpc,
                   hinst, dones, snap, installedAfterStop, lostResult>>

\* In English: "it waits for the instance's loops and returns."
StopJoin ==
    /\ spc = "join"
    /\ done[snap]
    /\ spc' = "done"
    /\ UNCHANGED <<stopped, snap, wWait>>
    /\ UNCHANGED sOnly

Stopper == StopWait \/ StopLock \/ StopInstance \/ StopJoin

-----------------------------------------------------------------------------

\* In English: "every goroutine has finished, or waits only for a peer
\* message or a call it will not make: nothing changes any more." This is
\* an expected ending, not a deadlock.
Finished ==
    /\ \A c \in Callers : cpc[c] = "idle" /\ calls[c] = MaxCalls
    /\ hpc \in {"idle", "exit"}
    /\ spc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Callers : Caller(c)
    \/ Handler
    \/ Stopper
    \/ Finished

\* In English: "every goroutine that can keep taking steps eventually
\* does" (weak fairness on each goroutine). The peer may answer any
\* request, so the handler is fair too.
Fairness ==
    /\ \A c \in Callers : WF_vars(Caller(c))
    /\ WF_vars(Handler)
    /\ WF_vars(Stopper)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants and properties. *)

\* In English: "every variable holds the kind of value it should."
TypeOK ==
    /\ status \in [Instances -> {"unused", "new", "running", "stopped"}]
    /\ done \in [Instances -> BOOLEAN]
    /\ current \in Instances
    /\ pending \in Callers \cup {None}
    /\ slot \in [Instances -> {"empty", "reply", "stop"}]
    /\ reqMu \in Callers \cup {None}
    /\ readers \subseteq Callers
    /\ writer \in {None, "H"}
    /\ stMu \in {None, "H"}

\* In English: "at most one caller is between recording its request and
\* returning" (requestMu, and the pending check under stateMu).
OnePending ==
    Cardinality({c \in Callers : cpc[c] \in {"send", "wait"}}) <= 1

\* In English: "whenever the handler is about to put a result in a slot,
\* the slot is empty": the one-slot channel never blocks the receive loop.
ResultSlotNeverFull ==
    hpc \in {"replySend", "doneSend"} => slot[hinst] = "empty"

\* In English: "no instance is installed after Stop set `stopped`."
NoInstallAfterStop == ~installedAfterStop

\* In English: "once Stop has returned and no restart is in progress, no
\* instance is running."
StopIsEffective ==
    (spc = "done" /\ WithStop /\ hpc \in {"idle", "exit"}) =>
        \A i \in Instances : status[i] /= "running"

\* In English: "no caller gives up with ErrProtocolShuttingDown while its
\* result sits in the slot."
NoResultLost == ~lostResult

\* In English: "nobody waits for protocolMu while holding stateMu": the
\* documented order protocolMu -> stateMu is never reversed.
LockOrderRespected ==
    stMu = "H" => hpc \notin {"initReadUnder", "doneReadUnder"}

\* In English: "a caller waiting for a reply always returns."
CallerAlwaysReleased ==
    \A c \in Callers : (cpc[c] = "wait") ~> (cpc[c] = "idle")

\* In English: "Stop always returns."
StopTerminates == <>(spc = "done")
=============================================================================
