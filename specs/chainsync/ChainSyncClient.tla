--------------------------- MODULE ChainSyncClient ---------------------------
(***************************************************************************)
(* Model `chainsync`, slice 1: the gOuroboros chain-sync client's sync window and   *)
(* Reintersect.                                                            *)
(*                                                                         *)
(* A running Sync keeps PipelineLimit MsgRequestNext outstanding. Three    *)
(* goroutines share the client (protocol/chainsync/client.go):             *)
(*   syncLoop   waits for a "ready" signal per consumed reply, takes       *)
(*              busyMutex, and tops the window back up;                    *)
(*   handler    (the protocol's recvLoop) runs each reply's handler: the   *)
(*              application's callback, then a ready signal - sent while   *)
(*              HOLDING lifecycleMutex, blocking until there is room       *)
(*              (readyForNextBlockChan has PipelineLimit slots) - then     *)
(*              requestNextAnswered retires the request;                   *)
(*   Reintersect stops the loop, takes busyMutex, waits until every       *)
(*              outstanding request is answered (quiesceSync), discards    *)
(*              leftover signals, sends MsgFindIntersect, and starts a new *)
(*              loop.                                                      *)
(*                                                                         *)
(* Questions: does a handler ever block on a full ready channel (it would  *)
(* hold lifecycleMutex, and Reintersect and Stop would hang)? Is           *)
(* MsgFindIntersect ever sent with a request outstanding? Is a reply from  *)
(* before Reintersect ever delivered after it returns? Does anything       *)
(* deadlock?                                                               *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex:                                  *)
(*   [C1] 838-848, 893-908: chain-sync agencies and transitions;           *)
(*        MsgFindIntersect only from StIdle; 1064-1076: the client "is     *)
(*        free to use MsgFindIntersect at any time later".                 *)
(*   [P1] 2180-2208: pipelining; replies come back in request order.       *)
(*   Reference, same commit, in ouroboros-network/protocols/lib/           *)
(*   Ouroboros/Network/Protocol/ChainSync/:                                *)
(*   [R2] ClientPipelined.hs 60-84: SendMsgFindIntersect is typed at Z,    *)
(*        so it can only be sent with nothing pipelined outstanding;       *)
(*        257-273: it is a plain Yield then Await.                         *)
(*   [R3] PipelineDecision.hs 24-38: Request (at Z), Pipeline, Collect.    *)
(*   gOuroboros, blinklabs-io/gouroboros 279ec482,                         *)
(*   protocol/chainsync/client.go:                                         *)
(*   [G1] syncLoop, sendRequestNext, requestNextAnswered, messageHandler,  *)
(*        handleRollForward / handleRollBackward (ready signal sent under  *)
(*        lifecycleMutex), Reintersect, quiesceSync, discardReadySignals,  *)
(*        sendInitialRequestAndStartSyncLoop; NewClient (readyForNext-     *)
(*        BlockChan has PipelineLimit slots; a zero limit becomes 75).     *)
(*                                                                         *)
(* Not in this slice: Stop, StopAfterDrain, Jump, GetCurrentTip,           *)
(* GetAvailableBlockRange, the block pipeline, timeouts.                   *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Limit,          \* PipelineLimit: requests the sync keeps outstanding
    MaxRequests,    \* how many MsgRequestNext are sent in total (keeps it finite)
    CallbackStops,  \* TRUE: a callback may return ErrStopSyncProcess
    \* Each switch below is TRUE in gOuroboros; FALSE removes one safeguard
    \* to show the invariants notice (the *Bug.cfg configs).
    TopUpByInFlight,  \* the loop sends Limit minus what is in flight
    DrainBeforeFind,  \* Reintersect waits for every request to be answered
    DiscardSignals    \* Reintersect throws away leftover ready signals

\* In English: "The value of a mutex that nobody holds."
\* Literally: "None is defined as "none"."
None == "none"

VARIABLES
    \* shared client state, guarded by lifecycleMutex in the code
    out,        \* outstandingRequestNext
    sig,        \* readyForNextBlockChan's contents, oldest first
    stopReqs,   \* syncStopRequests
    sent,       \* MsgRequestNext sent so far (model bound only)
    epoch,      \* how many times the client has (re)intersected
    \* the two mutexes: who holds each
    busy,       \* busyMutex
    lc,         \* lifecycleMutex
    \* syncLoop
    lpc,        \* its next step, or "none" when no loop runs
    inFlight,   \* its local count of requests whose replies it has not consumed
    toSend,     \* requests it is about to send
    loopStop,   \* TRUE once its stop channel is closed
    \* the handler (recvLoop)
    hpc,        \* its next step
    hsig,       \* the signal it is about to send
    \* Reintersect
    rpc,        \* its next step
    stopsBefore,
    found,      \* TRUE once MsgIntersectFound has arrived
    \* the wire and the honest server
    toServer, toClient,
    sview,      \* the server's state
    sepoch,     \* the server's count of intersections, stamped on its replies
    awaited,    \* TRUE once the server sent MsgAwaitReply for this request
    \* outcomes
    findEarly,  \* MsgFindIntersect was sent with a request outstanding
    stale,      \* a pre-Reintersect reply was delivered after Reintersect returned
    overflow    \* a handler found the ready channel full (it would block)

\* Literally: "vars is defined as the tuple of all twenty-four variables."
vars == <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight, toSend,
          loopStop, hpc, hsig, rpc, stopsBefore, found, toServer, toClient,
          sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "A sync is running: intersection 1 found, the initial request
\* sent, the loop waiting with that one request in flight."
\* Literally: "Init is defined as: out equals 1, and sig equals the empty
\*   sequence, and stopReqs equals 0, and sent equals 1, and epoch equals 1,
\*   and busy equals None, and lc equals None, and lpc equals "wait", and
\*   inFlight equals 1, and toSend equals 0, and loopStop equals FALSE, and hpc
\*   equals "idle", and hsig equals TRUE, and rpc equals "idle", and
\*   stopsBefore equals 0, and found equals FALSE, and toServer equals the
\*   sequence containing "MsgRequestNext", and toClient equals the empty
\*   sequence, and sview equals "StIdle", and sepoch equals 1, and awaited
\*   equals FALSE, and findEarly equals FALSE, and stale equals FALSE, and
\*   overflow equals FALSE."
Init ==
    /\ out = 1 /\ sig = <<>> /\ stopReqs = 0 /\ sent = 1 /\ epoch = 1
    /\ busy = None /\ lc = None
    /\ lpc = "wait" /\ inFlight = 1 /\ toSend = 0 /\ loopStop = FALSE
    /\ hpc = "idle" /\ hsig = TRUE
    /\ rpc = "idle" /\ stopsBefore = 0 /\ found = FALSE
    /\ toServer = <<"MsgRequestNext">> /\ toClient = <<>>
    /\ sview = "StIdle" /\ sepoch = 1 /\ awaited = FALSE
    /\ findEarly = FALSE /\ stale = FALSE /\ overflow = FALSE

-----------------------------------------------------------------------------
(* syncLoop [G1]. *)

\* In English: "The loop waits: if its stop channel is closed it exits; if a
\* signal is waiting it takes it - false means the sync was cancelled, so it
\* exits; true means a reply was consumed."
\* Literally: "LoopWait is defined as: lpc equals "wait", and either (loopStop
\*   is true, and lpc in the next state equals "exited", and sig is unchanged),
\*   or (sig does not equal the empty sequence, and sig in the next state
\*   equals the tail of sig, and lpc in the next state equals (if the head of
\*   sig then "lockBusy", else "exited")); and the other twenty-two variables
\*   are unchanged."
LoopWait ==
    /\ lpc = "wait"
    /\ \/ /\ loopStop
          /\ lpc' = "exited"
          /\ UNCHANGED sig
       \/ /\ sig /= <<>>
          /\ sig' = Tail(sig)
          /\ lpc' = IF Head(sig) THEN "lockBusy" ELSE "exited"
    /\ UNCHANGED <<out, stopReqs, sent, epoch, busy, lc, inFlight, toSend,
                   loopStop, hpc, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "The loop takes busyMutex when it is free, and goes on to take
\* lifecycleMutex."
\* Literally: "LoopLockBusy is defined as: lpc equals "lockBusy", and busy
\*   equals None, and busy in the next state equals "loop", and lpc in the next
\*   state equals "lockLC", and the other twenty-two variables are unchanged."
LoopLockBusy ==
    /\ lpc = "lockBusy" /\ busy = None
    /\ busy' = "loop" /\ lpc' = "lockLC"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, lc, inFlight, toSend,
                   loopStop, hpc, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Under lifecycleMutex: stopped? release both locks and exit.
\* Otherwise one reply was consumed; the requests to send are the window
\* minus what is still in flight."
\* Literally: "LoopTopUp is defined as: lpc equals "lockLC", and lc equals
\*   None, and if loopStop, then (busy in the next state equals None, and lpc
\*   in the next state equals "exited", and inFlight and toSend are unchanged),
\*   else (inFlight in the next state equals inFlight minus 1, and toSend in
\*   the next state equals (if TopUpByInFlight then Limit minus (inFlight minus
\*   1), else Limit), and lpc in the next state equals "send", and busy is
\*   unchanged); and the other twenty variables are unchanged."
LoopTopUp ==
    /\ lpc = "lockLC" /\ lc = None
    /\ IF loopStop
          THEN /\ busy' = None /\ lpc' = "exited"
               /\ UNCHANGED <<inFlight, toSend>>
          ELSE /\ inFlight' = inFlight - 1
               /\ toSend' = IF TopUpByInFlight THEN Limit - (inFlight - 1)
                                             ELSE Limit
               /\ lpc' = "send"
               /\ UNCHANGED busy
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, lc, loopStop, hpc, hsig,
                   rpc, stopsBefore, found, toServer, toClient, sview, sepoch,
                   awaited, findEarly, stale, overflow>>

\* sendRequestNext, once per request (it takes lifecycleMutex briefly). The
\* model stops sending at MaxRequests to stay finite.
\* Literally: "LoopSendOne is defined as: lpc equals "send", and toSend is
\*   greater than 0, and lc equals None, and if sent is less than MaxRequests,
\*   then (out in the next state equals out plus 1, and sent in the next state
\*   equals sent plus 1, and toServer in the next state equals toServer with
\*   "MsgRequestNext" appended, and inFlight in the next state equals inFlight
\*   plus 1), else out, sent, toServer and inFlight are unchanged; and toSend
\*   in the next state equals toSend minus 1, and the other nineteen variables
\*   are unchanged."
LoopSendOne ==
    /\ lpc = "send" /\ toSend > 0 /\ lc = None
    /\ IF sent < MaxRequests
          THEN /\ out' = out + 1 /\ sent' = sent + 1
               /\ toServer' = Append(toServer, "MsgRequestNext")
               /\ inFlight' = inFlight + 1
          ELSE UNCHANGED <<out, sent, toServer, inFlight>>
    /\ toSend' = toSend - 1
    /\ UNCHANGED <<sig, stopReqs, epoch, busy, lc, lpc, loopStop, hpc, hsig,
                   rpc, stopsBefore, found, toClient, sview, sepoch, awaited,
                   findEarly, stale, overflow>>

\* In English: "Done sending: release busyMutex and wait again."
\* Literally: "LoopSendDone is defined as: lpc equals "send", and toSend equals
\*   0, and lc equals None, and busy in the next state equals None, and lpc in
\*   the next state equals "wait", and the other twenty-two variables are
\*   unchanged."
LoopSendDone ==
    /\ lpc = "send" /\ toSend = 0 /\ lc = None
    /\ busy' = None /\ lpc' = "wait"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, lc, inFlight, toSend,
                   loopStop, hpc, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

-----------------------------------------------------------------------------
(* The handler, in the protocol's recvLoop: one reply at a time [G1]. *)

\* In English: "Take the next reply. MsgAwaitReply changes nothing here.
\* MsgIntersectFound is handed to Reintersect. A roll is delivered to the
\* application's callback - noting if it is from an earlier intersection
\* after Reintersect returned - and the callback may ask to stop."
\* Literally: "HandleTake is defined as: hpc equals "idle", and toClient does
\*   not equal the empty sequence, and, letting m be the head of toClient: if
\*   m's type equals "MsgAwaitReply", then hpc, hsig, found and stale are
\*   unchanged; else if m's type equals "MsgIntersectFound", then (found in the
\*   next state equals TRUE, and hpc, hsig and stale are unchanged); else
\*   (stale in the next state equals (stale is true, or rpc equals "done" and
\*   m's epoch is less than epoch), and there exists a stop in (if
\*   CallbackStops then BOOLEAN, else the set containing FALSE) such that hsig
\*   in the next state equals stop is not true, and hpc in the next state
\*   equals "lock", and found is unchanged); and toClient in the next state
\*   equals the tail of toClient, and the other nineteen variables are
\*   unchanged."
HandleTake ==
    /\ hpc = "idle" /\ toClient /= <<>>
    /\ LET m == Head(toClient) IN
       IF m.type = "MsgAwaitReply"
          THEN UNCHANGED <<hpc, hsig, found, stale>>
       ELSE IF m.type = "MsgIntersectFound"
          THEN /\ found' = TRUE
               /\ UNCHANGED <<hpc, hsig, stale>>
       ELSE /\ stale' = (stale \/ (rpc = "done" /\ m.epoch < epoch))
            /\ \E stop \in IF CallbackStops THEN BOOLEAN ELSE {FALSE} :
                  hsig' = ~stop
            /\ hpc' = "lock"
            /\ UNCHANGED found
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight,
                   toSend, loopStop, rpc, stopsBefore, toServer, sview,
                   sepoch, awaited, findEarly, overflow>>

\* In English: "Take lifecycleMutex to send the ready signal."
\* Literally: "HandleLock is defined as: hpc equals "lock", and lc equals None,
\*   and lc in the next state equals "handler", and hpc in the next state
\*   equals "send", and the other twenty-two variables are unchanged."
HandleLock ==
    /\ hpc = "lock" /\ lc = None
    /\ lc' = "handler" /\ hpc' = "send"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lpc, inFlight,
                   toSend, loopStop, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Send the signal if the channel has room, count a stop
\* request, and release lifecycleMutex. With no room it blocks HOLDING the
\* lock; the model records that and stops here."
\* Literally: "HandleSend is defined as: hpc equals "send", and if the length
\*   of sig is less than Limit, then (sig in the next state equals sig with
\*   hsig appended, and stopReqs in the next state equals (if hsig then
\*   stopReqs, else stopReqs plus 1), and lc in the next state equals None, and
\*   hpc in the next state equals "answer", and overflow is unchanged), else
\*   (overflow in the next state equals TRUE, and sig, stopReqs, lc and hpc are
\*   unchanged); and the other nineteen variables are unchanged."
HandleSend ==
    /\ hpc = "send"
    /\ IF Len(sig) < Limit
          THEN /\ sig' = Append(sig, hsig)
               /\ stopReqs' = IF hsig THEN stopReqs ELSE stopReqs + 1
               /\ lc' = None /\ hpc' = "answer"
               /\ UNCHANGED overflow
          ELSE /\ overflow' = TRUE
               /\ UNCHANGED <<sig, stopReqs, lc, hpc>>
    /\ UNCHANGED <<out, sent, epoch, busy, lpc, inFlight, toSend, loopStop,
                   hsig, rpc, stopsBefore, found, toServer, toClient, sview,
                   sepoch, awaited, findEarly, stale>>

\* requestNextAnswered, under lifecycleMutex.
\* In English: "Under lifecycleMutex, one fewer request is outstanding (never
\* below zero); the handler is idle again."
\* Literally: "HandleAnswer is defined as: hpc equals "answer", and lc equals
\*   None, and out in the next state equals (if out is greater than 0 then out
\*   minus 1, else 0), and hpc in the next state equals "idle", and the other
\*   twenty-two variables are unchanged."
HandleAnswer ==
    /\ hpc = "answer" /\ lc = None
    /\ out' = IF out > 0 THEN out - 1 ELSE 0
    /\ hpc' = "idle"
    /\ UNCHANGED <<sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight,
                   toSend, loopStop, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

-----------------------------------------------------------------------------
(* Reintersect, called once by the application [G1]. *)

\* In English: "Note the stop requests so far; close the loop's stop channel."
\* Literally: "ReBegin is defined as: rpc equals "idle", and lc equals None,
\*   and stopsBefore in the next state equals stopReqs, and loopStop in the
\*   next state equals TRUE, and rpc in the next state equals "waitLoop", and
\*   the other twenty-one variables are unchanged."
ReBegin ==
    /\ rpc = "idle" /\ lc = None
    /\ stopsBefore' = stopReqs
    /\ loopStop' = TRUE
    /\ rpc' = "waitLoop"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight,
                   toSend, hpc, hsig, found, toServer, toClient, sview,
                   sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Wait for the loop to exit, then take busyMutex."
\* Literally: "ReLockBusy is defined as: rpc equals "waitLoop", and lpc is a
\*   member of the set containing "exited" and "none", and busy equals None,
\*   and busy in the next state equals "re", and rpc in the next state equals
\*   "drain", and the other twenty-two variables are unchanged."
ReLockBusy ==
    /\ rpc = "waitLoop" /\ lpc \in {"exited", "none"} /\ busy = None
    /\ busy' = "re" /\ rpc' = "drain"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, lc, lpc, inFlight,
                   toSend, loopStop, hpc, hsig, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Wait until every outstanding request is answered; then
\* discard leftover ready signals; then, if a callback asked to stop during
\* the drain, give up (ErrStopSyncProcess)."
\* Literally: "ReDrained is defined as: rpc equals "drain", and lc equals None,
\*   and if DrainBeforeFind, then out equals 0; and sig in the next state
\*   equals (if DiscardSignals then the empty sequence, else sig), and rpc in
\*   the next state equals (if stopReqs does not equal stopsBefore then
\*   "stopped", else "find"), and busy in the next state equals (if stopReqs
\*   does not equal stopsBefore then None, else busy), and the other twenty-one
\*   variables are unchanged."
ReDrained ==
    /\ rpc = "drain" /\ lc = None
    /\ DrainBeforeFind => out = 0
    /\ sig' = IF DiscardSignals THEN <<>> ELSE sig
    /\ rpc' = IF stopReqs /= stopsBefore THEN "stopped" ELSE "find"
    /\ busy' = IF stopReqs /= stopsBefore THEN None ELSE busy
    /\ UNCHANGED <<out, stopReqs, sent, epoch, lc, lpc, inFlight, toSend,
                   loopStop, hpc, hsig, stopsBefore, found, toServer, toClient,
                   sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Send MsgFindIntersect - noting if a request is still
\* outstanding - and wait for the answer."
\* Literally: "ReFind is defined as: rpc equals "find", and toServer in the
\*   next state equals toServer with "MsgFindIntersect" appended, and findEarly
\*   in the next state equals (findEarly is true or out is greater than 0), and
\*   epoch in the next state equals epoch plus 1, and rpc in the next state
\*   equals "await", and the other twenty variables are unchanged."
ReFind ==
    /\ rpc = "find"
    /\ toServer' = Append(toServer, "MsgFindIntersect")
    /\ findEarly' = (findEarly \/ out > 0)
    /\ epoch' = epoch + 1
    /\ rpc' = "await"
    /\ UNCHANGED <<out, sig, stopReqs, sent, busy, lc, lpc, inFlight, toSend,
                   loopStop, hpc, hsig, stopsBefore, found, toClient, sview,
                   sepoch, awaited, stale, overflow>>

\* sendInitialRequestAndStartSyncLoop. In English: "Once intersected, send
\* the first request and start a new loop with it in flight; release
\* busyMutex."
\* Literally: "ReStart is defined as: rpc equals "await", and found is true,
\*   and lc equals None, and out in the next state equals out plus 1, and sent
\*   in the next state equals sent plus 1, and toServer in the next state
\*   equals toServer with "MsgRequestNext" appended, and lpc in the next state
\*   equals "wait", and inFlight in the next state equals 1, and loopStop in
\*   the next state equals FALSE, and toSend in the next state equals 0, and
\*   busy in the next state equals None, and rpc in the next state equals
\*   "done", and the other fifteen variables are unchanged."
ReStart ==
    /\ rpc = "await" /\ found /\ lc = None
    /\ out' = out + 1 /\ sent' = sent + 1
    /\ toServer' = Append(toServer, "MsgRequestNext")
    /\ lpc' = "wait" /\ inFlight' = 1 /\ loopStop' = FALSE /\ toSend' = 0
    /\ busy' = None /\ rpc' = "done"
    /\ UNCHANGED <<sig, stopReqs, epoch, lc, hpc, hsig, stopsBefore, found,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

-----------------------------------------------------------------------------
(* The honest server [C1][P1]: reads only when it is waiting for the       *)
(* client, answers each request in turn, stamping its intersection count.  *)

\* In English: "In StIdle, the server takes the next request: MsgFindIntersect
\* moves it to StIntersect and starts a new intersection, MsgRequestNext to
\* StCanAwait."
\* Literally: "ServerRecv is defined as: sview equals "StIdle", and toServer
\*   does not equal the empty sequence, and if the head of toServer equals
\*   "MsgFindIntersect", then (sview in the next state equals "StIntersect" and
\*   sepoch in the next state equals sepoch plus 1), else (sview in the next
\*   state equals "StCanAwait" and sepoch is unchanged); and toServer in the
\*   next state equals the tail of toServer, and awaited in the next state
\*   equals FALSE, and the other twenty variables are unchanged."
ServerRecv ==
    /\ sview = "StIdle" /\ toServer /= <<>>
    /\ IF Head(toServer) = "MsgFindIntersect"
          THEN /\ sview' = "StIntersect" /\ sepoch' = sepoch + 1
          ELSE /\ sview' = "StCanAwait" /\ UNCHANGED sepoch
    /\ toServer' = Tail(toServer)
    /\ awaited' = FALSE
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight,
                   toSend, loopStop, hpc, hsig, rpc, stopsBefore, found,
                   toClient, findEarly, stale, overflow>>

\* In English: "Waiting for a request's answer, the server may say
\* MsgAwaitReply once, then rolls forward or backward. Asked to intersect,
\* it finds the intersection."
\* Literally: "ServerSend of t is defined as: either (sview equals
\*   "StCanAwait", and t equals "MsgAwaitReply", and awaited is not true, and
\*   sview in the next state equals "StMustReply"), or (sview is a member of
\*   the set containing "StCanAwait" and "StMustReply", and t is a member of
\*   the set containing "MsgRollForward" and "MsgRollBackward", and sview in
\*   the next state equals "StIdle"), or (sview equals "StIntersect", and t
\*   equals "MsgIntersectFound", and sview in the next state equals "StIdle");
\*   and toClient in the next state equals toClient with the record whose field
\*   type is t and field epoch is sepoch appended, and awaited in the next
\*   state equals (awaited is true or t equals "MsgAwaitReply"), and the other
\*   twenty-one variables are unchanged."
ServerSend(t) ==
    /\ \/ /\ sview = "StCanAwait" /\ t = "MsgAwaitReply" /\ ~awaited
          /\ sview' = "StMustReply"
       \/ /\ sview \in {"StCanAwait", "StMustReply"}
          /\ t \in {"MsgRollForward", "MsgRollBackward"}
          /\ sview' = "StIdle"
       \/ /\ sview = "StIntersect" /\ t = "MsgIntersectFound"
          /\ sview' = "StIdle"
    /\ toClient' = Append(toClient, [type |-> t, epoch |-> sepoch])
    /\ awaited' = (awaited \/ t = "MsgAwaitReply")
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight,
                   toSend, loopStop, hpc, hsig, rpc, stopsBefore, found,
                   toServer, sepoch, findEarly, stale, overflow>>

-----------------------------------------------------------------------------

\* In English: "Finished: Reintersect returned or gave up, and nothing is in
\* flight or being handled - or a handler blocked."
\* Literally: "Finished is defined as: either (rpc is a member of the set
\*   containing "done" and "stopped", and toServer equals the empty sequence,
\*   and toClient equals the empty sequence, and hpc equals "idle", and lpc is
\*   a member of the set containing "wait", "exited" and "none", and busy
\*   equals None, and lc equals None), or overflow is true; and vars is
\*   unchanged."
Finished ==
    /\ \/ /\ rpc \in {"done", "stopped"}
          /\ toServer = <<>> /\ toClient = <<>> /\ hpc = "idle"
          /\ lpc \in {"wait", "exited", "none"} /\ busy = None /\ lc = None
       \/ overflow
    /\ UNCHANGED vars

\* In English: "A step is any one step of the loop, the handler, Reintersect or
\* the server, or staying finished."
\* Literally: "Next is defined as: LoopWait, or LoopLockBusy, or LoopTopUp, or
\*   LoopSendOne, or LoopSendDone, or HandleTake, or HandleLock, or HandleSend,
\*   or HandleAnswer, or ReBegin, or ReLockBusy, or ReDrained, or ReFind, or
\*   ReStart, or ServerRecv, or there exists a t in the set containing
\*   "MsgAwaitReply", "MsgRollForward", "MsgRollBackward" and
\*   "MsgIntersectFound" such that ServerSend of t, or Finished."
Next ==
    \/ LoopWait \/ LoopLockBusy \/ LoopTopUp \/ LoopSendOne \/ LoopSendDone
    \/ HandleTake \/ HandleLock \/ HandleSend \/ HandleAnswer
    \/ ReBegin \/ ReLockBusy \/ ReDrained \/ ReFind \/ ReStart
    \/ ServerRecv
    \/ \E t \in {"MsgAwaitReply", "MsgRollForward", "MsgRollBackward",
                 "MsgIntersectFound"} : ServerSend(t)
    \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "No handler ever finds the ready channel full."
\* Literally: "SignalsFit is defined as: overflow is not true."
SignalsFit == ~overflow

\* In English: "Requests whose ready signal is not yet sent." The handler
\* sends the signal BEFORE requestNextAnswered (messageHandler), so between
\* the two a request is in both sig and out; counting out alone would
\* report Limit + 1 for that moment, which is harmless.
\* Literally: "Unsignalled is defined as out minus (if hpc equals "answer" then
\*   1, else 0)."
Unsignalled == out - (IF hpc = "answer" THEN 1 ELSE 0)

\* In English: "The signals waiting plus the requests not yet signalled
\* never exceed the channel's slots" - why SignalsFit holds, if it does.
\* Literally: "SignalBudget is defined as: the length of sig plus Unsignalled
\*   is less than or equal to Limit."
SignalBudget == Len(sig) + Unsignalled <= Limit

\* In English: "MsgFindIntersect is never sent with a request outstanding"
\* - illegal outside StIdle [C1], and the reference's Zero rule [R2].
\* Literally: "FindOnlyWhenIdle is defined as: findEarly is not true."
FindOnlyWhenIdle == ~findEarly

\* In English: "Once Reintersect has returned, no reply from before it is
\* delivered" - as Reintersect's documentation promises.
\* Literally: "NoStaleAfterReintersect is defined as: stale is not true."
NoStaleAfterReintersect == ~stale

\* In English: "The loop never keeps more than the window outstanding."
\* Literally: "WindowBound is defined as: Unsignalled is less than or equal to
\*   Limit."
WindowBound == Unsignalled <= Limit

-----------------------------------------------------------------------------
(* Reachability probes: each is EXPECTED to be violated. A violation shows  *)
(* the state is reachable, so the invariants above are not passing only     *)
(* because the model never gets near the edge.                              *)

\* In English: "The ready channel is never full." Violated = it does fill.
\* Literally: "ProbeChannelNeverFull is defined as: the length of sig is less
\*   than Limit."
ProbeChannelNeverFull == Len(sig) < Limit

\* In English: "Reintersect never completes." Violated = it does.
\* Literally: "ProbeNeverReintersects is defined as: rpc does not equal
\*   "done"."
ProbeNeverReintersects == rpc /= "done"

\* In English: "Reintersect never gives up." Violated = a callback's stop
\* during the drain does make it return ErrStopSyncProcess.
\* Literally: "ProbeNeverStopped is defined as: rpc does not equal "stopped"."
ProbeNeverStopped == rpc /= "stopped"

\* In English: "Reintersect never has to wait for a reply." Violated = it
\* does start draining with requests outstanding.
\* Literally: "ProbeNeverDrainsWork is defined as: it is not the case that rpc
\*   equals "drain" and out is greater than 0."
ProbeNeverDrainsWork == ~(rpc = "drain" /\ out > 0)
=============================================================================
