--------------------------- MODULE ChainSyncClient ---------------------------
(***************************************************************************)
(* Model 04, slice 1: the gOuroboros chain-sync client's sync window and   *)
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
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
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

vars == <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight, toSend,
          loopStop, hpc, hsig, rpc, stopsBefore, found, toServer, toClient,
          sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "A sync is running: intersection 1 found, the initial request
\* sent, the loop waiting with that one request in flight."
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

LoopLockBusy ==
    /\ lpc = "lockBusy" /\ busy = None
    /\ busy' = "loop" /\ lpc' = "lockLC"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, lc, inFlight, toSend,
                   loopStop, hpc, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Under lifecycleMutex: stopped? release both locks and exit.
\* Otherwise one reply was consumed; the requests to send are the window
\* minus what is still in flight."
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
HandleLock ==
    /\ hpc = "lock" /\ lc = None
    /\ lc' = "handler" /\ hpc' = "send"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lpc, inFlight,
                   toSend, loopStop, hsig, rpc, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Send the signal if the channel has room, count a stop
\* request, and release lifecycleMutex. With no room it blocks HOLDING the
\* lock; the model records that and stops here."
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
ReBegin ==
    /\ rpc = "idle" /\ lc = None
    /\ stopsBefore' = stopReqs
    /\ loopStop' = TRUE
    /\ rpc' = "waitLoop"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, busy, lc, lpc, inFlight,
                   toSend, hpc, hsig, found, toServer, toClient, sview,
                   sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Wait for the loop to exit, then take busyMutex."
ReLockBusy ==
    /\ rpc = "waitLoop" /\ lpc \in {"exited", "none"} /\ busy = None
    /\ busy' = "re" /\ rpc' = "drain"
    /\ UNCHANGED <<out, sig, stopReqs, sent, epoch, lc, lpc, inFlight,
                   toSend, loopStop, hpc, hsig, stopsBefore, found, toServer,
                   toClient, sview, sepoch, awaited, findEarly, stale, overflow>>

\* In English: "Wait until every outstanding request is answered; then
\* discard leftover ready signals; then, if a callback asked to stop during
\* the drain, give up (ErrStopSyncProcess)."
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
Finished ==
    /\ \/ /\ rpc \in {"done", "stopped"}
          /\ toServer = <<>> /\ toClient = <<>> /\ hpc = "idle"
          /\ lpc \in {"wait", "exited", "none"} /\ busy = None /\ lc = None
       \/ overflow
    /\ UNCHANGED vars

Next ==
    \/ LoopWait \/ LoopLockBusy \/ LoopTopUp \/ LoopSendOne \/ LoopSendDone
    \/ HandleTake \/ HandleLock \/ HandleSend \/ HandleAnswer
    \/ ReBegin \/ ReLockBusy \/ ReDrained \/ ReFind \/ ReStart
    \/ ServerRecv
    \/ \E t \in {"MsgAwaitReply", "MsgRollForward", "MsgRollBackward",
                 "MsgIntersectFound"} : ServerSend(t)
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "No handler ever finds the ready channel full."
SignalsFit == ~overflow

\* In English: "Requests whose ready signal is not yet sent." The handler
\* sends the signal BEFORE requestNextAnswered (messageHandler), so between
\* the two a request is in both sig and out; counting out alone would
\* report Limit + 1 for that moment, which is harmless.
Unsignalled == out - (IF hpc = "answer" THEN 1 ELSE 0)

\* In English: "The signals waiting plus the requests not yet signalled
\* never exceed the channel's slots" - why SignalsFit holds, if it does.
SignalBudget == Len(sig) + Unsignalled <= Limit

\* In English: "MsgFindIntersect is never sent with a request outstanding"
\* - illegal outside StIdle [C1], and the reference's Zero rule [R2].
FindOnlyWhenIdle == ~findEarly

\* In English: "Once Reintersect has returned, no reply from before it is
\* delivered" - as Reintersect's documentation promises.
NoStaleAfterReintersect == ~stale

\* In English: "The loop never keeps more than the window outstanding."
WindowBound == Unsignalled <= Limit

-----------------------------------------------------------------------------
(* Reachability probes: each is EXPECTED to be violated. A violation shows  *)
(* the state is reachable, so the invariants above are not passing only     *)
(* because the model never gets near the edge.                              *)

\* In English: "The ready channel is never full." Violated = it does fill.
ProbeChannelNeverFull == Len(sig) < Limit

\* In English: "Reintersect never completes." Violated = it does.
ProbeNeverReintersects == rpc /= "done"

\* In English: "Reintersect never gives up." Violated = a callback's stop
\* during the drain does make it return ErrStopSyncProcess.
ProbeNeverStopped == rpc /= "stopped"

\* In English: "Reintersect never has to wait for a reply." Violated = it
\* does start draining with requests outstanding.
ProbeNeverDrainsWork == ~(rpc = "drain" /\ out > 0)
=============================================================================
