------------------------- MODULE LeiosVotesLifecycle -------------------------
(***************************************************************************)
(* The gOuroboros LeiosVotes client's Sync, vote loop and Stop, at the     *)
(* level of their locks and goroutines (protocol/leiosvotes/client.go:     *)
(* Sync, startVoteLoop, voteLoop, sendRequestNext, isStopping, Stop;       *)
(* protocol/protocol.go: RunLoop, join; muxer/loops.go:                    *)
(* StartProtocolLoops, CloseProtocolLoops). The LeiosNotify client         *)
(* (protocol/leiosnotify/client.go: Sync, startNotificationLoop,           *)
(* notificationLoop, sendRequests, Stop) has the same shape: busyMutex     *)
(* for the loop flag, sendMutex from the quitting check through the sends, *)
(* and a loop started through RunLoop, so this model covers both.          *)
(*                                                                         *)
(* Sync holds busyMutex. Under sendMutex it checks `stopping` and the      *)
(* protocol's done state and sends its requests; then it starts the vote   *)
(* loop through RunLoop and marks it running (syncRunning). The loop takes *)
(* a vote, calls VoteFunc, checks for shutdown under sendMutex and refills *)
(* under sendMutex; on the way out it clears syncRunning under busyMutex.  *)
(* Stop sets `stopping` and queues MsgDone under sendMutex, stops the      *)
(* protocol and waits for its goroutines, RunLoop's included [G3].         *)
(*                                                                         *)
(* RunLoop starts nothing once the connection has begun to close           *)
(* (CloseProtocolLoops) or the instance's goroutines have been joined.    *)
(*   7cd17437:  Sync marks the loop running before RunLoop and ignores     *)
(*              its result: Sync returns nil and the client stays marked   *)
(*              as syncing with no loop (LeiosVotesLifecycleRunLoopBug.cfg).*)
(*   fix:       Sync marks it running only when RunLoop started it, and    *)
(*              returns ErrProtocolShuttingDown otherwise.                 *)
(*                                                                         *)
(* Granularity: one step per lock acquire or release (the check-and-send   *)
(* under sendMutex is one step, as the lock makes it), per select choice,  *)
(* per user callback start and return.                                     *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoRequestAfterDone    no VotesRequestNext is queued after MsgDone.    *)
(*   SyncReportsLoop       a Sync that returned nil started a loop.        *)
(*   SyncFlagHasLoop       outside Sync, the client is marked as syncing   *)
(*                         only while a loop runs.                         *)
(*   NoCallbackAfterStop   once Stop has returned nil, the loop has ended. *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [C1] CIP-0164 03387471 lines 1386-1416: MsgDone from Idle; no         *)
(*        request after it.                                                *)
(*   [G3] gOuroboros 7cd17437, protocol/protocol.go RunLoop: "Stop and     *)
(*        StopForRestart wait for it ... RunLoop reports false, and starts *)
(*        nothing, once the instance's goroutines have been joined or the  *)
(*        connection has begun to close."                                  *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `syncPc`, `loop` and `stopPc` are program counters.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Fixed,          \* TRUE: Sync honours RunLoop's result; FALSE: 7cd17437
    StopLocked,     \* TRUE: Stop sets stopping and queues MsgDone under
                    \*   sendMutex (7cd17437); FALSE: a mutation without it
    ConnCloses,     \* TRUE: the connection may begin to close at any time
    MaxRequests     \* how many requests may be sent in all (keeps it finite)

VARIABLES
    busy,           \* who holds busyMutex: "none" or "sync"
    sendHeld,       \* Sync holds sendMutex between its check and its send
    syncPc,         \* Sync: "idle", "send", "queue", "start", "returned"
    syncResult,     \* what Sync returned: "none", "nil" or "shutdown"
    syncRunning,    \* Client.syncRunning
    loop,           \* the vote loop: "none", "running", "callback",
                    \*   "exiting" or "ended"
    stopping,       \* Client.stopping
    doneQueued,     \* MsgDone has been queued
    requestAfterDone, \* a request was queued after MsgDone
    outstanding,    \* votes asked for and not yet taken
    requests,       \* requests sent so far
    protoStopped,   \* the protocol has been told to stop (IsDone, DoneChan)
    loopsClosed,    \* RunLoop refuses to start a loop
    stopPc          \* Stop: "idle", "signalled", "returned"

vars == <<busy, sendHeld, syncPc, syncResult, syncRunning, loop, stopping, doneQueued,
          requestAfterDone, outstanding, requests, protoStopped, loopsClosed,
          stopPc>>

\* In English: "Nothing has happened yet."
Init ==
    /\ busy = "none"
    /\ sendHeld = FALSE
    /\ syncPc = "idle"
    /\ syncResult = "none"
    /\ syncRunning = FALSE
    /\ loop = "none"
    /\ stopping = FALSE
    /\ doneQueued = FALSE
    /\ requestAfterDone = FALSE
    /\ outstanding = 0
    /\ requests = 0
    /\ protoStopped = FALSE
    /\ loopsClosed = FALSE
    /\ stopPc = "idle"

\* In English: "Queue one request: count it, and note it if MsgDone is
\* already queued."
\* Literally: "QueueRequest is defined as: requests goes up by one,
\*   outstanding goes up by one, and requestAfterDone becomes true if
\*   doneQueued."
QueueRequest ==
    /\ requests' = requests + 1
    /\ outstanding' = outstanding + 1
    /\ requestAfterDone' = (requestAfterDone \/ doneQueued)

\* In English: "Shutdown as Sync and the loop see it: stopping, or the
\* protocol done."
ShuttingDown == stopping \/ protoStopped

-----------------------------------------------------------------------------
(* Sync. *)

\* In English: "Sync takes busyMutex; a loop already marked running makes it
\* return an error, which ends this model's single Sync as well."
SyncLock ==
    /\ syncPc = "idle" /\ busy = "none"
    /\ busy' = "sync"
    /\ syncPc' = "send"
    /\ UNCHANGED <<sendHeld, syncResult, syncRunning, loop, stopping, doneQueued,
                   requestAfterDone, outstanding, requests, protoStopped,
                   loopsClosed, stopPc>>

\* In English: "Sync takes sendMutex and checks for shutdown: if shutting
\* down it returns ErrProtocolShuttingDown, releasing both locks."
SyncCheck ==
    /\ syncPc = "send" /\ ~sendHeld /\ requests < MaxRequests
    /\ IF ShuttingDown
          THEN /\ syncPc' = "returned" /\ syncResult' = "shutdown"
               /\ busy' = "none"
               /\ UNCHANGED sendHeld
          ELSE /\ sendHeld' = TRUE
               /\ syncPc' = "queue"
               /\ UNCHANGED <<busy, syncResult>>
    /\ UNCHANGED <<syncRunning, loop, stopping, doneQueued, requestAfterDone,
                   outstanding, requests, protoStopped, loopsClosed, stopPc>>

\* In English: "Still under sendMutex, Sync queues its request and
\* releases sendMutex."
SyncQueue ==
    /\ syncPc = "queue"
    /\ QueueRequest
    /\ sendHeld' = FALSE
    /\ syncPc' = "start"
    /\ UNCHANGED <<busy, syncResult, syncRunning, loop, stopping, doneQueued,
                   protoStopped, loopsClosed, stopPc>>

\* In English: "RunLoop starts the loop unless loops are closed. At
\* 7cd17437 Sync marks the loop running whatever RunLoop did and returns
\* nil; with the fix it marks it only if the loop started, and returns
\* ErrProtocolShuttingDown otherwise. Either way it releases busyMutex."
SyncStart ==
    /\ syncPc = "start"
    /\ loop' = IF loopsClosed THEN loop ELSE "running"
    /\ syncRunning' = IF Fixed THEN ~loopsClosed ELSE TRUE
    /\ syncResult' = IF Fixed /\ loopsClosed THEN "shutdown" ELSE "nil"
    /\ busy' = "none"
    /\ syncPc' = "returned"
    /\ UNCHANGED <<sendHeld, stopping, doneQueued, requestAfterDone, outstanding,
                   requests, protoStopped, loopsClosed, stopPc>>

-----------------------------------------------------------------------------
(* The vote loop. *)

\* In English: "A vote arrives and the loop calls VoteFunc."
LoopVote ==
    /\ loop = "running" /\ outstanding > 0 /\ ~protoStopped
    /\ outstanding' = outstanding - 1
    /\ loop' = "callback"
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, stopping, doneQueued,
                   requestAfterDone, requests, protoStopped, loopsClosed,
                   stopPc>>

\* In English: "VoteFunc returns. Under sendMutex, as one step, the loop
\* checks for shutdown (isStopping, then sendRequestNext's own check): if
\* shutting down it leaves; otherwise it may refill with one request."
LoopAfterVote ==
    /\ loop = "callback" /\ ~sendHeld
    /\ IF ShuttingDown \/ requests >= MaxRequests
          THEN /\ loop' = "exiting"
               /\ UNCHANGED <<requestAfterDone, outstanding, requests>>
          ELSE /\ QueueRequest
               /\ loop' = "running"
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, stopping, doneQueued,
                   protoStopped, loopsClosed, stopPc>>

\* In English: "DoneChan closes: a waiting loop leaves."
LoopDone ==
    /\ loop = "running" /\ protoStopped
    /\ loop' = "exiting"
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, stopping, doneQueued,
                   requestAfterDone, outstanding, requests, protoStopped,
                   loopsClosed, stopPc>>

\* In English: "The loop's deferred function clears syncRunning under
\* busyMutex, and the loop has ended."
LoopExit ==
    /\ loop = "exiting" /\ busy = "none"
    /\ syncRunning' = FALSE
    /\ loop' = "ended"
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, stopping, doneQueued,
                   requestAfterDone, outstanding, requests, protoStopped,
                   loopsClosed, stopPc>>

-----------------------------------------------------------------------------
(* Stop and the connection. *)

\* In English: "Stop, under sendMutex as one step (or, in the mutation, in
\* two unlocked steps whose first is this), sets stopping and queues
\* MsgDone, then tells the protocol to stop."
StopSignal ==
    /\ stopPc = "idle"
    /\ StopLocked => ~sendHeld
    /\ stopping' = TRUE
    /\ doneQueued' = StopLocked
    /\ stopPc' = IF StopLocked THEN "signalled" ELSE "queue"
    /\ protoStopped' = StopLocked
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, loop,
                   requestAfterDone, outstanding, requests, loopsClosed>>

\* In English: "The mutation's second step: MsgDone queued, protocol told."
StopQueue ==
    /\ stopPc = "queue"
    /\ doneQueued' = TRUE
    /\ protoStopped' = TRUE
    /\ stopPc' = "signalled"
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, loop, stopping,
                   requestAfterDone, outstanding, requests, loopsClosed>>

\* In English: "Stop's join returns once the loop is not running; no loop
\* starts after the join (RunLoop refuses then)."
StopJoin ==
    /\ stopPc = "signalled"
    /\ loop \in {"none", "ended"}
    /\ stopPc' = "returned"
    /\ loopsClosed' = TRUE
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, loop, stopping,
                   doneQueued, requestAfterDone, outstanding, requests,
                   protoStopped>>

\* In English: "The connection begins to close: RunLoop starts nothing
\* more. The protocol itself is stopped later."
ConnClose ==
    /\ ConnCloses /\ ~loopsClosed
    /\ loopsClosed' = TRUE
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, loop, stopping,
                   doneQueued, requestAfterDone, outstanding, requests,
                   protoStopped, stopPc>>

\* In English: "Then the connection stops the protocol."
ConnStopsProtocol ==
    /\ loopsClosed /\ ~protoStopped
    /\ protoStopped' = TRUE
    /\ UNCHANGED <<sendHeld, busy, syncPc, syncResult, syncRunning, loop, stopping,
                   doneQueued, requestAfterDone, outstanding, requests,
                   loopsClosed, stopPc>>

\* In English: "Nothing more can happen."
Finished ==
    /\ syncPc \in {"idle", "returned"}
    /\ loop \in {"none", "ended"}
    /\ stopPc \in {"idle", "returned"}

Next ==
    \/ SyncLock \/ SyncCheck \/ SyncQueue \/ SyncStart
    \/ LoopVote \/ LoopAfterVote \/ LoopDone \/ LoopExit
    \/ StopSignal \/ StopQueue \/ StopJoin
    \/ ConnClose \/ ConnStopsProtocol
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
    /\ busy \in {"none", "sync"}
    /\ sendHeld \in BOOLEAN
    /\ syncPc \in {"idle", "send", "queue", "start", "returned"}
    /\ syncResult \in {"none", "nil", "shutdown"}
    /\ loop \in {"none", "running", "callback", "exiting", "ended"}
    /\ stopPc \in {"idle", "queue", "signalled", "returned"}
    /\ requests \in 0..MaxRequests
    /\ outstanding \in 0..MaxRequests

\* In English: "No request is queued after MsgDone [C1]."
NoRequestAfterDone == ~requestAfterDone

\* In English: "A Sync that returned nil started a loop."
SyncReportsLoop == syncResult = "nil" => loop # "none"

\* In English: "Outside Sync, the client is marked as syncing only while a
\* loop has not ended."
SyncFlagHasLoop ==
    (syncRunning /\ syncPc \in {"idle", "returned"})
        => loop \in {"running", "callback", "exiting"}

\* In English: "Once Stop has returned, the loop is not running VoteFunc
\* and cannot start to."
NoCallbackAfterStop == stopPc = "returned" => loop \in {"none", "ended"}

\* Probe, EXPECTED to be violated: "The connection never closes before
\* Sync starts its loop."
ProbeNoCloseBeforeStart == ~(syncPc = "start" /\ loopsClosed)
=============================================================================
