-------------------------- MODULE PerasClientOpMu --------------------------
(***************************************************************************)
(* The gOuroboros Peras votes client's request exchange lock, and the      *)
(* server's await goroutine, at the level of their goroutines              *)
(* (protocol/perasvotes/client.go: Sync, Done, RequestObjectIDs,           *)
(* RequestObjects; protocol/perasvotes/server.go: handleRequestObjectIDs,   *)
(* awaitObjectIDs; protocol/protocol.go: RunLoop, join).                   *)
(*                                                                         *)
(* Client. Every client call takes one lock for its whole request/reply    *)
(* exchange, so a reply belongs to the caller waiting for it. `Sync` holds *)
(* it for its whole life and calls the user's `VoteFunc` while holding it. *)
(*   main:  the lock is a sync.Mutex (opMu). A call blocks on it whatever  *)
(*          its context does, so                                           *)
(*          - C13: a VoteFunc that calls the client back waits for the     *)
(*            Sync that is running it: a deadlock;                         *)
(*          - C14: Done(ctx) waits for Sync and ignores its own context.   *)
(*   fix:   the lock is a one-slot channel taken in a select with the      *)
(*          caller's context (lockOp), and a call whose context carries    *)
(*          this client's VoteFunc marker fails at once with               *)
(*          ErrCalledFromVoteFunc.                                         *)
(*                                                                         *)
(* Server. On a blocking request with nothing to send, the server answers  *)
(* MsgAwaitReply and runs the user's AwaitObjectIDsFunc on a goroutine.    *)
(*   main:  a bare `go`: a panic in the callback kills the process, and    *)
(*          Stop's join does not wait for it (C15).                        *)
(*   fix:   RunLoop: the panic is recovered and reported on the protocol's *)
(*          error channel, and the goroutine is in Stop's join.            *)
(*                                                                         *)
(* Granularity: one step per lock acquire or release, per select choice,   *)
(* and per user callback start and return.                                 *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `sync`, `re`, `other` and `await` are program counters.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Fixed,          \* TRUE: fix/perasvotes-op-lock-and-await-panic; FALSE: main
    ReentryCtx,     \* the context VoteFunc passes when it calls the client back:
                    \*   "none" (it does not), "own" (its CallbackContext's Context),
                    \*   "foreignCancel" (another context, which ends),
                    \*   "foreignBackground" (another context, which never ends)
    DoneCaller,     \* TRUE: another goroutine calls Done(ctx) with a context that ends
    ServerAnswers,  \* FALSE: the server never answers Sync's request (the Go test gates it)
    Await,          \* TRUE: model the server's await goroutine and Stop
    AwaitOutcomes   \* what AwaitObjectIDsFunc may do: a subset of {"return", "panic", "hang"}

VARIABLES
    holder,         \* who holds the exchange lock: "none", "sync" or "other"
    sync,           \* Sync's next step
    re,             \* the VoteFunc's call back into the client: "idle", "call", "wait", "returned"
    reCancelled,    \* the context of that call has ended
    other,          \* the Done caller: "idle", "wait", "holding", "returned"
    otherCancelled, \* the Done caller's context has ended
    await,          \* the await goroutine: "none", "running", "panicking", "ended"
    crashed,        \* a panic escaped a goroutine: the process died
    reported,       \* a recovered panic reached the protocol's error channel
    stopper,        \* Stop(ctx) on the server: "idle", "joining", "returned"
    stopResult      \* what Stop returned: "none", "nil", "ctxErr"

\* In English: "all the variables."
\* Literally: "vars is defined as the tuple of all eleven variables."
vars == <<holder, sync, re, reCancelled, other, otherCancelled, await, crashed,
          reported, stopper, stopResult>>

\* In English: "Sync is about to take the lock; nobody else has started;
\* the await goroutine runs if it is modelled."
\* Literally: "Init is defined as: holder equals "none", sync equals "lock",
\*   re equals "idle", reCancelled is false, other equals "idle",
\*   otherCancelled is false, await equals "running" if Await else "none",
\*   crashed and reported are false, stopper equals "idle", and stopResult
\*   equals "none"."
Init ==
    /\ holder = "none"
    /\ sync = "lock"
    /\ re = "idle"
    /\ reCancelled = FALSE
    /\ other = "idle"
    /\ otherCancelled = FALSE
    /\ await = IF Await THEN "running" ELSE "none"
    /\ crashed = FALSE
    /\ reported = FALSE
    /\ stopper = "idle"
    /\ stopResult = "none"

\* In English: "the client's variables" and "the server's variables".
\* Literally: "clientVars is defined as the tuple of holder, sync, re,
\*   reCancelled, other and otherCancelled; serverVars is defined as the tuple
\*   of await, crashed, reported, stopper and stopResult."
clientVars == <<holder, sync, re, reCancelled, other, otherCancelled>>
serverVars == <<await, crashed, reported, stopper, stopResult>>

-----------------------------------------------------------------------------
(* Sync. *)

\* In English: "Sync takes the free lock."
\* Literally: "SyncLock is defined as: sync equals "lock", holder equals
\*   "none", holder becomes "sync", and sync becomes "exchange"."
SyncLock ==
    /\ sync = "lock" /\ holder = "none"
    /\ holder' = "sync" /\ sync' = "exchange"
    /\ UNCHANGED <<re, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "The server answers Sync's request, and Sync starts VoteFunc
\* on the vote, still holding the lock."
\* Literally: "SyncCallback is defined as: sync equals "exchange", and
\*   ServerAnswers, and sync becomes "callback"."
SyncCallback ==
    /\ sync = "exchange" /\ ServerAnswers
    /\ sync' = "callback"
    /\ UNCHANGED <<holder, re, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "VoteFunc calls the client back (RequestObjectIDs,
\* RequestObjects or Done) with the context ReentryCtx names."
\* Literally: "ReCall is defined as: sync equals "callback", ReentryCtx is
\*   not "none", re equals "idle", and re becomes "call"."
ReCall ==
    /\ sync = "callback" /\ ReentryCtx # "none" /\ re = "idle"
    /\ re' = "call"
    /\ UNCHANGED <<holder, sync, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "With the fix, a call carrying this client's VoteFunc marker
\* returns ErrCalledFromVoteFunc at once. Otherwise it starts waiting for
\* the lock."
\* Literally: "ReCheck is defined as: re equals "call", and re becomes
\*   "returned" if Fixed and ReentryCtx equals "own", else "wait"."
ReCheck ==
    /\ re = "call"
    /\ re' = IF Fixed /\ ReentryCtx = "own" THEN "returned" ELSE "wait"
    /\ UNCHANGED <<holder, sync, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "The call back takes the lock if it is free, runs its
\* exchange and releases it. It never is free while Sync runs VoteFunc; the
\* step is here so that nothing is assumed."
\* Literally: "ReLock is defined as: re equals "wait", holder equals "none",
\*   and re becomes "returned"."
ReLock ==
    /\ re = "wait" /\ holder = "none"
    /\ re' = "returned"
    /\ UNCHANGED <<holder, sync, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "The call back's context ends, if it is one that can."
\* Literally: "ReCancel is defined as: ReentryCtx is "own" or
\*   "foreignCancel", reCancelled is false, re is "call" or "wait", and
\*   reCancelled becomes true."
ReCancel ==
    /\ ReentryCtx \in {"own", "foreignCancel"} /\ ~reCancelled
    /\ re \in {"call", "wait"}
    /\ reCancelled' = TRUE
    /\ UNCHANGED <<holder, sync, re, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "With the fix, a waiting call whose context ended gives up
\* (the select in lockOp). A sync.Mutex has no such way out."
\* Literally: "ReGiveUp is defined as: Fixed, re equals "wait",
\*   reCancelled, and re becomes "returned"."
ReGiveUp ==
    /\ Fixed /\ re = "wait" /\ reCancelled
    /\ re' = "returned"
    /\ UNCHANGED <<holder, sync, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "VoteFunc returns, once its call back (if any) has
\* returned, and Sync releases the lock and ends."
\* Literally: "SyncEnd is defined as: sync equals "callback", and
\*   (ReentryCtx equals "none" or re equals "returned"), and holder becomes
\*   "none", and sync becomes "done"."
SyncEnd ==
    /\ sync = "callback"
    /\ \/ ReentryCtx = "none"
       \/ re = "returned"
    /\ holder' = "none" /\ sync' = "done"
    /\ UNCHANGED <<re, reCancelled, other, otherCancelled>> /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* Another goroutine's Done(ctx). *)

\* In English: "Another goroutine calls Done and starts waiting for the lock."
\* Literally: "OtherCall is defined as: DoneCaller, other equals "idle", and
\*   other becomes "wait"."
OtherCall ==
    /\ DoneCaller /\ other = "idle"
    /\ other' = "wait"
    /\ UNCHANGED <<holder, sync, re, reCancelled, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "Done takes the free lock, sends MsgDone and releases it."
\* Literally: "OtherLock is defined as: other equals "wait", holder equals
\*   "none", holder becomes "other", and other becomes "holding"."
OtherLock ==
    /\ other = "wait" /\ holder = "none"
    /\ holder' = "other" /\ other' = "holding"
    /\ UNCHANGED <<sync, re, reCancelled, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "Done has sent MsgDone; it releases the lock and returns."
\* Literally: "OtherUnlock is defined as: other equals "holding", holder
\*   becomes "none", and other becomes "returned"."
OtherUnlock ==
    /\ other = "holding"
    /\ holder' = "none" /\ other' = "returned"
    /\ UNCHANGED <<sync, re, reCancelled, otherCancelled>> /\ UNCHANGED serverVars

\* In English: "Done's context ends while it waits."
\* Literally: "OtherCancel is defined as: other equals "wait", otherCancelled
\*   is false, and otherCancelled becomes true."
OtherCancel ==
    /\ other = "wait" /\ ~otherCancelled
    /\ otherCancelled' = TRUE
    /\ UNCHANGED <<holder, sync, re, reCancelled, other>> /\ UNCHANGED serverVars

\* In English: "With the fix, Done gives up once its context ended."
\* Literally: "OtherGiveUp is defined as: Fixed, other equals "wait",
\*   otherCancelled, and other becomes "returned"."
OtherGiveUp ==
    /\ Fixed /\ other = "wait" /\ otherCancelled
    /\ other' = "returned"
    /\ UNCHANGED <<holder, sync, re, reCancelled, otherCancelled>> /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* The server's await goroutine, and Stop(ctx). *)

\* In English: "AwaitObjectIDsFunc returns: the goroutine replies and ends."
\* Literally: "AwaitReturn is defined as: await equals "running", "return"
\*   is in AwaitOutcomes, and await becomes "ended"."
AwaitReturn ==
    /\ await = "running" /\ "return" \in AwaitOutcomes
    /\ await' = "ended"
    /\ UNCHANGED clientVars /\ UNCHANGED <<crashed, reported, stopper, stopResult>>

\* In English: "AwaitObjectIDsFunc panics."
\* Literally: "AwaitPanic is defined as: await equals "running", "panic" is
\*   in AwaitOutcomes, and await becomes "panicking"."
AwaitPanic ==
    /\ await = "running" /\ "panic" \in AwaitOutcomes
    /\ await' = "panicking"
    /\ UNCHANGED clientVars /\ UNCHANGED <<crashed, reported, stopper, stopResult>>

\* In English: "The panic unwinds the goroutine. Under RunLoop, recoverLoop
\* turns it into an error on the protocol's error channel and the loop is
\* counted done. On a bare goroutine nothing recovers it, and the process
\* dies."
\* Literally: "AwaitUnwind is defined as: await equals "panicking", await
\*   becomes "ended", crashed becomes not Fixed, and reported becomes Fixed."
AwaitUnwind ==
    /\ await = "panicking"
    /\ await' = "ended"
    /\ crashed' = ~Fixed
    /\ reported' = Fixed
    /\ UNCHANGED clientVars /\ UNCHANGED <<stopper, stopResult>>

\* In English: "Stop(ctx) signals the protocol to stop and starts its join.
\* A callback that honours its context then returns ("hang" is one that
\* does not)."
\* Literally: "StopCall is defined as: Await, stopper equals "idle", and
\*   stopper becomes "joining"."
StopCall ==
    /\ Await /\ stopper = "idle"
    /\ stopper' = "joining"
    /\ UNCHANGED clientVars /\ UNCHANGED <<await, crashed, reported, stopResult>>

\* In English: "The join returns nil once the loops it counts are done. On
\* main it counts only the engine's own loops, so it does not wait for the
\* bare goroutine; with the fix RunLoop adds the await goroutine to it."
\* Literally: "StopJoined is defined as: stopper equals "joining", and (not
\*   Fixed, or await is "none" or "ended"), and stopper becomes "returned"
\*   and stopResult becomes "nil"."
StopJoined ==
    /\ stopper = "joining"
    /\ ~Fixed \/ await \in {"none", "ended"}
    /\ stopper' = "returned" /\ stopResult' = "nil"
    /\ UNCHANGED clientVars /\ UNCHANGED <<await, crashed, reported>>

\* In English: "Stop's own context ends first: the join returns its error."
\* Literally: "StopCtxEnds is defined as: stopper equals "joining", and
\*   stopper becomes "returned" and stopResult becomes "ctxErr"."
StopCtxEnds ==
    /\ stopper = "joining"
    /\ stopper' = "returned" /\ stopResult' = "ctxErr"
    /\ UNCHANGED clientVars /\ UNCHANGED <<await, crashed, reported>>

\* In English: "A callback that honours its context returns once Stop has
\* signalled."
\* Literally: "AwaitStopped is defined as: await equals "running", stopper
\*   is not "idle", AwaitOutcomes is not just {"hang"}, and await becomes
\*   "ended"."
AwaitStopped ==
    /\ await = "running" /\ stopper # "idle"
    /\ AwaitOutcomes # {"hang"}
    /\ await' = "ended"
    /\ UNCHANGED clientVars /\ UNCHANGED <<crashed, reported, stopper, stopResult>>

-----------------------------------------------------------------------------

\* In English: "any step of any goroutine, or of a context ending."
\* Literally: "Progress is defined as the disjunction of every step above."
Progress ==
    \/ SyncLock \/ SyncCallback \/ ReCall \/ ReCheck \/ ReLock \/ ReCancel
    \/ ReGiveUp \/ SyncEnd
    \/ OtherCall \/ OtherLock \/ OtherUnlock \/ OtherCancel \/ OtherGiveUp
    \/ AwaitReturn \/ AwaitPanic \/ AwaitUnwind \/ AwaitStopped
    \/ StopCall \/ StopJoined \/ StopCtxEnds

\* In English: "Once nothing can move, nothing changes. Whether that is a
\* proper ending is what the invariants judge."
\* Literally: "Rest is defined as: Progress is not enabled, and vars is
\*   unchanged."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is a goroutine's step, or resting once none can move."
\* Literally: "Next is defined as: Progress or Rest."
Next == Progress \/ Rest

\* In English: "start in Init; every later step is a Next step."
\* Literally: "Spec is defined as: Init, and always every step is a Next
\*   step or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "no step can be taken."
\* Literally: "Quiescent is defined as: Progress is not enabled."
Quiescent == ~ENABLED Progress

\* In English: "A call VoteFunc makes back into its client never waits for
\* ever: once nothing can move, it has returned, unless its context is one
\* that never ends (the documented case: it waits for Sync). The reference
\* inbound side issues every request from its one protocol thread
\* (ouroboros-network ObjectDiffusion Inbound), so no request re-enters."
\* Literally: "VoteFuncCallReturns is defined as: if Quiescent and
\*   ReentryCtx is not "foreignBackground", then re is "idle" or
\*   "returned"."
VoteFuncCallReturns ==
    (Quiescent /\ ReentryCtx # "foreignBackground") => re \in {"idle", "returned"}

\* In English: "A Done whose context ended has returned once nothing can
\* move: a call honours its own context."
\* Literally: "CancelledDoneReturns is defined as: if Quiescent and
\*   otherCancelled, then other is not "wait"."
CancelledDoneReturns == (Quiescent /\ otherCancelled) => other # "wait"

\* In English: "every call has returned and Sync has ended, once nothing
\* can move." Stronger than the two above: it also asks a call with a
\* context that never ends to return.
\* Literally: "EveryCallReturns is defined as: if Quiescent then sync is
\*   "done", re is "idle" or "returned", and other is "idle" or "returned"."
EveryCallReturns ==
    Quiescent => /\ sync = "done"
                 /\ re \in {"idle", "returned"}
                 /\ other \in {"idle", "returned"}

\* In English: "A panic in a user callback never kills the process."
\* Literally: "NoProcessCrash is defined as: crashed is false."
NoProcessCrash == ~crashed

\* In English: "Stop returns nil only once the await goroutine has ended:
\* nothing the server started outlives a successful Stop."
\* Literally: "StopJoinsAwait is defined as: if stopResult equals "nil"
\*   then await is "none" or "ended"."
StopJoinsAwait == stopResult = "nil" => await \in {"none", "ended"}

\* In English: "The lock is held by one caller at most, and Sync holds it
\* from its first exchange until VoteFunc has returned."
\* Literally: "LockSound is defined as: holder is one of "none", "sync" and
\*   "other", and if sync is "exchange" or "callback" then holder equals
\*   "sync"."
LockSound ==
    /\ holder \in {"none", "sync", "other"}
    /\ (sync \in {"exchange", "callback"}) => holder = "sync"
=============================================================================
