----------------------- MODULE BlockFetchBusyDelivery -----------------------
(***************************************************************************)
(* Model 06, slice 3: the block-fetch client's locks, its user callbacks,  *)
(* and Stop, one Go primitive per step.                                    *)
(*                                                                         *)
(* Each goroutine is a stack of frames with a program counter, in the      *)
(* style of specs/connection/ConnectionShutdown.tla. A frame is pushed     *)
(* when a user callback calls Client.Stop, so a callback can re-enter the  *)
(* client exactly as Go code can. The goroutines (protocol/blockfetch/     *)
(* client.go at gOuroboros origin/main f9ba2d3c):                          *)
(*                                                                         *)
(*   s1, s2  callers of Stop (:473-550).                                   *)
(*   recv    the engine's recvLoop running the handlers: handleBlock       *)
(*           (:1401; queueMutex then deliveryMu hand over hand at :1443,   *)
(*           pipelineContext :553 -> lifecycleMutex, recordBlock under     *)
(*           queueMutex :1542, BlockFunc under deliveryMu :1581) and       *)
(*           handleBatchDone (:1707; remove, then resolve, which calls     *)
(*           RangeDoneFunc).                                               *)
(*   dl      watchRangeDeadline for request 1 (:1071): timer, removes the  *)
(*           protocol's requests under queueMutex, SendError, then resolves*)
(*           each under its deliveryMu (:1107-1111).                       *)
(*   sw      the shutdown watcher (:460 -> :1315): waits for DoneChan,     *)
(*           drains, resolves.                                             *)
(*   snd     RequestRange's sendRequestRange for request 3, as open PR     *)
(*           #3114 (head d10daf24) has it: token, append marked sending,   *)
(*           send, unmark, token back, then resolve a deferred drain.      *)
(*                                                                         *)
(* A callback (BlockFunc, RangeDoneFunc) is a step of the goroutine that   *)
(* calls it. It may return, call Stop (a new frame), or call RequestRange  *)
(* (the send token and queueMutex, briefly).                               *)
(*                                                                         *)
(* No specification source: this is gOuroboros's own Go API. The reference *)
(* client (ouroboros-network 5f356486ab3e, ouroboros-network/lib/Ouroboros/*)
(* Network/BlockFetch/Client.hs:272) hands each block to addFetchedBlock   *)
(* on the protocol thread with no client lock held, and has no completion  *)
(* callback at all; that is the contract followed here.                    *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Fixed,                  \* TRUE: Stop's not-running branch releases
                            \* lifecycleMutex before resolving, and resolves
                            \* each request under its deliveryMu (the fix).
                            \* FALSE: origin/main.
    Stoppers,               \* which of "s1", "s2" call Stop
    CbStop,                 \* goroutines whose callbacks may call Stop
    CbRequestRange,         \* TRUE: a callback may call RequestRange
    WithSender,             \* TRUE: snd runs
    MaxDepth,               \* most frames on one goroutine (2: one re-entry)
    \* Mutations, each FALSE in the code as it is:
    ResolveUnderQueue,      \* a drain resolves while still holding queueMutex
    NoOnce,                 \* resolve without resolveOnce
    DeadlineResolvesQueued, \* the deadline watcher resolves before removing
    EarlyDeferredCallback,  \* snd resolves before handing the token back
    SenderIgnoresDeferred   \* snd never resolves a request a drain deferred

VARIABLES
    st,     \* the shared state, one record (fields below)
    stk,    \* stk[g]: goroutine g's frames, innermost last
    cbHeld  \* cbHeld[g]: the locks g held when it entered a user callback

\* Literally: "vars is defined as the tuple of st, stk and cbHeld."
vars == <<st, stk, cbHeld>>

\* In English: "The six goroutines."
\* Literally: "G is defined as the set of "s1", "s2", "recv", "dl", "sw" and
\*   "snd"."
G == {"s1", "s2", "recv", "dl", "sw", "snd"}

\* In English: "Requests 1 and 2 are outstanding at the start; 3 is snd's."
\* Literally: "R is defined as the set of 1, 2 and 3."
R == {1, 2, 3}

\* In English: "A lock is held by a goroutine, or by nobody."
\* Literally: "Owner is defined as G union the set containing "none"."
Owner == G \cup {"none"}

\* In English: "A new frame starts at label l with nothing to drain."
\* Literally: "Frame of l is defined as the record whose pc is l, pend is the
\*   empty sequence, withD is FALSE, ret is "done", cbReq is 0 and cbRet is
\*   "done"."
Frame(l) == [pc |-> l, pend |-> <<>>, withD |-> FALSE, ret |-> "done",
             cbReq |-> 0, cbRet |-> "done"]

\* In English: "The innermost frame of goroutine g."
\* Literally: "Top of g is defined as element Len of stk of g of stk of g."
Top(g) == stk[g][Len(stk[g])]

\* In English: "Goroutine g's current label."
\* Literally: "Pc of g is defined as the pc field of Top of g."
Pc(g) == Top(g).pc

\* In English: "The set of the elements of sequence s."
\* Literally: "Elems of s is defined as the set of s of i for i in 1 to Len
\*   of s."
Elems(s) == {s[i] : i \in 1..Len(s)}

\* In English: "Sequence s without the elements in set x."
\* Literally: "Without of s and x is defined as the subsequence of s of the
\*   elements r such that r is not a member of x."
Without(s, x) == SelectSeq(s, LAMBDA r : r \notin x)

\* In English: "The locks goroutine g holds right now."
\* Every lock name is a pair: "L", 0; "Q", 0; "T", 0; or "D", r.
\* Literally: "HeldBy of g is defined as the set of pairs n, 0 for n in the
\*   names among "L", "Q", "T" whose field of st equals g, union the set of
\*   pairs "D", r for r in R such that st.D of r equals g."
HeldBy(g) == {<<n, 0>> : n \in {n2 \in {"L", "Q", "T"} : st[n2] = g}}
             \cup {<<"D", r>> : r \in {r2 \in R : st.D[r2] = g}}

-----------------------------------------------------------------------------
(* Frame and lock helpers. *)

\* In English: "Move g's innermost frame to label l; nothing else changes
\* in the frames."
\* Literally: "Goto of g and l is defined as: stk in the next state equals stk
\*   except that the pc of g's innermost frame is l."
Goto(g, l) == stk' = [stk EXCEPT ![g][Len(stk[g])].pc = l]

\* In English: "Replace g's innermost frame with f."
\* Literally: "SetTop of g and f is defined as: stk in the next state equals
\*   stk except that g's innermost frame is f."
SetTop(g, f) == stk' = [stk EXCEPT ![g][Len(stk[g])] = f]

\* In English: "Start a drain of p (taking queueMutex first when first is
\* "dr_lockq"), resolving behind deliveryMu when withD, then go to ret."
\* Literally: "Drain of g, first, p, withD and ret is defined as SetTop of g
\*   and Top of g except that pc is first, pend is p, withD is withD and ret
\*   is ret."
Drain(g, first, p, withD, ret) ==
    SetTop(g, [Top(g) EXCEPT !.pc = first, !.pend = p, !.withD = withD,
                             !.ret = ret])

\* In English: "Return from g's innermost frame: a goroutine's last frame
\* ends it; returning from a Stop called by a callback ends that callback."
\* Literally: "Pop of g is defined as: if Len of stk of g equals 1, then Goto
\*   of g and "done" and cbHeld is unchanged; else stk in the next state
\*   equals stk except that g's stack is its first Len minus 1 frames, and
\*   if that leaves one frame, cbHeld of g in the next state is empty, else
\*   cbHeld is unchanged."
Pop(g) ==
    IF Len(stk[g]) = 1
        THEN Goto(g, "done") /\ UNCHANGED cbHeld
        ELSE /\ stk' = [stk EXCEPT ![g] = SubSeq(@, 1, Len(@) - 1)]
             /\ IF Len(stk[g]) = 2 THEN cbHeld' = [cbHeld EXCEPT ![g] = {}]
                                   ELSE UNCHANGED cbHeld

\* In English: "Enter a user callback for request r, coming back at label
\* back; remember which locks are held on entry (those held now, less the
\* ones this same step releases)."
\* Literally: "EnterCb of g, r, back and released is defined as: SetTop of g
\*   and Top of g except that pc is "cb", cbReq is r and cbRet is back, and
\*   cbHeld of g in the next state is cbHeld of g union (HeldBy of g minus
\*   released)."
EnterCb(g, r, back, released) ==
    /\ SetTop(g, [Top(g) EXCEPT !.pc = "cb", !.cbReq = r, !.cbRet = back])
    /\ cbHeld' = [cbHeld EXCEPT ![g] = @ \cup (HeldBy(g) \ released)]

\* In English: "Leave a callback: go back to where it was called, and if this
\* was the outermost callback, g no longer holds anything across one."
\* Literally: "LeaveCb of g is defined as: Goto of g and the cbRet of Top of
\*   g, and if Len of stk of g equals 1 then cbHeld of g in the next state is
\*   empty, else cbHeld is unchanged."
LeaveCb(g) ==
    /\ Goto(g, Top(g).cbRet)
    /\ IF Len(stk[g]) = 1 THEN cbHeld' = [cbHeld EXCEPT ![g] = {}]
                          ELSE UNCHANGED cbHeld

-----------------------------------------------------------------------------
(* Initial state. *)

\* In English: "Requests 1 and 2 have been sent and are queued; the server
\* will answer request 1 (a block, then MsgBatchDone) and then request 2; the
\* client is running and nobody holds a lock."
\* Literally: "Init is defined as: st equals the record whose L, Q and T are
\*   "none", D maps each r in R to "none", lstate is "running", proto is
\*   "running", recvExited is FALSE, queue is the sequence 1, 2, wire is the
\*   four answers, once maps each r to "none", cbRuns maps each r to 0,
\*   sending and deferred map each r to FALSE, and sendOk is FALSE; and stk
\*   maps s1 and s2 to a frame at "stop" if they are in Stoppers else at
\*   "done", recv to "rv_idle", dl to "dl_wait", sw to "sw_wait", snd to
\*   "sn_tok" if WithSender else "done"; and cbHeld maps every g to the
\*   empty set."
Init ==
    /\ st = [L |-> "none", Q |-> "none", T |-> "none",
             D |-> [r \in R |-> "none"],
             lstate |-> "running", proto |-> "running", recvExited |-> FALSE,
             queue |-> <<1, 2>>,
             wire |-> <<<<"blk", 1>>, <<"done", 1>>, <<"blk", 2>>, <<"done", 2>>>>,
             once |-> [r \in R |-> "none"], cbRuns |-> [r \in R |-> 0],
             sending |-> [r \in R |-> FALSE], deferred |-> [r \in R |-> FALSE],
             sendOk |-> FALSE]
    /\ stk = [g \in G |->
                << Frame(CASE g \in {"s1", "s2"} -> IF g \in Stoppers THEN "stop" ELSE "done"
                           [] g = "recv" -> "rv_idle"
                           [] g = "dl"   -> "dl_wait"
                           [] g = "sw"   -> "sw_wait"
                           [] g = "snd"  -> IF WithSender THEN "sn_tok" ELSE "done") >>]
    /\ cbHeld = [g \in G |-> {}]

-----------------------------------------------------------------------------
(* Stop (:473-550). New and Starting branches are the same shape as the     *)
(* Stopped branch and are not modelled separately.                          *)

\* In English: "c.lifecycleMutex.Lock() (:474). A goroutine that already
\* holds it waits forever: Go mutexes are not reentrant."
\* Literally: "StopLock of g is defined as: Pc of g equals "stop", and st.L
\*   equals "none", and st in the next state equals st except L is g, and
\*   Goto of g and "stop_branch", and cbHeld is unchanged."
StopLock(g) ==
    /\ Pc(g) = "stop" /\ st.L = "none"
    /\ st' = [st EXCEPT !.L = g]
    /\ Goto(g, "stop_branch") /\ UNCHANGED cbHeld

\* In English: "The switch on lifecycleState (:477). Running: go on to the
\* normal stop. Stopped: on main, failOutstanding runs with lifecycleMutex
\* still held (:486); with the fix, the lock is released first and each
\* request is resolved behind its deliveryMu."
\* Literally: "StopBranch of g is defined as: Pc of g equals "stop_branch",
\*   and if st.lstate equals "running" then Goto of g and "stop_send" and st
\*   is unchanged; else if Fixed then st.L in the next state is "none" and
\*   Drain of g from "dr_lockq" with an empty list, withD TRUE, back to
\*   "stop_end"; else st is unchanged and Drain of g from "dr_lockq", withD
\*   FALSE, back to "stop_unlock_end"; and cbHeld is unchanged."
StopBranch(g) ==
    /\ Pc(g) = "stop_branch"
    /\ IF st.lstate = "running"
         THEN Goto(g, "stop_send") /\ UNCHANGED st
         ELSE IF Fixed
           THEN /\ st' = [st EXCEPT !.L = "none"]
                /\ Drain(g, "dr_lockq", <<>>, TRUE, "stop_end")
           ELSE /\ UNCHANGED st
                /\ Drain(g, "dr_lockq", <<>>, FALSE, "stop_unlock_end")
    /\ UNCHANGED cbHeld

\* In English: "pipelineCancel, the bounded MsgClientDone write (at most
\* 250ms, :517-521), Protocol.Stop and lifecycleState = Stopped (:530-532),
\* still holding lifecycleMutex. None of it waits on another goroutine."
\* Literally: "StopSend of g is defined as: Pc of g equals "stop_send", and
\*   st in the next state equals st except proto is "stopping" and lstate is
\*   "stopped", and Goto of g and "stop_unlock", and cbHeld is unchanged."
StopSend(g) ==
    /\ Pc(g) = "stop_send"
    /\ st' = [st EXCEPT !.proto = "stopping", !.lstate = "stopped"]
    /\ Goto(g, "stop_unlock") /\ UNCHANGED cbHeld

\* In English: "c.lifecycleMutex.Unlock() before waiting (:535)."
\* Literally: "StopUnlock of g is defined as: Pc of g equals "stop_unlock",
\*   and st.L in the next state is "none", and Goto of g and "stop_wait",
\*   and cbHeld is unchanged."
StopUnlock(g) ==
    /\ Pc(g) = "stop_unlock"
    /\ st' = [st EXCEPT !.L = "none"]
    /\ Goto(g, "stop_wait") /\ UNCHANGED cbHeld

\* In English: "<-doneChan (:536): DoneChan closes only after recvLoop exits.
\* Then failOutstanding (:540)."
\* Literally: "StopWait of g is defined as: Pc of g equals "stop_wait", and
\*   st.recvExited is true, and Drain of g from "dr_lockq", withD FALSE, back
\*   to "stop_relock", and st and cbHeld are unchanged."
StopWait(g) ==
    /\ Pc(g) = "stop_wait" /\ st.recvExited
    /\ Drain(g, "dr_lockq", <<>>, FALSE, "stop_relock")
    /\ UNCHANGED <<st, cbHeld>>

\* In English: "c.lifecycleMutex.Lock() again (:543)."
\* Literally: "StopRelock of g is defined as: Pc of g equals "stop_relock",
\*   and st.L equals "none", and st.L in the next state is g, and Goto of g
\*   and "stop_unlock_end", and cbHeld is unchanged."
StopRelock(g) ==
    /\ Pc(g) = "stop_relock" /\ st.L = "none"
    /\ st' = [st EXCEPT !.L = g]
    /\ Goto(g, "stop_unlock_end") /\ UNCHANGED cbHeld

\* In English: "The deferred Unlock, and return."
\* Literally: "StopUnlockEnd of g is defined as: Pc of g equals
\*   "stop_unlock_end", and st.L in the next state is "none", and Pop of g."
StopUnlockEnd(g) ==
    /\ Pc(g) = "stop_unlock_end"
    /\ st' = [st EXCEPT !.L = "none"]
    /\ Pop(g)

\* In English: "Return, holding nothing (the fixed not-running branch)."
\* Literally: "StopEnd of g is defined as: Pc of g equals "stop_end", and
\*   Pop of g, and st is unchanged."
StopEnd(g) ==
    /\ Pc(g) = "stop_end"
    /\ Pop(g) /\ UNCHANGED st

-----------------------------------------------------------------------------
(* Drain and resolve: failOutstanding (:1259), failOutstandingForProtocol   *)
(* (:1281), and the resolve loops of the deadline watcher and the handlers. *)
(* With PR #3114, a request still sending is taken out but left to its      *)
(* sender (resolvableLocked).                                               *)

\* In English: "c.queueMutex.Lock()."
\* Literally: "DrLockQ of g is defined as: Pc of g equals "dr_lockq", and
\*   st.Q equals "none", and st.Q in the next state is g, and Goto of g and
\*   "dr_take", and cbHeld is unchanged."
DrLockQ(g) ==
    /\ Pc(g) = "dr_lockq" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "dr_take") /\ UNCHANGED cbHeld

\* In English: "drainLocked plus resolvableLocked: empty the queue, keep the
\* requests not still sending, and mark the sending ones deferred."
\* Literally: "DrTake of g is defined as: Pc of g equals "dr_take", and st in
\*   the next state equals st except queue is empty and deferred of r is
\*   (deferred of r, or r is in the queue and sending), and SetTop of g with
\*   pend the queue's requests that are not sending and pc "dr_next" if
\*   ResolveUnderQueue else "dr_unlockq", and cbHeld is unchanged."
DrTake(g) ==
    /\ Pc(g) = "dr_take"
    /\ st' = [st EXCEPT !.queue = <<>>,
                        !.deferred = [r \in R |-> @[r] \/
                                       (r \in Elems(st.queue) /\ st.sending[r])]]
    /\ SetTop(g, [Top(g) EXCEPT !.pend = SelectSeq(st.queue, LAMBDA r : ~st.sending[r]),
                               !.pc = IF ResolveUnderQueue THEN "dr_next" ELSE "dr_unlockq"])
    /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Unlock() before any callback."
\* Literally: "DrUnlockQ of g is defined as: Pc of g equals "dr_unlockq",
\*   and st.Q in the next state is "none", and Goto of g and "dr_next", and
\*   cbHeld is unchanged."
DrUnlockQ(g) ==
    /\ Pc(g) = "dr_unlockq"
    /\ st' = [st EXCEPT !.Q = "none"]
    /\ Goto(g, "dr_next") /\ UNCHANGED cbHeld

\* In English: "Next request, or done: then go back to ret (releasing
\* queueMutex first under the ResolveUnderQueue mutation)."
\* Literally: "DrNext of g is defined as: Pc of g equals "dr_next", and if
\*   pend of Top of g is empty, then (if ResolveUnderQueue and st.Q equals g
\*   then st.Q in the next state is "none", else st is unchanged) and Goto
\*   of g and ret; else Goto of g and "dr_lockd" if withD else "dr_resolve",
\*   and st is unchanged; and cbHeld is unchanged."
DrNext(g) ==
    /\ Pc(g) = "dr_next"
    /\ IF Top(g).pend = <<>>
         THEN /\ IF ResolveUnderQueue /\ st.Q = g
                   THEN st' = [st EXCEPT !.Q = "none"] ELSE UNCHANGED st
              /\ Goto(g, Top(g).ret)
         ELSE /\ Goto(g, IF Top(g).withD THEN "dr_lockd" ELSE "dr_resolve")
              /\ UNCHANGED st
    /\ UNCHANGED cbHeld

\* In English: "queued.deliveryMu.Lock() (:1108)."
\* Literally: "DrLockD of g is defined as: Pc of g equals "dr_lockd", and
\*   st.D of the head of pend equals "none", and st.D of it in the next state
\*   is g, and Goto of g and "dr_resolve", and cbHeld is unchanged."
DrLockD(g) ==
    /\ Pc(g) = "dr_lockd" /\ st.D[Head(Top(g).pend)] = "none"
    /\ st' = [st EXCEPT !.D[Head(Top(g).pend)] = g]
    /\ Goto(g, "dr_resolve") /\ UNCHANGED cbHeld

\* In English: "resolve (:1217): resolveOnce.Do. The first caller closes
\* retired and runs RangeDoneFunc; a later caller does nothing once it is
\* done, and waits while another goroutine is inside it (sync.Once blocks
\* concurrent callers until the first returns)."
\* Literally: "DrResolve of g is defined as: Pc of g equals "dr_resolve",
\*   and with r the head of pend: if NoOnce or once of r equals "none", then
\*   st in the next state is st except once of r is g (unless NoOnce) and
\*   cbRuns of r is one more, and EnterCb of g, r, "dr_resdone" and the
\*   empty set; else
\*   once of r equals "done" and Goto of g and "dr_after" and st and cbHeld
\*   are unchanged."
DrResolve(g) ==
    /\ Pc(g) = "dr_resolve"
    /\ LET r == Head(Top(g).pend) IN
         IF NoOnce \/ st.once[r] = "none"
           THEN /\ st' = [st EXCEPT !.once[r] = IF NoOnce THEN @ ELSE g,
                                    !.cbRuns[r] = @ + 1]
                /\ EnterCb(g, r, "dr_resdone", {})
           ELSE /\ st.once[r] = "done"
                /\ Goto(g, "dr_after") /\ UNCHANGED <<st, cbHeld>>

\* In English: "The callback returned; resolveOnce.Do finishes."
\* Literally: "DrResDone of g is defined as: Pc of g equals "dr_resdone",
\*   and st in the next state is st except once of the head of pend is
\*   "done" (unchanged under NoOnce), and Goto of g and "dr_after", and
\*   cbHeld is unchanged."
DrResDone(g) ==
    /\ Pc(g) = "dr_resdone"
    /\ st' = [st EXCEPT !.once[Head(Top(g).pend)] = IF NoOnce THEN @ ELSE "done"]
    /\ Goto(g, "dr_after") /\ UNCHANGED cbHeld

\* In English: "After resolving: unlock deliveryMu if it was taken, else
\* move on."
\* Literally: "DrAfter of g is defined as: Pc of g equals "dr_after", and if
\*   withD then Goto of g and "dr_unlockd", else SetTop of g with pend its
\*   tail and pc "dr_next"; and st and cbHeld are unchanged."
DrAfter(g) ==
    /\ Pc(g) = "dr_after"
    /\ IF Top(g).withD
         THEN Goto(g, "dr_unlockd")
         ELSE SetTop(g, [Top(g) EXCEPT !.pend = Tail(@), !.pc = "dr_next"])
    /\ UNCHANGED <<st, cbHeld>>

\* In English: "queued.deliveryMu.Unlock() (:1110)."
\* Literally: "DrUnlockD of g is defined as: Pc of g equals "dr_unlockd",
\*   and st.D of the head of pend in the next state is "none", and SetTop of
\*   g with pend its tail and pc "dr_next", and cbHeld is unchanged."
DrUnlockD(g) ==
    /\ Pc(g) = "dr_unlockd"
    /\ st' = [st EXCEPT !.D[Head(Top(g).pend)] = "none"]
    /\ SetTop(g, [Top(g) EXCEPT !.pend = Tail(@), !.pc = "dr_next"])
    /\ UNCHANGED cbHeld

-----------------------------------------------------------------------------
(* A user callback. *)

\* In English: "The callback returns."
\* Literally: "CbReturn of g is defined as: Pc of g equals "cb", and LeaveCb
\*   of g, and st is unchanged."
CbReturn(g) == Pc(g) = "cb" /\ LeaveCb(g) /\ UNCHANGED st

\* In English: "The callback calls client.Stop(): when it returns, the
\* callback returns too."
\* Literally: "CbCallStop of g is defined as: Pc of g equals "cb", and g is
\*   in CbStop, and Len of stk of g is less than MaxDepth, and stk of g in
\*   the next state is (with s the stack of g) s with its innermost frame
\*   moved to that frame's cbRet,
\*   followed by a new frame at "stop"; and st and cbHeld are unchanged."
CbCallStop(g) ==
    /\ Pc(g) = "cb" /\ g \in CbStop /\ Len(stk[g]) < MaxDepth
    /\ LET s == stk[g]
           back == [s EXCEPT ![Len(s)].pc = s[Len(s)].cbRet]
       IN stk' = [stk EXCEPT ![g] = Append(back, Frame("stop"))]
    /\ UNCHANGED <<st, cbHeld>>

\* In English: "The callback calls RequestRange: it takes the send token
\* (:995) and queueMutex (:1001). On a stopping protocol the send fails and
\* the request is removed; only the lock steps matter here."
\* Literally: "CbRequest of g is defined as: Pc of g equals "cb", and
\*   CbRequestRange is true, and Goto of g and "cb_rr_tok", and st and
\*   cbHeld are unchanged."
CbRequest(g) ==
    /\ Pc(g) = "cb" /\ CbRequestRange
    /\ Goto(g, "cb_rr_tok") /\ UNCHANGED <<st, cbHeld>>

\* In English: "<-c.rangeSendToken."
\* Literally: "CbTok of g is defined as: Pc of g equals "cb_rr_tok", and st.T
\*   equals "none", and st.T in the next state is g, and Goto of g and
\*   "cb_rr_q", and cbHeld is unchanged."
CbTok(g) ==
    /\ Pc(g) = "cb_rr_tok" /\ st.T = "none"
    /\ st' = [st EXCEPT !.T = g]
    /\ Goto(g, "cb_rr_q") /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Lock()."
\* Literally: "CbQ of g is defined as: Pc of g equals "cb_rr_q", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "cb_rr_unq", and cbHeld is unchanged."
CbQ(g) ==
    /\ Pc(g) = "cb_rr_q" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "cb_rr_unq") /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Unlock()."
\* Literally: "CbUnQ of g is defined as: Pc of g equals "cb_rr_unq", and st.Q
\*   in the next state is "none", and Goto of g and "cb_rr_untok", and cbHeld
\*   is unchanged."
CbUnQ(g) ==
    /\ Pc(g) = "cb_rr_unq"
    /\ st' = [st EXCEPT !.Q = "none"]
    /\ Goto(g, "cb_rr_untok") /\ UNCHANGED cbHeld

\* In English: "The token goes back and the callback returns."
\* Literally: "CbUnTok of g is defined as: Pc of g equals "cb_rr_untok", and
\*   st.T in the next state is "none", and LeaveCb of g."
CbUnTok(g) ==
    /\ Pc(g) = "cb_rr_untok"
    /\ st' = [st EXCEPT !.T = "none"]
    /\ LeaveCb(g)

-----------------------------------------------------------------------------
(* recvLoop and the handlers. *)

\* In English: "Between messages: the loop exits once the protocol is
\* stopping (DoneChan then closes), or it handles the next answer."
\* Literally: "RecvIdle of g is defined as: g equals "recv", and Pc of g
\*   equals "rv_idle", and either (st.proto equals "stopping" and st.
\*   recvExited in the next state is TRUE and Goto of g and "done") or (wire
\*   is not empty and st is unchanged and Goto of g and "rv_b_q" if the head
\*   is a block else "rv_d_q"); and cbHeld is unchanged."
RecvIdle(g) ==
    /\ g = "recv" /\ Pc(g) = "rv_idle"
    /\ \/ /\ st.proto = "stopping"
          /\ st' = [st EXCEPT !.recvExited = TRUE]
          /\ Goto(g, "done")
       \/ /\ st.wire /= <<>>
          /\ UNCHANGED st
          /\ Goto(g, IF Head(st.wire)[1] = "blk" THEN "rv_b_q" ELSE "rv_d_q")
    /\ UNCHANGED cbHeld

\* In English: "The request this answer is for."
\* Literally: "WireReq is defined as element 2 of the head of st.wire."
WireReq == Head(st.wire)[2]

\* In English: "handleBlock: c.queueMutex.Lock() (:1417)."
\* Literally: "RvBQ of g is defined as: Pc of g equals "rv_b_q", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "rv_b_head", and cbHeld is unchanged."
RvBQ(g) ==
    /\ Pc(g) = "rv_b_q" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "rv_b_head") /\ UNCHANGED cbHeld

\* In English: "headForResponse (:1418): the block must be for the head of the
\* queue; otherwise the handler unlocks and returns an error, which stops the
\* protocol."
\* Literally: "RvBHead of g is defined as: Pc of g equals "rv_b_head", and if
\*   the queue is not empty and its head equals WireReq, then Goto of g and
\*   "rv_b_lockd" and st is unchanged; else st in the next state is st
\*   except Q is "none", proto is "stopping" and wire is its tail, and Goto
\*   of g and "rv_idle"; and cbHeld is unchanged."
RvBHead(g) ==
    /\ Pc(g) = "rv_b_head"
    /\ IF st.queue /= <<>> /\ Head(st.queue) = WireReq
         THEN Goto(g, "rv_b_lockd") /\ UNCHANGED st
         ELSE /\ st' = [st EXCEPT !.Q = "none", !.proto = "stopping",
                                  !.wire = Tail(@)]
              /\ Goto(g, "rv_idle")
    /\ UNCHANGED cbHeld

\* In English: "req.deliveryMu.Lock() while still holding queueMutex
\* (:1443): the queueMutex -> deliveryMu edge."
\* Literally: "RvBLockD of g is defined as: Pc of g equals "rv_b_lockd", and
\*   st.D of WireReq equals "none", and st.D of WireReq in the next state is
\*   g, and Goto of g and "rv_b_unq", and cbHeld is unchanged."
RvBLockD(g) ==
    /\ Pc(g) = "rv_b_lockd" /\ st.D[WireReq] = "none"
    /\ st' = [st EXCEPT !.D[WireReq] = g]
    /\ Goto(g, "rv_b_unq") /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Unlock() (:1444)."
\* Literally: "RvBUnQ of g is defined as: Pc of g equals "rv_b_unq", and st.Q
\*   in the next state is "none", and Goto of g and "rv_b_pipe", and cbHeld
\*   is unchanged."
RvBUnQ(g) ==
    /\ Pc(g) = "rv_b_unq"
    /\ st' = [st EXCEPT !.Q = "none"]
    /\ Goto(g, "rv_b_pipe") /\ UNCHANGED cbHeld

\* In English: "pipelineContext (:553), with deliveryMu held: the
\* deliveryMu -> lifecycleMutex edge."
\* Literally: "RvBPipe of g is defined as: Pc of g equals "rv_b_pipe", and
\*   st.L equals "none", and st.L in the next state is g, and Goto of g and
\*   "rv_b_unpipe", and cbHeld is unchanged."
RvBPipe(g) ==
    /\ Pc(g) = "rv_b_pipe" /\ st.L = "none"
    /\ st' = [st EXCEPT !.L = g]
    /\ Goto(g, "rv_b_unpipe") /\ UNCHANGED cbHeld

\* In English: "pipelineContext's deferred Unlock."
\* Literally: "RvBUnPipe of g is defined as: Pc of g equals "rv_b_unpipe",
\*   and st.L in the next state is "none", and Goto of g and "rv_b_rec", and
\*   cbHeld is unchanged."
RvBUnPipe(g) ==
    /\ Pc(g) = "rv_b_unpipe"
    /\ st' = [st EXCEPT !.L = "none"]
    /\ Goto(g, "rv_b_rec") /\ UNCHANGED cbHeld

\* In English: "recordBlock under c.queueMutex (:1542), deliveryMu still held:
\* the deliveryMu -> queueMutex edge."
\* Literally: "RvBRec of g is defined as: Pc of g equals "rv_b_rec", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "rv_b_unrec", and cbHeld is unchanged."
RvBRec(g) ==
    /\ Pc(g) = "rv_b_rec" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "rv_b_unrec") /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Unlock() (:1544), then BlockFunc (:1581) with
\* deliveryMu held."
\* Literally: "RvBUnRec of g is defined as: Pc of g equals "rv_b_unrec", and
\*   st.Q in the next state is "none", and EnterCb of g, WireReq, "rv_b_und"
\*   and the set containing the pair "Q", 0."
RvBUnRec(g) ==
    /\ Pc(g) = "rv_b_unrec"
    /\ st' = [st EXCEPT !.Q = "none"]
    /\ EnterCb(g, WireReq, "rv_b_und", {<<"Q", 0>>})

\* In English: "The deferred req.deliveryMu.Unlock() (:1445); the block is
\* handled."
\* Literally: "RvBUnD of g is defined as: Pc of g equals "rv_b_und", and st in
\*   the next state is st except D of WireReq is "none" and wire is its tail,
\*   and Goto of g and "rv_idle", and cbHeld is unchanged."
RvBUnD(g) ==
    /\ Pc(g) = "rv_b_und"
    /\ st' = [st EXCEPT !.D[WireReq] = "none", !.wire = Tail(@)]
    /\ Goto(g, "rv_idle") /\ UNCHANGED cbHeld

\* In English: "handleBatchDone: c.queueMutex.Lock() (:1715)."
\* Literally: "RvDQ of g is defined as: Pc of g equals "rv_d_q", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "rv_d_take", and cbHeld is unchanged."
RvDQ(g) ==
    /\ Pc(g) = "rv_d_q" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "rv_d_take") /\ UNCHANGED cbHeld

\* In English: "If the head is this request, remove it and unlock (:1752-
\* 1753), then resolve it on this goroutine (:1768: RangeDoneFunc).
\* Otherwise unlock and fail the protocol."
\* Literally: "RvDTake of g is defined as: Pc of g equals "rv_d_take", and if
\*   the queue is not empty and its head equals WireReq, then st in the next
\*   state is st except Q is "none", queue is its tail and wire is its tail,
\*   and Drain of g from "dr_next" with the list WireReq, withD FALSE, back
\*   to "rv_idle"; else st in the next state is st except Q is "none", proto
\*   is "stopping" and wire is its tail, and Goto of g and "rv_idle"; and
\*   cbHeld is unchanged."
RvDTake(g) ==
    /\ Pc(g) = "rv_d_take"
    /\ IF st.queue /= <<>> /\ Head(st.queue) = WireReq
         THEN /\ st' = [st EXCEPT !.Q = "none", !.queue = Tail(@), !.wire = Tail(@)]
              /\ Drain(g, "dr_next", <<WireReq>>, FALSE, "rv_idle")
         ELSE /\ st' = [st EXCEPT !.Q = "none", !.proto = "stopping",
                                  !.wire = Tail(@)]
              /\ Goto(g, "rv_idle")
    /\ UNCHANGED cbHeld

-----------------------------------------------------------------------------
(* watchRangeDeadline for request 1 (:1071-1115). *)

\* In English: "The select (:1074): request 1 retired (resolveOnce has
\* started), the protocol's DoneChan closed, or the timer fired. Go picks at
\* random among ready cases, and the timer can always fire."
\* Literally: "DlWait of g is defined as: g equals "dl", and Pc of g equals
\*   "dl_wait", and either (once of 1 does not equal "none", or st.
\*   recvExited) and Goto of g and "done", or Goto of g and "dl_q"; and st
\*   and cbHeld are unchanged."
DlWait(g) ==
    /\ g = "dl" /\ Pc(g) = "dl_wait"
    /\ \/ (st.once[1] /= "none" \/ st.recvExited) /\ Goto(g, "done")
       \/ Goto(g, "dl_q")
    /\ UNCHANGED <<st, cbHeld>>

\* In English: "c.queueMutex.Lock() (:1082)."
\* Literally: "DlQ of g is defined as: Pc of g equals "dl_q", and st.Q equals
\*   "none", and st.Q in the next state is g, and Goto of g and "dl_take",
\*   and cbHeld is unchanged."
DlQ(g) ==
    /\ Pc(g) = "dl_q" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "dl_take") /\ UNCHANGED cbHeld

\* In English: "If request 1 is still queued, take every request of its
\* protocol out (:1095-1097; all three share one protocol here), deferring a
\* sending one to its sender (#3114's resolvableLocked), and unlock; else just
\* unlock and return (:1091-1093). Under the DeadlineResolvesQueued mutation
\* the requests stay queued until after they are resolved."
\* Literally: "DlTake of g is defined as: Pc of g equals "dl_take", and if 1
\*   is in the queue, then st in the next state is st except Q is "none",
\*   queue is empty unless DeadlineResolvesQueued, and deferred marks the
\*   queued sending requests, and SetTop of g with pend the queued requests
\*   not sending and pc "dl_senderr"; else st.Q in the next state is "none"
\*   and Goto of g and "done"; and cbHeld is unchanged."
DlTake(g) ==
    /\ Pc(g) = "dl_take"
    /\ IF 1 \in Elems(st.queue)
         THEN /\ st' = [st EXCEPT !.Q = "none",
                          !.queue = IF DeadlineResolvesQueued THEN @ ELSE <<>>,
                          !.deferred = [r \in R |-> @[r] \/
                                         (r \in Elems(st.queue) /\ st.sending[r])]]
              /\ SetTop(g, [Top(g) EXCEPT
                              !.pend = SelectSeq(st.queue, LAMBDA r : ~st.sending[r]),
                              !.pc = "dl_senderr"])
         ELSE /\ st' = [st EXCEPT !.Q = "none"]
              /\ Goto(g, "done")
    /\ UNCHANGED cbHeld

\* In English: "req.protocol.SendError(err) (:1102) stops the protocol; then
\* resolve each request under its deliveryMu (:1107-1111)."
\* Literally: "DlSendErr of g is defined as: Pc of g equals "dl_senderr", and
\*   st.proto in the next state is "stopping", and SetTop of g with pc
\*   "dr_next", withD TRUE and ret "dl_q2" if DeadlineResolvesQueued else
\*   "done", and cbHeld is unchanged."
DlSendErr(g) ==
    /\ Pc(g) = "dl_senderr"
    /\ st' = [st EXCEPT !.proto = "stopping"]
    /\ SetTop(g, [Top(g) EXCEPT !.pc = "dr_next", !.withD = TRUE,
                    !.ret = IF DeadlineResolvesQueued THEN "dl_q2" ELSE "done"])
    /\ UNCHANGED cbHeld

\* In English: "Mutation only: take queueMutex again to remove the requests
\* after resolving them."
\* Literally: "DlQ2 of g is defined as: Pc of g equals "dl_q2", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "dl_rm", and cbHeld is unchanged."
DlQ2(g) ==
    /\ Pc(g) = "dl_q2" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "dl_rm") /\ UNCHANGED cbHeld

\* In English: "Mutation only: remove them and unlock."
\* Literally: "DlRm of g is defined as: Pc of g equals "dl_rm", and st in the
\*   next state is st except Q is "none" and queue is the queue without 1, 2
\*   and 3, and Goto of g and "done", and cbHeld is unchanged."
DlRm(g) ==
    /\ Pc(g) = "dl_rm"
    /\ st' = [st EXCEPT !.Q = "none", !.queue = Without(@, R)]
    /\ Goto(g, "done") /\ UNCHANGED cbHeld

-----------------------------------------------------------------------------
(* The shutdown watcher (:460, :1315). *)

\* In English: "<-proto.DoneChan(), then failOutstandingForProtocol."
\* Literally: "SwWait of g is defined as: g equals "sw", and Pc of g equals
\*   "sw_wait", and st.recvExited, and Drain of g from "dr_lockq", withD
\*   FALSE, back to "done", and st and cbHeld are unchanged."
SwWait(g) ==
    /\ g = "sw" /\ Pc(g) = "sw_wait" /\ st.recvExited
    /\ Drain(g, "dr_lockq", <<>>, FALSE, "done")
    /\ UNCHANGED <<st, cbHeld>>

-----------------------------------------------------------------------------
(* sendRequestRange for request 3, as PR #3114 has it. *)

\* In English: "<-c.rangeSendToken (:995)."
\* Literally: "SnTok of g is defined as: Pc of g equals "sn_tok", and st.T
\*   equals "none", and st.T in the next state is g, and Goto of g and
\*   "sn_q", and cbHeld is unchanged."
SnTok(g) ==
    /\ Pc(g) = "sn_tok" /\ st.T = "none"
    /\ st' = [st EXCEPT !.T = g]
    /\ Goto(g, "sn_q") /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Lock() (:1001)."
\* Literally: "SnQ of g is defined as: Pc of g equals "sn_q", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "sn_app", and cbHeld is unchanged."
SnQ(g) ==
    /\ Pc(g) = "sn_q" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "sn_app") /\ UNCHANGED cbHeld

\* In English: "Append request 3 marked sending, and unlock (:1033-1036)."
\* Literally: "SnApp of g is defined as: Pc of g equals "sn_app", and st in
\*   the next state is st except Q is "none", queue has 3 appended and
\*   sending of 3 is TRUE, and Goto of g and "sn_send", and cbHeld is
\*   unchanged."
SnApp(g) ==
    /\ Pc(g) = "sn_app"
    /\ st' = [st EXCEPT !.Q = "none", !.queue = Append(@, 3), !.sending[3] = TRUE]
    /\ Goto(g, "sn_send") /\ UNCHANGED cbHeld

\* In English: "proto.SendMessageContext: it succeeds or fails while the
\* protocol's loops run, and fails once they have exited."
\* Literally: "SnSend of g is defined as: Pc of g equals "sn_send", and there
\*   exists ok in BOOLEAN such that (ok implies not st.recvExited) and st.
\*   sendOk in the next state is ok, and Goto of g and "sn_q2", and cbHeld
\*   is unchanged."
SnSend(g) ==
    /\ Pc(g) = "sn_send"
    /\ \E ok \in BOOLEAN :
         /\ ok => ~st.recvExited
         /\ st' = [st EXCEPT !.sendOk = ok]
    /\ Goto(g, "sn_q2") /\ UNCHANGED cbHeld

\* In English: "c.queueMutex.Lock() after the send."
\* Literally: "SnQ2 of g is defined as: Pc of g equals "sn_q2", and st.Q
\*   equals "none", and st.Q in the next state is g, and Goto of g and
\*   "sn_fin", and cbHeld is unchanged."
SnQ2(g) ==
    /\ Pc(g) = "sn_q2" /\ st.Q = "none"
    /\ st' = [st EXCEPT !.Q = g]
    /\ Goto(g, "sn_fin") /\ UNCHANGED cbHeld

\* In English: "Clear sending; a failed send removes its request; unlock.
\* A deferred request whose send succeeded is resolved by the sender, after
\* the token goes back (#3114), or before it under EarlyDeferredCallback."
\* Literally: "SnFin of g is defined as: Pc of g equals "sn_fin", and st in
\*   the next state is st except Q is "none", sending of 3 is FALSE, and
\*   queue is without 3 if the send failed; and if EarlyDeferredCallback and
\*   sendOk and deferred of 3, then Drain of g from "dr_next" with the list
\*   3, withD FALSE, back to "sn_untok"; else Goto of g and "sn_untok"; and
\*   cbHeld is unchanged."
SnFin(g) ==
    /\ Pc(g) = "sn_fin"
    /\ st' = [st EXCEPT !.Q = "none", !.sending[3] = FALSE,
                        !.queue = IF st.sendOk THEN @ ELSE Without(@, {3})]
    /\ IF EarlyDeferredCallback /\ st.sendOk /\ st.deferred[3]
         THEN Drain(g, "dr_next", <<3>>, FALSE, "sn_untok")
         ELSE Goto(g, "sn_untok")
    /\ UNCHANGED cbHeld

\* In English: "c.rangeSendToken <- struct{}{}; then resolve a deferred
\* request if the send succeeded."
\* Literally: "SnUnTok of g is defined as: Pc of g equals "sn_untok", and
\*   st.T in the next state is "none", and if sendOk and deferred of 3 and
\*   not EarlyDeferredCallback and not SenderIgnoresDeferred, then Drain of g
\*   from "dr_next" with the list 3, withD FALSE, back to "done"; else Goto
\*   of g and "done"; and cbHeld is unchanged."
SnUnTok(g) ==
    /\ Pc(g) = "sn_untok"
    /\ st' = [st EXCEPT !.T = "none"]
    /\ IF st.sendOk /\ st.deferred[3] /\ ~EarlyDeferredCallback /\ ~SenderIgnoresDeferred
         THEN Drain(g, "dr_next", <<3>>, FALSE, "done")
         ELSE Goto(g, "done")
    /\ UNCHANGED cbHeld

-----------------------------------------------------------------------------
(* The whole system. *)

\* In English: "Goroutine g takes one step."
\* Literally: "Step of g is defined as the disjunction of every action
\*   above applied to g."
Step(g) ==
    \/ StopLock(g) \/ StopBranch(g) \/ StopSend(g) \/ StopUnlock(g)
    \/ StopWait(g) \/ StopRelock(g) \/ StopUnlockEnd(g) \/ StopEnd(g)
    \/ DrLockQ(g) \/ DrTake(g) \/ DrUnlockQ(g) \/ DrNext(g) \/ DrLockD(g)
    \/ DrResolve(g) \/ DrResDone(g) \/ DrAfter(g) \/ DrUnlockD(g)
    \/ CbReturn(g) \/ CbCallStop(g) \/ CbRequest(g) \/ CbTok(g) \/ CbQ(g)
    \/ CbUnQ(g) \/ CbUnTok(g)
    \/ RecvIdle(g) \/ RvBQ(g) \/ RvBHead(g) \/ RvBLockD(g) \/ RvBUnQ(g)
    \/ RvBPipe(g) \/ RvBUnPipe(g) \/ RvBRec(g) \/ RvBUnRec(g) \/ RvBUnD(g)
    \/ RvDQ(g) \/ RvDTake(g)
    \/ DlWait(g) \/ DlQ(g) \/ DlTake(g) \/ DlSendErr(g) \/ DlQ2(g) \/ DlRm(g)
    \/ SwWait(g)
    \/ SnTok(g) \/ SnQ(g) \/ SnApp(g) \/ SnSend(g) \/ SnQ2(g) \/ SnFin(g)
    \/ SnUnTok(g)

\* In English: "Every goroutine has finished."
\* Literally: "AllDone is defined as: for all g in G, Pc of g equals
\*   "done"."
AllDone == \A g \in G : Pc(g) = "done"

\* In English: "Some goroutine steps; once all have finished, nothing
\* changes (so a finished run is not reported as a deadlock)."
\* Literally: "Next is defined as: there exists g in G such that Step of g,
\*   or AllDone and vars is unchanged."
Next == (\E g \in G : Step(g)) \/ (AllDone /\ UNCHANGED vars)

\* Literally: "Spec is defined as Init and always [Next] over vars."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Who waits for whom. *)

\* In English: "The lock goroutine g is trying to take, if any."
\* Literally: "Wants of g is defined as: the case analysis of Pc of g giving
\*   the pair "L", 0, "Q", 0, "T", 0, "D", r, or "none", 0."
Wants(g) ==
    LET p == Pc(g) IN
    CASE p \in {"stop", "stop_relock", "rv_b_pipe"} -> <<"L", 0>>
      [] p \in {"dr_lockq", "rv_b_q", "rv_b_rec", "rv_d_q", "dl_q", "dl_q2",
                "sn_q", "sn_q2", "cb_rr_q"} -> <<"Q", 0>>
      [] p \in {"sn_tok", "cb_rr_tok"} -> <<"T", 0>>
      [] p = "dr_lockd" -> <<"D", Head(Top(g).pend)>>
      [] p = "rv_b_lockd" -> <<"D", WireReq>>
      [] OTHER -> <<"none", 0>>

\* In English: "The current owner of lock n."
\* Literally: "OwnerOf of n is defined as: if element 1 of n equals "D" then
\*   st.D of element 2 of n, else the field of st named by element 1 of n."
OwnerOf(n) == IF n[1] = "D" THEN st.D[n[2]] ELSE st[n[1]]

\* In English: "The goroutines g is blocked on: the owner of a lock it
\* wants, recvLoop while Stop waits for DoneChan, or another goroutine still
\* inside resolveOnce for the request g is resolving."
\* Literally: "BlockedOn of g is defined as: the set of h in G such that
\*   element 1 of Wants of g is not "none" and OwnerOf of it equals h, or Pc of g equals
\*   "stop_wait" and st.recvExited is false and h equals "recv", or Pc of g
\*   equals "dr_resolve" and NoOnce is false and once of the head of pend
\*   equals h."
BlockedOn(g) ==
    {h \in G :
        \/ Wants(g)[1] /= "none" /\ OwnerOf(Wants(g)) = h
        \/ Pc(g) = "stop_wait" /\ ~st.recvExited /\ h = "recv"
        \/ Pc(g) = "dr_resolve" /\ ~NoOnce /\ st.once[Head(Top(g).pend)] = h}

\* In English: "The goroutine g is blocked on, or "none". There is at most
\* one: a lock, a sync.Once and a goroutine's exit each have one owner."
\* Literally: "WaitTarget of g is defined as: if BlockedOn of g is empty
\*   then "none", else the chosen h in BlockedOn of g."
WaitTarget(g) == IF BlockedOn(g) = {} THEN "none" ELSE CHOOSE h \in BlockedOn(g) : TRUE

\* In English: "Follow the waits-for chain from g for k steps."
\* Literally: "Follow of g and k is defined recursively: if k equals 0 or g
\*   equals "none" then g, else Follow of WaitTarget of g and k minus 1."
RECURSIVE Follow(_, _)
Follow(g, k) == IF k = 0 \/ g = "none" THEN g ELSE Follow(WaitTarget(g), k - 1)

\* In English: "g waits, through a chain of at most six goroutines, for
\* itself."
\* Literally: "InCycle of g is defined as: there exists k in 1 to 6 such that
\*   Follow of g and k equals g."
InCycle(g) == \E k \in 1..6 : Follow(g, k) = g

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "No goroutine ever waits, directly or through others, for
\* itself: no deadlock among the client's goroutines, including a goroutine
\* re-taking a lock it holds."
\* Literally: "NoWaitCycle is defined as: for all g in G, not InCycle of
\*   g."
NoWaitCycle == \A g \in G : ~InCycle(g)

\* In English: "Hazard X1's shape never appears: one goroutine holding
\* lifecycleMutex and waiting for queueMutex, another holding queueMutex
\* and waiting for some deliveryMu, and a third holding that deliveryMu and
\* waiting for lifecycleMutex."
\* Literally: "NoX1Shape is defined as: there do not exist a, b, c in G and r
\*   in R such that st.L equals a and Wants of a equals the pair "Q", 0 and
\*   st.Q equals b and Wants of b equals the pair "D", r and st.D of r
\*   equals c and Wants of c equals the pair "L", 0."
NoX1Shape ==
    ~\E a, b, c \in G, r \in R :
        /\ st.L = a /\ Wants(a) = <<"Q", 0>>
        /\ st.Q = b /\ Wants(b) = <<"D", r>>
        /\ st.D[r] = c /\ Wants(c) = <<"L", 0>>

\* In English: "No user callback runs while its goroutine holds
\* lifecycleMutex (hazard B1)."
\* Literally: "NoCallbackUnderLifecycle is defined as: for all g in G, the
\*   pair "L", 0 is not in cbHeld of g."
NoCallbackUnderLifecycle == \A g \in G : <<"L", 0>> \notin cbHeld[g]

\* In English: "No user callback runs under queueMutex."
\* Literally: "NoCallbackUnderQueue is defined as: for all g in G, the pair
\*   "Q", 0 is not in cbHeld of g."
NoCallbackUnderQueue == \A g \in G : <<"Q", 0>> \notin cbHeld[g]

\* In English: "No user callback runs while its goroutine holds the send
\* token."
\* Literally: "NoCallbackUnderToken is defined as: for all g in G, the pair
\*   "T", 0 is not in cbHeld of g."
NoCallbackUnderToken == \A g \in G : <<"T", 0>> \notin cbHeld[g]

\* In English: "While recvLoop delivers a block for request r (it holds r's
\* deliveryMu), nobody else has resolved r or is resolving it: the order
\* deliveryMu exists to keep (client.go:111-114)."
\* Literally: "NoResolveDuringDelivery is defined as: for all r in R, if
\*   st.D of r equals "recv" then once of r is "none" or "recv"."
NoResolveDuringDelivery ==
    \A r \in R : st.D[r] = "recv" => st.once[r] \in {"none", "recv"}

\* In English: "RangeDoneFunc runs at most once per request."
\* Literally: "RangeDoneOnce is defined as: for all r in R, cbRuns of r is
\*   at most 1."
RangeDoneOnce == \A r \in R : st.cbRuns[r] <= 1

\* In English: "When everything has finished, the queue is empty and every
\* request whose id was handed out (1 and 2, and 3 if its send succeeded)
\* got its RangeDoneFunc."
\* Literally: "AllResolvedAtEnd is defined as: AllDone implies the queue is
\*   empty and for all r in 1, 2, and 3 if sendOk, cbRuns of r is at least
\*   1."
AllResolvedAtEnd ==
    AllDone => /\ st.queue = <<>>
               /\ \A r \in {1, 2} \cup (IF st.sendOk THEN {3} ELSE {}) :
                    st.cbRuns[r] >= 1

\* In English: "When the first Stop has returned, the shutdown watcher has
\* finished too: no callback of this generation can run after Stop (hazard
\* B3). Expected to fail: nothing joins the watcher."
\* Literally: "StopJoinsWatcher is defined as: if Pc of "s1" equals "done"
\*   and "s1" is in Stoppers, then Pc of "sw" equals "done"."
StopJoinsWatcher == ("s1" \in Stoppers /\ Pc("s1") = "done") => Pc("sw") = "done"

\* In English: "Probe: a callback's Stop never runs to completion. Expected
\* to be violated: it can."
\* Literally: "ProbeNoReentrantStopReturns is defined as: there is no g in
\*   G such that Len of stk of g equals 2 and Pc of g is "stop_end" or
\*   "stop_unlock_end"."
ProbeNoReentrantStopReturns ==
    ~\E g \in G : Len(stk[g]) = 2 /\ Pc(g) \in {"stop_end", "stop_unlock_end"}

\* In English: "Probe: the sender never resolves a request a drain left to it.
\* Expected to be violated: #3114's deferred path is reachable here."
\* Literally: "ProbeNoDeferredResolve is defined as: once of 3 does not equal
\*   "snd"."
ProbeNoDeferredResolve == st.once[3] /= "snd"

\* In English: "Probe: the deadline watcher never resolves under a deliveryMu
\* while recvLoop waits for lifecycleMutex. Expected to be violated."
\* Literally: "ProbeNoDeadlineCallback is defined as: once of 1 does not
\*   equal "dl"."
ProbeNoDeadlineCallback == st.once[1] /= "dl"

=============================================================================
