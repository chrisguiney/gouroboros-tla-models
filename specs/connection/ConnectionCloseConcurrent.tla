----------------------- MODULE ConnectionCloseConcurrent -----------------------
(***************************************************************************)
(* Model `connection`, part 5, fifth pass: several callbacks closing one   *)
(* connection at once. ConnectionTeardown.tla has one callback, so its     *)
(* CloseContext ends when connClosedChan closes; it cannot show what the   *)
(* wait after that does when two callbacks are in CloseContext together.   *)
(*                                                                         *)
(* Goroutines (gOuroboros f60a0213, connection.go, muxer/loops.go):        *)
(*   loop i  a protocol instance's loop, running callback i. The callback  *)
(*           either returns or calls CloseContext with its own context:    *)
(*           ExcuseProtocolLoops(i) (:331), requestClose, wait for         *)
(*           connClosedChan (:337), then WaitProtocolLoopsExcept(i)        *)
(*           (:340), which waits for every loop but i's, excused or not.   *)
(*   sd      shutdown: <-doneChan; stopProtocols; WaitProtocolLoops        *)
(*           (:466), which skips excused loops; close(connClosedChan).     *)
(*   user    plain Close: requestClose, wait for connClosedChan, then      *)
(*           WaitProtocolLoopsExcept(nil): every loop.                     *)
(*   foreign CloseContext with a context that marks no instance of this    *)
(*           connection (another connection's callback): its owner is not  *)
(*           nil, but ExcuseProtocolLoops finds no loop, and the doc       *)
(*           (connection.go:310-312) promises it waits like Close.         *)
(*                                                                         *)
(* A loop exits once shutdown has stopped the protocols and its callback   *)
(* has returned. Every step is monotonic, so every behaviour ends; a state *)
(* with nothing enabled that is not Finished is a hang, and TLC reports it *)
(* as a deadlock.                                                          *)
(*                                                                         *)
(* Reference: the mux cancels and waits for every mini-protocol thread     *)
(* once, however many ask it to stop (network-mux Network/Mux.hs:280-287,  *)
(* Control/Concurrent/JobPool.hs:105-109); a thread that asks is not       *)
(* waited for by another that asks.                                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Inst,       \* the protocol instances, one loop and one callback each
    UserCloses, \* TRUE: the user also calls plain Close
    ForeignCloses, \* TRUE: CloseContext is called with another connection's context
    Fix         \* a subset of {"skipClosing", "selfJoin", "userSkipsClosing",
                \* "foreignAsClose"}:
                \* "skipClosing": after connClosedChan, CloseContext waits
                \*   only for loops that are not excused (WaitProtocolLoops),
                \*   so it never waits for another callback that is itself
                \*   in CloseContext. Without it: f60a0213's
                \*   WaitProtocolLoopsExcept(own), which does.
                \* "selfJoin" (mutation, with "skipClosing"): the wait
                \*   includes the caller's own loop.
                \* "userSkipsClosing" (mutation, with "skipClosing"): plain
                \*   Close's wait also skips excused loops.
                \* "foreignAsClose": a CloseContext whose context excused no
                \*   loop waits for every loop, as Close does. Without it:
                \*   c321f708, which branches on the owner being non-nil and
                \*   so skips every loop excused by another callback.

\* In English: "Fix names only these switches, and UserCloses and
\* ForeignCloses are booleans."
\* Literally: "Assume Fix is a subset of the set containing "skipClosing",
\*   "selfJoin", "userSkipsClosing" and "foreignAsClose", and UserCloses
\*   and ForeignCloses are members of BOOLEAN."
ASSUME Fix \subseteq {"skipClosing", "selfJoin", "userSkipsClosing", "foreignAsClose"}
       /\ UserCloses \in BOOLEAN /\ ForeignCloses \in BOOLEAN

VARIABLES
    cb,       \* callback i: "running", "closing" (CloseContext, waiting for
              \* connClosedChan), "joining" (its wait after that), "closed"
              \* (CloseContext returned, the callback goes on), "done"
    loop,     \* loop i: "running" or "exited"
    excused,  \* loop i is excused by its callback's CloseContext
    doneChan, \* doneChan is closed
    sd,       \* shutdown: "idle", "join", "done" (connClosedChan closed)
    user,     \* plain Close: "idle", "closing", "joining", "returned"
    foreign   \* the foreign-context CloseContext: same states as user

\* Literally: "vars is defined as the tuple of cb, loop, excused, doneChan,
\*   sd, user and foreign."
vars == <<cb, loop, excused, doneChan, sd, user, foreign>>

\* In English: "Every callback is running on its loop; nothing is closed."
\* Literally: "Init is defined as: cb maps every i in Inst to "running",
\*   and loop maps every i in Inst to "running", and excused maps every i
\*   in Inst to FALSE, and doneChan equals FALSE, and sd equals "idle",
\*   and user and foreign equal "idle"."
Init ==
    /\ cb = [i \in Inst |-> "running"]
    /\ loop = [i \in Inst |-> "running"]
    /\ excused = [i \in Inst |-> FALSE]
    /\ doneChan = FALSE
    /\ sd = "idle"
    /\ user = "idle"
    /\ foreign = "idle"

-----------------------------------------------------------------------------
(* The waits *)

\* In English: "Loop j does not hold up a wait that skips excused loops:
\* it has exited, or it is excused."
\* Literally: "Gone of j is defined as: loop of j equals "exited", or
\*   excused of j is true."
Gone(j) == loop[j] = "exited" \/ excused[j]

\* In English: "Callback i's CloseContext, after connClosedChan, may
\* return. With the fix it waits only for loops that are neither excused
\* nor, unless the selfJoin mutation, its own; f60a0213 waits for every
\* other loop, excused or not."
\* Literally: "CloserJoined of i is defined as: if "skipClosing" is a
\*   member of Fix, then for every j in Inst, loop of j equals "exited", or
\*   excused of j is true and (j does not equal i or "selfJoin" is not a
\*   member of Fix); else for every j in Inst other than i, loop of j
\*   equals "exited"."
CloserJoined(i) ==
    IF "skipClosing" \in Fix
        THEN \A j \in Inst :
                loop[j] = "exited" \/ (excused[j] /\ (j /= i \/ "selfJoin" \notin Fix))
        ELSE \A j \in Inst \ {i} : loop[j] = "exited"

\* In English: "Plain Close, after connClosedChan, may return once every
\* loop has exited (under the userSkipsClosing mutation, every loop not
\* excused)."
\* Literally: "UserJoined is defined as: for every j in Inst, loop of j
\*   equals "exited", or "userSkipsClosing" is a member of Fix and excused
\*   of j is true."
UserJoined ==
    \A j \in Inst : loop[j] = "exited" \/ ("userSkipsClosing" \in Fix /\ excused[j])

-----------------------------------------------------------------------------
(* Callbacks and loops *)

\* In English: "Callback i returns, whether it never closed or its
\* CloseContext has returned."
\* Literally: "CbReturn of i is defined as: cb of i is a member of the set
\*   containing "running" and "closed", and cb in the next state equals cb
\*   with i mapped to "done", and the rest is unchanged."
CbReturn(i) ==
    /\ cb[i] \in {"running", "closed"}
    /\ cb' = [cb EXCEPT ![i] = "done"]
    /\ UNCHANGED <<loop, excused, doneChan, sd, user, foreign>>

\* In English: "Callback i calls CloseContext with its own context: it
\* excuses its loop, then closes doneChan (once)."
\* Literally: "CbClose of i is defined as: cb of i equals "running", and
\*   excused in the next state equals excused with i mapped to TRUE, and
\*   doneChan in the next state equals TRUE, and cb in the next state
\*   equals cb with i mapped to "closing", and the rest is unchanged."
CbClose(i) ==
    /\ cb[i] = "running"
    /\ excused' = [excused EXCEPT ![i] = TRUE]
    /\ doneChan' = TRUE
    /\ cb' = [cb EXCEPT ![i] = "closing"]
    /\ UNCHANGED <<loop, sd, user, foreign>>

\* In English: "connClosedChan is closed: callback i's CloseContext goes on
\* to its loop wait."
\* Literally: "CbShutdownDone of i is defined as: cb of i equals
\*   "closing", and sd equals "done", and cb in the next state equals cb
\*   with i mapped to "joining", and the rest is unchanged."
CbShutdownDone(i) ==
    /\ cb[i] = "closing" /\ sd = "done"
    /\ cb' = [cb EXCEPT ![i] = "joining"]
    /\ UNCHANGED <<loop, excused, doneChan, sd, user, foreign>>

\* In English: "Callback i's loop wait ends and CloseContext returns."
\* Literally: "CbJoin of i is defined as: cb of i equals "joining", and
\*   CloserJoined of i, and cb in the next state equals cb with i mapped
\*   to "closed", and the rest is unchanged."
CbJoin(i) ==
    /\ cb[i] = "joining" /\ CloserJoined(i)
    /\ cb' = [cb EXCEPT ![i] = "closed"]
    /\ UNCHANGED <<loop, excused, doneChan, sd, user, foreign>>

\* In English: "Loop i exits once shutdown has stopped the protocols and
\* its callback has returned."
\* Literally: "LoopExit of i is defined as: loop of i equals "running",
\*   and sd does not equal "idle", and cb of i equals "done", and loop in
\*   the next state equals loop with i mapped to "exited", and the rest is
\*   unchanged."
LoopExit(i) ==
    /\ loop[i] = "running" /\ sd /= "idle" /\ cb[i] = "done"
    /\ loop' = [loop EXCEPT ![i] = "exited"]
    /\ UNCHANGED <<cb, excused, doneChan, sd, user, foreign>>

-----------------------------------------------------------------------------
(* Shutdown and the user *)

\* In English: "Shutdown begins once doneChan is closed and stops the
\* protocols, so loops may exit."
\* Literally: "SdBegin is defined as: sd equals "idle", and doneChan is
\*   true, and sd in the next state equals "join", and the rest is
\*   unchanged."
SdBegin ==
    /\ sd = "idle" /\ doneChan
    /\ sd' = "join"
    /\ UNCHANGED <<cb, loop, excused, doneChan, user, foreign>>

\* In English: "Shutdown's join waits for every loop not excused, then
\* closes connClosedChan."
\* Literally: "SdJoin is defined as: sd equals "join", and for every j in
\*   Inst, Gone of j, and sd in the next state equals "done", and the rest
\*   is unchanged."
SdJoin ==
    /\ sd = "join" /\ \A j \in Inst : Gone(j)
    /\ sd' = "done"
    /\ UNCHANGED <<cb, loop, excused, doneChan, user, foreign>>

\* In English: "The user calls plain Close: close doneChan (once)."
\* Literally: "UserClose is defined as: UserCloses is true, and user
\*   equals "idle", and doneChan in the next state equals TRUE, and user
\*   in the next state equals "closing", and the rest is unchanged."
UserClose ==
    /\ UserCloses /\ user = "idle"
    /\ doneChan' = TRUE
    /\ user' = "closing"
    /\ UNCHANGED <<cb, loop, excused, sd, foreign>>

\* In English: "The user's Close sees connClosedChan closed, then its loop
\* wait ends and it returns."
\* Literally: "UserStep is defined as: either (user equals "closing", and
\*   sd equals "done", and user in the next state equals "joining"), or
\*   (user equals "joining", and UserJoined, and user in the next state
\*   equals "returned"); and the rest is unchanged."
UserStep ==
    /\ \/ user = "closing" /\ sd = "done" /\ user' = "joining"
       \/ user = "joining" /\ UserJoined /\ user' = "returned"
    /\ UNCHANGED <<cb, loop, excused, doneChan, sd, foreign>>

\* In English: "CloseContext with a context marking none of this
\* connection's instances: close doneChan (once); after connClosedChan,
\* wait for every loop with foreignAsClose, else only for loops that are not
\* excused."
\* Literally: "ForeignStep is defined as: ForeignCloses is true, and either
\*   (foreign equals "idle", and doneChan in the next state equals TRUE, and
\*   foreign in the next state equals "closing"), or (foreign equals
\*   "closing", and sd equals "done", and foreign in the next state equals
\*   "joining", and doneChan is unchanged), or (foreign equals "joining",
\*   and for every j in Inst, loop of j equals "exited" or ("foreignAsClose"
\*   is not a member of Fix and excused of j is true), and foreign in the
\*   next state equals "returned", and doneChan is unchanged); and cb, loop,
\*   excused, sd and user are unchanged."
ForeignStep ==
    /\ ForeignCloses
    /\ \/ foreign = "idle" /\ doneChan' = TRUE /\ foreign' = "closing"
       \/ foreign = "closing" /\ sd = "done" /\ foreign' = "joining"
          /\ UNCHANGED doneChan
       \/ /\ foreign = "joining"
          /\ \A j \in Inst :
                loop[j] = "exited" \/ ("foreignAsClose" \notin Fix /\ excused[j])
          /\ foreign' = "returned"
          /\ UNCHANGED doneChan
    /\ UNCHANGED <<cb, loop, excused, sd, user>>

\* In English: "Nothing is left waiting: every callback has returned, no
\* Close is pending, and, once doneChan is closed, shutdown is done and
\* every loop has exited."
\* Literally: "Finished is defined as: for every i in Inst, cb of i equals
\*   "done", and user is a member of the set containing "idle" and
\*   "returned", and if doneChan is true then sd equals "done" and for
\*   every i in Inst, loop of i equals "exited"."
Finished ==
    /\ \A i \in Inst : cb[i] = "done"
    /\ user \in {"idle", "returned"}
    /\ foreign \in {"idle", "returned"}
    /\ doneChan => (sd = "done" /\ \A i \in Inst : loop[i] = "exited")

\* In English: "One step of any goroutine, or the stutter of a finished
\* system, so only a stuck state is reported as a deadlock."
\* Literally: "Next is defined as: there exists an i in Inst such that
\*   CbReturn of i, or CbClose of i, or CbShutdownDone of i, or CbJoin of
\*   i, or LoopExit of i; or SdBegin, or SdJoin, or UserClose, or
\*   UserStep, or ForeignStep, or (Finished and vars is unchanged)."
Next ==
    \/ \E i \in Inst :
          CbReturn(i) \/ CbClose(i) \/ CbShutdownDone(i) \/ CbJoin(i) \/ LoopExit(i)
    \/ SdBegin \/ SdJoin \/ UserClose \/ UserStep \/ ForeignStep
    \/ Finished /\ UNCHANGED vars

\* Literally: "Spec is defined as: Init, and always Next or vars is
\*   unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

\* In English: "When plain Close returns, every protocol loop has exited,
\* including one whose callback closed the connection."
\* Literally: "CloseWaitsForEveryLoop is defined as: if user equals
\*   "returned", then for every j in Inst, loop of j equals "exited"."
CloseWaitsForEveryLoop ==
    user = "returned" => \A j \in Inst : loop[j] = "exited"

\* In English: "When a CloseContext whose context marks none of this
\* connection's instances returns, every protocol loop has exited, as for
\* Close."
\* Literally: "ForeignCloseWaitsForEveryLoop is defined as: if foreign
\*   equals "returned", then for every j in Inst, loop of j equals
\*   "exited"."
ForeignCloseWaitsForEveryLoop ==
    foreign = "returned" => \A j \in Inst : loop[j] = "exited"

\* In English: "When a callback's CloseContext returns, every other loop
\* has exited, except one whose own callback is also closing."
\* Literally: "CloseContextWaitsForOthers is defined as: for every i in
\*   Inst, if cb of i equals "closed", then for every j in Inst other than
\*   i, Gone of j."
CloseContextWaitsForOthers ==
    \A i \in Inst : cb[i] = "closed" => \A j \in Inst \ {i} : Gone(j)

\* In English: "TypeOK: every variable holds a value of its kind."
\* Literally: "TypeOK is defined as: cb is a function from Inst to the set
\*   of the five callback states, and loop is a function from Inst to the
\*   set containing "running" and "exited", and excused is a function from
\*   Inst to BOOLEAN, and doneChan is a member of BOOLEAN, and sd is a
\*   member of the set of shutdown states, and user is a member of the set
\*   of Close states."
TypeOK ==
    /\ cb \in [Inst -> {"running", "closing", "joining", "closed", "done"}]
    /\ loop \in [Inst -> {"running", "exited"}]
    /\ excused \in [Inst -> BOOLEAN]
    /\ doneChan \in BOOLEAN
    /\ sd \in {"idle", "join", "done"}
    /\ user \in {"idle", "closing", "joining", "returned"}
    /\ foreign \in {"idle", "closing", "joining", "returned"}
=============================================================================
