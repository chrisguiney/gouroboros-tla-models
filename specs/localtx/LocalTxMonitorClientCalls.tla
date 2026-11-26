---------------------- MODULE LocalTxMonitorClientCalls ----------------------
(***************************************************************************)
(* The local-tx-monitor client's public calls, and what each one does      *)
(* locally before it sends: the guards that keep the client from sending  *)
(* a message its protocol state does not allow, and from sending anything *)
(* once Stop has been called.                                              *)
(*                                                                         *)
(* LocalTxMonitor.tla checks the two sides talking; its client only ever   *)
(* sends what is legal. This module asks the other question: given the     *)
(* calls an application may make, in any order and racing Stop, does the   *)
(* client ever send an illegal message? Such a message is refused by the   *)
(* client's own send loop and tears the whole node-to-client connection    *)
(* down, while the call that sent it may already have returned nil.        *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex*)
(*        2055-2103 (local tx-monitor agency table) and 2105-2166          *)
(*        (messages): from StIdle the client may send MsgAcquire or        *)
(*        MsgDone; from StAcquired MsgAwaitAcquire, MsgRelease or a query  *)
(*        (MsgNextTx, MsgHasTx, MsgGetSizes, MsgGetMeasures); the server   *)
(*        holds agency in StAcquiring and StBusy.                          *)
(*   [S2] the same file, 27-36: a message that is not allowed closes the   *)
(*        connection.                                                      *)
(*   [R1] ouroboros-network 5f356486ab3e .../Protocol/LocalTxMonitor/      *)
(*        Client.hs 121-166: the typed client offers MsgRelease and the    *)
(*        queries only in its acquired continuation and MsgDone only in    *)
(*        its idle one, so "release while idle" or "done while acquired"   *)
(*        cannot be written.                                               *)
(*                                                                         *)
(* gOuroboros protocol/localtxmonitor/client.go at 7cd17437:               *)
(*   [G1] Acquire, Release, HasTxForEra, NextTx and GetSizes take          *)
(*        busyMutex and return ErrProtocolShuttingDown at once if Stop     *)
(*        was called (stopping()). GetMeasures does not check.             *)
(*   [G2] release() sends MsgRelease whatever `acquired` says, then clears *)
(*        it.                                                              *)
(*   [G3] a query with nothing acquired calls acquire() first; acquire()   *)
(*        sends MsgAcquire (MsgAwaitAcquire from StAcquired).              *)
(*   [G4] every wait selects on its result channel, stopRequested (sets    *)
(*        `abandoned`) and DoneChan; deliverResult also gives up on        *)
(*        stopRequested.                                                   *)
(*   [G5] Stop closes stopRequested, takes busyMutex, and sends MsgDone    *)
(*        unless a call was abandoned; it never releases first.            *)
(*   [G6] protocol/protocol.go sendLoop: an illegal message is a protocol  *)
(*        error (SendError), which stops the protocol and the connection.  *)
(*        A message queued while the server holds agency waits in the      *)
(*        send queue and is checked when agency returns.                   *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend at the top of                   *)
(* specs/keepalive/KeepAlive.tla and the "Reading a formula literally"     *)
(* table in the top-level README.                                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences   \* numbers, and lists (the send queue)

CONSTANTS
    MaxCalls,              \* how many public calls the application may make (keeps the model finite)
    ReleaseChecksAcquired, \* TRUE: Release with nothing acquired returns an error and sends nothing
                           \* FALSE: gOuroboros at 7cd17437 [G2]
    MeasuresChecksStop,    \* TRUE: GetMeasures refuses once Stop was called, like every other call
                           \* FALSE: gOuroboros at 7cd17437 [G1]
    StopReleases,          \* TRUE: Stop from StAcquired sends MsgRelease, then MsgDone
                           \* FALSE: gOuroboros at 7cd17437 [G5]
    ReleaseClearsFlag      \* TRUE: release() clears `acquired` [G2]
                           \* FALSE: a mutation that leaves it set

\* In English: "The calls an application can make. Query stands for
\* HasTxForEra, NextTx and GetSizes, which behave alike; Measures is
\* GetMeasures, which differs only in its stop check."
\* Literally: "Calls is defined as the set containing "Acquire", "Release",
\*   "Query" and "Measures"."
Calls == {"Acquire", "Release", "Query", "Measures"}

\* In English: "The states the client's protocol can be in, plus Failed
\* (its own send loop refused a message and tore the connection down [G6])
\* and Closed (Stop stopped the protocol without a message)."
\* Literally: "PStates is defined as the set containing "StIdle",
\*   "StAcquiring", "StAcquired", "StBusy", "StDone", "Failed" and "Closed"."
PStates == {"StIdle", "StAcquiring", "StAcquired", "StBusy", "StDone", "Failed", "Closed"}

\* In English: "The client's messages: MsgAcquire (MsgAwaitAcquire from
\* StAcquired has the same bytes), MsgRelease, a query, and MsgDone."
\* Literally: "Msgs is defined as the set containing "MsgAcquire",
\*   "MsgRelease", "MsgQuery" and "MsgDone"."
Msgs == {"MsgAcquire", "MsgRelease", "MsgQuery", "MsgDone"}

\* In English: "Which client message is legal in which state, and where it
\* leads [S1]."
\* Literally: "Legal of s and m is defined as: s equals "StIdle" and m is a
\*   member of the set containing "MsgAcquire" and "MsgDone"; or s equals
\*   "StAcquired" and m is a member of the set containing "MsgAcquire",
\*   "MsgRelease" and "MsgQuery"."
Legal(s, m) ==
    \/ s = "StIdle" /\ m \in {"MsgAcquire", "MsgDone"}
    \/ s = "StAcquired" /\ m \in {"MsgAcquire", "MsgRelease", "MsgQuery"}

\* In English: "The state after the client sends m from s: legal messages
\* move along the table; anything else is refused by the send loop and
\* the connection fails [S2][G6]."
\* Literally: "SendTo of s and m is defined as: if Legal of s and m is
\*   false then "Failed", otherwise the case m equals "MsgAcquire" gives
\*   "StAcquiring", m equals "MsgRelease" gives "StIdle", m equals "MsgQuery"
\*   gives "StBusy", and m equals "MsgDone" gives "StDone"."
SendTo(s, m) ==
    IF ~Legal(s, m) THEN "Failed"
    ELSE CASE m = "MsgAcquire" -> "StAcquiring"
           [] m = "MsgRelease" -> "StIdle"
           [] m = "MsgQuery"   -> "StBusy"
           [] m = "MsgDone"    -> "StDone"

\* In English: "Whether a call returns at once once Stop has been called."
\* Literally: "ChecksStop of c is defined as: c does not equal "Measures",
\*   or MeasuresChecksStop is true."
ChecksStop(c) == c /= "Measures" \/ MeasuresChecksStop

\* In English: "The client holds agency in StIdle and StAcquired [S1]."
\* Literally: "ClientAgency of s is defined as: s is a member of the set
\*   containing "StIdle" and "StAcquired"."
ClientAgency(s) == s \in {"StIdle", "StAcquired"}

\* In English: "The server holds agency in StAcquiring and StBusy [S1]."
\* Literally: "ServerAgency of s is defined as: s is a member of the set
\*   containing "StAcquiring" and "StBusy"."
ServerAgency(s) == s \in {"StAcquiring", "StBusy"}

VARIABLES
    pstate,    \* the client protocol's state, as its send loop sees it
    queue,     \* client messages queued while the server holds agency [G6]
    acquired,  \* the client's `acquired` flag
    lock,      \* busyMutex: "free", or held by a "call" waiting for the server
    waiting,   \* what the call holding the lock waits for: "none", "acquired",
               \* "acquiredThenQuery" (a query that had to acquire first), or "reply"
    late,      \* TRUE when the call holding the lock began after Stop was called
    lateSent,  \* TRUE once a call that began after Stop was called sent something
    calls,     \* calls made so far
    stopReq,   \* TRUE once Stop was called (stopRequested is closed)
    abandoned, \* TRUE once Stop ended a call that waited for the server
    stopDone   \* TRUE once Stop ran under the lock and stopped the protocol

\* Literally: "vars is defined as the tuple of all eleven variables."
vars == <<pstate, queue, acquired, lock, waiting, late, lateSent, calls,
          stopReq, abandoned, stopDone>>

\* In English: "At the start the protocol is in StIdle, nothing is queued,
\* acquired or held, and Stop has not been called."
\* Literally: "Init is defined as: pstate equals "StIdle", queue equals the
\*   empty sequence, acquired equals FALSE, lock equals "free", waiting
\*   equals "none", late equals FALSE, lateSent equals FALSE, calls equals 0,
\*   stopReq equals FALSE, abandoned equals FALSE and stopDone equals FALSE."
Init ==
    /\ pstate = "StIdle"
    /\ queue = <<>>
    /\ acquired = FALSE
    /\ lock = "free"
    /\ waiting = "none"
    /\ late = FALSE
    /\ lateSent = FALSE
    /\ calls = 0
    /\ stopReq = FALSE
    /\ abandoned = FALSE
    /\ stopDone = FALSE

\* In English: "Send m: with agency the send loop checks it against the
\* state at once; while the server holds agency it waits in the queue
\* [G6]. Every send by a call that began after Stop was called is
\* recorded."
\* Literally: "Send of m is defined as: if ClientAgency of pstate then pstate
\*   in the next state equals SendTo of pstate and m and queue is unchanged,
\*   otherwise queue in the next state equals queue with m appended and
\*   pstate is unchanged; and lateSent in the next state equals lateSent or
\*   stopReq."
Send(m) ==
    /\ IF ClientAgency(pstate)
          THEN pstate' = SendTo(pstate, m) /\ UNCHANGED queue
          ELSE queue' = Append(queue, m) /\ UNCHANGED pstate
    /\ lateSent' = (lateSent \/ stopReq)

\* In English: "A call that returns without sending: only the call count
\* changes."
\* Literally: "ReturnsAtOnce is defined as: calls in the next state equals
\*   calls plus 1, and every other variable is unchanged."
ReturnsAtOnce ==
    /\ calls' = calls + 1
    /\ UNCHANGED <<pstate, queue, acquired, lock, waiting, late, lateSent,
                   stopReq, abandoned, stopDone>>

\* In English: "Call c begins: it takes busyMutex [G1]. If Stop was called
\* and the call checks for it, it returns at once. Release either refuses
\* (with the check) or sends MsgRelease and clears `acquired` [G2]; it does
\* not wait. Acquire sends MsgAcquire and waits. A query sends its query if
\* a snapshot is acquired, otherwise MsgAcquire first [G3]. Calls after
\* Stop has finished fail in the send queue and are not modelled; at most
\* one message waits in the queue (keeps the model finite)."
\* Literally: "Begin of c is defined as: lock equals "free", and calls is
\*   less than MaxCalls, and stopDone is false, and pstate is a member of
\*   the union of ClientAgency and ServerAgency states, and queue is empty,
\*   and either (stopReq and ChecksStop of c, and ReturnsAtOnce), or (not
\*   (stopReq and ChecksStop of c), and one of the following: c is
\*   "Release", ReleaseChecksAcquired, acquired is false, and ReturnsAtOnce;
\*   or c is "Release" and not (ReleaseChecksAcquired and not acquired),
\*   Send of "MsgRelease", acquired becomes the opposite of
\*   ReleaseClearsFlag-and-true, calls goes up by one; or c is "Acquire", or c
\*   is a query and acquired is false: Send of "MsgAcquire", the lock is taken
\*   by the call, waiting becomes "acquired" (or "acquiredThenQuery" for a
\*   query), late becomes stopReq; or c is a query and acquired is true:
\*   Send of "MsgQuery", the lock is taken, waiting becomes "reply", late
\*   becomes stopReq)."
Begin(c) ==
    /\ lock = "free"
    /\ calls < MaxCalls
    /\ ~stopDone
    /\ ClientAgency(pstate) \/ ServerAgency(pstate)
    /\ queue = <<>>
    /\ \/ /\ stopReq /\ ChecksStop(c)                  \* stopping() [G1]
          /\ ReturnsAtOnce
       \/ /\ ~(stopReq /\ ChecksStop(c))
          /\ \/ /\ c = "Release"
                /\ ReleaseChecksAcquired /\ ~acquired   \* refuses, sends nothing
                /\ ReturnsAtOnce
             \/ /\ c = "Release"
                /\ ~(ReleaseChecksAcquired /\ ~acquired)
                /\ Send("MsgRelease")                   \* [G2]
                /\ acquired' = (acquired /\ ~ReleaseClearsFlag)
                /\ calls' = calls + 1
                /\ UNCHANGED <<lock, waiting, late, stopReq, abandoned, stopDone>>
             \/ /\ \/ c = "Acquire"
                   \/ c \in {"Query", "Measures"} /\ ~acquired  \* [G3]
                /\ Send("MsgAcquire")
                /\ lock' = "call"
                /\ waiting' = IF c = "Acquire" THEN "acquired" ELSE "acquiredThenQuery"
                /\ late' = stopReq
                /\ calls' = calls + 1
                /\ UNCHANGED <<acquired, stopReq, abandoned, stopDone>>
             \/ /\ c \in {"Query", "Measures"} /\ acquired
                /\ Send("MsgQuery")
                /\ lock' = "call"
                /\ waiting' = "reply"
                /\ late' = stopReq
                /\ calls' = calls + 1
                /\ UNCHANGED <<acquired, stopReq, abandoned, stopDone>>

\* In English: "The state the send loop reaches when agency returns in
\* StAcquired: the queued message, if any, is checked then [G6]."
\* Literally: "Flushed is defined as: if queue is empty then "StAcquired",
\*   otherwise SendTo of "StAcquired" and the head of queue."
Flushed == IF queue = <<>> THEN "StAcquired" ELSE SendTo("StAcquired", Head(queue))

\* In English: "The server answers: from StAcquiring with MsgAcquired, which
\* the client's handler records by setting `acquired` whether or not a
\* caller still waits; from StBusy with the reply. Agency returns in
\* StAcquired and the send loop checks any queued message. A caller still
\* waiting gets the answer: a query that had to acquire first now sends its
\* query (it does not check Stop again), any other call returns and frees
\* the lock."
\* Literally: "Answer is defined as: ServerAgency of pstate, and queue in the
\*   next state is empty, and acquired in the next state is acquired or
\*   pstate equals "StAcquiring", and either (waiting is
\*   "acquiredThenQuery", and pstate in the next state is SendTo of Flushed
\*   and "MsgQuery" if ClientAgency of Flushed, otherwise Flushed; waiting
\*   becomes "reply"; lateSent becomes lateSent or late) or (waiting is not
\*   "acquiredThenQuery", pstate becomes Flushed, waiting becomes "none",
\*   lock becomes "free" if a call waited, late becomes FALSE); calls,
\*   stopReq, abandoned and stopDone are unchanged."
Answer ==
    /\ ServerAgency(pstate)
    /\ queue' = <<>>
    /\ acquired' = (acquired \/ pstate = "StAcquiring")     \* handleAcquired
    /\ \/ /\ waiting = "acquiredThenQuery"
          /\ pstate' = IF ClientAgency(Flushed) THEN SendTo(Flushed, "MsgQuery")
                       ELSE Flushed
          /\ waiting' = "reply"
          /\ lateSent' = (lateSent \/ late)
          /\ UNCHANGED <<lock, late>>
       \/ /\ waiting /= "acquiredThenQuery"
          /\ pstate' = Flushed
          /\ waiting' = "none"
          /\ lock' = IF waiting = "none" THEN lock ELSE "free"
          /\ late' = FALSE
          /\ UNCHANGED lateSent
    /\ UNCHANGED <<calls, stopReq, abandoned, stopDone>>

\* In English: "A waiting call returns once the protocol failed or was
\* closed (DoneChan [G4])."
\* Literally: "CallSeesDone is defined as: waiting is not "none", and pstate
\*   is a member of the set containing "Failed" and "Closed", and waiting
\*   becomes "none", lock becomes "free", late becomes FALSE, and the rest
\*   is unchanged."
CallSeesDone ==
    /\ waiting /= "none"
    /\ pstate \in {"Failed", "Closed"}
    /\ waiting' = "none"
    /\ lock' = "free"
    /\ late' = FALSE
    /\ UNCHANGED <<pstate, queue, acquired, lateSent, calls, stopReq,
                   abandoned, stopDone>>

\* In English: "Stop is called (closes stopRequested), at any time, once."
\* Literally: "StopRequest is defined as: stopReq is false, and stopReq in
\*   the next state is true, and the rest is unchanged."
StopRequest ==
    /\ ~stopReq
    /\ stopReq' = TRUE
    /\ UNCHANGED <<pstate, queue, acquired, lock, waiting, late, lateSent,
                   calls, abandoned, stopDone>>

\* In English: "A call waiting for the server sees stopRequested, records
\* that it abandoned the wait, and returns, freeing the lock [G4]."
\* Literally: "StopCancel is defined as: stopReq is true, and waiting is not
\*   "none", and abandoned becomes TRUE, waiting becomes "none", lock becomes
\*   "free", late becomes FALSE, and the rest is unchanged."
StopCancel ==
    /\ stopReq
    /\ waiting /= "none"
    /\ abandoned' = TRUE
    /\ waiting' = "none"
    /\ lock' = "free"
    /\ late' = FALSE
    /\ UNCHANGED <<pstate, queue, acquired, lateSent, calls, stopReq, stopDone>>

\* In English: "Stop takes the lock and ends the run [G5]. After an
\* abandoned call the server holds agency, so it closes without a message.
\* Otherwise from StIdle it sends MsgDone; from StAcquired it sends
\* MsgRelease then MsgDone with StopReleases, and MsgDone alone without,
\* which is illegal there. Then it stops the protocol, dropping anything
\* still queued."
\* Literally: "StopRun is defined as: stopReq is true, and stopDone is
\*   false, and lock is "free", and stopDone becomes TRUE, and queue becomes
\*   empty, and pstate becomes: "Closed" if abandoned; otherwise, if pstate
\*   is "StAcquired" and StopReleases, "StDone"; otherwise, if ClientAgency of
\*   pstate, SendTo of pstate and "MsgDone"; otherwise pstate; and acquired
\*   becomes FALSE if Stop released, and the rest is unchanged."
StopRun ==
    /\ stopReq /\ ~stopDone
    /\ lock = "free"
    /\ stopDone' = TRUE
    /\ queue' = <<>>
    /\ pstate' =
         IF abandoned THEN "Closed"
         ELSE IF pstate = "StAcquired" /\ StopReleases THEN "StDone"
         ELSE IF ClientAgency(pstate) THEN SendTo(pstate, "MsgDone")
         ELSE pstate
    /\ acquired' = IF pstate = "StAcquired" /\ StopReleases THEN FALSE ELSE acquired
    /\ UNCHANGED <<lock, waiting, late, lateSent, calls, stopReq, abandoned>>

\* In English: "Once Stop has run, or the connection failed, and no call
\* holds the lock, the behaviour may end."
\* Literally: "Finished is defined as: (stopDone or pstate equals "Failed"),
\*   and lock equals "free", and all variables are unchanged."
Finished ==
    /\ stopDone \/ pstate = "Failed"
    /\ lock = "free"
    /\ UNCHANGED vars

\* Literally: "Next is defined as: there exists a c in Calls such that Begin
\*   of c, or Answer, or CallSeesDone, or StopRequest, or StopCancel, or
\*   StopRun, or Finished."
Next ==
    \/ \E c \in Calls : Begin(c)
    \/ Answer
    \/ CallSeesDone
    \/ StopRequest
    \/ StopCancel
    \/ StopRun
    \/ Finished

\* Literally: "Spec is defined as: Init, and always either Next or vars
\*   stays the same."
Spec == Init /\ [][Next]_vars

\* ---- Invariants ---------------------------------------------------------

\* In English: "Every variable holds a value of the right kind."
TypeOK ==
    /\ pstate \in PStates
    /\ queue \in Seq(Msgs) /\ Len(queue) <= 1
    /\ acquired \in BOOLEAN
    /\ lock \in {"free", "call"}
    /\ waiting \in {"none", "acquired", "acquiredThenQuery", "reply"}
    /\ late \in BOOLEAN /\ lateSent \in BOOLEAN
    /\ calls \in 0..MaxCalls
    /\ stopReq \in BOOLEAN /\ abandoned \in BOOLEAN /\ stopDone \in BOOLEAN

\* In English: "The client never sends a message its state does not allow,
\* whatever the application calls: its own send loop never tears the
\* connection down [S1][S2][R1]."
\* Literally: "NoIllegalSend is defined as: pstate does not equal "Failed"."
NoIllegalSend == pstate /= "Failed"

\* In English: "A call that begins after Stop was called sends nothing
\* [G1]. Otherwise it hands the server agency again, and Stop, finding the
\* call abandoned, closes without MsgDone."
\* Literally: "NoSendFromLateCall is defined as: lateSent is false."
NoSendFromLateCall == ~lateSent

\* In English: "While no call is in progress and the protocol is in StIdle
\* or StAcquired, the `acquired` flag says which."
\* Literally: "FlagMatchesState is defined as: if lock is "free" and
\*   ClientAgency of pstate, then acquired is true if and only if pstate
\*   equals "StAcquired"."
FlagMatchesState ==
    (lock = "free" /\ ClientAgency(pstate))
        => (acquired <=> pstate = "StAcquired")

\* ---- Reachability probes (each must fail on the passing config) ---------

\* In English: "Stop never abandons a waiting call."
ProbeNoAbandon == ~abandoned
=============================================================================
