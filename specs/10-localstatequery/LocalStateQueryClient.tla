----------------------- MODULE LocalStateQueryClient -----------------------
(***************************************************************************)
(* The gOuroboros local-state-query client: several goroutines calling it  *)
(* at once, the implicit acquire, Release, Stop, and the version gate on   *)
(* the immutable tip.                                                      *)
(*                                                                         *)
(* What the code does (protocol/localstatequery/client.go):                *)
(*   - Every public call (the Acquire, Release and Get calls) holds        *)
(*     busyMutex from before it sends until after its answer arrives, so   *)
(*     at most one request is outstanding.                                 *)
(*   - acquire() sends MsgReAcquire if the client believes it holds a      *)
(*     state (the `acquired` flag), else MsgAcquire, then waits on the     *)
(*     unbuffered acquireResultChan.                                       *)
(*   - runQueryMaxItems() first acquires the volatile tip if `acquired` is *)
(*     false (the implicit acquire), then sends MsgQuery and waits on the  *)
(*     unbuffered queryResultChan. Before the fix it never released what   *)
(*     it acquired; with it (ReleaseImplicit), endCall releases it as the  *)
(*     public call returns, still holding busyMutex.                       *)
(*   - Some calls make two queries (GetEpochNo, GetCurrentProtocolParams:  *)
(*     the era, then a query for that era); Query2 is such a call.         *)
(*   - release() sends MsgRelease and clears `acquired`, whatever the      *)
(*     flag was.                                                           *)
(*   - The handler (one goroutine, protocol.Protocol's recvLoop) sets      *)
(*     `acquired` on MsgAcquired, clears it on MsgFailure, then hands the  *)
(*     answer over the channel; MsgResult is handed over as is.            *)
(*   - Stop closes stopChan; once the receive and send loops exit,         *)
(*     DoneChan closes, and a goroutine started by Start closes both       *)
(*     result channels, so a waiting call returns ErrProtocolShuttingDown. *)
(*   - protocol.Protocol checks each message against StateMap as it is     *)
(*     sent and as it is read; one that is not legal is a protocol error   *)
(*     that tears the connection down.                                     *)
(*                                                                         *)
(* Questions:                                                              *)
(*   OwnAnswer             does every call receive the answer to its own   *)
(*                         request?                                        *)
(*   NoViolation           does either side ever see a message its state   *)
(*                         does not allow?                                 *)
(*   FlagMatchesState      when nothing is in flight, does `acquired` say  *)
(*                         what the protocol state says?                   *)
(*   FreshImplicitSnapshot does a query made with no explicit acquire      *)
(*                         answer from a state at least as new as the      *)
(*                         chain when the call began?                      *)
(*   OneSnapshotPerCall    do all the queries of one call answer from the  *)
(*                         same ledger state?                              *)
(*   and, by TLC's deadlock check, does every call return, also when Stop  *)
(*   lands with a request outstanding?                                     *)
(*                                                                         *)
(* Sources (ouroboros-network 5f356486ab3e; README.md has links):          *)
(*   [S3] miniprotocols.tex 1950-2008: messages and transitions.           *)
(*   [R2] LocalStateQuery/Type.hs 114-130: VolatileTip and ImmutableTip    *)
(*        cannot fail; ImmutableTip "Requires at least NodeToClientV_16".  *)
(*   [R3] LocalStateQuery/Codec.hs 89-96, 130-137: the reference refuses   *)
(*        to encode an ImmutableTip acquire unless v16 was negotiated.     *)
(*   [R5] LocalStateQuery/Client.hs 36-89: the reference client is a       *)
(*        continuation per state; each answer goes to the continuation     *)
(*        that sent the request, and nothing acquires implicitly.          *)
(*   [G1] gOuroboros 61046085 protocol/localstatequery/client.go: acquire, *)
(*        release, runQueryMaxItems, handleAcquired, handleFailure,        *)
(*        handleResult, Start; protocol/protocol.go: stop, enqueueMessage. *)
(*   [G2] gOuroboros 35982911 (branch                                      *)
(*        fix/localstatequery-implicit-acquire) client.go: endCall,        *)
(*        runQueryMaxItems; GetEpochNo makes two queries.                  *)
(*                                                                         *)
(* Not modelled: query encodings, the cached era (currentEra), timeouts    *)
(* (an expired timeout is a protocol error, like the violations here), and *)
(* the server's callbacks.                                                 *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Callers,                \* the goroutines calling the client
    OpsPerCaller,           \* how many calls each goroutine makes
    Ops,                    \* which calls they may make (a subset of AllOps)
    MaxTip,                 \* how far the server's chain may grow
    MayStop,                \* TRUE: Stop may be called at any moment
    OldVersion,             \* TRUE: node-to-client version below 16 was negotiated
    \* Fixes and designs, FALSE in gOuroboros today:
    GateImmutable,          \* acquiring the immutable tip on OldVersion returns an error
    ReleaseChecksAcquired,  \* Release with nothing acquired returns an error
    ReleaseImplicit,        \* a call whose query acquired implicitly releases as it returns [G2]
    ReleasePerQuery,        \* (rejected design) release after each implicitly acquired query
    \* Mutations, FALSE in gOuroboros today, to check the checks:
    NoMutex,                \* calls do not take busyMutex
    KeepAcquiredOnFailure   \* handleFailure leaves `acquired` set

None == "none"

AllOps == {"AcqPoint", "AcqVolatile", "AcqImmutable", "Release", "Query",
           "Query2"}

\* In English: "The calls that query: Query makes one query, Query2 two."
QueryOps == {"Query", "Query2"}

\* In English: "How many queries call o makes."
QueriesIn(o) == IF o = "Query2" THEN 2 ELSE 1

\* In English: "The acquire target each Acquire call names."
OpTarget(o) == CASE o = "AcqPoint"     -> "SpecificPoint"
               []   o = "AcqVolatile"  -> "VolatileTip"
               []   o = "AcqImmutable" -> "ImmutableTip"
               []   OTHER              -> None

\* The transition table, as in LocalStateQuery.tla [S3].
Transitions ==
    { <<"StIdle",      "MsgAcquire",   "StAcquiring">>,
      <<"StIdle",      "MsgDone",      "StDone">>,
      <<"StAcquiring", "MsgAcquired",  "StAcquired">>,
      <<"StAcquiring", "MsgFailure",   "StIdle">>,
      <<"StAcquired",  "MsgQuery",     "StQuerying">>,
      <<"StAcquired",  "MsgReAcquire", "StAcquiring">>,
      <<"StAcquired",  "MsgRelease",   "StIdle">>,
      <<"StQuerying",  "MsgResult",    "StAcquired">> }

IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

\* In English: "A message: its type, its target (acquires only), the call
\* that sent the request it belongs to, and the snapshot a result was
\* computed from."
Msg(t, tg, c, sn) == [type |-> t, target |-> tg, for |-> c, snap |-> sn]

VARIABLES
    cpc,        \* cpc[c]: call c's next step
    op,         \* op[c]: the call c is making
    left,       \* left[c]: calls c has still to make
    cont,       \* cont[c]: after an acquire answer, "unlock" or "query"
    implicit,   \* implicit[c]: this query acquired the volatile tip itself
    startTip,   \* startTip[c]: the server's tip when the call began
    qleft,      \* qleft[c]: queries call c has still to make
    seen,       \* seen[c]: the snapshots call c's results came from
    busy,       \* who holds busyMutex, or None
    acquired,   \* the client's `acquired` flag
    explicit,   \* ghost: the state held was acquired by an Acquire call
    cstate,     \* the client protocol.Protocol's state, or "Violation"
    sstate,     \* the server's state, or "Violation"
    toServer,   \* messages on the wire to the server
    toClient,   \* messages on the wire to the client
    hpc,        \* the handler: "idle", or "give" while it blocks handing hmsg over
    hmsg,       \* the answer the handler is handing over
    pending,    \* the request the server is answering
    snap,       \* the snapshot the server holds for this client, or None
    tip,        \* the server's chain tip
    stopped,    \* Stop was called
    done,       \* DoneChan closed: the result channels are closed
    wrong,      \* ghost: some call received an answer to another call's request
    stale,      \* ghost: an implicit query answered from a state older than its start
    split       \* ghost: two queries of one call answered from different states

vars == <<cpc, op, left, cont, implicit, startTip, qleft, seen, busy,
          acquired, explicit, cstate, sstate, toServer, toClient, hpc, hmsg,
          pending, snap, tip, stopped, done, wrong, stale, split>>

callerVars == <<cpc, op, left, cont, implicit, startTip, qleft, seen>>
serverVars == <<sstate, pending, snap, tip>>

NoMsg == Msg(None, None, None, None)

\* In English: "Every call is about to start; both sides are in StIdle; the
\* chain is at 0."
Init ==
    /\ cpc = [c \in Callers |-> "start"]
    /\ op = [c \in Callers |-> None]
    /\ left = [c \in Callers |-> OpsPerCaller]
    /\ cont = [c \in Callers |-> "unlock"]
    /\ implicit = [c \in Callers |-> FALSE]
    /\ startTip = [c \in Callers |-> 0]
    /\ qleft = [c \in Callers |-> 0]                \* no call has begun
    /\ seen = [c \in Callers |-> {}]                \* no results yet
    /\ busy = None /\ acquired = FALSE /\ explicit = FALSE
    /\ cstate = "StIdle" /\ sstate = "StIdle"
    /\ toServer = <<>> /\ toClient = <<>>
    /\ hpc = "idle" /\ hmsg = NoMsg
    /\ pending = NoMsg /\ snap = None /\ tip = 0
    /\ stopped = FALSE /\ done = FALSE
    /\ wrong = FALSE /\ stale = FALSE /\ split = FALSE

-----------------------------------------------------------------------------
(* Sending [G1]: protocol.Protocol refuses to queue once stopped, and its  *)
(* send loop checks each message against the client's state. Callers hold  *)
(* busyMutex, so their sends never interleave (unless NoMutex).            *)

\* In English: "Call c sends m and then goes to step next: if the protocol
\* is stopped, SendMessage fails and the call returns; if m is not legal in
\* the client's state, that is a protocol error; otherwise the client moves
\* to the next state and m goes on the wire."
SendThen(c, m, next) ==
    IF stopped \/ done
        THEN /\ cpc' = [cpc EXCEPT ![c] = "unlock"]           \* ErrProtocolShuttingDown
             /\ UNCHANGED <<cstate, toServer>>
        ELSE IF ~IsLegal(cstate, m.type)
        THEN /\ cstate' = "Violation"                          \* sendLoop: SendError
             /\ cpc' = [cpc EXCEPT ![c] = next]                \* SendMessage already returned nil
             /\ UNCHANGED toServer
        ELSE /\ cstate' = After(cstate, m.type)
             /\ toServer' = Append(toServer, m)
             /\ cpc' = [cpc EXCEPT ![c] = next]

\* In English: "The acquire message for target tg: MsgReAcquire if the
\* client believes it holds a state, else MsgAcquire [G1 acquire]."
AcquireMsg(c, tg) ==
    Msg(IF acquired THEN "MsgReAcquire" ELSE "MsgAcquire", tg, c, None)

-----------------------------------------------------------------------------
(* The calls [G1].                                                         *)

\* In English: "Goroutine c picks its next call, notes the chain tip, and
\* starts with all of the call's queries still to make and none answered."
Begin(c) ==
    /\ cpc[c] = "start" /\ left[c] > 0
    /\ \E o \in Ops :
         /\ op' = [op EXCEPT ![c] = o]
         /\ cpc' = [cpc EXCEPT ![c] = IF NoMutex THEN "body" ELSE "lock"]
         /\ qleft' = [qleft EXCEPT ![c] = QueriesIn(o)]   \* queries to make
    /\ seen' = [seen EXCEPT ![c] = {}]                    \* no results yet
    /\ left' = [left EXCEPT ![c] = @ - 1]
    /\ startTip' = [startTip EXCEPT ![c] = tip]
    /\ UNCHANGED <<cont, implicit, busy, acquired, explicit, cstate, toServer,
                   toClient, hpc, hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "Take busyMutex when nobody holds it."
Lock(c) ==
    /\ cpc[c] = "lock" /\ busy = None
    /\ busy' = c
    /\ cpc' = [cpc EXCEPT ![c] = "body"]
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, cont, implicit, startTip, acquired, explicit,
                   cstate, toServer, toClient, hpc, hmsg, stopped, done,
                   wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "Acquire, AcquireVolatileTip, AcquireImmutableTip: with the
\* version gate, the immutable tip on an old version is an error and nothing
\* is sent; otherwise send the acquire and wait for its answer."
BodyAcquire(c) ==
    /\ cpc[c] = "body" /\ OpTarget(op[c]) /= None
    /\ IF GateImmutable /\ OldVersion /\ op[c] = "AcqImmutable"
          THEN /\ cpc' = [cpc EXCEPT ![c] = "unlock"]
               /\ UNCHANGED <<cstate, toServer, cont>>
          ELSE /\ SendThen(c, AcquireMsg(c, OpTarget(op[c])), "acq_wait")
               /\ cont' = [cont EXCEPT ![c] = "unlock"]
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, implicit, startTip, busy, acquired, explicit,
                   toClient, hpc, hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "Release: with the check, nothing acquired is an error;
\* otherwise send MsgRelease and clear the flag [G1 release]."
BodyRelease(c) ==
    /\ cpc[c] = "body" /\ op[c] = "Release"
    /\ IF ReleaseChecksAcquired /\ ~acquired
          THEN /\ cpc' = [cpc EXCEPT ![c] = "unlock"]
               /\ UNCHANGED <<cstate, toServer, acquired, explicit>>
          ELSE /\ SendThen(c, Msg("MsgRelease", None, c, None), "unlock")
               \* release() clears the flag only once SendMessage succeeded.
               /\ acquired' = (acquired /\ (stopped \/ done))
               /\ explicit' = (explicit /\ (stopped \/ done))
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, cont, implicit, startTip, busy, toClient, hpc,
                   hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "A call's next query: if nothing is acquired, first acquire
\* the volatile tip and come back; otherwise send MsgQuery
\* [G1 runQueryMaxItems]."
BodyQuery(c) ==
    /\ cpc[c] \in {"body", "query"} /\ op[c] \in QueryOps   \* a query call, at a query
    /\ IF ~acquired /\ cpc[c] = "body"
          THEN /\ SendThen(c, AcquireMsg(c, "VolatileTip"), "acq_wait")
               /\ cont' = [cont EXCEPT ![c] = "query"]
               /\ implicit' = [implicit EXCEPT ![c] = TRUE]
          ELSE /\ SendThen(c, Msg("MsgQuery", None, c, None), "query_wait")
               /\ UNCHANGED <<cont, implicit>>
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, startTip, busy, acquired, explicit, toClient, hpc,
                   hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "Waiting on acquireResultChan: take the handler's acquire
\* answer, or return ErrProtocolShuttingDown once the channel is closed. A
\* failure ends the call; success goes on to the query if there is one."
AcqWait(c) ==
    /\ cpc[c] = "acq_wait"
    /\ \/ /\ hpc = "give" /\ hmsg.type \in {"MsgAcquired", "MsgFailure"}
          /\ hpc' = "idle"
          /\ wrong' = (wrong \/ hmsg.for /= c)
          /\ cpc' = [cpc EXCEPT ![c] =
                       IF hmsg.type = "MsgAcquired" THEN cont[c] ELSE "unlock"]
          /\ explicit' = (hmsg.type = "MsgAcquired" /\ op[c] \notin QueryOps)
       \/ /\ done
          /\ cpc' = [cpc EXCEPT ![c] = "unlock"]
          /\ UNCHANGED <<hpc, wrong, explicit>>
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, cont, implicit, startTip, busy, acquired, cstate,
                   toServer, toClient, hmsg, stopped, done, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "Waiting on queryResultChan: take the result, or return once
\* the channel is closed. A result from a snapshot older than the chain at
\* the start of a call that did not acquire explicitly is stale. A result
\* from a different snapshot than an earlier result of the same call splits
\* the call. Then: with the rejected per-query design, release what this
\* query acquired; else make the call's next query; else, with the fix,
\* release what the call acquired; else return."
QueryWait(c) ==
    /\ cpc[c] = "query_wait"
    /\ \/ /\ hpc = "give" /\ hmsg.type = "MsgResult"
          /\ hpc' = "idle"
          /\ wrong' = (wrong \/ hmsg.for /= c)
          /\ stale' = (stale \/ (~explicit /\ hmsg.snap < startTip[c]))
          /\ split' = (split \/ (seen[c] /= {} /\ hmsg.snap \notin seen[c]))
          /\ seen' = [seen EXCEPT ![c] = @ \union {hmsg.snap}]   \* note the snapshot
          /\ qleft' = [qleft EXCEPT ![c] = @ - 1]                 \* one query done
          /\ cpc' = [cpc EXCEPT ![c] =
                       IF ReleasePerQuery /\ implicit[c] THEN "rel_query"
                       ELSE IF qleft[c] > 1 THEN "body"
                       ELSE IF ReleaseImplicit /\ implicit[c] THEN "rel_implicit"
                       ELSE "unlock"]
       \/ /\ done
          /\ cpc' = [cpc EXCEPT ![c] = "unlock"]
          /\ UNCHANGED <<hpc, wrong, stale, split, qleft, seen>>
    /\ UNCHANGED <<op, left, cont, implicit, startTip, busy, acquired, explicit,
                   cstate, toServer, toClient, hmsg, stopped, done>>
    /\ UNCHANGED serverVars

\* In English: "The fix [G2 endCall]: as the call returns, still holding
\* busyMutex, release what its queries acquired; release() clears the flag
\* only once SendMessage succeeded."
ReleaseOwn(c) ==
    /\ cpc[c] = "rel_implicit"
    /\ SendThen(c, Msg("MsgRelease", None, c, None), "unlock")
    /\ acquired' = (acquired /\ (stopped \/ done))   \* cleared unless shutting down
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, cont, implicit, startTip, busy, explicit, toClient,
                   hpc, hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "The rejected design: release what this one query acquired,
\* then make the call's next query (which acquires again), or return."
ReleaseOwnQuery(c) ==
    /\ cpc[c] = "rel_query"
    /\ SendThen(c, Msg("MsgRelease", None, c, None),
                IF qleft[c] > 0 THEN "body" ELSE "unlock")  \* next query, or return
    /\ acquired' = (acquired /\ (stopped \/ done))   \* cleared unless shutting down
    /\ implicit' = [implicit EXCEPT ![c] = FALSE]     \* the next query acquires anew
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, cont, startTip, busy, explicit, toClient,
                   hpc, hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

\* In English: "Return: release busyMutex and go on to the next call."
Unlock(c) ==
    /\ cpc[c] = "unlock"
    /\ busy' = IF busy = c THEN None ELSE busy
    /\ implicit' = [implicit EXCEPT ![c] = FALSE]
    /\ cpc' = [cpc EXCEPT ![c] = IF left[c] > 0 THEN "start" ELSE "done"]
    /\ UNCHANGED <<qleft, seen>>
    /\ UNCHANGED <<op, left, cont, startTip, acquired, explicit, cstate,
                   toServer, toClient, hpc, hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* The handler [G1]: reads one message at a time, checks it against the    *)
(* client's state, updates the flag, then blocks handing the answer over   *)
(* an unbuffered channel. It stops reading once DoneChan is closed.        *)

\* In English: "Read the next message. Not legal in the client's state: a
\* protocol error. MsgAcquired sets `acquired`; MsgFailure clears it (unless
\* the mutation); then the handler blocks until a call takes the answer."
HandlerRead ==
    /\ hpc = "idle" /\ ~done /\ toClient /= <<>>
    /\ LET m == Head(toClient) IN
         IF ~IsLegal(cstate, m.type)
            THEN /\ cstate' = "Violation"
                 /\ UNCHANGED <<hpc, hmsg, acquired, explicit>>
            ELSE /\ cstate' = After(cstate, m.type)
                 /\ hpc' = "give" /\ hmsg' = m
                 /\ acquired' = CASE m.type = "MsgAcquired" -> TRUE
                                []   m.type = "MsgFailure"  -> acquired /\ KeepAcquiredOnFailure
                                []   OTHER                  -> acquired
                 /\ explicit' = IF m.type = "MsgFailure" THEN FALSE ELSE explicit
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<busy, toServer, stopped, done, wrong, stale, split>>
    /\ UNCHANGED callerVars /\ UNCHANGED serverVars

-----------------------------------------------------------------------------
(* The server, as the reference allows [S3][R2][R3].                       *)

\* In English: "Read the next request. An immutable-tip acquire on an old
\* version cannot be decoded [R2][R3]; a message not legal in the server's
\* state is a violation; otherwise move on. Release drops the snapshot."
ServerRead ==
    /\ toServer /= <<>> /\ sstate /= "Violation"
    /\ LET m == Head(toServer) IN
         /\ sstate' = IF OldVersion /\ m.target = "ImmutableTip" THEN "Violation"
                      ELSE IF ~IsLegal(sstate, m.type) THEN "Violation"
                      ELSE After(sstate, m.type)
         /\ pending' = m
         /\ snap' = IF m.type = "MsgRelease" THEN None ELSE snap
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<tip>>
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toClient, hpc, hmsg,
                   stopped, done, wrong, stale, split>>
    /\ UNCHANGED callerVars

\* In English: "In StAcquiring, acquire: the volatile tip is the chain tip;
\* a point or the immutable tip may be any state up to the tip. Or, for a
\* point only, fail [R2]. Failing drops the old state [S3]."
ServerAcquire ==
    /\ sstate = "StAcquiring"
    /\ \/ /\ \E s \in IF pending.target = "VolatileTip" THEN {tip} ELSE 0..tip :
                snap' = s
          /\ sstate' = "StAcquired"
          /\ toClient' = Append(toClient, Msg("MsgAcquired", None, pending.for, None))
       \/ /\ pending.target = "SpecificPoint"
          /\ snap' = None
          /\ sstate' = "StIdle"
          /\ toClient' = Append(toClient, Msg("MsgFailure", None, pending.for, None))
    /\ UNCHANGED <<pending, tip>>
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, hpc, hmsg,
                   stopped, done, wrong, stale, split>>
    /\ UNCHANGED callerVars

\* In English: "In StQuerying, answer from the snapshot held."
ServerResult ==
    /\ sstate = "StQuerying"
    /\ sstate' = "StAcquired"
    /\ toClient' = Append(toClient, Msg("MsgResult", None, pending.for, snap))
    /\ UNCHANGED <<pending, snap, tip>>
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, hpc, hmsg,
                   stopped, done, wrong, stale, split>>
    /\ UNCHANGED callerVars

\* In English: "The chain grows."
Tick ==
    /\ tip < MaxTip
    /\ tip' = tip + 1
    /\ UNCHANGED <<sstate, pending, snap>>
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, toClient, hpc,
                   hmsg, stopped, done, wrong, stale, split>>
    /\ UNCHANGED callerVars

-----------------------------------------------------------------------------
(* Stopping [G1].                                                          *)

\* In English: "Stop may be called at any moment."
Stop ==
    /\ MayStop /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, toClient, hpc,
                   hmsg, done, wrong, stale, split>>
    /\ UNCHANGED callerVars /\ UNCHANGED serverVars

\* In English: "Once stopped, or after a protocol error on either side, the
\* loops exit when the handler is not blocked, DoneChan closes, and the
\* result channels are closed."
Teardown ==
    /\ ~done /\ hpc = "idle"
    /\ stopped \/ cstate = "Violation" \/ sstate = "Violation"
    /\ done' = TRUE
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, toClient, hpc,
                   hmsg, stopped, wrong, stale, split>>
    /\ UNCHANGED callerVars /\ UNCHANGED serverVars

\* In English: "Every call has returned."
Finished ==
    /\ \A c \in Callers : cpc[c] = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Callers :
          \/ Begin(c) \/ Lock(c) \/ BodyAcquire(c) \/ BodyRelease(c)
          \/ BodyQuery(c) \/ AcqWait(c) \/ QueryWait(c) \/ ReleaseOwn(c)
          \/ ReleaseOwnQuery(c)
          \/ Unlock(c)
    \/ HandlerRead
    \/ ServerRead \/ ServerAcquire \/ ServerResult \/ Tick
    \/ Stop \/ Teardown
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "No call ever receives an answer to another call's request."
OwnAnswer == ~wrong

\* In English: "Neither side ever sees a message its state does not allow."
NoViolation == cstate /= "Violation" /\ sstate /= "Violation"

\* In English: "When no call is inside the client, the handler is idle,
\* nothing is on the wire and the protocol is running, the `acquired` flag
\* is TRUE exactly when the protocol is in StAcquired."
FlagMatchesState ==
    ( /\ \A c \in Callers : cpc[c] \in {"start", "lock", "done"}
      /\ hpc = "idle" /\ toServer = <<>> /\ toClient = <<>>
      /\ ~done /\ NoViolation )
    => (acquired <=> cstate = "StAcquired")

\* In English: "A query made with no explicit acquire never answers from a
\* state older than the chain when the call began."
FreshImplicitSnapshot == ~stale

\* In English: "All the queries of one call answer from the same ledger
\* state, so a call that asks for the era and then for that era's data
\* never decodes one state's answer with another state's era."
OneSnapshotPerCall == ~split

\* Reachability probes, EXPECTED to be violated.
\* "Stop never lands while a call waits for its answer."
ProbeNoStopWhileWaiting ==
    ~(stopped /\ \E c \in Callers : cpc[c] \in {"acq_wait", "query_wait"})
\* "No query ever acquires implicitly."
ProbeNoImplicit == \A c \in Callers : ~implicit[c]
\* "No MsgReAcquire is ever sent."
ProbeNoReAcquire == \A i \in 1..Len(toServer) : toServer[i].type /= "MsgReAcquire"
\* "No acquire ever fails."
ProbeNoFailure == hmsg.type /= "MsgFailure"
\* "Two calls never wait inside the client at once."
ProbeOneInside ==
    ~(\E c, d \in Callers : c /= d /\ cpc[c] \in {"lock"} /\ cpc[d] \in {"acq_wait", "query_wait"})
=============================================================================
