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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
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

\* Literally: "None is defined as "none"."
None == "none"

\* Literally: "AllOps is defined as the set containing "AcqPoint",
\*   "AcqVolatile", "AcqImmutable", "Release", "Query" and "Query2"."
AllOps == {"AcqPoint", "AcqVolatile", "AcqImmutable", "Release", "Query",
           "Query2"}

\* In English: "The calls that query: Query makes one query, Query2 two."
\* Literally: "QueryOps is defined as the set containing "Query" and "Query2"."
QueryOps == {"Query", "Query2"}

\* In English: "How many queries call o makes."
\* Literally: "QueriesIn of o is defined as: if o equals "Query2" then 2, else
\*   1."
QueriesIn(o) == IF o = "Query2" THEN 2 ELSE 1

\* In English: "The acquire target each Acquire call names."
\* Literally: "OpTarget of o is defined as: in the case o equals "AcqPoint",
\*   "SpecificPoint"; in the case o equals "AcqVolatile", "VolatileTip"; in the
\*   case o equals "AcqImmutable", "ImmutableTip"; in every other case, None."
OpTarget(o) == CASE o = "AcqPoint"     -> "SpecificPoint"
               []   o = "AcqVolatile"  -> "VolatileTip"
               []   o = "AcqImmutable" -> "ImmutableTip"
               []   OTHER              -> None

\* The transition table, as in LocalStateQuery.tla [S3].
\* Literally: "Transitions is defined as the set containing these eight tuples:
\*   <<"StIdle", "MsgAcquire", "StAcquiring">>, <<"StIdle", "MsgDone",
\*   "StDone">>, <<"StAcquiring", "MsgAcquired", "StAcquired">>,
\*   <<"StAcquiring", "MsgFailure", "StIdle">>, <<"StAcquired", "MsgQuery",
\*   "StQuerying">>, <<"StAcquired", "MsgReAcquire", "StAcquiring">>,
\*   <<"StAcquired", "MsgRelease", "StIdle">>, and <<"StQuerying", "MsgResult",
\*   "StAcquired">>."
Transitions ==
    { <<"StIdle",      "MsgAcquire",   "StAcquiring">>,
      <<"StIdle",      "MsgDone",      "StDone">>,
      <<"StAcquiring", "MsgAcquired",  "StAcquired">>,
      <<"StAcquiring", "MsgFailure",   "StIdle">>,
      <<"StAcquired",  "MsgQuery",     "StQuerying">>,
      <<"StAcquired",  "MsgReAcquire", "StAcquiring">>,
      <<"StAcquired",  "MsgRelease",   "StIdle">>,
      <<"StQuerying",  "MsgResult",    "StAcquired">> }

\* In English: "Message type t is legal in state s if a row starts with s, t."
\* Literally: "IsLegal of s and t is defined as: there exists a tr that is a
\*   member of Transitions such that element 1 of tr equals s and element 2 of
\*   tr equals t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
\* In English: "The state that sending t in s moves to."
\* Literally: "After of s and t is defined as element 3 of the tr, chosen from
\*   Transitions, such that element 1 of tr equals s and element 2 of tr equals
\*   t."
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

\* In English: "A message: its type, its target (acquires only), the call
\* that sent the request it belongs to, and the snapshot a result was
\* computed from."
\* Literally: "Msg of t, tg, c and sn is defined as the record whose field type
\*   is t, whose field target is tg, whose field for is c, and whose field snap
\*   is sn."
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

\* Literally: "vars is defined as the tuple of all twenty-five variables."
vars == <<cpc, op, left, cont, implicit, startTip, qleft, seen, busy,
          acquired, explicit, cstate, sstate, toServer, toClient, hpc, hmsg,
          pending, snap, tip, stopped, done, wrong, stale, split>>

\* Literally: "callerVars is defined as the tuple of cpc, op, left, cont,
\*   implicit, startTip, qleft and seen."
callerVars == <<cpc, op, left, cont, implicit, startTip, qleft, seen>>
\* Literally: "serverVars is defined as the tuple of sstate, pending, snap and
\*   tip."
serverVars == <<sstate, pending, snap, tip>>

\* In English: "The empty message: every field is None."
\* Literally: "NoMsg is defined as Msg of None, None, None and None."
NoMsg == Msg(None, None, None, None)

\* In English: "Every call is about to start; both sides are in StIdle; the
\* chain is at 0."
\* Literally: "Init is defined as: cpc equals the function that maps every c in
\*   Callers to "start", and op equals the function that maps every c in
\*   Callers to None, and left equals the function that maps every c in Callers
\*   to OpsPerCaller, and cont equals the function that maps every c in Callers
\*   to "unlock", and implicit equals the function that maps every c in Callers
\*   to FALSE, and startTip equals the function that maps every c in Callers to
\*   0, and qleft equals the function that maps every c in Callers to 0, and
\*   seen equals the function that maps every c in Callers to the empty set,
\*   and busy equals None and acquired equals FALSE and explicit equals FALSE,
\*   and cstate equals "StIdle" and sstate equals "StIdle", and toServer equals
\*   the empty sequence and toClient equals the empty sequence, and hpc equals
\*   "idle" and hmsg equals NoMsg, and pending equals NoMsg and snap equals
\*   None and tip equals 0, and stopped equals FALSE and done equals FALSE, and
\*   wrong equals FALSE and stale equals FALSE and split equals FALSE."
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
\* Literally: "SendThen of c, m and next is defined as: if stopped or done,
\*   then cpc in the next state equals cpc except that its c entry is "unlock",
\*   and cstate and toServer are unchanged; else if IsLegal of cstate and m's
\*   type is not true, then cstate in the next state equals "Violation", and
\*   cpc in the next state equals cpc except that its c entry is next, and
\*   toServer is unchanged; else cstate in the next state equals After of
\*   cstate and m's type, and toServer in the next state equals toServer with m
\*   appended, and cpc in the next state equals cpc except that its c entry is
\*   next."
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
\* Literally: "AcquireMsg of c and tg is defined as Msg of (if acquired then
\*   "MsgReAcquire", else "MsgAcquire"), tg, c, and None."
AcquireMsg(c, tg) ==
    Msg(IF acquired THEN "MsgReAcquire" ELSE "MsgAcquire", tg, c, None)

-----------------------------------------------------------------------------
(* The calls [G1].                                                         *)

\* In English: "Goroutine c picks its next call, notes the chain tip, and
\* starts with all of the call's queries still to make and none answered."
\* Literally: "Begin of c is defined as: cpc of c equals "start" and left of c
\*   is greater than 0, and there exists an o in Ops such that op in the next
\*   state equals op except that its c entry is o, and cpc in the next state
\*   equals cpc except that its c entry is (if NoMutex then "body", else
\*   "lock"), and qleft in the next state equals qleft except that its c entry
\*   is QueriesIn of o; and seen in the next state equals seen except that its
\*   c entry is the empty set, and left in the next state equals left except
\*   that its c entry is the old entry minus 1, and startTip in the next state
\*   equals startTip except that its c entry is tip, and cont, implicit, busy,
\*   acquired, explicit, cstate, toServer, toClient, hpc, hmsg, stopped, done,
\*   wrong, stale and split are unchanged, and serverVars is unchanged."
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
\* Literally: "Lock of c is defined as: cpc of c equals "lock" and busy equals
\*   None, and busy in the next state equals c, and cpc in the next state
\*   equals cpc except that its c entry is "body", and qleft and seen are
\*   unchanged, and op, left, cont, implicit, startTip, acquired, explicit,
\*   cstate, toServer, toClient, hpc, hmsg, stopped, done, wrong, stale and
\*   split are unchanged, and serverVars is unchanged."
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
\* Literally: "BodyAcquire of c is defined as: cpc of c equals "body" and
\*   OpTarget of op of c does not equal None, and if GateImmutable and
\*   OldVersion and op of c equals "AcqImmutable", then cpc in the next state
\*   equals cpc except that its c entry is "unlock", and cstate, toServer and
\*   cont are unchanged; else SendThen of c, AcquireMsg of c and OpTarget of op
\*   of c, and "acq_wait", and cont in the next state equals cont except that
\*   its c entry is "unlock"; and qleft and seen are unchanged, and op, left,
\*   implicit, startTip, busy, acquired, explicit, toClient, hpc, hmsg,
\*   stopped, done, wrong, stale and split are unchanged, and serverVars is
\*   unchanged."
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
\* Literally: "BodyRelease of c is defined as: cpc of c equals "body" and op of
\*   c equals "Release", and if ReleaseChecksAcquired is true and acquired is
\*   not true, then cpc in the next state equals cpc except that its c entry is
\*   "unlock", and cstate, toServer, acquired and explicit are unchanged; else
\*   SendThen of c, Msg of "MsgRelease", None, c and None, and "unlock", and
\*   acquired in the next state equals (acquired and (stopped or done)), and
\*   explicit in the next state equals (explicit and (stopped or done)); and
\*   qleft and seen are unchanged, and op, left, cont, implicit, startTip,
\*   busy, toClient, hpc, hmsg, stopped, done, wrong, stale and split are
\*   unchanged, and serverVars is unchanged."
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
\* Literally: "BodyQuery of c is defined as: cpc of c is a member of the set
\*   containing "body" and "query", and op of c is a member of QueryOps, and if
\*   acquired is not true and cpc of c equals "body", then SendThen of c,
\*   AcquireMsg of c and "VolatileTip", and "acq_wait", and cont in the next
\*   state equals cont except that its c entry is "query", and implicit in the
\*   next state equals implicit except that its c entry is TRUE; else SendThen
\*   of c, Msg of "MsgQuery", None, c and None, and "query_wait", and cont and
\*   implicit are unchanged; and qleft and seen are unchanged, and op, left,
\*   startTip, busy, acquired, explicit, toClient, hpc, hmsg, stopped, done,
\*   wrong, stale and split are unchanged, and serverVars is unchanged."
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
\* Literally: "AcqWait of c is defined as: cpc of c equals "acq_wait", and
\*   either (hpc equals "give" and hmsg's type is a member of the set
\*   containing "MsgAcquired" and "MsgFailure", and hpc in the next state
\*   equals "idle", and wrong in the next state equals (wrong, or hmsg's for
\*   does not equal c), and cpc in the next state equals cpc except that its c
\*   entry is (if hmsg's type equals "MsgAcquired" then cont of c, else
\*   "unlock"), and explicit in the next state equals (hmsg's type equals
\*   "MsgAcquired" and op of c is not a member of QueryOps)), or (done is true,
\*   and cpc in the next state equals cpc except that its c entry is "unlock",
\*   and hpc, wrong and explicit are unchanged); and qleft and seen are
\*   unchanged, and op, left, cont, implicit, startTip, busy, acquired, cstate,
\*   toServer, toClient, hmsg, stopped, done, stale and split are unchanged,
\*   and serverVars is unchanged."
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
\* Literally: "QueryWait of c is defined as: cpc of c equals "query_wait", and
\*   either (hpc equals "give" and hmsg's type equals "MsgResult", and hpc in
\*   the next state equals "idle", and wrong in the next state equals (wrong,
\*   or hmsg's for does not equal c), and stale in the next state equals
\*   (stale, or explicit is not true and hmsg's snap is less than startTip of
\*   c), and split in the next state equals (split, or seen of c does not equal
\*   the empty set and hmsg's snap is not a member of seen of c), and seen in
\*   the next state equals seen except that its c entry is the union of the old
\*   entry and the set containing hmsg's snap, and qleft in the next state
\*   equals qleft except that its c entry is the old entry minus 1, and cpc in
\*   the next state equals cpc except that its c entry is: if ReleasePerQuery
\*   and implicit of c, then "rel_query"; else if qleft of c is greater than 1,
\*   then "body"; else if ReleaseImplicit and implicit of c, then
\*   "rel_implicit"; else "unlock"), or (done is true, and cpc in the next
\*   state equals cpc except that its c entry is "unlock", and hpc, wrong,
\*   stale, split, qleft and seen are unchanged); and op, left, cont, implicit,
\*   startTip, busy, acquired, explicit, cstate, toServer, toClient, hmsg,
\*   stopped and done are unchanged, and serverVars is unchanged."
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
\* Literally: "ReleaseOwn of c is defined as: cpc of c equals "rel_implicit",
\*   and SendThen of c, Msg of "MsgRelease", None, c and None, and "unlock",
\*   and acquired in the next state equals (acquired and (stopped or done)),
\*   and qleft and seen are unchanged, and op, left, cont, implicit, startTip,
\*   busy, explicit, toClient, hpc, hmsg, stopped, done, wrong, stale and split
\*   are unchanged, and serverVars is unchanged."
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
\* Literally: "ReleaseOwnQuery of c is defined as: cpc of c equals "rel_query",
\*   and SendThen of c, Msg of "MsgRelease", None, c and None, and (if qleft of
\*   c is greater than 0 then "body", else "unlock"), and acquired in the next
\*   state equals (acquired and (stopped or done)), and implicit in the next
\*   state equals implicit except that its c entry is FALSE, and qleft and seen
\*   are unchanged, and op, left, cont, startTip, busy, explicit, toClient,
\*   hpc, hmsg, stopped, done, wrong, stale and split are unchanged, and
\*   serverVars is unchanged."
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
\* Literally: "Unlock of c is defined as: cpc of c equals "unlock", and busy in
\*   the next state equals (if busy equals c then None, else busy), and
\*   implicit in the next state equals implicit except that its c entry is
\*   FALSE, and cpc in the next state equals cpc except that its c entry is (if
\*   left of c is greater than 0 then "start", else "done"), and qleft and seen
\*   are unchanged, and op, left, cont, startTip, acquired, explicit, cstate,
\*   toServer, toClient, hpc, hmsg, stopped, done, wrong, stale and split are
\*   unchanged, and serverVars is unchanged."
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
\* Literally: "HandlerRead is defined as: hpc equals "idle" and done is not
\*   true and toClient does not equal the empty sequence, and, letting m be the
\*   head of toClient: if IsLegal of cstate and m's type is not true, then
\*   cstate in the next state equals "Violation", and hpc, hmsg, acquired and
\*   explicit are unchanged; else cstate in the next state equals After of
\*   cstate and m's type, and hpc in the next state equals "give" and hmsg in
\*   the next state equals m, and acquired in the next state equals: in the
\*   case m's type equals "MsgAcquired", TRUE; in the case m's type equals
\*   "MsgFailure", acquired and KeepAcquiredOnFailure; in every other case,
\*   acquired; and explicit in the next state equals (if m's type equals
\*   "MsgFailure" then FALSE, else explicit); and toClient in the next state
\*   equals the tail of toClient, and busy, toServer, stopped, done, wrong,
\*   stale and split are unchanged, and callerVars is unchanged and serverVars
\*   is unchanged."
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
\* Literally: "ServerRead is defined as: toServer does not equal the empty
\*   sequence and sstate does not equal "Violation", and, letting m be the head
\*   of toServer: sstate in the next state equals (if OldVersion and m's target
\*   equals "ImmutableTip" then "Violation"; else if IsLegal of sstate and m's
\*   type is not true then "Violation"; else After of sstate and m's type), and
\*   pending in the next state equals m, and snap in the next state equals (if
\*   m's type equals "MsgRelease" then None, else snap); and toServer in the
\*   next state equals the tail of toServer, and tip is unchanged, and busy,
\*   acquired, explicit, cstate, toClient, hpc, hmsg, stopped, done, wrong,
\*   stale and split are unchanged, and callerVars is unchanged."
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
\* Literally: "ServerAcquire is defined as: sstate equals "StAcquiring", and
\*   either (there exists an s in (if pending's target equals "VolatileTip"
\*   then the set containing tip, else 0 through tip) such that snap in the
\*   next state equals s, and sstate in the next state equals "StAcquired", and
\*   toClient in the next state equals toClient with Msg of "MsgAcquired",
\*   None, pending's for, and None appended), or (pending's target equals
\*   "SpecificPoint", and snap in the next state equals None, and sstate in the
\*   next state equals "StIdle", and toClient in the next state equals toClient
\*   with Msg of "MsgFailure", None, pending's for, and None appended); and
\*   pending and tip are unchanged, and busy, acquired, explicit, cstate,
\*   toServer, hpc, hmsg, stopped, done, wrong, stale and split are unchanged,
\*   and callerVars is unchanged."
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
\* Literally: "ServerResult is defined as: sstate equals "StQuerying", and
\*   sstate in the next state equals "StAcquired", and toClient in the next
\*   state equals toClient with Msg of "MsgResult", None, pending's for, and
\*   snap appended, and pending, snap and tip are unchanged, and busy,
\*   acquired, explicit, cstate, toServer, hpc, hmsg, stopped, done, wrong,
\*   stale and split are unchanged, and callerVars is unchanged."
ServerResult ==
    /\ sstate = "StQuerying"
    /\ sstate' = "StAcquired"
    /\ toClient' = Append(toClient, Msg("MsgResult", None, pending.for, snap))
    /\ UNCHANGED <<pending, snap, tip>>
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, hpc, hmsg,
                   stopped, done, wrong, stale, split>>
    /\ UNCHANGED callerVars

\* In English: "The chain grows."
\* Literally: "Tick is defined as: tip is less than MaxTip, and tip in the next
\*   state equals tip plus 1, and sstate, pending and snap are unchanged, and
\*   busy, acquired, explicit, cstate, toServer, toClient, hpc, hmsg, stopped,
\*   done, wrong, stale and split are unchanged, and callerVars is unchanged."
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
\* Literally: "Stop is defined as: MayStop is true and stopped is not true, and
\*   stopped in the next state equals TRUE, and busy, acquired, explicit,
\*   cstate, toServer, toClient, hpc, hmsg, done, wrong, stale and split are
\*   unchanged, and callerVars is unchanged and serverVars is unchanged."
Stop ==
    /\ MayStop /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, toClient, hpc,
                   hmsg, done, wrong, stale, split>>
    /\ UNCHANGED callerVars /\ UNCHANGED serverVars

\* In English: "Once stopped, or after a protocol error on either side, the
\* loops exit when the handler is not blocked, DoneChan closes, and the
\* result channels are closed."
\* Literally: "Teardown is defined as: done is not true and hpc equals "idle",
\*   and (stopped is true, or cstate equals "Violation", or sstate equals
\*   "Violation"), and done in the next state equals TRUE, and busy, acquired,
\*   explicit, cstate, toServer, toClient, hpc, hmsg, stopped, wrong, stale and
\*   split are unchanged, and callerVars is unchanged and serverVars is
\*   unchanged."
Teardown ==
    /\ ~done /\ hpc = "idle"
    /\ stopped \/ cstate = "Violation" \/ sstate = "Violation"
    /\ done' = TRUE
    /\ UNCHANGED <<busy, acquired, explicit, cstate, toServer, toClient, hpc,
                   hmsg, stopped, wrong, stale, split>>
    /\ UNCHANGED callerVars /\ UNCHANGED serverVars

\* In English: "Every call has returned."
\* Literally: "Finished is defined as: for all c in Callers, cpc of c equals
\*   "done", and vars is unchanged."
Finished ==
    /\ \A c \in Callers : cpc[c] = "done"
    /\ UNCHANGED vars

\* In English: "A step is a step of some call, the handler reading, a server
\* step, the chain growing, Stop, teardown, or, once every call has returned,
\* nothing."
\* Literally: "Next is defined as: there exists a c in Callers such that Begin
\*   of c, or Lock of c, or BodyAcquire of c, or BodyRelease of c, or BodyQuery
\*   of c, or AcqWait of c, or QueryWait of c, or ReleaseOwn of c, or
\*   ReleaseOwnQuery of c, or Unlock of c; or HandlerRead; or ServerRead, or
\*   ServerAcquire, or ServerResult, or Tick; or Stop, or Teardown; or
\*   Finished."
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

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "No call ever receives an answer to another call's request."
\* Literally: "OwnAnswer is defined as: wrong is not true."
OwnAnswer == ~wrong

\* In English: "Neither side ever sees a message its state does not allow."
\* Literally: "NoViolation is defined as: cstate does not equal "Violation",
\*   and sstate does not equal "Violation"."
NoViolation == cstate /= "Violation" /\ sstate /= "Violation"

\* In English: "When no call is inside the client, the handler is idle,
\* nothing is on the wire and the protocol is running, the `acquired` flag
\* is TRUE exactly when the protocol is in StAcquired."
\* Literally: "FlagMatchesState is defined as: if (for all c in Callers, cpc of
\*   c is a member of the set containing "start", "lock" and "done", and hpc
\*   equals "idle" and toServer equals the empty sequence and toClient equals
\*   the empty sequence, and done is not true and NoViolation is true), then
\*   (acquired is true if and only if cstate equals "StAcquired")."
FlagMatchesState ==
    ( /\ \A c \in Callers : cpc[c] \in {"start", "lock", "done"}
      /\ hpc = "idle" /\ toServer = <<>> /\ toClient = <<>>
      /\ ~done /\ NoViolation )
    => (acquired <=> cstate = "StAcquired")

\* In English: "A query made with no explicit acquire never answers from a
\* state older than the chain when the call began."
\* Literally: "FreshImplicitSnapshot is defined as: stale is not true."
FreshImplicitSnapshot == ~stale

\* In English: "All the queries of one call answer from the same ledger
\* state, so a call that asks for the era and then for that era's data
\* never decodes one state's answer with another state's era."
\* Literally: "OneSnapshotPerCall is defined as: split is not true."
OneSnapshotPerCall == ~split

\* Reachability probes, EXPECTED to be violated.
\* "Stop never lands while a call waits for its answer."
\* Literally: "ProbeNoStopWhileWaiting is defined as: it is not the case that
\*   (stopped is true and there exists a c in Callers such that cpc of c is a
\*   member of the set containing "acq_wait" and "query_wait")."
ProbeNoStopWhileWaiting ==
    ~(stopped /\ \E c \in Callers : cpc[c] \in {"acq_wait", "query_wait"})
\* "No query ever acquires implicitly."
\* Literally: "ProbeNoImplicit is defined as: for all c in Callers, implicit of
\*   c is not true."
ProbeNoImplicit == \A c \in Callers : ~implicit[c]
\* "No MsgReAcquire is ever sent."
\* Literally: "ProbeNoReAcquire is defined as: for all i in 1 through the
\*   length of toServer, element i of toServer's type does not equal
\*   "MsgReAcquire"."
ProbeNoReAcquire == \A i \in 1..Len(toServer) : toServer[i].type /= "MsgReAcquire"
\* "No acquire ever fails."
\* Literally: "ProbeNoFailure is defined as: hmsg's type does not equal
\*   "MsgFailure"."
ProbeNoFailure == hmsg.type /= "MsgFailure"
\* "Two calls never wait inside the client at once."
\* Literally: "ProbeOneInside is defined as: it is not the case that there
\*   exist a c and a d in Callers such that c does not equal d, and cpc of c is
\*   a member of the set containing "lock", and cpc of d is a member of the set
\*   containing "acq_wait" and "query_wait"."
ProbeOneInside ==
    ~(\E c, d \in Callers : c /= d /\ cpc[c] \in {"lock"} /\ cpc[d] \in {"acq_wait", "query_wait"})
=============================================================================
