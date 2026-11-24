--------------------------- MODULE BlockFetchQueue ---------------------------
(***************************************************************************)
(* Model 06, slice 1: how the block-fetch client matches each answer to    *)
(* the MsgRequestRange that asked for it, and how every request is         *)
(* resolved exactly once, including when the protocol shuts down.          *)
(*                                                                         *)
(* What the code does (protocol/blockfetch/client.go):                     *)
(*   RequestRange (or GetBlockRange, GetBlock) takes a send token, appends *)
(*   a request to a FIFO queue, queues its MsgRequestRange on the          *)
(*   protocol, and gives the token back (sendRequestRange). The token is   *)
(*   what keeps queue order equal to wire order.                           *)
(*   The handler matches every answer to the head of the queue             *)
(*   (headForResponse): MsgStartBatch and MsgNoBlocks need a head that has *)
(*   not started, MsgBlock and MsgBatchDone one that has. MsgNoBlocks and  *)
(*   MsgBatchDone remove the head and resolve it: RangeDoneFunc, once      *)
(*   (resolve, guarded by resolveOnce).                                    *)
(*   When the protocol stops (a peer error, a range deadline, Stop), a     *)
(*   watcher drains the whole queue and resolves every entry with          *)
(*   ErrProtocolShuttingDown (failOutstandingForProtocol, failOutstanding, *)
(*   watchRangeDeadline).                                                  *)
(*                                                                         *)
(* The engine's part is not re-modelled: Model 03 (EnginePipelining.tla)   *)
(* shows that with an honest peer the engine delivers block-fetch answers  *)
(* in order and never refuses one. So here the handler simply reads the    *)
(* server's answers in order.                                              *)
(*                                                                         *)
(* Sources (IntersectMBO/ouroboros-network 5f356486ab3e; README has links):*)
(*   [B1] docs/network-spec/miniprotocols.tex 1139-1204: block-fetch       *)
(*        states, agency, and transitions.                                 *)
(*   [P1] miniprotocols.tex 2180-2208: pipelining; answers come back in    *)
(*        request order, so the client knows which answer is whose.        *)
(*   [R3] .../Protocol/BlockFetch/Client.hs 152-170: each pipelined        *)
(*        request carries its own receiver, run on that request's answer.  *)
(*   gOuroboros, blinklabs-io/gouroboros 61046085:                         *)
(*   [G1] protocol/blockfetch/client.go: sendRequestRange (965-1058: the   *)
(*        token, append, send, and removeLocked when the send fails),      *)
(*        headForResponse (1175), handleStartBatch (1353), handleNoBlocks  *)
(*        (1377), handleBatchDone (1707), resolve (1217),                  *)
(*        failOutstanding (1259), failOutstandingForProtocol (1281),       *)
(*        watchRangeDeadline (1071).                                       *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Callers,   \* how many RequestRange calls the application makes
    \* TRUE as in gOuroboros: the send token covers the append and the send.
    UseSendToken,
    \* TRUE as in gOuroboros: a watcher resolves the queue on shutdown.
    DrainOnShutdown,
    \* FALSE as in gOuroboros: the drain also resolves a request whose
    \* MsgRequestRange is not yet queued, though RequestRange will then
    \* return an error for it. TRUE is a possible fix: leave those to their
    \* caller, which removes them when its send fails.
    DrainSkipsUnsent,
    \* FALSE as in gOuroboros 61046085. TRUE is the fix on gOuroboros branch
    \* fix/blockfetch-no-callback-for-unsent: the send's outcome and the
    \* caller clearing its "sending" mark are separate steps, and a drain
    \* that finds a request still sending takes it out of the queue without
    \* resolving it, recording the drain's error for its caller instead
    \* (rangeRequest.sending, rangeRequest.drainErr).
    DrainDefersSending,
    \* TRUE with DrainDefersSending: a caller whose send succeeded resolves
    \* the request a drain left to it. FALSE is a mutation.
    SenderResolvesDrained,
    \* TRUE as in gOuroboros: MsgNoBlocks takes its request out of the queue
    \* (removeLocked in handleNoBlocks). FALSE is a mutation.
    NoBlocksRemovesHead,
    \* TRUE as in gOuroboros: MsgStartBatch marks its request started
    \* (handleStartBatch). FALSE is a mutation.
    StartMarksStarted

Ids == 1..Callers

VARIABLES
    caller,    \* caller[i]: "new", "appended" (in the queue, send pending),
               \* "sendOk" (the send succeeded, the caller has not yet
               \* cleared its sending mark; DrainDefersSending only),
               \* "sent" (RequestRange returned the id), "refused"
               \* (RequestRange returned an error)
    handedOver, \* ids a drain took out of the queue while still sending,
                \* left for their callers to resolve
    token,     \* the caller holding the send token, or 0
    queue,     \* the client's FIFO: records [id, started]
    up,        \* TRUE while the protocol runs
    toServer,  \* MsgRequestRange in flight, by id
    sv,        \* the server: [id, phase]; phase "idle", "busy", "block"
               \* (owes a block), or "end" (owes MsgBatchDone)
    toClient,  \* answers in flight: [id, m], m in {"SB","NB","B","BD"}.
               \* The id is for checking only; it is not on the wire.
    done,      \* done[i]: how many times RangeDoneFunc ran for request i
    misrouted, \* TRUE once an answer was applied to another request
    clientErr  \* TRUE once the handler refused an honest answer

vars == <<caller, handedOver, token, queue, up, toServer, sv, toClient, done,
          misrouted, clientErr>>

\* In English: "Nobody has called yet; the protocol runs; nothing in flight."
Init ==
    /\ caller = [i \in Ids |-> "new"]
    /\ handedOver = {}
    /\ token = 0
    /\ queue = <<>>
    /\ up = TRUE
    /\ toServer = <<>>
    /\ sv = [id |-> 0, phase |-> "idle"]
    /\ toClient = <<>>
    /\ done = [i \in Ids |-> 0]
    /\ misrouted = FALSE
    /\ clientErr = FALSE

\* In English: "The queue with request i taken out, wherever it is."
\* SelectSeq(s, Test) keeps the items of list s for which Test is true, in
\* order; LAMBDA r : P is an unnamed test, like a Go func literal. Both are
\* in "Specifying Systems" section 18.1 (the Sequences module).
Without(q, i) == SelectSeq(q, LAMBDA r : r.id /= i)

\* In English: "Request i is somewhere in the queue."
Queued(q, i) == \E k \in 1..Len(q) : q[k].id = i

-----------------------------------------------------------------------------
(* The callers [G1]. *)

\* In English: "Caller i takes the send token (if the code uses one) and
\* appends its request to the queue." The code may take the token even
\* after the protocol stopped: its select has both cases ready.
Admit(i) ==
    /\ caller[i] = "new"
    /\ UseSendToken => token = 0               \* the token is free
    /\ token' = IF UseSendToken THEN i ELSE token
    /\ queue' = Append(queue, [id |-> i, started |-> FALSE])
    /\ caller' = [caller EXCEPT ![i] = "appended"]
    /\ UNCHANGED <<handedOver, up, toServer, sv, toClient, done, misrouted,
                   clientErr>>

\* In English: "Caller i queues its MsgRequestRange and returns the id. If
\* the protocol has stopped, the send fails: the caller removes its request
\* if it is still queued (removeLocked) and returns an error. Either way it
\* hands the token back. With DrainDefersSending, a successful send only
\* moves the caller to "sendOk"; SendFinish then returns the id."
Send(i) ==
    /\ caller[i] = "appended"
    /\ IF up
          THEN /\ toServer' = Append(toServer, i)
               /\ caller' = [caller EXCEPT ![i] =
                                IF DrainDefersSending THEN "sendOk"
                                                      ELSE "sent"]
               /\ UNCHANGED queue
          ELSE /\ queue' = Without(queue, i)
               /\ caller' = [caller EXCEPT ![i] = "refused"]
               /\ UNCHANGED toServer
    /\ token' = IF token = i THEN 0 ELSE token
    /\ UNCHANGED <<handedOver, up, sv, toClient, done, misrouted, clientErr>>

\* In English: "Caller i, whose send succeeded, clears its sending mark and
\* returns the id. If a drain took the request while it was still sending,
\* the caller resolves it now with the drain's error." (DrainDefersSending)
SendFinish(i) ==
    /\ caller[i] = "sendOk"
    /\ caller' = [caller EXCEPT ![i] = "sent"]
    /\ done' = IF SenderResolvesDrained /\ i \in handedOver
                  THEN [done EXCEPT ![i] = @ + 1]
                  ELSE done
    /\ UNCHANGED <<handedOver, token, queue, up, toServer, sv, toClient,
                   misrouted, clientErr>>

-----------------------------------------------------------------------------
(* The honest server [B1]: it takes requests in order and answers each     *)
(* with MsgNoBlocks, or MsgStartBatch, one MsgBlock, and MsgBatchDone.     *)
(* It keeps going whether or not the client's protocol still runs.         *)

\* In English: "Idle, the server takes the next request."
ServerTake ==
    /\ sv.phase = "idle" /\ toServer /= <<>>
    /\ sv' = [id |-> Head(toServer), phase |-> "busy"]
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<caller, handedOver, token, queue, up, toClient, done,
                   misrouted, clientErr>>

\* In English: "Busy, the server answers MsgNoBlocks or MsgStartBatch;
\* streaming, it sends the block, then MsgBatchDone."
ServerAnswer ==
    /\ \/ /\ sv.phase = "busy"
          /\ \/ /\ toClient' = Append(toClient, [id |-> sv.id, m |-> "NB"])
                /\ sv' = [sv EXCEPT !.phase = "idle"]
             \/ /\ toClient' = Append(toClient, [id |-> sv.id, m |-> "SB"])
                /\ sv' = [sv EXCEPT !.phase = "block"]
       \/ /\ sv.phase = "block"
          /\ toClient' = Append(toClient, [id |-> sv.id, m |-> "B"])
          /\ sv' = [sv EXCEPT !.phase = "end"]
       \/ /\ sv.phase = "end"
          /\ toClient' = Append(toClient, [id |-> sv.id, m |-> "BD"])
          /\ sv' = [sv EXCEPT !.phase = "idle"]
    /\ UNCHANGED <<caller, handedOver, token, queue, up, toServer, done,
                   misrouted, clientErr>>

-----------------------------------------------------------------------------
(* The client's handler [G1]. *)

\* In English: "The handler takes the next answer and applies it to the
\* head of the queue, which must be in the right phase (headForResponse):
\* not started for MsgStartBatch and MsgNoBlocks, started for MsgBlock and
\* MsgBatchDone. Otherwise it refuses the answer and the protocol stops.
\* MsgNoBlocks and MsgBatchDone remove the head and resolve it."
ClientRecv ==
    /\ up /\ toClient /= <<>>
    /\ LET a == Head(toClient)
           wantStarted == a.m \in {"B", "BD"}
       IN IF queue = <<>> \/ Head(queue).started /= wantStarted
             THEN /\ clientErr' = TRUE
                  /\ up' = FALSE                         \* SendError
                  /\ UNCHANGED <<queue, done, misrouted>>
             ELSE LET h == Head(queue) IN
                  /\ misrouted' = (misrouted \/ h.id /= a.id)
                  /\ CASE a.m = "SB" ->
                            /\ queue' = IF StartMarksStarted
                                 THEN [queue EXCEPT ![1].started = TRUE]
                                 ELSE queue
                            /\ UNCHANGED done
                       [] a.m = "B" ->
                            UNCHANGED <<queue, done>>    \* delivered to h
                       [] a.m = "NB" ->
                            /\ queue' = IF NoBlocksRemovesHead
                                            THEN Tail(queue) ELSE queue
                            /\ done' = [done EXCEPT ![h.id] = @ + 1]
                       [] a.m = "BD" ->
                            /\ queue' = Tail(queue)
                            /\ done' = [done EXCEPT ![h.id] = @ + 1]
                  /\ UNCHANGED <<up, clientErr>>
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<caller, handedOver, token, toServer, sv>>

\* In English: "The protocol stops: the peer sent something wrong, a range
\* outlived its deadline, the connection closed, or the application
\* called Stop. This model does not care which."
Shutdown ==
    /\ up
    /\ up' = FALSE
    /\ UNCHANGED <<caller, handedOver, token, queue, toServer, sv, toClient,
                   done, misrouted, clientErr>>

\* In English: "Once stopped, answers still arriving are dropped."
ClientDrop ==
    /\ ~up /\ toClient /= <<>>
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<caller, handedOver, token, queue, up, toServer, sv, done,
                   misrouted, clientErr>>

\* In English: "Once stopped, the watcher takes every queued request out
\* and resolves each with ErrProtocolShuttingDown. With DrainSkipsUnsent,
\* a request whose caller has not yet sent it is left to that caller, still
\* queued. With DrainDefersSending, every request leaves the queue, but one
\* whose caller is still sending is handed over to that caller unresolved."
Drain ==
    /\ DrainOnShutdown
    /\ ~up
    /\ LET sending(r) == caller[r.id] \in {"appended", "sendOk"}
           resolveNow(r) ==
               IF DrainDefersSending THEN ~sending(r)
               ELSE ~DrainSkipsUnsent \/ caller[r.id] = "sent"
           leave(r) == ~DrainDefersSending /\ ~resolveNow(r)
           taken == SelectSeq(queue, resolveNow)
           given == SelectSeq(queue, LAMBDA r :
                                DrainDefersSending /\ sending(r))
           ids == {taken[k].id : k \in 1..Len(taken)}
       IN /\ (taken /= <<>> \/ given /= <<>>)
          /\ queue' = SelectSeq(queue, leave)
          /\ handedOver' = handedOver \cup {given[k].id : k \in 1..Len(given)}
          /\ done' = [i \in Ids |-> IF i \in ids THEN done[i] + 1
                                                ELSE done[i]]
    /\ UNCHANGED <<caller, token, up, toServer, sv, toClient, misrouted,
                   clientErr>>

-----------------------------------------------------------------------------

\* In English: "Every caller has its answer, and nothing is left to do."
Finished ==
    /\ \A i \in Ids : caller[i] \in {"sent", "refused"}
    /\ toServer = <<>> /\ toClient = <<>> /\ sv.phase = "idle"
    /\ queue = <<>> \/ ~DrainOnShutdown

\* In English: "Once finished, nothing changes (an explicit end, so TLC
\* does not report the end as a deadlock)."
Quiet ==
    /\ Finished
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Ids : Admit(i) \/ Send(i) \/ SendFinish(i)
    \/ ServerTake \/ ServerAnswer
    \/ ClientRecv \/ Shutdown \/ ClientDrop \/ Drain
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every answer is applied to the request that asked for it."
AnswersReachTheirRequest == ~misrouted

\* In English: "An honest server's answer is never refused."
HonestAnswersAccepted == ~clientErr

\* In English: "RangeDoneFunc runs at most once per request."
ResolvedAtMostOnce == \A i \in Ids : done[i] <= 1

\* In English: "Once everything is over, every request RequestRange
\* returned an id for was resolved exactly once."
EveryReturnedIdResolved ==
    Finished => \A i \in Ids : caller[i] = "sent" => done[i] = 1

\* In English: "RangeDoneFunc never runs for a request whose RequestRange
\* returned an error: the caller never got that id."
NoCallbackForRefused ==
    \A i \in Ids : caller[i] = "refused" => done[i] = 0

\* Reachability probes, each EXPECTED to be violated.
\* In English: "There is never more than one request queued." Violated = the
\* client does pipeline.
ProbeNeverPipelined == Len(queue) <= 1
\* In English: "No caller is ever refused." Violated = the shutdown path
\* that refuses a caller is reachable.
ProbeNeverRefused == \A i \in Ids : caller[i] /= "refused"
\* In English: "A MsgNoBlocks never resolves a request while another is
\* queued behind it." Violated = MsgNoBlocks happens mid-pipeline.
ProbeNoBlocksMidPipeline ==
    ~(Len(queue) >= 2 /\ toClient /= <<>> /\ Head(toClient).m = "NB")
\* In English: "A drain never hands a request whose send succeeded over to
\* its caller." Violated = with DrainDefersSending, the path where the
\* caller resolves the request itself is reachable.
ProbeNeverHandedOverAndSent ==
    \A i \in Ids : ~(i \in handedOver /\ caller[i] = "sent")
=============================================================================
