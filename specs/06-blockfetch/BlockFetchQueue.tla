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
(*        on branch fix/blockfetch-reference-behaviour RequestRange; the   *)
(*        send outcome and the removal are separate steps (SendFail,       *)
(*        SendRefused), so the token's release can be placed between them. *)
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
    StartMarksStarted,
    \* TRUE: a send can fail while the protocol still runs, because the
    \* caller's context or the range deadline ends while MsgRequestRange
    \* waits to be queued (SendMessageContext with rangeCtx).
    SendCanFail,
    \* TRUE as in gOuroboros 61046085 and the fix at d10daf24 on branch
    \* fix/blockfetch-reference-behaviour: a caller whose send failed hands
    \* the token back only after removing its request from the queue.
    \* FALSE is that branch at 395b9c2e, where a deferred function hands the
    \* token back as soon as the send returns, before the removal.
    TokenCoversRemoval

\* In English: "Each caller's request id."
\* Literally: "Ids is defined as 1 through Callers."
Ids == 1..Callers

VARIABLES
    caller,    \* caller[i]: "new", "appended" (in the queue, send pending),
               \* "sendOk" (the send succeeded, the caller has not yet
               \* cleared its sending mark; DrainDefersSending only),
               \* "sendFailed" (the send failed, the caller has not yet
               \* taken its request out of the queue),
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

\* Literally: "vars is defined as the tuple of all eleven variables."
vars == <<caller, handedOver, token, queue, up, toServer, sv, toClient, done,
          misrouted, clientErr>>

\* In English: "Nobody has called yet; the protocol runs; nothing in flight."
\* Literally: "Init is defined as: caller equals the function that maps every i
\*   in Ids to "new", and handedOver equals the empty set, and token equals 0,
\*   and queue equals the empty sequence, and up equals TRUE, and toServer
\*   equals the empty sequence, and sv equals the record whose field id is 0 and
\*   field phase is "idle", and toClient equals the empty sequence, and done
\*   equals the function that maps every i in Ids to 0, and misrouted equals
\*   FALSE, and clientErr equals FALSE."
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
\* Literally: "Without of q and i is defined as SelectSeq of q and the unnamed
\*   test that, given r, is r's id does not equal i."
Without(q, i) == SelectSeq(q, LAMBDA r : r.id /= i)

\* In English: "Request i is somewhere in the queue."
\* Literally: "Queued of q and i is defined as: there exists a k in 1 through
\*   the length of q such that element k of q's id equals i."
Queued(q, i) == \E k \in 1..Len(q) : q[k].id = i

-----------------------------------------------------------------------------
(* The callers [G1]. *)

\* In English: "Caller i takes the send token (if the code uses one) and
\* appends its request to the queue." The code may take the token even
\* after the protocol stopped: its select has both cases ready.
\* Literally: "Admit of i is defined as: caller of i equals "new", and if
\*   UseSendToken is true, then token equals 0, and token in the next state
\*   equals: if UseSendToken then i, else token; and queue in the next state
\*   equals queue with the record whose field id is i and field started is FALSE
\*   appended, and caller in the next state equals caller except that its i
\*   entry is "appended", and handedOver, up, toServer, sv, toClient, done,
\*   misrouted and clientErr are unchanged."
Admit(i) ==
    /\ caller[i] = "new"
    /\ UseSendToken => token = 0               \* the token is free
    /\ token' = IF UseSendToken THEN i ELSE token
    /\ queue' = Append(queue, [id |-> i, started |-> FALSE])
    /\ caller' = [caller EXCEPT ![i] = "appended"]
    /\ UNCHANGED <<handedOver, up, toServer, sv, toClient, done, misrouted,
                   clientErr>>

\* In English: "Caller i queues its MsgRequestRange and returns the id, and
\* hands the token back. With DrainDefersSending, a successful send only
\* moves the caller to "sendOk"; SendFinish then returns the id."
\* Literally: "Send of i is defined as: caller of i equals "appended", and up is
\*   true, and toServer in the next state equals toServer with i appended, and
\*   caller in the next state equals caller except that its i entry is: if
\*   DrainDefersSending then "sendOk", else "sent"; and token in the next state
\*   equals: if token equals i then 0, else token; and handedOver, queue, up,
\*   sv, toClient, done, misrouted and clientErr are unchanged."
Send(i) ==
    /\ caller[i] = "appended"
    /\ up
    /\ toServer' = Append(toServer, i)
    /\ caller' = [caller EXCEPT ![i] =
                     IF DrainDefersSending THEN "sendOk" ELSE "sent"]
    /\ token' = IF token = i THEN 0 ELSE token
    /\ UNCHANGED <<handedOver, queue, up, sv, toClient, done, misrouted,
                   clientErr>>

\* In English: "Caller i's send fails: always once the protocol has
\* stopped, and with SendCanFail also while it runs. Nothing reaches the
\* wire. Without TokenCoversRemoval the token is handed back here, while
\* the request is still queued."
\* Literally: "SendFail of i is defined as: caller of i equals "appended", and
\*   (up is not true, or SendCanFail is true), and caller in the next state
\*   equals caller except that its i entry is "sendFailed", and token in the
\*   next state equals: if TokenCoversRemoval is not true and token equals i
\*   then 0, else token; and handedOver, queue, up, toServer, sv, toClient,
\*   done, misrouted and clientErr are unchanged."
SendFail(i) ==
    /\ caller[i] = "appended"
    /\ ~up \/ SendCanFail
    /\ caller' = [caller EXCEPT ![i] = "sendFailed"]
    /\ token' = IF ~TokenCoversRemoval /\ token = i THEN 0 ELSE token
    /\ UNCHANGED <<handedOver, queue, up, toServer, sv, toClient, done,
                   misrouted, clientErr>>

\* In English: "Caller i, whose send failed, takes its request out of the
\* queue if it is still there (removeLocked), hands the token back if it
\* still holds it, and returns an error."
\* Literally: "SendRefused of i is defined as: caller of i equals "sendFailed",
\*   and queue in the next state equals Without of queue and i, and caller in
\*   the next state equals caller except that its i entry is "refused", and
\*   token in the next state equals: if token equals i then 0, else token; and
\*   handedOver, up, toServer, sv, toClient, done, misrouted and clientErr are
\*   unchanged."
SendRefused(i) ==
    /\ caller[i] = "sendFailed"
    /\ queue' = Without(queue, i)
    /\ caller' = [caller EXCEPT ![i] = "refused"]
    /\ token' = IF token = i THEN 0 ELSE token
    /\ UNCHANGED <<handedOver, up, toServer, sv, toClient, done, misrouted,
                   clientErr>>

\* In English: "Caller i, whose send succeeded, clears its sending mark and
\* returns the id. If a drain took the request while it was still sending,
\* the caller resolves it now with the drain's error." (DrainDefersSending)
\* Literally: "SendFinish of i is defined as: caller of i equals "sendOk", and
\*   caller in the next state equals caller except that its i entry is "sent",
\*   and done in the next state equals: if SenderResolvesDrained is true and i
\*   is a member of handedOver, then done except that its i entry is the old
\*   entry plus 1, else done; and handedOver, token, queue, up, toServer, sv,
\*   toClient, misrouted and clientErr are unchanged."
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
\* Literally: "ServerTake is defined as: sv's phase equals "idle", and toServer
\*   does not equal the empty sequence, and sv in the next state equals the
\*   record whose field id is the head of toServer and field phase is "busy",
\*   and toServer in the next state equals the tail of toServer, and caller,
\*   handedOver, token, queue, up, toClient, done, misrouted and clientErr are
\*   unchanged."
ServerTake ==
    /\ sv.phase = "idle" /\ toServer /= <<>>
    /\ sv' = [id |-> Head(toServer), phase |-> "busy"]
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<caller, handedOver, token, queue, up, toClient, done,
                   misrouted, clientErr>>

\* In English: "Busy, the server answers MsgNoBlocks or MsgStartBatch;
\* streaming, it sends the block, then MsgBatchDone."
\* Literally: "ServerAnswer is defined as: either (sv's phase equals "busy", and
\*   either (toClient in the next state equals toClient with the record whose
\*   field id is sv's id and field m is "NB" appended, and sv in the next state
\*   equals sv except that its phase field is "idle") or (toClient in the next
\*   state equals toClient with the record whose field id is sv's id and field m
\*   is "SB" appended, and sv in the next state equals sv except that its phase
\*   field is "block")), or (sv's phase equals "block", and toClient in the next
\*   state equals toClient with the record whose field id is sv's id and field m
\*   is "B" appended, and sv in the next state equals sv except that its phase
\*   field is "end"), or (sv's phase equals "end", and toClient in the next
\*   state equals toClient with the record whose field id is sv's id and field m
\*   is "BD" appended, and sv in the next state equals sv except that its phase
\*   field is "idle"); and caller, handedOver, token, queue, up, toServer, done,
\*   misrouted and clientErr are unchanged."
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
\* Literally: "ClientRecv is defined as: up is true, and toClient does not equal
\*   the empty sequence, and, letting a be the head of toClient and wantStarted
\*   be (a's m is a member of the set containing "B" and "BD"): if queue equals
\*   the empty sequence or the head of queue's started does not equal
\*   wantStarted, then clientErr in the next state equals TRUE, and up in the
\*   next state equals FALSE, and queue, done and misrouted are unchanged; else,
\*   letting h be the head of queue: misrouted in the next state equals
\*   (misrouted or h's id does not equal a's id), and, in the case a's m equals
\*   "SB", queue in the next state equals (if StartMarksStarted then queue
\*   except that its element 1's started field is TRUE, else queue) and done is
\*   unchanged; in the case a's m equals "B", queue and done are unchanged; in
\*   the case a's m equals "NB", queue in the next state equals (if
\*   NoBlocksRemovesHead then the tail of queue, else queue) and done in the
\*   next state equals done except that its h's id entry is the old entry plus
\*   1; in the case a's m equals "BD", queue in the next state equals the tail
\*   of queue and done in the next state equals done except that its h's id
\*   entry is the old entry plus 1; and up and clientErr are unchanged; and
\*   toClient in the next state equals the tail of toClient, and caller,
\*   handedOver, token, toServer and sv are unchanged."
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
\* Literally: "Shutdown is defined as: up is true, and up in the next state
\*   equals FALSE, and caller, handedOver, token, queue, toServer, sv, toClient,
\*   done, misrouted and clientErr are unchanged."
Shutdown ==
    /\ up
    /\ up' = FALSE
    /\ UNCHANGED <<caller, handedOver, token, queue, toServer, sv, toClient,
                   done, misrouted, clientErr>>

\* In English: "Once stopped, answers still arriving are dropped."
\* Literally: "ClientDrop is defined as: up is not true, and toClient does not
\*   equal the empty sequence, and toClient in the next state equals the tail of
\*   toClient, and caller, handedOver, token, queue, up, toServer, sv, done,
\*   misrouted and clientErr are unchanged."
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
\* Literally: "Drain is defined as: DrainOnShutdown is true, and up is not true,
\*   and, letting sending of r be (caller of r's id is a member of the set
\*   containing "appended", "sendOk" and "sendFailed"), resolveNow of r be (if
\*   DrainDefersSending then sending of r is not true, else DrainSkipsUnsent is
\*   not true or caller of r's id equals "sent"), leave of r be
\*   (DrainDefersSending is not true and resolveNow of r is not true), taken be
\*   SelectSeq of queue and resolveNow, given be SelectSeq of queue and the
\*   unnamed test that, given r, is DrainDefersSending and sending of r, and ids
\*   be the set of element k of taken's id, for every k that is a member of 1
\*   through the length of taken: (taken does not equal the empty sequence or
\*   given does not equal the empty sequence), and queue in the next state
\*   equals SelectSeq of queue and leave, and handedOver in the next state
\*   equals the union of handedOver and the set of element k of given's id, for
\*   every k that is a member of 1 through the length of given, and done in the
\*   next state equals the function that maps every i in Ids to: if i is a
\*   member of ids then done of i plus 1, else done of i; and caller, token, up,
\*   toServer, sv, toClient, misrouted and clientErr are unchanged."
Drain ==
    /\ DrainOnShutdown
    /\ ~up
    /\ LET sending(r) == caller[r.id] \in {"appended", "sendOk", "sendFailed"}
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
\* Literally: "Finished is defined as: for all i in Ids, caller of i is a member
\*   of the set containing "sent" and "refused"; and toServer equals the empty
\*   sequence, and toClient equals the empty sequence, and sv's phase equals
\*   "idle"; and queue equals the empty sequence or DrainOnShutdown is not
\*   true."
Finished ==
    /\ \A i \in Ids : caller[i] \in {"sent", "refused"}
    /\ toServer = <<>> /\ toClient = <<>> /\ sv.phase = "idle"
    /\ queue = <<>> \/ ~DrainOnShutdown

\* In English: "Once finished, nothing changes (an explicit end, so TLC
\* does not report the end as a deadlock)."
\* Literally: "Quiet is defined as: Finished, and vars is unchanged."
Quiet ==
    /\ Finished
    /\ UNCHANGED vars

\* In English: "A step is any one caller, server, handler or shutdown step, or
\* nothing left to do."
\* Literally: "Next is defined as: there exists an i in Ids such that Admit of i
\*   or Send of i or SendFinish of i or SendFail of i or SendRefused of i; or
\*   ServerTake or ServerAnswer; or ClientRecv or Shutdown or ClientDrop or
\*   Drain; or Quiet."
Next ==
    \/ \E i \in Ids : Admit(i) \/ Send(i) \/ SendFinish(i)
                      \/ SendFail(i) \/ SendRefused(i)
    \/ ServerTake \/ ServerAnswer
    \/ ClientRecv \/ Shutdown \/ ClientDrop \/ Drain
    \/ Quiet

\* In English: "Start in Init, and take only Next steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every answer is applied to the request that asked for it."
\* Literally: "AnswersReachTheirRequest is defined as: misrouted is not true."
AnswersReachTheirRequest == ~misrouted

\* In English: "An honest server's answer is never refused."
\* Literally: "HonestAnswersAccepted is defined as: clientErr is not true."
HonestAnswersAccepted == ~clientErr

\* In English: "RangeDoneFunc runs at most once per request."
\* Literally: "ResolvedAtMostOnce is defined as: for all i in Ids, done of i is
\*   less than or equal to 1."
ResolvedAtMostOnce == \A i \in Ids : done[i] <= 1

\* In English: "Once everything is over, every request RequestRange
\* returned an id for was resolved exactly once."
\* Literally: "EveryReturnedIdResolved is defined as: if Finished, then for all
\*   i in Ids, if caller of i equals "sent", then done of i equals 1."
EveryReturnedIdResolved ==
    Finished => \A i \in Ids : caller[i] = "sent" => done[i] = 1

\* In English: "RangeDoneFunc never runs for a request whose RequestRange
\* returned an error: the caller never got that id."
\* Literally: "NoCallbackForRefused is defined as: for all i in Ids, if caller
\*   of i equals "refused", then done of i equals 0."
NoCallbackForRefused ==
    \A i \in Ids : caller[i] = "refused" => done[i] = 0

\* Reachability probes, each EXPECTED to be violated.
\* In English: "There is never more than one request queued." Violated = the
\* client does pipeline.
\* Literally: "ProbeNeverPipelined is defined as: the length of queue is less
\*   than or equal to 1."
ProbeNeverPipelined == Len(queue) <= 1
\* In English: "No caller is ever refused." Violated = the shutdown path
\* that refuses a caller is reachable.
\* Literally: "ProbeNeverRefused is defined as: for all i in Ids, caller of i
\*   does not equal "refused"."
ProbeNeverRefused == \A i \in Ids : caller[i] /= "refused"
\* In English: "A MsgNoBlocks never resolves a request while another is
\* queued behind it." Violated = MsgNoBlocks happens mid-pipeline.
\* Literally: "ProbeNoBlocksMidPipeline is defined as: (the length of queue is
\*   greater than or equal to 2, and toClient does not equal the empty sequence,
\*   and the head of toClient's m equals "NB") is not true."
ProbeNoBlocksMidPipeline ==
    ~(Len(queue) >= 2 /\ toClient /= <<>> /\ Head(toClient).m = "NB")
\* In English: "No send fails while the protocol runs." Violated = the
\* SendCanFail path is reachable.
\* Literally: "ProbeNeverFailsWhileUp is defined as: for all i in Ids, (caller
\*   of i equals "sendFailed" and up is true) is not true."
ProbeNeverFailsWhileUp == \A i \in Ids : ~(caller[i] = "sendFailed" /\ up)
\* In English: "A drain never hands a request whose send succeeded over to
\* its caller." Violated = with DrainDefersSending, the path where the
\* caller resolves the request itself is reachable.
\* Literally: "ProbeNeverHandedOverAndSent is defined as: for all i in Ids, (i
\*   is a member of handedOver and caller of i equals "sent") is not true."
ProbeNeverHandedOverAndSent ==
    \A i \in Ids : ~(i \in handedOver /\ caller[i] = "sent")
=============================================================================
