------------------------- MODULE BlockFetchClientDone -------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 6: a range requested after Stop has queued    *)
(* MsgClientDone.                                                          *)
(*                                                                         *)
(* gOuroboros files: protocol/blockfetch/client.go (RequestRange,          *)
(* sendRequestRange, stop, failOutstandingOnProtocolDone) and              *)
(* protocol/protocol.go (enqueueMessage, sendLoop), at                     *)
(* blinklabs-io/gouroboros 7cd17437.                                       *)
(*                                                                         *)
(* What the code does [G1][G2]:                                            *)
(*   RequestRange takes no lifecycle lock. It appends the request to the   *)
(*   client's queue and puts MsgRequestRange on the protocol's send queue; *)
(*   enqueueMessage refuses only a stopped protocol, and does not look at  *)
(*   the protocol state. Stop, under lifecycleMutex, puts MsgClientDone on *)
(*   the same send queue and waits up to 250 ms for it to be written. The  *)
(*   send loop takes the queue in order. A MsgRequestRange may go out in   *)
(*   StIdle, or pipelined in StBusy/StStreaming; MsgClientDone only in     *)
(*   StIdle, so behind an outstanding range it is held, and so is          *)
(*   everything queued after it. In StDone no role has agency and the send *)
(*   loop takes nothing more. Once the protocol stops, its shutdown        *)
(*   watcher resolves every request still queued with                      *)
(*   ErrProtocolShuttingDown, through RangeDoneFunc.                       *)
(*                                                                         *)
(* Question: can a MsgRequestRange reach the wire after MsgClientDone, and *)
(* is every caller released?                                               *)
(*                                                                         *)
(* Sources (IntersectMBO/ouroboros-network 5f356486ab3e; README links):    *)
(*   [B1] docs/network-spec/miniprotocols.tex 1190-1204: MsgClientDone     *)
(*        only from StIdle, to StDone; StDone has no agency.               *)
(*   [S1] miniprotocols.tex 27-36: an unexpected message aborts the        *)
(*        connection.                                                      *)
(*   [R3] .../Protocol/BlockFetch/Client.hs 130-132, 148-150:              *)
(*        SendMsgDonePipelined only with nothing outstanding.              *)
(*   gOuroboros 7cd17437:                                                  *)
(*   [G1] protocol/blockfetch/client.go: RequestRange 910-956,             *)
(*        sendRequestRange 1126-1237, stop 604-702,                        *)
(*        failOutstandingOnProtocolDone 1535-1538.                         *)
(*   [G2] protocol/protocol.go: enqueueMessage 1038-1109, sendLoop         *)
(*        1405-1716 (a held message blocks the queue behind it; with no    *)
(*        agency the loop waits on sendReadyChan).                         *)
(*                                                                         *)
(* One answer stands for MsgNoBlocks, or a whole batch. StBusy stands for  *)
(* StBusy and StStreaming.                                                 *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table.                                                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Reqs,              \* the requests the caller may make, e.g. {1, 2, 3}
    \* Mutations, each FALSE in the code as it is:
    EngineSendsInDone, \* the send loop writes a queued message in StDone
    NoShutdownDrain    \* no shutdown watcher resolves what is left

VARIABLES
    es,        \* the client protocol state: "Idle", "Busy", "Done"
    sq,        \* the protocol's send queue: "RR" and "Done", in order
    owed,      \* MsgRequestRange written and not yet answered
    toClient,  \* answers in flight to the client
    cq,        \* the client's request queue (c.queue), oldest first
    req,       \* req[r]: "none", "queued" (caller has its id), "refused",
               \* "resolved" (RangeDoneFunc has run)
    stop,      \* the Stop caller: "running", "waitDone", "stopped"
    up,        \* TRUE until the protocol stops
    sv,        \* the server: "idle", "busy" (owes one answer), "done"
    toServer,  \* client messages in flight to the server
    doneOut,   \* TRUE once MsgClientDone was written
    badSend,   \* TRUE once a MsgRequestRange was written after it
    srvBad     \* TRUE once the server got a message its state forbids

vars == <<es, sq, owed, toClient, cq, req, stop, up, sv, toServer, doneOut,
          badSend, srvBad>>

\* In English: "Running in StIdle with nothing queued or requested."
\* Literally: "Init is defined as: es equals "Idle", and sq, toServer and cq
\*   are empty sequences, and owed and toClient equal 0, and every request is
\*   "none", and stop equals "running", and up is TRUE, and sv equals "idle",
\*   and doneOut, badSend and srvBad are FALSE."
Init ==
    /\ es = "Idle" /\ sq = <<>> /\ owed = 0 /\ toClient = 0
    /\ cq = <<>> /\ req = [r \in Reqs |-> "none"]
    /\ stop = "running" /\ up = TRUE
    /\ sv = "idle" /\ toServer = <<>>
    /\ doneOut = FALSE /\ badSend = FALSE /\ srvBad = FALSE

-----------------------------------------------------------------------------
(* The client [G1].                                                        *)

\* In English: "A caller requests range r. On a stopped protocol it is
\* refused. Otherwise, holding the send token, it is appended to the client
\* queue and its MsgRequestRange to the send queue, and the caller gets its
\* id - whether or not Stop has already queued MsgClientDone."
\* Literally: "Request(r) is defined as: req[r] equals "none", and if up
\*   then req' maps r to "queued", and cq' is cq with r appended, and sq' is
\*   sq with "RR" appended; else req' maps r to "refused" and cq and sq are
\*   unchanged; and the other variables are unchanged."
Request(r) ==
    /\ req[r] = "none"
    /\ IF up
          THEN /\ req' = [req EXCEPT ![r] = "queued"]
               /\ cq' = Append(cq, r)
               /\ sq' = Append(sq, "RR")
          ELSE /\ req' = [req EXCEPT ![r] = "refused"]
               /\ UNCHANGED <<cq, sq>>
    /\ UNCHANGED <<es, owed, toClient, stop, up, sv, toServer, doneOut,
                   badSend, srvBad>>

\* In English: "Stop of the running client queues MsgClientDone."
\* Literally: "StopQueue is defined as: stop equals "running", and up is
\*   true, and sq' is sq with "Done" appended, and stop' equals "waitDone",
\*   and the other variables are unchanged."
StopQueue ==
    /\ stop = "running" /\ up
    /\ sq' = Append(sq, "Done")
    /\ stop' = "waitDone"
    /\ UNCHANGED <<es, owed, toClient, cq, req, up, sv, toServer, doneOut,
                   badSend, srvBad>>

\* In English: "Stop stops the protocol: MsgClientDone was written, or the
\* 250 ms ran out first (the connection is then given up on, which in this
\* model is the protocol stopping with answers left unread)."
\* Literally: "StopFinish is defined as: stop equals "waitDone", and stop'
\*   equals "stopped", and up' is FALSE, and the other variables are
\*   unchanged."
StopFinish ==
    /\ stop = "waitDone"
    /\ stop' = "stopped" /\ up' = FALSE
    /\ UNCHANGED <<es, sq, owed, toClient, cq, req, sv, toServer, doneOut,
                   badSend, srvBad>>

\* In English: "An answer reaches the running client and resolves the head
\* of its queue; the last answer owed returns it to StIdle."
\* Literally: "ClientRecv is defined as: up is true, and toClient is
\*   greater than 0, and cq is not empty, and toClient' is toClient minus 1,
\*   and owed' is owed minus 1, and es' is "Idle" if owed' is 0 and "Busy"
\*   otherwise, and req' maps the head of cq to "resolved", and cq' is its
\*   tail, and the other variables are unchanged."
ClientRecv ==
    /\ up /\ toClient > 0 /\ cq /= <<>>
    /\ toClient' = toClient - 1
    /\ owed' = owed - 1
    /\ es' = IF owed - 1 = 0 THEN "Idle" ELSE "Busy"
    /\ req' = [req EXCEPT ![Head(cq)] = "resolved"]
    /\ cq' = Tail(cq)
    /\ UNCHANGED <<sq, stop, up, sv, toServer, doneOut, badSend, srvBad>>

\* In English: "The stopped protocol's shutdown watcher resolves every
\* request still in the client queue."
\* Literally: "ShutdownDrain is defined as: NoShutdownDrain is false, and up
\*   is false, and cq is not empty, and req' maps every request in cq to
\*   "resolved", and cq' is empty, and the other variables are unchanged."
ShutdownDrain ==
    /\ ~NoShutdownDrain /\ ~up /\ cq /= <<>>
    /\ req' = [r \in Reqs |->
                  IF \E i \in 1..Len(cq) : cq[i] = r THEN "resolved"
                  ELSE req[r]]
    /\ cq' = <<>>
    /\ UNCHANGED <<es, sq, owed, toClient, stop, up, sv, toServer, doneOut,
                   badSend, srvBad>>

-----------------------------------------------------------------------------
(* The engine's send loop [G2].                                            *)

\* In English: "The send loop writes a queued MsgRequestRange: in StIdle,
\* or pipelined while answers are owed. In StDone it takes nothing (unless
\* the EngineSendsInDone mutation)."
\* Literally: "SendRR is defined as: up is true, and sq is not empty, and
\*   the head of sq is "RR", and (es is "Idle" or "Busy", or
\*   EngineSendsInDone is true), and sq' is the tail of sq, and toServer' is
\*   toServer with "RR" appended, and owed' is owed plus 1, and es' is "Busy"
\*   unless es is "Done", and badSend' is badSend or doneOut, and the other
\*   variables are unchanged."
SendRR ==
    /\ up /\ sq /= <<>> /\ Head(sq) = "RR"
    /\ es \in {"Idle", "Busy"} \/ EngineSendsInDone
    /\ sq' = Tail(sq)
    /\ toServer' = Append(toServer, "RR")
    /\ owed' = owed + 1
    /\ es' = IF es = "Done" THEN "Done" ELSE "Busy"
    /\ badSend' = (badSend \/ doneOut)
    /\ UNCHANGED <<toClient, cq, req, stop, up, sv, doneOut, srvBad>>

\* In English: "The send loop writes MsgClientDone, which it holds until
\* StIdle; the protocol is then in StDone."
\* Literally: "SendDone is defined as: up is true, and sq is not empty, and
\*   the head of sq is "Done", and es equals "Idle", and sq' is the tail of
\*   sq, and toServer' is toServer with "Done" appended, and es' equals
\*   "Done", and doneOut' is TRUE, and the other variables are unchanged."
SendDone ==
    /\ up /\ sq /= <<>> /\ Head(sq) = "Done" /\ es = "Idle"
    /\ sq' = Tail(sq)
    /\ toServer' = Append(toServer, "Done")
    /\ es' = "Done" /\ doneOut' = TRUE
    /\ UNCHANGED <<owed, toClient, cq, req, stop, up, sv, badSend, srvBad>>

-----------------------------------------------------------------------------
(* An honest server [B1]: one message at a time, in order.                 *)

\* In English: "The idle server takes the next client message: a range
\* makes it busy, MsgClientDone ends the run. In StDone, anything is a
\* violation [S1]."
\* Literally: "ServerTake is defined as: toServer is not empty, and sv is
\*   "idle" or "done", and if sv is "done" then srvBad' is TRUE and sv is
\*   unchanged, else sv' is "busy" for "RR" and "done" for "Done" and srvBad
\*   is unchanged; and toServer' is the tail of toServer, and the other
\*   variables are unchanged."
ServerTake ==
    /\ toServer /= <<>> /\ sv \in {"idle", "done"}
    /\ IF sv = "done"
          THEN /\ srvBad' = TRUE /\ UNCHANGED sv
          ELSE /\ sv' = IF Head(toServer) = "RR" THEN "busy" ELSE "done"
               /\ UNCHANGED srvBad
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<es, sq, owed, toClient, cq, req, stop, up, doneOut,
                   badSend>>

\* In English: "The busy server answers."
\* Literally: "ServerAnswer is defined as: sv equals "busy", and toClient'
\*   is toClient plus 1, and sv' equals "idle", and the other variables are
\*   unchanged."
ServerAnswer ==
    /\ sv = "busy"
    /\ toClient' = toClient + 1 /\ sv' = "idle"
    /\ UNCHANGED <<es, sq, owed, cq, req, stop, up, toServer, doneOut,
                   badSend, srvBad>>

-----------------------------------------------------------------------------

\* In English: "Every caller has its outcome: each request was never made,
\* refused, or resolved."
\* Literally: "AllReleased is defined as: for every r in Reqs, req[r] is
\*   not "queued"."
AllReleased == \A r \in Reqs : req[r] /= "queued"

\* In English: "Nothing is left to do: the client stopped, every caller has
\* its outcome, and the server is not mid-answer."
\* Literally: "Finished is defined as: stop equals "stopped", and
\*   AllReleased, and sv is not "busy", and toServer is empty or sv is
\*   "done"; and the variables are unchanged."
Finished ==
    /\ stop = "stopped" /\ AllReleased
    /\ sv /= "busy"
    /\ toServer = <<>> \/ sv = "done"
    /\ UNCHANGED vars

\* In English: "A step is one step of the client, the engine or the server,
\* or nothing left to do."
\* Literally: "Next is defined as: some request r takes Request(r), or
\*   StopQueue, StopFinish, ClientRecv, ShutdownDrain, SendRR, SendDone,
\*   ServerTake or ServerAnswer is a step, or Finished."
Next ==
    \/ \E r \in Reqs : Request(r)
    \/ StopQueue \/ StopFinish \/ ClientRecv \/ ShutdownDrain
    \/ SendRR \/ SendDone
    \/ ServerTake \/ ServerAnswer
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Every variable holds a value of the right kind."
\* Literally: "TypeOK is defined as: each variable is in its set."
TypeOK ==
    /\ es \in {"Idle", "Busy", "Done"}
    /\ owed \in Nat /\ toClient \in Nat
    /\ req \in [Reqs -> {"none", "queued", "refused", "resolved"}]
    /\ stop \in {"running", "waitDone", "stopped"}
    /\ up \in BOOLEAN
    /\ sv \in {"idle", "busy", "done"}

\* In English: "No MsgRequestRange is written after MsgClientDone."
\* Literally: "NoRequestAfterDone is defined as: badSend is false."
NoRequestAfterDone == ~badSend

\* In English: "The server never receives a message its state forbids."
\* Literally: "ServerNeverViolated is defined as: srvBad is false."
ServerNeverViolated == ~srvBad

\* In English: "Every request still in the client queue is one whose caller
\* is waiting for it."
\* Literally: "QueueHoldsQueued is defined as: for every i in 1 through
\*   the length of cq, req[cq[i]] equals "queued"."
QueueHoldsQueued == \A i \in 1..Len(cq) : req[cq[i]] = "queued"

\* Probes, each EXPECTED to be violated (reachability).
\* In English: "No MsgRequestRange is ever queued behind MsgClientDone."
\* Violated = the case this slice is about is reached.
\* Literally: "ProbeNoRequestBehindDone is defined as: there are no i less
\*   than j in 1 through the length of sq with sq[i] equal to "Done" and
\*   sq[j] equal to "RR"."
ProbeNoRequestBehindDone ==
    ~\E i, j \in 1..Len(sq) : i < j /\ sq[i] = "Done" /\ sq[j] = "RR"
\* In English: "Never is every caller released while a MsgRequestRange is
\* still unsent behind a written MsgClientDone." Violated = the shutdown
\* drain releases such a caller.
\* Literally: "ProbeNoUnsentResolved is defined as: not (up is false, and
\*   doneOut, and "RR" is among the elements of sq, and AllReleased)."
ProbeNoUnsentResolved ==
    ~(~up /\ doneOut /\ "RR" \in {sq[i] : i \in 1..Len(sq)} /\ AllReleased)
=============================================================================
