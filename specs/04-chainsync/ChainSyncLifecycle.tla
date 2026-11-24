-------------------------- MODULE ChainSyncLifecycle --------------------------
(***************************************************************************)
(* Model 04, slice 2: stopping and restarting the chain-sync client on one *)
(* connection.                                                             *)
(*                                                                         *)
(* The client can stop two ways (protocol/chainsync/client.go):            *)
(*   Stop            gives MsgDone 250 ms to be delivered, then            *)
(*                   unregisters the protocol whether or not it was sent.  *)
(*                   MsgDone is legal only in StIdle, so with a            *)
(*                   MsgRequestNext unanswered it waits for the replies;   *)
(*                   at the chain tip the server may not reply for a whole *)
(*                   block interval.                                       *)
(*   StopAfterDrain  waits for every outstanding MsgRequestNext to be      *)
(*                   answered, then sends MsgDone from StIdle.             *)
(* Then Start registers a fresh protocol instance in StIdle, and Sync      *)
(* sends MsgFindIntersect and resumes pipelined MsgRequestNext.            *)
(*                                                                         *)
(* While the protocol is unregistered, the muxer drops its messages        *)
(* silently (a tombstone, muxer.go). Once Start registers the new          *)
(* instance, they are delivered to it.                                     *)
(*                                                                         *)
(* Question: does either side ever receive a message its state machine     *)
(* does not allow?                                                         *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex:                                  *)
(*   [C1] 838-848, 893-908: chain-sync agencies and transitions; MsgDone   *)
(*        only from StIdle.                                                *)
(*   [S1] 27-36: a message not expected in the current state aborts the    *)
(*        connection.                                                      *)
(*   [P1] 2180-2208: pipelining; replies come back in request order.       *)
(*   gOuroboros, blinklabs-io/gouroboros c1bc50c6:                         *)
(*   [G1] protocol/chainsync/client.go: Stop, stopRunning, finishStop (the *)
(*        250 ms MsgDone timeout), StopAfterDrain, Start (zeroes           *)
(*        outstandingRequestNext: "Requests sent on the stopped instance   *)
(*        are never answered"), Sync, prepareIdleProtocol.                 *)
(*   [G2] muxer/muxer.go: readLoop drops ingress for a tombstoned          *)
(*        (unregistered) protocol role.                                    *)
(*   [G3] protocol/protocol.go: a queued message waits for agency;         *)
(*        SendMessageContextAndWait gives up when its context ends.        *)
(*                                                                         *)
(* The server is the honest one from slice 1, simplified: it takes one     *)
(* message at a time in order, and answers it (MsgAwaitReply is left out;  *)
(* a slow answer is just an answer that comes later). After MsgDone it     *)
(* restarts in StIdle (spec 5.7; gOuroboros StopForRestart).               *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Limit,         \* PipelineLimit
    MaxRequests,   \* MsgRequestNext sent in total (keeps it finite)
    MaxStarts,     \* how many times the client may be restarted
    UseStop,       \* TRUE: the application may call Stop
    UseDrain,      \* TRUE: the application may call StopAfterDrain
    \* FALSE in gOuroboros. TRUE: Start refuses to restart after a Stop
    \* that left requests unanswered, so the connection must be closed.
    StartRefusesAbandoned

VARIABLES
    \* the client
    cs,         \* "running", "syncing", "stopping", "draining", "stopped"
    expect,     \* replies this instance awaits, oldest first: "RN" or "FI"
    reg,        \* TRUE while the protocol is registered with the muxer
    abandoned,  \* TRUE once a Stop unregistered with requests unanswered
    starts,     \* times Start has run (model bound)
    sent,       \* MsgRequestNext sent so far (model bound)
    \* the wire and the server
    toServer,   \* client messages in flight: "RN", "FI", "Done"
    toClient,   \* server replies in flight: "RN" (a roll) or "FI"
    sv,         \* the server: "idle", or the message it is answering
    \* outcome
    violation   \* "none", or the reply a side received when its state does
                \* not allow it: "RN" (a roll) or "FI" (MsgIntersectFound)

vars == <<cs, expect, reg, abandoned, starts, sent, toServer, toClient, sv,
          violation>>

\* In English: "The client is running but not syncing; nothing is in flight."
Init ==
    /\ cs = "running" /\ expect = <<>> /\ reg = TRUE /\ abandoned = FALSE
    /\ starts = 0 /\ sent = 0
    /\ toServer = <<>> /\ toClient = <<>> /\ sv = "idle"
    /\ violation = "none"

-----------------------------------------------------------------------------
(* The client [G1]. *)

\* Sync. In English: "Running, with nothing outstanding (prepareIdleProtocol):
\* send MsgFindIntersect and await its answer."
Sync ==
    /\ cs = "running" /\ expect = <<>>
    /\ toServer' = Append(toServer, "FI")
    /\ expect' = <<"FI">>
    /\ cs' = "syncing"
    /\ UNCHANGED <<reg, abandoned, starts, sent, toClient, sv, violation>>

\* The sync loop. In English: "Once the intersection is answered, keep up to
\* Limit MsgRequestNext outstanding."
SendRequestNext ==
    /\ cs = "syncing"
    /\ \A i \in 1..Len(expect) : expect[i] = "RN"
    /\ Len(expect) < Limit /\ sent < MaxRequests
    /\ toServer' = Append(toServer, "RN")
    /\ expect' = Append(expect, "RN")
    /\ sent' = sent + 1
    /\ UNCHANGED <<cs, reg, abandoned, starts, toClient, sv, violation>>

\* In English: "A reply reaches the client. If the protocol is unregistered,
\* the muxer drops it [G2]. Otherwise it must be the answer the instance is
\* waiting for; anything else is a protocol violation [S1]."
ClientRecv ==
    /\ toClient /= <<>>
    /\ LET m == Head(toClient) IN
       IF ~reg
          THEN UNCHANGED <<expect, violation>>
       ELSE IF expect /= <<>> /\ Head(expect) = m
          THEN /\ expect' = Tail(expect)
               /\ UNCHANGED violation
       ELSE /\ violation' = m
            /\ UNCHANGED expect
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<cs, reg, abandoned, starts, sent, toServer, sv>>

\* Stop. In English: "The sync stops sending; MsgDone is queued."
StopBegin ==
    /\ UseStop /\ cs \in {"running", "syncing"}
    /\ cs' = "stopping"
    /\ UNCHANGED <<expect, reg, abandoned, starts, sent, toServer, toClient,
                   sv, violation>>

\* In English: "MsgDone goes out once every request is answered [G3] - or
\* the 250 ms timer fires first, and the protocol is unregistered without
\* it, leaving the server owing replies."
StopFinish ==
    /\ cs = "stopping"
    /\ \/ /\ expect = <<>>
          /\ toServer' = Append(toServer, "Done")
          /\ UNCHANGED abandoned
       \/ /\ expect /= <<>>
          /\ abandoned' = TRUE
          /\ UNCHANGED toServer
    /\ cs' = "stopped" /\ reg' = FALSE /\ expect' = <<>>
    /\ UNCHANGED <<starts, sent, toClient, sv, violation>>

\* StopAfterDrain. In English: "Stop sending, wait for every reply, then
\* send MsgDone from StIdle."
DrainBegin ==
    /\ UseDrain /\ cs \in {"running", "syncing"}
    /\ cs' = "draining"
    /\ UNCHANGED <<expect, reg, abandoned, starts, sent, toServer, toClient,
                   sv, violation>>

DrainFinish ==
    /\ cs = "draining" /\ expect = <<>>
    /\ toServer' = Append(toServer, "Done")
    /\ cs' = "stopped" /\ reg' = FALSE
    /\ UNCHANGED <<expect, abandoned, starts, sent, toClient, sv, violation>>

\* Start. In English: "Register a fresh instance in StIdle, expecting
\* nothing (outstandingRequestNext = 0). With StartRefusesAbandoned, a Stop
\* that left requests unanswered makes Start refuse instead."
Start ==
    /\ cs = "stopped" /\ starts < MaxStarts
    /\ ~(StartRefusesAbandoned /\ abandoned)
    /\ cs' = "running" /\ reg' = TRUE /\ expect' = <<>>
    /\ starts' = starts + 1
    /\ UNCHANGED <<abandoned, sent, toServer, toClient, sv, violation>>

-----------------------------------------------------------------------------
(* The server. *)

\* In English: "Idle, the server takes the next message. MsgDone ends the
\* run and it restarts idle; anything else it will answer."
ServerTake ==
    /\ sv = "idle" /\ toServer /= <<>>
    /\ sv' = IF Head(toServer) = "Done" THEN "idle" ELSE Head(toServer)
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<cs, expect, reg, abandoned, starts, sent, toClient,
                   violation>>

ServerReply ==
    /\ sv \in {"RN", "FI"}
    /\ toClient' = Append(toClient, sv)
    /\ sv' = "idle"
    /\ UNCHANGED <<cs, expect, reg, abandoned, starts, sent, toServer,
                   violation>>

-----------------------------------------------------------------------------

\* In English: "Nothing left to do: no messages in flight, the server idle."
Quiet ==
    /\ toServer = <<>> /\ toClient = <<>> /\ sv = "idle"
    /\ UNCHANGED vars

Next ==
    \/ Sync \/ SendRequestNext \/ ClientRecv
    \/ StopBegin \/ StopFinish \/ DrainBegin \/ DrainFinish \/ Start
    \/ ServerTake \/ ServerReply
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "No side ever receives a message it does not expect."
NoViolation == violation = "none"

\* Probes, each EXPECTED to be violated.
\* In English: "Stop never abandons requests." Violated = it does.
ProbeNeverAbandons == ~abandoned
\* In English: "The client never restarts." Violated = it does.
ProbeNeverRestarts == starts = 0
\* In English: "A late roll never breaks a restarted client." Violated = the
\* violation also comes from the common case: Stop at the chain tip with a
\* MsgRequestNext unanswered, not only Stop during MsgFindIntersect.
ProbeNoRollViolation == violation /= "RN"
\* In English: "A restarted client never resumes syncing." Violated = it does.
ProbeNeverResyncs == ~(starts > 0 /\ cs = "syncing" /\ expect = <<"RN">>)
=============================================================================
