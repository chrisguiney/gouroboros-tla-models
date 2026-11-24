-------------------------- MODULE ChainSyncLifecycle --------------------------
(***************************************************************************)
(* Model `chainsync`, slice 2: stopping and restarting the chain-sync client on one *)
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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Limit,         \* PipelineLimit
    MaxRequests,   \* MsgRequestNext sent in total (keeps it finite)
    MaxStarts,     \* how many times the client may be restarted
    UseStop,       \* TRUE: the application may call Stop
    UseDrain,      \* TRUE: the application may call StopAfterDrain
    \* TRUE with the fix in review (stoppedWithoutDone): Start refuses to
    \* restart after a Stop that left requests unanswered.
    StartRefusesAbandoned,
    \* TRUE with the fix in review (ErrStoppedWithoutDone): a Stop that
    \* could not deliver MsgDone reports an error, and the connection is
    \* closed, as the reference does when hot protocols do not terminate.
    CloseOnAbandon

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
    closing,    \* TRUE once an error has asked the connection to close
    closed,     \* TRUE once the connection is closed
    \* outcome
    violation   \* "none", or the reply a side received when its state does
                \* not allow it: "RN" (a roll) or "FI" (MsgIntersectFound)

\* Literally: "vars is defined as the tuple of all twelve variables."
vars == <<cs, expect, reg, abandoned, starts, sent, toServer, toClient, sv,
          closing, closed, violation>>

\* In English: "The client is running but not syncing; nothing is in flight."
\* Literally: "Init is defined as: cs equals "running", and expect equals the
\*   empty sequence, and reg equals TRUE, and abandoned equals FALSE, and
\*   starts equals 0, and sent equals 0, and toServer equals the empty
\*   sequence, and toClient equals the empty sequence, and sv equals "idle",
\*   and closing equals FALSE, and closed equals FALSE, and violation equals
\*   "none"."
Init ==
    /\ cs = "running" /\ expect = <<>> /\ reg = TRUE /\ abandoned = FALSE
    /\ starts = 0 /\ sent = 0
    /\ toServer = <<>> /\ toClient = <<>> /\ sv = "idle"
    /\ closing = FALSE /\ closed = FALSE
    /\ violation = "none"

-----------------------------------------------------------------------------
(* The client [G1].                                                        *)
(*                                                                         *)
(* Every action below starts with the same two lines:                      *)
(*   /\ ~closed                    "the connection is still open"          *)
(*   /\ UNCHANGED <<closing, closed>>  "this step does not close it"       *)
(* Only StopFinish (which may ask for a close) and ConnClose differ.       *)

\* Sync. In English: "Running, with nothing outstanding (prepareIdleProtocol):
\* send MsgFindIntersect and await its answer."
\* Literally: "Sync is defined as: closed is not true, and closing and closed
\*   are unchanged, and cs equals "running", and expect equals the empty
\*   sequence, and toServer in the next state equals toServer with "FI"
\*   appended, and expect in the next state equals the sequence containing
\*   "FI", and cs in the next state equals "syncing", and reg, abandoned,
\*   starts, sent, toClient, sv and violation are unchanged."
Sync ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ cs = "running" /\ expect = <<>>
    /\ toServer' = Append(toServer, "FI")
    /\ expect' = <<"FI">>
    /\ cs' = "syncing"
    /\ UNCHANGED <<reg, abandoned, starts, sent, toClient, sv, violation>>

\* The sync loop. In English: "Once the intersection is answered, keep up to
\* Limit MsgRequestNext outstanding."
\* Literally: "SendRequestNext is defined as: closed is not true, and closing
\*   and closed are unchanged, and cs equals "syncing", and for all i in 1
\*   through the length of expect, element i of expect equals "RN"; and the
\*   length of expect is less than Limit, and sent is less than MaxRequests,
\*   and toServer in the next state equals toServer with "RN" appended, and
\*   expect in the next state equals expect with "RN" appended, and sent in the
\*   next state equals sent plus 1, and cs, reg, abandoned, starts, toClient,
\*   sv and violation are unchanged."
SendRequestNext ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
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
\* Literally: "ClientRecv is defined as: closed is not true, and closing and
\*   closed are unchanged, and toClient does not equal the empty sequence, and,
\*   letting m be the head of toClient: if reg is not true, then expect and
\*   violation are unchanged; else if expect does not equal the empty sequence
\*   and the head of expect equals m, then (expect in the next state equals the
\*   tail of expect, and violation is unchanged); else (violation in the next
\*   state equals m, and expect is unchanged); and toClient in the next state
\*   equals the tail of toClient, and cs, reg, abandoned, starts, sent,
\*   toServer and sv are unchanged."
ClientRecv ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
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
\* Literally: "StopBegin is defined as: closed is not true, and closing and
\*   closed are unchanged, and UseStop is true, and cs is a member of the set
\*   containing "running" and "syncing", and cs in the next state equals
\*   "stopping", and expect, reg, abandoned, starts, sent, toServer, toClient,
\*   sv and violation are unchanged."
StopBegin ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ UseStop /\ cs \in {"running", "syncing"}
    /\ cs' = "stopping"
    /\ UNCHANGED <<expect, reg, abandoned, starts, sent, toServer, toClient,
                   sv, violation>>

\* In English: "MsgDone goes out once every request is answered [G3] - or
\* the 250 ms timer fires first, and the protocol is unregistered without
\* it, leaving the server owing replies."
\* Literally: "StopFinish is defined as: closed is not true, and cs equals
\*   "stopping", and either (expect equals the empty sequence, and toServer in
\*   the next state equals toServer with "Done" appended, and abandoned is
\*   unchanged), or (expect does not equal the empty sequence, and abandoned in
\*   the next state equals TRUE, and toServer is unchanged); and cs in the next
\*   state equals "stopped", and reg in the next state equals FALSE, and expect
\*   in the next state equals the empty sequence, and closing in the next state
\*   equals (closing is true, or CloseOnAbandon is true and expect does not
\*   equal the empty sequence), and starts, sent, toClient, sv, closed and
\*   violation are unchanged."
StopFinish ==
    /\ ~closed
    /\ cs = "stopping"
    /\ \/ /\ expect = <<>>
          /\ toServer' = Append(toServer, "Done")
          /\ UNCHANGED abandoned
       \/ /\ expect /= <<>>
          /\ abandoned' = TRUE
          /\ UNCHANGED toServer
    /\ cs' = "stopped" /\ reg' = FALSE /\ expect' = <<>>
    \* "With the fix, stopping with replies owed asks the connection to close."
    /\ closing' = (closing \/ (CloseOnAbandon /\ expect /= <<>>))
    /\ UNCHANGED <<starts, sent, toClient, sv, closed, violation>>

\* StopAfterDrain. In English: "Stop sending, wait for every reply, then
\* send MsgDone from StIdle."
\* Literally: "DrainBegin is defined as: closed is not true, and closing and
\*   closed are unchanged, and UseDrain is true, and cs is a member of the set
\*   containing "running" and "syncing", and cs in the next state equals
\*   "draining", and expect, reg, abandoned, starts, sent, toServer, toClient,
\*   sv and violation are unchanged."
DrainBegin ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ UseDrain /\ cs \in {"running", "syncing"}
    /\ cs' = "draining"
    /\ UNCHANGED <<expect, reg, abandoned, starts, sent, toServer, toClient,
                   sv, violation>>

\* In English: "Once every reply has arrived, send MsgDone, and the protocol is
\* stopped and unregistered."
\* Literally: "DrainFinish is defined as: closed is not true, and closing and
\*   closed are unchanged, and cs equals "draining", and expect equals the
\*   empty sequence, and toServer in the next state equals toServer with "Done"
\*   appended, and cs in the next state equals "stopped", and reg in the next
\*   state equals FALSE, and expect, abandoned, starts, sent, toClient, sv and
\*   violation are unchanged."
DrainFinish ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ cs = "draining" /\ expect = <<>>
    /\ toServer' = Append(toServer, "Done")
    /\ cs' = "stopped" /\ reg' = FALSE
    /\ UNCHANGED <<expect, abandoned, starts, sent, toClient, sv, violation>>

\* Start. In English: "Register a fresh instance in StIdle, expecting
\* nothing (outstandingRequestNext = 0). With StartRefusesAbandoned, a Stop
\* that left requests unanswered makes Start refuse instead."
\* Literally: "Start is defined as: closed is not true, and closing and closed
\*   are unchanged, and cs equals "stopped", and starts is less than MaxStarts,
\*   and it is not the case that StartRefusesAbandoned is true and abandoned is
\*   true, and cs in the next state equals "running", and reg in the next state
\*   equals TRUE, and expect in the next state equals the empty sequence, and
\*   starts in the next state equals starts plus 1, and abandoned, sent,
\*   toServer, toClient, sv and violation are unchanged."
Start ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ cs = "stopped" /\ starts < MaxStarts
    /\ ~(StartRefusesAbandoned /\ abandoned)
    /\ cs' = "running" /\ reg' = TRUE /\ expect' = <<>>
    /\ starts' = starts + 1
    /\ UNCHANGED <<abandoned, sent, toServer, toClient, sv, violation>>

-----------------------------------------------------------------------------
(* The server. *)

\* In English: "Idle, the server takes the next message. MsgDone ends the
\* run and it restarts idle; anything else it will answer."
\* Literally: "ServerTake is defined as: closed is not true, and closing and
\*   closed are unchanged, and sv equals "idle", and toServer does not equal
\*   the empty sequence, and sv in the next state equals (if the head of
\*   toServer equals "Done" then "idle", else the head of toServer), and
\*   toServer in the next state equals the tail of toServer, and cs, expect,
\*   reg, abandoned, starts, sent, toClient and violation are unchanged."
ServerTake ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ sv = "idle" /\ toServer /= <<>>
    /\ sv' = IF Head(toServer) = "Done" THEN "idle" ELSE Head(toServer)
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<cs, expect, reg, abandoned, starts, sent, toClient,
                   violation>>

\* In English: "The server answers the message it took, and is idle again."
\* Literally: "ServerReply is defined as: closed is not true, and closing and
\*   closed are unchanged, and sv is a member of the set containing "RN" and
\*   "FI", and toClient in the next state equals toClient with sv appended, and
\*   sv in the next state equals "idle", and cs, expect, reg, abandoned,
\*   starts, sent, toServer and violation are unchanged."
ServerReply ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ sv \in {"RN", "FI"}
    /\ toClient' = Append(toClient, sv)
    /\ sv' = "idle"
    /\ UNCHANGED <<cs, expect, reg, abandoned, starts, sent, toServer,
                   violation>>

\* In English: "The connection acts on the error and closes: the muxer
\* stops, and nothing more is sent or delivered. Until then, Start and the
\* server's late replies can still happen (Connection handles the error on
\* its own goroutine)."
\* Literally: "ConnClose is defined as: closing is true, and closed is not
\*   true, and closed in the next state equals TRUE, and the other eleven
\*   variables are unchanged."
ConnClose ==
    /\ closing /\ ~closed
    /\ closed' = TRUE
    /\ UNCHANGED <<cs, expect, reg, abandoned, starts, sent, toServer, toClient,
                   sv, closing, violation>>

-----------------------------------------------------------------------------

\* In English: "Nothing left to do: no messages in flight and the server
\* idle - or the connection is closed, and nothing more can happen."
\* Literally: "Quiet is defined as: (toServer equals the empty sequence and
\*   toClient equals the empty sequence and sv equals "idle", or closed is
\*   true), and vars is unchanged."
Quiet ==
    /\ \/ toServer = <<>> /\ toClient = <<>> /\ sv = "idle"
       \/ closed
    /\ UNCHANGED vars

\* In English: "A step is any one client, application, server or connection
\* step, or staying quiet."
\* Literally: "Next is defined as: Sync, or SendRequestNext, or ClientRecv, or
\*   StopBegin, or StopFinish, or DrainBegin, or DrainFinish, or Start, or
\*   ServerTake, or ServerReply, or ConnClose, or Quiet."
Next ==
    \/ Sync \/ SendRequestNext \/ ClientRecv
    \/ StopBegin \/ StopFinish \/ DrainBegin \/ DrainFinish \/ Start
    \/ ServerTake \/ ServerReply \/ ConnClose
    \/ Quiet

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "No side ever receives a message it does not expect."
\* Literally: "NoViolation is defined as: violation equals "none"."
NoViolation == violation = "none"

\* In English: "No side receives a message it does not expect on a
\* connection that is staying open." A violation on a connection already
\* closing for ErrStoppedWithoutDone changes nothing: it is closed either way.
\* Literally: "NoViolationOnLiveConnection is defined as: violation equals
\*   "none", or closing is true."
NoViolationOnLiveConnection == violation = "none" \/ closing

\* Probes, each EXPECTED to be violated.
\* In English: "Stop never abandons requests." Violated = it does.
\* Literally: "ProbeNeverAbandons is defined as: abandoned is not true."
ProbeNeverAbandons == ~abandoned
\* In English: "The client never restarts." Violated = it does.
\* Literally: "ProbeNeverRestarts is defined as: starts equals 0."
ProbeNeverRestarts == starts = 0
\* In English: "A late roll never breaks a restarted client." Violated = the
\* violation also comes from the common case: Stop at the chain tip with a
\* MsgRequestNext unanswered, not only Stop during MsgFindIntersect.
\* Literally: "ProbeNoRollViolation is defined as: violation does not equal
\*   "RN"."
ProbeNoRollViolation == violation /= "RN"
\* In English: "A restarted client never resumes syncing." Violated = it does.
\* Literally: "ProbeNeverResyncs is defined as: it is not the case that starts
\*   is greater than 0 and cs equals "syncing" and expect equals the sequence
\*   containing "RN"."
ProbeNeverResyncs == ~(starts > 0 /\ cs = "syncing" /\ expect = <<"RN">>)
=============================================================================
