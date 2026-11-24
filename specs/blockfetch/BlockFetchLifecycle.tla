------------------------- MODULE BlockFetchLifecycle -------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 2: stopping the block-fetch client with ranges          *)
(* outstanding, and starting it again on the same connection.              *)
(*                                                                         *)
(* What the code does (protocol/blockfetch/client.go, Stop and Start):     *)
(*   Stop queues MsgClientDone and waits up to 250 ms for it to be         *)
(*   written, then unregisters the protocol whether or not it was.         *)
(*   MsgClientDone is legal only in StIdle, so while a range is            *)
(*   outstanding it waits in the send queue for the range's last answer.   *)
(*   If that takes longer than 250 ms, Stop returns "context deadline      *)
(*   exceeded" and the server is left owing answers.                       *)
(*   Start then registers a fresh protocol instance in StIdle. While the   *)
(*   protocol is unregistered the muxer drops its messages; once Start     *)
(*   registers the new instance, they are delivered to it.                 *)
(*                                                                         *)
(* This is chain-sync's Stop problem (specs/chainsync, slice 2) in      *)
(* block-fetch. Block-fetch has no StopAfterDrain.                         *)
(*                                                                         *)
(* Question: does either side ever receive a message its state machine     *)
(* does not allow?                                                         *)
(*                                                                         *)
(* Sources (IntersectMBO/ouroboros-network 5f356486ab3e; README has links):*)
(*   [B1] docs/network-spec/miniprotocols.tex 1190-1204: MsgClientDone     *)
(*        only from StIdle; every other client message is MsgRequestRange. *)
(*   [S1] miniprotocols.tex 27-36: an unexpected message aborts the        *)
(*        connection.                                                      *)
(*   [P1] miniprotocols.tex 2180-2208: answers come back in request order. *)
(*   [R3] .../Protocol/BlockFetch/Client.hs 130-132, 148-150: the          *)
(*        pipelined client sends MsgClientDone only with nothing           *)
(*        outstanding (SendMsgDonePipelined is typed at Z).                *)
(*   [R4] ouroboros-network/lib/Ouroboros/Network/BlockFetch/Client.hs     *)
(*        182-190: on Terminate the fetch client collects every            *)
(*        outstanding answer, then sends MsgClientDone.                    *)
(*   gOuroboros, blinklabs-io/gouroboros 61046085:                         *)
(*   [G1] protocol/blockfetch/client.go: Stop (473-549, the 250 ms timer at *)
(*        519), Start (366-454).                                           *)
(*   [G2] muxer/muxer.go: a tombstoned (unregistered) protocol role's      *)
(*        ingress is dropped.                                              *)
(*                                                                         *)
(* An answer is modelled as one message. A real one is MsgNoBlocks, or     *)
(* MsgStartBatch, blocks, and MsgBatchDone; a restarted instance in StIdle *)
(* already refuses the first of them, so the rest change nothing.          *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Limit,         \* ranges the client keeps outstanding (1: GetBlockRange)
    MaxRequests,   \* MsgRequestRange sent in total (keeps it finite)
    MaxStarts,     \* how many times the client may be restarted
    \* TRUE with the fix (ErrStoppedWithoutDone): a Stop that could not
    \* deliver MsgClientDone reports an error, and the connection is closed.
    CloseOnAbandon,
    \* TRUE with the fix (stoppedWithoutDone): Start refuses to restart
    \* after such a Stop.
    StartRefusesAbandoned

VARIABLES
    cs,         \* the client: "running", "stopping", "stopped"
    owed,       \* answers this instance still awaits
    reg,        \* TRUE while the protocol is registered with the muxer
    abandoned,  \* TRUE once a Stop unregistered with answers owed
    starts,     \* times Start has run (model bound)
    sent,       \* MsgRequestRange sent so far (model bound)
    toServer,   \* client messages in flight: "RR" or "Done"
    toClient,   \* answers in flight (each "Ans")
    sv,         \* the server: "idle", or "busy" while it owes an answer
    closing,    \* TRUE once an error has asked the connection to close
    closed,     \* TRUE once the connection is closed
    violation   \* TRUE once a side received a message its state forbids

\* Literally: "vars is defined as the tuple of all twelve variables."
vars == <<cs, owed, reg, abandoned, starts, sent, toServer, toClient, sv,
          closing, closed, violation>>

\* In English: "The client is running; nothing is in flight."
\* Literally: "Init is defined as: cs equals "running", and owed equals 0, and
\*   reg equals TRUE, and abandoned equals FALSE, and starts equals 0, and sent
\*   equals 0, and toServer equals the empty sequence, and toClient equals the
\*   empty sequence, and sv equals "idle", and closing equals FALSE, and closed
\*   equals FALSE, and violation equals FALSE."
Init ==
    /\ cs = "running" /\ owed = 0 /\ reg = TRUE /\ abandoned = FALSE
    /\ starts = 0 /\ sent = 0
    /\ toServer = <<>> /\ toClient = <<>> /\ sv = "idle"
    /\ closing = FALSE /\ closed = FALSE
    /\ violation = FALSE

-----------------------------------------------------------------------------
(* The client [G1]. Every action but StopFinish and ConnClose starts with  *)
(* "the connection is still open" and leaves closing and closed alone.     *)

\* In English: "Running, the client asks for another range while it has
\* fewer than Limit outstanding."
\* Literally: "Request is defined as: closed is not true, and closing and closed
\*   are unchanged, and cs equals "running", and owed is less than Limit, and
\*   sent is less than MaxRequests, and toServer in the next state equals
\*   toServer with "RR" appended, and owed in the next state equals owed plus 1,
\*   and sent in the next state equals sent plus 1, and cs, reg, abandoned,
\*   starts, toClient, sv and violation are unchanged."
Request ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ cs = "running" /\ owed < Limit /\ sent < MaxRequests
    /\ toServer' = Append(toServer, "RR")
    /\ owed' = owed + 1
    /\ sent' = sent + 1
    /\ UNCHANGED <<cs, reg, abandoned, starts, toClient, sv, violation>>

\* In English: "An answer reaches the client. Unregistered, the muxer drops
\* it [G2]. Otherwise the instance must be owed one; if not, it is in StIdle
\* and the answer is a protocol violation [S1]."
\* Literally: "ClientRecv is defined as: closed is not true, and closing and
\*   closed are unchanged, and toClient does not equal the empty sequence, and:
\*   if reg is not true, then owed and violation are unchanged; else if owed is
\*   greater than 0, then owed in the next state equals owed minus 1, and
\*   violation is unchanged; else violation in the next state equals TRUE, and
\*   owed is unchanged; and toClient in the next state equals the tail of
\*   toClient, and cs, reg, abandoned, starts, sent, toServer and sv are
\*   unchanged."
ClientRecv ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ toClient /= <<>>
    /\ IF ~reg
          THEN UNCHANGED <<owed, violation>>
       ELSE IF owed > 0
          THEN /\ owed' = owed - 1
               /\ UNCHANGED violation
       ELSE /\ violation' = TRUE
            /\ UNCHANGED owed
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<cs, reg, abandoned, starts, sent, toServer, sv>>

\* In English: "Stop: no more requests; MsgClientDone is queued."
\* Literally: "StopBegin is defined as: closed is not true, and closing and
\*   closed are unchanged, and cs equals "running", and cs in the next state
\*   equals "stopping", and owed, reg, abandoned, starts, sent, toServer,
\*   toClient, sv and violation are unchanged."
StopBegin ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ cs = "running"
    /\ cs' = "stopping"
    /\ UNCHANGED <<owed, reg, abandoned, starts, sent, toServer, toClient, sv,
                   violation>>

\* In English: "MsgClientDone goes out once every answer is in - or the
\* 250 ms timer fires first, and the protocol is unregistered without it,
\* leaving the server owing answers. With CloseOnAbandon, that asks the
\* connection to close."
\* Literally: "StopFinish is defined as: closed is not true, and cs equals
\*   "stopping", and either (owed equals 0, and toServer in the next state
\*   equals toServer with "Done" appended, and abandoned is unchanged) or (owed
\*   is greater than 0, and abandoned in the next state equals TRUE, and
\*   toServer is unchanged), and cs in the next state equals "stopped", and reg
\*   in the next state equals FALSE, and owed in the next state equals 0, and
\*   closing in the next state equals (closing or (CloseOnAbandon is true and
\*   owed is greater than 0)), and starts, sent, toClient, sv, closed and
\*   violation are unchanged."
StopFinish ==
    /\ ~closed
    /\ cs = "stopping"
    /\ \/ /\ owed = 0
          /\ toServer' = Append(toServer, "Done")
          /\ UNCHANGED abandoned
       \/ /\ owed > 0
          /\ abandoned' = TRUE
          /\ UNCHANGED toServer
    /\ cs' = "stopped" /\ reg' = FALSE /\ owed' = 0
    /\ closing' = (closing \/ (CloseOnAbandon /\ owed > 0))
    /\ UNCHANGED <<starts, sent, toClient, sv, closed, violation>>

\* In English: "Start registers a fresh instance in StIdle, owed nothing.
\* With StartRefusesAbandoned, it refuses after a Stop that abandoned
\* answers."
\* Literally: "Start is defined as: closed is not true, and closing and closed
\*   are unchanged, and cs equals "stopped", and starts is less than MaxStarts,
\*   and (StartRefusesAbandoned is true and abandoned is true) is not true, and
\*   cs in the next state equals "running", and reg in the next state equals
\*   TRUE, and owed in the next state equals 0, and starts in the next state
\*   equals starts plus 1, and abandoned, sent, toServer, toClient, sv and
\*   violation are unchanged."
Start ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ cs = "stopped" /\ starts < MaxStarts
    /\ ~(StartRefusesAbandoned /\ abandoned)
    /\ cs' = "running" /\ reg' = TRUE /\ owed' = 0
    /\ starts' = starts + 1
    /\ UNCHANGED <<abandoned, sent, toServer, toClient, sv, violation>>

-----------------------------------------------------------------------------
(* The honest server [B1][P1]: one message at a time, in order. After      *)
(* MsgClientDone it restarts in StIdle.                                    *)

\* In English: "Idle, the server takes the next message: MsgClientDone
\* ends the run and it stays idle for the next; a range makes it busy."
\* Literally: "ServerTake is defined as: closed is not true, and closing and
\*   closed are unchanged, and sv equals "idle", and toServer does not equal the
\*   empty sequence, and sv in the next state equals: if the head of toServer
\*   equals "Done" then "idle", else "busy"; and toServer in the next state
\*   equals the tail of toServer, and cs, owed, reg, abandoned, starts, sent,
\*   toClient and violation are unchanged."
ServerTake ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ sv = "idle" /\ toServer /= <<>>
    /\ sv' = IF Head(toServer) = "Done" THEN "idle" ELSE "busy"
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<cs, owed, reg, abandoned, starts, sent, toClient,
                   violation>>

\* In English: "Busy, the server answers the range, however late."
\* Literally: "ServerAnswer is defined as: closed is not true, and closing and
\*   closed are unchanged, and sv equals "busy", and toClient in the next state
\*   equals toClient with "Ans" appended, and sv in the next state equals
\*   "idle", and cs, owed, reg, abandoned, starts, sent, toServer and violation
\*   are unchanged."
ServerAnswer ==
    /\ ~closed
    /\ UNCHANGED <<closing, closed>>
    /\ sv = "busy"
    /\ toClient' = Append(toClient, "Ans")
    /\ sv' = "idle"
    /\ UNCHANGED <<cs, owed, reg, abandoned, starts, sent, toServer,
                   violation>>

\* In English: "The connection acts on the error and closes; nothing more
\* is sent or delivered. Until then Start and late answers can still happen,
\* because the connection handles errors on its own goroutine."
\* Literally: "ConnClose is defined as: closing is true, and closed is not true,
\*   and closed in the next state equals TRUE, and cs, owed, reg, abandoned,
\*   starts, sent, toServer, toClient, sv, closing and violation are unchanged."
ConnClose ==
    /\ closing /\ ~closed
    /\ closed' = TRUE
    /\ UNCHANGED <<cs, owed, reg, abandoned, starts, sent, toServer, toClient,
                   sv, closing, violation>>

-----------------------------------------------------------------------------

\* In English: "Nothing left to do: nothing in flight and the server idle,
\* or the connection closed."
\* Literally: "Quiet is defined as: (toServer equals the empty sequence and
\*   toClient equals the empty sequence and sv equals "idle") or closed is true;
\*   and vars is unchanged."
Quiet ==
    /\ \/ toServer = <<>> /\ toClient = <<>> /\ sv = "idle"
       \/ closed
    /\ UNCHANGED vars

\* In English: "A step is any one client, server or connection step, or nothing
\* left to do."
\* Literally: "Next is defined as: Request or ClientRecv or StopBegin or
\*   StopFinish or Start, or ServerTake or ServerAnswer or ConnClose, or Quiet."
Next ==
    \/ Request \/ ClientRecv \/ StopBegin \/ StopFinish \/ Start
    \/ ServerTake \/ ServerAnswer \/ ConnClose
    \/ Quiet

\* In English: "Start in Init, and take only Next steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next step
\*   or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "No side ever receives a message it does not expect."
\* Literally: "NoViolation is defined as: violation is not true."
NoViolation == ~violation

\* In English: "No side receives a message it does not expect on a
\* connection that is staying open."
\* Literally: "NoViolationOnLiveConnection is defined as: violation is not true,
\*   or closing is true."
NoViolationOnLiveConnection == ~violation \/ closing

\* Probes, each EXPECTED to be violated.
\* In English: "Stop never abandons answers." Violated = it does.
\* Literally: "ProbeNeverAbandons is defined as: abandoned is not true."
ProbeNeverAbandons == ~abandoned
\* In English: "The client never restarts." Violated = it does.
\* Literally: "ProbeNeverRestarts is defined as: starts equals 0."
ProbeNeverRestarts == starts = 0
\* In English: "Stop never delivers MsgClientDone." Violated = a clean stop
\* is reachable too.
\* Literally: "ProbeNeverCleanStop is defined as: (there exists a k in 1
\*   through the length of toServer such that element k of toServer equals
\*   "Done") is not true."
ProbeNeverCleanStop == ~\E k \in 1..Len(toServer) : toServer[k] = "Done"
=============================================================================
