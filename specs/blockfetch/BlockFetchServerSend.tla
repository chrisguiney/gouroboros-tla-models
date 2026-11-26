------------------------- MODULE BlockFetchServerSend -------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 9: the server's answers reach the wire only   *)
(* in the states the state machine allows them in; in particular MsgBlock  *)
(* only in StStreaming.                                                    *)
(*                                                                         *)
(* gOuroboros files: protocol/blockfetch/server.go (StartBatch, NoBlocks,  *)
(* Block, BatchDone) and protocol/protocol.go (enqueueMessage, sendLoop,   *)
(* transitionState), at blinklabs-io/gouroboros 7cd17437.                  *)
(*                                                                         *)
(* What the code does [G1][G2]:                                            *)
(*   The server's send methods put the message on the protocol's send      *)
(*   queue whatever the state; they refuse only a stopped protocol. The    *)
(*   send loop runs only while the server has agency (StBusy,              *)
(*   StStreaming; the server never pipelines), takes the queue in order,   *)
(*   and applies each message's state transition before its segment is     *)
(*   written. A message the current state does not allow fails the         *)
(*   transition: the protocol reports the error and stops, and nothing of  *)
(*   that batch is written. In StIdle and StDone the server has no agency, *)
(*   so a message queued then waits.                                       *)
(*                                                                         *)
(* Question: is every message the server writes legal in the state it is   *)
(* written in?                                                             *)
(*                                                                         *)
(* Sources (IntersectMBO/ouroboros-network 5f356486ab3e; README links):    *)
(*   [B1] docs/network-spec/miniprotocols.tex 1190-1204: StBusy:           *)
(*        MsgStartBatch to StStreaming, MsgNoBlocks to StIdle;             *)
(*        StStreaming: MsgBlock to StStreaming, MsgBatchDone to StIdle;    *)
(*        the server has agency only in StBusy and StStreaming.            *)
(*   [R1] .../Protocol/BlockFetch/Type.hs 57-83: the same, as types.       *)
(*   gOuroboros 7cd17437:                                                  *)
(*   [G1] protocol/blockfetch/server.go 132-215.                           *)
(*   [G2] protocol/protocol.go: enqueueMessage 1038-1109, sendLoop         *)
(*        1405-1716 (transitionState before the segment is written).       *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table.                                                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxCalls,      \* server send calls, in any order (a misusing caller)
    MaxRanges,     \* MsgRequestRange the client sends
    \* Mutation, FALSE in the code as it is:
    WriteUnchecked \* the send loop writes a message without checking that
                   \* its state allows it

Answers == {"StartBatch", "NoBlocks", "Block", "BatchDone"}

\* In English: "The state a server answer leads to from state s, or "bad"
\* if s does not allow it [B1]."
\* Literally: "Next state Nxt(s, m) is defined as: in "Busy", "Streaming"
\*   for StartBatch and "Idle" for NoBlocks; in "Streaming", "Streaming"
\*   for Block and "Idle" for BatchDone; otherwise "bad"."
Nxt(s, m) ==
    CASE s = "Busy" /\ m = "StartBatch" -> "Streaming"
      [] s = "Busy" /\ m = "NoBlocks" -> "Idle"
      [] s = "Streaming" /\ m = "Block" -> "Streaming"
      [] s = "Streaming" /\ m = "BatchDone" -> "Idle"
      [] OTHER -> "bad"

VARIABLES
    ss,       \* the server's protocol state: "Idle", "Busy", "Streaming"
    sq,       \* the server's send queue
    calls,    \* send calls made so far
    ranges,   \* MsgRequestRange the client sent so far
    up,       \* TRUE until the server protocol stops on an error
    wire,     \* what the server wrote: records [m |-> msg, in |-> state]
    badWrite  \* TRUE once a message was written in a state forbidding it

vars == <<ss, sq, calls, ranges, up, wire, badWrite>>

\* Literally: "Init is defined as: ss equals "Idle", sq and wire are empty,
\*   calls and ranges are 0, up is TRUE, and badWrite is FALSE."
Init ==
    /\ ss = "Idle" /\ sq = <<>> /\ calls = 0 /\ ranges = 0
    /\ up = TRUE /\ wire = <<>> /\ badWrite = FALSE

\* In English: "Any goroutine calls one of the server's send methods: the
\* message is queued whatever the state [G1]."
\* Literally: "Call(m) is defined as: up is true, and calls is less than
\*   MaxCalls, and sq' is sq with m appended, and calls' is calls plus 1,
\*   and the other variables are unchanged."
Call(m) ==
    /\ up /\ calls < MaxCalls
    /\ sq' = Append(sq, m) /\ calls' = calls + 1
    /\ UNCHANGED <<ss, ranges, up, wire, badWrite>>

\* In English: "The client's MsgRequestRange arrives in StIdle."
\* Literally: "ClientRange is defined as: up is true, and ss equals "Idle",
\*   and ranges is less than MaxRanges, and ss' equals "Busy", and ranges'
\*   is ranges plus 1, and the other variables are unchanged."
ClientRange ==
    /\ up /\ ss = "Idle" /\ ranges < MaxRanges
    /\ ss' = "Busy" /\ ranges' = ranges + 1
    /\ UNCHANGED <<sq, calls, up, wire, badWrite>>

\* In English: "With agency, the send loop takes the head of the queue: a
\* message the state allows is written and its transition applied; one it
\* does not allow stops the protocol unwritten (unless WriteUnchecked)."
\* Literally: "SendHead is defined as: up is true, and ss is "Busy" or
\*   "Streaming", and sq is not empty, and sq' is its tail, and with m the
\*   head and n equal to Nxt(ss, m): if n is not "bad" then wire' is wire
\*   with [m, ss] appended and ss' equals n; else if WriteUnchecked then
\*   wire' is wire with [m, ss] appended, badWrite' is TRUE and ss is
\*   unchanged; else up' is FALSE and wire is unchanged."
SendHead ==
    /\ up /\ ss \in {"Busy", "Streaming"} /\ sq /= <<>>
    /\ sq' = Tail(sq)
    /\ LET m == Head(sq)
           n == Nxt(ss, m)
       IN IF n /= "bad"
             THEN /\ wire' = Append(wire, [m |-> m, in |-> ss])
                  /\ ss' = n
                  /\ UNCHANGED <<up, badWrite>>
          ELSE IF WriteUnchecked
             THEN /\ wire' = Append(wire, [m |-> m, in |-> ss])
                  /\ badWrite' = TRUE
                  /\ UNCHANGED <<ss, up>>
          ELSE /\ up' = FALSE
               /\ UNCHANGED <<ss, wire, badWrite>>
    /\ UNCHANGED <<calls, ranges>>

\* Literally: "Next is defined as: some answer m takes Call(m), or
\*   ClientRange or SendHead is a step, or nothing changes."
Next ==
    \/ \E m \in Answers : Call(m)
    \/ ClientRange \/ SendHead
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* In English: "Each variable holds a value of the right kind."
TypeOK ==
    /\ ss \in {"Idle", "Busy", "Streaming"}
    /\ up \in BOOLEAN /\ badWrite \in BOOLEAN

\* In English: "Every MsgBlock the server wrote was written in StStreaming."
\* Literally: "BlockOnlyInStreaming is defined as: for every i in 1 through
\*   the length of wire, if wire[i].m is "Block" then wire[i].in is
\*   "Streaming"."
BlockOnlyInStreaming ==
    \A i \in 1..Len(wire) : wire[i].m = "Block" => wire[i].in = "Streaming"

\* In English: "Every message the server wrote is legal where it was
\* written."
\* Literally: "WireFollowsStateMap is defined as: for every i in 1 through
\*   the length of wire, Nxt(wire[i].in, wire[i].m) is not "bad"."
WireFollowsStateMap ==
    \A i \in 1..Len(wire) : Nxt(wire[i].in, wire[i].m) /= "bad"

\* Probes, each EXPECTED to be violated (reachability).
\* In English: "No block is ever written." Violated = a block is served.
\* Literally: "ProbeNoBlock is defined as: no wire element is a "Block"."
ProbeNoBlock == \A i \in 1..Len(wire) : wire[i].m /= "Block"
\* In English: "A misplaced call never stops the server." Violated = it does.
\* Literally: "ProbeNeverRefused is defined as: up is true."
ProbeNeverRefused == up
=============================================================================
