----------------------------- MODULE MuxIngress -----------------------------
(***************************************************************************)
(* Model 02, part 3: two mini-protocols sharing one demultiplexer.         *)
(*                                                                         *)
(* The muxer reads every segment of the connection in ONE loop, in the     *)
(* order the peer sent them, and puts each on its mini-protocol's queue.   *)
(* Each queue has a limit, and all queues together share a connection      *)
(* budget. A segment that does not fit either ends the connection, or -    *)
(* for a protocol with backpressure switched on - makes the loop wait,     *)
(* which holds up EVERY protocol behind it.                                *)
(*                                                                         *)
(* Two protocols, named for what they stand for:                           *)
(*   "Bulk" - a protocol that asked for data it cannot size in advance,    *)
(*            like a block-fetch range; the only kind that switches on     *)
(*            backpressure in gOuroboros.                                  *)
(*   "Ping" - a small request/response protocol, like keep-alive or a      *)
(*            local state query.                                           *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [M1] docs/network-spec/mux.tex 36-58 (ouroboros-network 5f356486ab3e):*)
(*        segments of a mini-protocol arrive in order.                     *)
(*   [M3] docs/network-spec/mux.tex 123-131: a fixed-size buffer per       *)
(*        mini-protocol; "each mini-protocol implements its own mechanism  *)
(*        for flow control, which guarantees that this buffer never        *)
(*        overflows"; an overflow means the peer broke the protocol, and   *)
(*        the connection is shut down.                                     *)
(* gOuroboros code (read, not guessed):                                    *)
(*   muxer/muxer.go readLoop - one loop for every protocol; it calls       *)
(*     enqueue and, on ErrIngressOverflow, ends the connection.            *)
(*   muxer/muxer.go segmentChannel.enqueue - a segment fits when its queue *)
(*     stays within the protocol's limit and the connection budget has     *)
(*     room; with backpressure it waits instead of failing, and "an empty  *)
(*     queue always admits", past both.                                    *)
(*   muxer/muxer.go segmentChannel.forward - moves a segment from the      *)
(*     queue to the protocol's channel, returning its budget.              *)
(*   protocol/protocol.go SetIngressBackpressure - "Pausing the read loop  *)
(*     stops every protocol on the connection, keep-alive included".       *)
(*   protocol/blockfetch/client.go - switches backpressure on while it has *)
(*     unestimated requests outstanding.                                   *)
(*                                                                         *)
(* Units are segments; the budget counts them too. gOuroboros allocates   *)
(* each payload at its exact length, so the budget charges bytes plus a    *)
(* small fixed overhead per segment, and counting segments loses nothing   *)
(* that matters here.                                                      *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    LimitBulk,          \* how many segments Bulk's queue may hold
    LimitPing,          \* how many segments Ping's queue may hold
    Budget,             \* how many segments all queues together may hold
    Backpressure,       \* the set of protocols with backpressure switched on
    EmptyQueueAdmits,   \* TRUE (gOuroboros): an empty backpressured queue always admits
    BulkWindow,         \* how many Bulk segments the peer may send for one request
    Pings,              \* how many Ping exchanges there are
    Dependency          \* TRUE: Bulk's consumer needs a Ping answer before its next segment

Protocols == {"Bulk", "Ping"}

\* In English: "Limit[p] is how many segments protocol p's queue may hold."
Limit == [p \in Protocols |-> IF p = "Bulk" THEN LimitBulk ELSE LimitPing]

\* Each protocol's channel between its queue and its reader holds one
\* segment here (ten in gOuroboros; one is enough to show the effect).
ChanCap == 1

VARIABLES
    allowance,  \* allowance[p]: segments the peer may still send for p (flow control)
    wire,       \* segments sent by the peer, not yet read by the demuxer, oldest first
    queue,      \* queue[p]: segments on p's muxer queue
    chan,       \* chan[p]: segments on p's channel, waiting for its reader
    got,        \* got[p]: segments p's reader has consumed
    waitingPing,\* TRUE while Bulk's consumer waits for a Ping answer
    closed      \* TRUE once an overflow has ended the connection

vars == <<allowance, wire, queue, chan, got, waitingPing, closed>>

\* In English: "the total number of segments on all queues."
Queued == queue["Bulk"] + queue["Ping"]

\* In English: "At the start, Bulk has asked for BulkWindow segments; Ping's
\* peer may send one Ping (one exchange is outstanding at a time, as in
\* keep-alive), or none yet when Ping answers Bulk's questions; everything
\* else is empty."
Init ==
    /\ allowance = [p \in Protocols |->
                       IF p = "Bulk" THEN BulkWindow
                       ELSE IF Dependency \/ Pings = 0 THEN 0 ELSE 1]
    /\ wire = <<>>
    /\ queue = [p \in Protocols |-> 0]
    /\ chan = [p \in Protocols |-> 0]
    /\ got = [p \in Protocols |-> 0]
    /\ waitingPing = FALSE
    /\ closed = FALSE

-----------------------------------------------------------------------------

\* In English: "While the connection is open, the peer can send a segment
\* for p if p's flow control allows one more [M3]."
PeerSends(p) ==
    /\ ~closed
    /\ allowance[p] > 0
    /\ wire' = Append(wire, p)
    /\ allowance' = [allowance EXCEPT ![p] = @ - 1]
    /\ UNCHANGED <<queue, chan, got, waitingPing, closed>>

\* In English: "p's queue is empty and p has backpressure on: then
\* gOuroboros admits the segment past both its limit and the budget."
EmptyAdmit(p) == EmptyQueueAdmits /\ p \in Backpressure /\ queue[p] = 0

\* In English: "The segment fits p's queue limit, and fits the budget."
FitsQueue(p)  == queue[p] + 1 <= Limit[p] \/ EmptyAdmit(p)
FitsBudget(p) == Queued + 1 <= Budget \/ EmptyAdmit(p)

\* In English: "The demuxer reads the oldest segment on the wire, for
\* protocol p. If it fits, it goes on p's queue. If not and p has
\* backpressure, the demuxer waits - this step cannot happen, and neither
\* can anything else that needs the demuxer. If not and p has no
\* backpressure, the connection ends with an overflow."
Demux ==
    /\ ~closed
    /\ wire /= <<>>
    /\ LET p == Head(wire) IN
         IF FitsQueue(p) /\ FitsBudget(p)
            THEN /\ queue' = [queue EXCEPT ![p] = @ + 1]    \* it fits: queue it
                 /\ wire' = Tail(wire)
                 /\ UNCHANGED closed
         ELSE IF p \in Backpressure
            THEN FALSE                                      \* wait (no step)
            ELSE /\ closed' = TRUE                          \* overflow: hang up
                 /\ UNCHANGED <<queue, wire>>
    /\ UNCHANGED <<allowance, chan, got, waitingPing>>

\* In English: "p's forwarder moves a segment from its queue to its channel
\* when the channel has room; the segment no longer counts against the
\* budget."
Forward(p) ==
    /\ ~closed
    /\ queue[p] > 0
    /\ chan[p] < ChanCap
    /\ queue' = [queue EXCEPT ![p] = @ - 1]
    /\ chan' = [chan EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<allowance, wire, got, waitingPing, closed>>

\* In English: "Bulk's reader consumes a segment, unless it is waiting for a
\* Ping answer. With Dependency, it then asks a Ping question (giving the
\* peer one Ping to send) and waits for the answer."
ConsumeBulk ==
    /\ ~closed
    /\ chan["Bulk"] > 0
    /\ ~waitingPing
    /\ chan' = [chan EXCEPT !["Bulk"] = @ - 1]
    /\ got' = [got EXCEPT !["Bulk"] = @ + 1]
    /\ IF Dependency /\ got["Bulk"] < Pings
          THEN /\ allowance' = [allowance EXCEPT !["Ping"] = @ + 1]
               /\ waitingPing' = TRUE
          ELSE UNCHANGED <<allowance, waitingPing>>
    /\ UNCHANGED <<wire, queue, closed>>

\* In English: "Ping's reader consumes an answer; Bulk stops waiting. On its
\* own (without Dependency), the next exchange may then start."
ConsumePing ==
    /\ ~closed
    /\ chan["Ping"] > 0
    /\ chan' = [chan EXCEPT !["Ping"] = @ - 1]
    /\ got' = [got EXCEPT !["Ping"] = @ + 1]
    /\ waitingPing' = FALSE
    /\ allowance' = IF ~Dependency /\ got["Ping"] + 1 < Pings
                       THEN [allowance EXCEPT !["Ping"] = @ + 1]
                       ELSE allowance
    /\ UNCHANGED <<wire, queue, closed>>

\* In English: "Everything has been delivered, or the connection has
\* closed." Any other state where nothing can happen is a deadlock.
Finished ==
    /\ \/ closed
       \/ /\ \A p \in Protocols : allowance[p] = 0 /\ queue[p] = 0 /\ chan[p] = 0
          /\ wire = <<>>
          /\ ~waitingPing
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Protocols : PeerSends(p) \/ Forward(p)
    \/ Demux \/ ConsumeBulk \/ ConsumePing
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Traffic that follows flow control never makes the
\* connection hang up."
NoOverflow == ~closed

\* In English: "No queue ever holds more than its limit, except the one
\* segment an empty backpressured queue may admit."
QueuesWithinLimits ==
    \A p \in Protocols : queue[p] <= Limit[p] \/ (p \in Backpressure /\ queue[p] = 1)
=============================================================================
