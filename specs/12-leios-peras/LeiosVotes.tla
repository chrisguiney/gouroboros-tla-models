------------------------------ MODULE LeiosVotes ------------------------------
(***************************************************************************)
(* Model 12, LeiosVotes: the token state machine of CIP-0164, the          *)
(* gOuroboros client's vote loop and RequestNext, Stop, and the server.    *)
(*                                                                         *)
(* The protocol is not in the network specification, and the reference    *)
(* node does not implement it (it sends votes over LeiosNotify). The only *)
(* source is CIP-0164, Figure 6b and the pipelining text around it;        *)
(* README.md says how authoritative that is.                               *)
(*                                                                         *)
(* The client (protocol/leiosvotes/client.go):                             *)
(*   Sync          queues PipelineLimit requests of RequestNextCount votes *)
(*                 and starts voteLoop.                                    *)
(*   voteLoop      takes votes; when what is owed falls to the refill      *)
(*                 threshold it queues another request. A callback may     *)
(*                 stop the loop (ErrStopVoteProcess); then, or once Stop  *)
(*                 has run, it drains the votes still owed and ends.       *)
(*   RequestNext   when no loop runs: one request, then its votes.         *)
(*   Stop          queues MsgDone; nothing is sent after it (sendMutex).   *)
(* The loop and RequestNext read the same vote channel, so a vote goes to  *)
(* whichever is reading. The client's send loop writes a request only in   *)
(* Idle: its state map lets it pipeline nothing.                           *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoServerViolation  does the server ever refuse a client's message?   *)
(*   NoClientViolation  does the client ever get a vote nobody asked for? *)
(*   OwnVotes           does the loop or RequestNext ever take a vote that *)
(*                      answers the other's request?                       *)
(*   Deadlock           TLC checks it.                                     *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [C1] CIP-0164 (cardano-foundation/CIPs 03387471), Figure 6b: Idle     *)
(*        -RequestNext(N)-> Busy{tokens := N}; Vote keeps Busy while       *)
(*        tokens > 1 and returns to Idle on the last; MsgDone from Idle.   *)
(*   [C2] CIP-0164, the paragraphs after Figures 6a and 6c: the next       *)
(*        request is sent before the previous batch is delivered, by       *)
(*        protocol pipelining; intended use is 1000 tokens then 100 more   *)
(*        after each 100 received.                                         *)
(*   [G1] gOuroboros 61046085, protocol/leiosvotes/client.go (Sync,        *)
(*        voteLoop, drainVotes, RequestNext, Stop), leiosvotes.go          *)
(*        (StateMap, matchRequestNext), server.go (handleRequestNext).     *)
(*                                                                         *)
(* Not modelled: counts above MaxRequestNextCount, timeouts, vote content. *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Count,                 \* RequestNextCount: votes per loop request
    Depth,                 \* PipelineLimit
    MaxRefills,            \* refills the loop may queue (keeps it finite)
    ClientPipelines,       \* FALSE: gOuroboros' client; TRUE: a client following [C2]
    ServerHoldsPipelined,  \* FALSE today; TRUE: the fix, the server holds a request that arrives in Busy
    DrainOnStop            \* TRUE as in gOuroboros; FALSE is a mutation

LoopGen == "loop"   \* tags a request (and its votes) the loop sent
CallGen == "call"   \* tags RequestNext's request

\* In English: "A request message for n votes, tagged with who sent it."
Req(n, g) == [t |-> "Req", n |-> n, g |-> g]
DoneMsg == [t |-> "Done", n |-> 0, g |-> "none"]

VARIABLES
    lpc,          \* the loop: "Off", "Run", "Drain"
    outstanding,  \* votes the loop is still owed
    refills,      \* refills queued so far
    synced,       \* Sync has run
    rpc,          \* RequestNext: "idle", "wait", "done"
    stopping,     \* Stop has run
    queue,        \* the client's send queue: messages not yet written
    c2s,          \* written client messages in flight
    s2c,          \* votes in flight, each tagged with its request
    cowed,        \* votes the client is owed for requests it has written
    inbox,        \* votes handed to the vote channel, not yet taken
    srv,          \* the server: [st |-> "Idle" | "Busy" | "Done", tokens, g]
    srvHeld,      \* requests the server holds while Busy
    sviol,        \* the server refused a client message
    cviol,        \* the client got a vote it was not owed
    foreign       \* a reader took a vote answering the other reader's request

vars == <<lpc, outstanding, refills, synced, rpc, stopping, queue, c2s, s2c,
          cowed, inbox, srv, srvHeld, sviol, cviol, foreign>>

Init ==
    /\ lpc = "Off" /\ outstanding = 0 /\ refills = 0 /\ synced = FALSE
    /\ rpc = "idle" /\ stopping = FALSE
    /\ queue = <<>> /\ c2s = <<>> /\ s2c = <<>> /\ cowed = 0 /\ inbox = <<>>
    /\ srv = [st |-> "Idle", tokens |-> 0, g |-> "none"] /\ srvHeld = <<>>
    /\ sviol = FALSE /\ cviol = FALSE /\ foreign = FALSE

\* In English: "Requests the loop sends as one batch."
SyncBatch == [i \in 1..Depth |-> Req(Count, LoopGen)]

\* --- The client application. ---------------------------------------------

\* In English: "Sync, once, with no loop running and Stop not yet run."
Sync ==
    /\ ~synced /\ ~stopping /\ lpc = "Off" /\ rpc /= "wait"
    /\ queue' = queue \o SyncBatch
    /\ outstanding' = Depth * Count /\ lpc' = "Run" /\ synced' = TRUE
    /\ UNCHANGED <<refills, rpc, stopping, c2s, s2c, cowed, inbox, srv, srvHeld,
                   sviol, cviol, foreign>>

\* In English: "The loop takes a vote. It is foreign if it answers
\* RequestNext's request. Then the callback continues or stops the loop;
\* after Stop the loop drains; otherwise it refills when what it is owed
\* falls to (Depth - 1) * Count."
LoopTake ==
    /\ lpc = "Run" /\ inbox /= <<>>
    /\ foreign' = (foreign \/ Head(inbox) /= LoopGen)
    /\ inbox' = Tail(inbox)
    /\ \/ /\ lpc' = IF DrainOnStop THEN "Drain" ELSE "Off"   \* callback: ErrStopVoteProcess
          /\ outstanding' = outstanding - 1
          /\ UNCHANGED <<queue, refills>>
       \/ /\ stopping                                       \* Stop has run
          /\ lpc' = IF DrainOnStop THEN "Drain" ELSE "Off"
          /\ outstanding' = outstanding - 1
          /\ UNCHANGED <<queue, refills>>
       \/ /\ ~stopping                                      \* carry on
          /\ IF outstanding - 1 <= (Depth - 1) * Count /\ refills < MaxRefills
             THEN /\ queue' = Append(queue, Req(Count, LoopGen))
                  /\ outstanding' = outstanding - 1 + Count
                  /\ refills' = refills + 1
             ELSE /\ outstanding' = outstanding - 1
                  /\ UNCHANGED <<queue, refills>>
          /\ lpc' = IF outstanding' = 0 THEN "Off" ELSE "Run"
    /\ UNCHANGED <<synced, rpc, stopping, c2s, s2c, cowed, srv, srvHeld, sviol,
                   cviol>>

\* In English: "Draining: take each vote still owed; then the loop ends."
LoopDrain ==
    /\ lpc = "Drain"
    /\ IF outstanding = 0
       THEN lpc' = "Off" /\ UNCHANGED <<inbox, outstanding, foreign>>
       ELSE /\ inbox /= <<>>
            /\ foreign' = (foreign \/ Head(inbox) /= LoopGen)
            /\ inbox' = Tail(inbox) /\ outstanding' = outstanding - 1
            /\ UNCHANGED lpc
    /\ UNCHANGED <<refills, synced, rpc, stopping, queue, c2s, s2c, cowed, srv,
                   srvHeld, sviol, cviol>>

\* In English: "RequestNext(1), once, with no loop running and before Stop."
RequestNext ==
    /\ rpc = "idle" /\ lpc = "Off" /\ ~stopping
    /\ queue' = Append(queue, Req(1, CallGen)) /\ rpc' = "wait"
    /\ UNCHANGED <<lpc, outstanding, refills, synced, stopping, c2s, s2c, cowed,
                   inbox, srv, srvHeld, sviol, cviol, foreign>>

\* In English: "RequestNext takes its vote."
CallTake ==
    /\ rpc = "wait" /\ inbox /= <<>>
    /\ foreign' = (foreign \/ Head(inbox) /= CallGen)
    /\ inbox' = Tail(inbox) /\ rpc' = "done"
    /\ UNCHANGED <<lpc, outstanding, refills, synced, stopping, queue, c2s, s2c,
                   cowed, srv, srvHeld, sviol, cviol>>

\* In English: "Stop, once: queue MsgDone."
Stop ==
    /\ ~stopping
    /\ stopping' = TRUE /\ queue' = Append(queue, DoneMsg)
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, c2s, s2c, cowed,
                   inbox, srv, srvHeld, sviol, cviol, foreign>>

\* --- The client protocol. ------------------------------------------------

\* In English: "The send loop writes the oldest queued message: in Idle
\* (nothing owed), or, for a request from a pipelining client, at any time
\* [C2]. MsgDone is written only in Idle [C1]."
ClientWrite ==
    /\ queue /= <<>>
    /\ LET m == Head(queue) IN
       /\ \/ cowed = 0
          \/ ClientPipelines /\ m.t = "Req"
       /\ c2s' = Append(c2s, m)
       /\ cowed' = cowed + m.n
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, stopping, s2c, inbox,
                   srv, srvHeld, sviol, cviol, foreign>>

\* In English: "The client reads a vote: it must be owed; it goes to the
\* vote channel."
ClientRecv ==
    /\ s2c /= <<>>
    /\ IF cowed = 0
       THEN cviol' = TRUE /\ UNCHANGED <<cowed, inbox>>
       ELSE cowed' = cowed - 1 /\ inbox' = Append(inbox, Head(s2c))
            /\ UNCHANGED cviol
    /\ s2c' = Tail(s2c)
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, stopping, queue, c2s,
                   srv, srvHeld, sviol, foreign>>

\* --- The server. ---------------------------------------------------------

\* In English: "In Idle the server handles a held request first, then the
\* oldest message on the wire: a request with N > 0 makes it Busy with N
\* tokens; MsgDone ends the run [C1]. In Busy, a request is held (with the
\* fix) or refused (today); MsgDone is refused."
ServerRead ==
    /\ ~sviol /\ srv.st /= "Done"
    /\ \/ /\ srv.st = "Idle" /\ srvHeld /= <<>>
          /\ srv' = [st |-> "Busy", tokens |-> Head(srvHeld).n, g |-> Head(srvHeld).g]
          /\ srvHeld' = Tail(srvHeld)
          /\ UNCHANGED <<c2s, sviol>>
       \/ /\ srvHeld = <<>> \/ srv.st = "Busy"
          /\ c2s /= <<>>
          /\ LET m == Head(c2s) IN
             IF srv.st = "Idle"
             THEN IF m.t = "Done"
                  THEN srv' = [st |-> "Done", tokens |-> 0, g |-> "none"]
                       /\ UNCHANGED <<srvHeld, sviol>>
                  ELSE srv' = [st |-> "Busy", tokens |-> m.n, g |-> m.g]
                       /\ UNCHANGED <<srvHeld, sviol>>
             ELSE IF m.t = "Req" /\ ServerHoldsPipelined
                  THEN srvHeld' = Append(srvHeld, m) /\ UNCHANGED <<srv, sviol>>
                  ELSE sviol' = TRUE /\ UNCHANGED <<srv, srvHeld>>
          /\ c2s' = Tail(c2s)
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, stopping, queue, s2c,
                   cowed, inbox, cviol, foreign>>

\* In English: "In Busy the server sends one vote; the last token returns
\* it to Idle [C1]."
ServerVote ==
    /\ srv.st = "Busy"
    /\ s2c' = Append(s2c, srv.g)
    /\ srv' = IF srv.tokens = 1 THEN [st |-> "Idle", tokens |-> 0, g |-> "none"]
              ELSE [srv EXCEPT !.tokens = @ - 1]
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, stopping, queue, c2s,
                   cowed, inbox, srvHeld, sviol, cviol, foreign>>

\* In English: "Over: the server finished after MsgDone, or a side hung up."
Ended == srv.st = "Done" \/ sviol \/ cviol

Next ==
    \/ Sync \/ LoopTake \/ LoopDrain \/ RequestNext \/ CallTake \/ Stop
    \/ ClientWrite \/ ClientRecv \/ ServerRead \/ ServerVote
    \/ Ended /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "The server never refused a client message."
NoServerViolation == ~sviol

\* In English: "The client never got a vote it was not owed."
NoClientViolation == ~cviol

\* In English: "Neither reader took a vote answering the other's request."
OwnVotes == ~foreign

\* Probes, EXPECTED to be violated.
\* In English: "The server never holds a pipelined request."
ProbeNeverHeld == srvHeld = <<>>
\* In English: "RequestNext never gets its vote after a loop ran."
ProbeNoCallAfterLoop == ~(synced /\ rpc = "done")
=============================================================================
