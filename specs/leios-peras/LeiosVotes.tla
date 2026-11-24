------------------------------ MODULE LeiosVotes ------------------------------
(***************************************************************************)
(* Model `leios-peras`, LeiosVotes: the token state machine of CIP-0164, the          *)
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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Count,                 \* RequestNextCount: votes per loop request
    Depth,                 \* PipelineLimit
    MaxRefills,            \* refills the loop may queue (keeps it finite)
    ClientPipelines,       \* FALSE: gOuroboros' client; TRUE: a client following [C2]
    ServerHoldsPipelined,  \* FALSE today; TRUE: the fix, the server holds a request that arrives in Busy
    DrainOnStop            \* TRUE as in gOuroboros; FALSE is a mutation

\* Literally: "LoopGen is defined as "loop"."
LoopGen == "loop"   \* tags a request (and its votes) the loop sent
\* Literally: "CallGen is defined as "call"."
CallGen == "call"   \* tags RequestNext's request

\* In English: "A request message for n votes, tagged with who sent it."
\* Literally: "Req of n and g is defined as the record whose field t is "Req",
\*   whose field n is n, and whose field g is g."
Req(n, g) == [t |-> "Req", n |-> n, g |-> g]
\* In English: "The MsgDone message: it asks for no votes and belongs to no
\* reader."
\* Literally: "DoneMsg is defined as the record whose field t is "Done", whose
\*   field n is 0, and whose field g is "none"."
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

\* Literally: "vars is defined as the tuple of all sixteen variables."
vars == <<lpc, outstanding, refills, synced, rpc, stopping, queue, c2s, s2c,
          cowed, inbox, srv, srvHeld, sviol, cviol, foreign>>

\* In English: "The loop is off and owed nothing, nothing has been synced,
\* requested, stopped, queued, written or handed over, the server is idle and
\* holds nothing, and nothing has gone wrong."
\* Literally: "Init is defined as: lpc equals "Off" and outstanding equals 0
\*   and refills equals 0 and synced equals FALSE, and rpc equals "idle" and
\*   stopping equals FALSE, and queue equals the empty sequence and c2s equals
\*   the empty sequence and s2c equals the empty sequence and cowed equals 0
\*   and inbox equals the empty sequence, and srv equals the record whose field
\*   st is "Idle", whose field tokens is 0, and whose field g is "none", and
\*   srvHeld equals the empty sequence, and sviol equals FALSE and cviol equals
\*   FALSE and foreign equals FALSE."
Init ==
    /\ lpc = "Off" /\ outstanding = 0 /\ refills = 0 /\ synced = FALSE
    /\ rpc = "idle" /\ stopping = FALSE
    /\ queue = <<>> /\ c2s = <<>> /\ s2c = <<>> /\ cowed = 0 /\ inbox = <<>>
    /\ srv = [st |-> "Idle", tokens |-> 0, g |-> "none"] /\ srvHeld = <<>>
    /\ sviol = FALSE /\ cviol = FALSE /\ foreign = FALSE

\* In English: "Requests the loop sends as one batch."
\* Literally: "SyncBatch is defined as the function that maps every i in 1
\*   through Depth to Req of Count and LoopGen."
SyncBatch == [i \in 1..Depth |-> Req(Count, LoopGen)]

\* --- The client application. ---------------------------------------------

\* In English: "Sync, once, with no loop running and Stop not yet run."
\* Literally: "Sync is defined as: synced is not true and stopping is not true
\*   and lpc equals "Off" and rpc does not equal "wait", and queue in the next
\*   state equals queue followed by SyncBatch, and outstanding in the next
\*   state equals Depth times Count and lpc in the next state equals "Run" and
\*   synced in the next state equals TRUE, and refills, rpc, stopping, c2s,
\*   s2c, cowed, inbox, srv, srvHeld, sviol, cviol and foreign are unchanged."
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
\* Literally: "LoopTake is defined as: lpc equals "Run" and inbox does not
\*   equal the empty sequence, and foreign in the next state equals (foreign,
\*   or the head of inbox does not equal LoopGen), and inbox in the next state
\*   equals the tail of inbox, and either (lpc in the next state equals (if
\*   DrainOnStop then "Drain", else "Off"), and outstanding in the next state
\*   equals outstanding minus 1, and queue and refills are unchanged), or
\*   (stopping is true, and lpc in the next state equals (if DrainOnStop then
\*   "Drain", else "Off"), and outstanding in the next state equals outstanding
\*   minus 1, and queue and refills are unchanged), or (stopping is not true,
\*   and if outstanding minus 1 is less than or equal to (Depth minus 1) times
\*   Count and refills is less than MaxRefills, then queue in the next state
\*   equals queue with Req of Count and LoopGen appended, and outstanding in
\*   the next state equals outstanding minus 1 plus Count, and refills in the
\*   next state equals refills plus 1; else outstanding in the next state
\*   equals outstanding minus 1, and queue and refills are unchanged; and lpc
\*   in the next state equals (if outstanding in the next state equals 0 then
\*   "Off", else "Run")); and synced, rpc, stopping, c2s, s2c, cowed, srv,
\*   srvHeld, sviol and cviol are unchanged."
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
\* Literally: "LoopDrain is defined as: lpc equals "Drain", and if outstanding
\*   equals 0, then lpc in the next state equals "Off" and inbox, outstanding
\*   and foreign are unchanged; else inbox does not equal the empty sequence,
\*   and foreign in the next state equals (foreign, or the head of inbox does
\*   not equal LoopGen), and inbox in the next state equals the tail of inbox
\*   and outstanding in the next state equals outstanding minus 1, and lpc is
\*   unchanged; and refills, synced, rpc, stopping, queue, c2s, s2c, cowed,
\*   srv, srvHeld, sviol and cviol are unchanged."
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
\* Literally: "RequestNext is defined as: rpc equals "idle" and lpc equals
\*   "Off" and stopping is not true, and queue in the next state equals queue
\*   with Req of 1 and CallGen appended and rpc in the next state equals
\*   "wait", and lpc, outstanding, refills, synced, stopping, c2s, s2c, cowed,
\*   inbox, srv, srvHeld, sviol, cviol and foreign are unchanged."
RequestNext ==
    /\ rpc = "idle" /\ lpc = "Off" /\ ~stopping
    /\ queue' = Append(queue, Req(1, CallGen)) /\ rpc' = "wait"
    /\ UNCHANGED <<lpc, outstanding, refills, synced, stopping, c2s, s2c, cowed,
                   inbox, srv, srvHeld, sviol, cviol, foreign>>

\* In English: "RequestNext takes its vote."
\* Literally: "CallTake is defined as: rpc equals "wait" and inbox does not
\*   equal the empty sequence, and foreign in the next state equals (foreign,
\*   or the head of inbox does not equal CallGen), and inbox in the next state
\*   equals the tail of inbox and rpc in the next state equals "done", and lpc,
\*   outstanding, refills, synced, stopping, queue, c2s, s2c, cowed, srv,
\*   srvHeld, sviol and cviol are unchanged."
CallTake ==
    /\ rpc = "wait" /\ inbox /= <<>>
    /\ foreign' = (foreign \/ Head(inbox) /= CallGen)
    /\ inbox' = Tail(inbox) /\ rpc' = "done"
    /\ UNCHANGED <<lpc, outstanding, refills, synced, stopping, queue, c2s, s2c,
                   cowed, srv, srvHeld, sviol, cviol>>

\* In English: "Stop, once: queue MsgDone."
\* Literally: "Stop is defined as: stopping is not true, and stopping in the
\*   next state equals TRUE and queue in the next state equals queue with
\*   DoneMsg appended, and lpc, outstanding, refills, synced, rpc, c2s, s2c,
\*   cowed, inbox, srv, srvHeld, sviol, cviol and foreign are unchanged."
Stop ==
    /\ ~stopping
    /\ stopping' = TRUE /\ queue' = Append(queue, DoneMsg)
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, c2s, s2c, cowed,
                   inbox, srv, srvHeld, sviol, cviol, foreign>>

\* --- The client protocol. ------------------------------------------------

\* In English: "The send loop writes the oldest queued message: in Idle
\* (nothing owed), or, for a request from a pipelining client, at any time
\* [C2]. MsgDone is written only in Idle [C1]."
\* Literally: "ClientWrite is defined as: queue does not equal the empty
\*   sequence, and, letting m be the head of queue: (cowed equals 0, or
\*   ClientPipelines is true and m's t equals "Req"), and c2s in the next state
\*   equals c2s with m appended, and cowed in the next state equals cowed plus
\*   m's n; and queue in the next state equals the tail of queue, and lpc,
\*   outstanding, refills, synced, rpc, stopping, s2c, inbox, srv, srvHeld,
\*   sviol, cviol and foreign are unchanged."
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
\* Literally: "ClientRecv is defined as: s2c does not equal the empty sequence,
\*   and if cowed equals 0, then cviol in the next state equals TRUE and cowed
\*   and inbox are unchanged, else cowed in the next state equals cowed minus 1
\*   and inbox in the next state equals inbox with the head of s2c appended,
\*   and cviol is unchanged; and s2c in the next state equals the tail of s2c,
\*   and lpc, outstanding, refills, synced, rpc, stopping, queue, c2s, srv,
\*   srvHeld, sviol and foreign are unchanged."
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
\* Literally: "ServerRead is defined as: sviol is not true and srv's st does
\*   not equal "Done", and either (srv's st equals "Idle" and srvHeld does not
\*   equal the empty sequence, and srv in the next state equals the record
\*   whose field st is "Busy", whose field tokens is the head of srvHeld's n,
\*   and whose field g is the head of srvHeld's g, and srvHeld in the next
\*   state equals the tail of srvHeld, and c2s and sviol are unchanged), or
\*   ((srvHeld equals the empty sequence, or srv's st equals "Busy"), and c2s
\*   does not equal the empty sequence, and, letting m be the head of c2s: if
\*   srv's st equals "Idle", then (if m's t equals "Done", then srv in the next
\*   state equals the record whose field st is "Done", whose field tokens is 0,
\*   and whose field g is "none", and srvHeld and sviol are unchanged; else srv
\*   in the next state equals the record whose field st is "Busy", whose field
\*   tokens is m's n, and whose field g is m's g, and srvHeld and sviol are
\*   unchanged); else if m's t equals "Req" and ServerHoldsPipelined is true,
\*   then srvHeld in the next state equals srvHeld with m appended and srv and
\*   sviol are unchanged; else sviol in the next state equals TRUE and srv and
\*   srvHeld are unchanged; and c2s in the next state equals the tail of c2s);
\*   and lpc, outstanding, refills, synced, rpc, stopping, queue, s2c, cowed,
\*   inbox, cviol and foreign are unchanged."
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
\* Literally: "ServerVote is defined as: srv's st equals "Busy", and s2c in the
\*   next state equals s2c with srv's g appended, and srv in the next state
\*   equals (if srv's tokens equals 1 then the record whose field st is "Idle",
\*   whose field tokens is 0, and whose field g is "none", else srv except that
\*   its tokens field is the old field minus 1), and lpc, outstanding, refills,
\*   synced, rpc, stopping, queue, c2s, cowed, inbox, srvHeld, sviol, cviol and
\*   foreign are unchanged."
ServerVote ==
    /\ srv.st = "Busy"
    /\ s2c' = Append(s2c, srv.g)
    /\ srv' = IF srv.tokens = 1 THEN [st |-> "Idle", tokens |-> 0, g |-> "none"]
              ELSE [srv EXCEPT !.tokens = @ - 1]
    /\ UNCHANGED <<lpc, outstanding, refills, synced, rpc, stopping, queue, c2s,
                   cowed, inbox, srvHeld, sviol, cviol, foreign>>

\* In English: "Over: the server finished after MsgDone, or a side hung up."
\* Literally: "Ended is defined as: srv's st equals "Done", or sviol is true,
\*   or cviol is true."
Ended == srv.st = "Done" \/ sviol \/ cviol

\* In English: "A step is an application step, a client protocol step, a server
\* step, or, once over, nothing."
\* Literally: "Next is defined as: Sync, or LoopTake, or LoopDrain, or
\*   RequestNext, or CallTake, or Stop, or ClientWrite, or ClientRecv, or
\*   ServerRead, or ServerVote, or Ended is true and vars is unchanged."
Next ==
    \/ Sync \/ LoopTake \/ LoopDrain \/ RequestNext \/ CallTake \/ Stop
    \/ ClientWrite \/ ClientRecv \/ ServerRead \/ ServerVote
    \/ Ended /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "The server never refused a client message."
\* Literally: "NoServerViolation is defined as: sviol is not true."
NoServerViolation == ~sviol

\* In English: "The client never got a vote it was not owed."
\* Literally: "NoClientViolation is defined as: cviol is not true."
NoClientViolation == ~cviol

\* In English: "Neither reader took a vote answering the other's request."
\* Literally: "OwnVotes is defined as: foreign is not true."
OwnVotes == ~foreign

\* Probes, EXPECTED to be violated.
\* In English: "The server never holds a pipelined request."
\* Literally: "ProbeNeverHeld is defined as: srvHeld equals the empty
\*   sequence."
ProbeNeverHeld == srvHeld = <<>>
\* In English: "RequestNext never gets its vote after a loop ran."
\* Literally: "ProbeNoCallAfterLoop is defined as: it is not the case that
\*   (synced is true and rpc equals "done")."
ProbeNoCallAfterLoop == ~(synced /\ rpc = "done")
=============================================================================
