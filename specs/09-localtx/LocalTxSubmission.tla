------------------------- MODULE LocalTxSubmission -------------------------
(***************************************************************************)
(* The local-tx-submission mini-protocol (node-to-client): a local client  *)
(* (a wallet, cardano-cli) submits one transaction at a time and the node  *)
(* accepts or rejects it. This model covers the states and agency, which   *)
(* caller each answer reaches, the node holding its answer while its       *)
(* mempool is full, timeouts, and MsgDone with restarts.                   *)
(*                                                                         *)
(* Every rule follows the specification. Where the specification and the  *)
(* reference implementation differ, the model follows the reference and    *)
(* says so.                                                                *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e unless      *)
(* noted; specs/09-localtx/README.md has links. Paths shortened with ...   *)
(* are under ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/.  *)
(*   Specification (docs/network-spec/):                                   *)
(*   [S1] miniprotocols.tex 27-36: one side has agency at a time; an       *)
(*        unexpected message aborts the connection.                        *)
(*   [S2] miniprotocols.tex 1840-1878: states, agency, messages; the       *)
(*        client "MUST wait for a reply".                                  *)
(*   [S3] miniprotocols.tex 1880-1886: "No size limits", "No timeouts".    *)
(*   [S4] connection-manager.tex 489-503: a server-side mini-protocol that *)
(*        terminates cleanly is restarted in its initial state; 629-634: a *)
(*        node-to-client server runs in ResponderMode.                     *)
(*   Reference implementation:                                             *)
(*   [R1] .../LocalTxSubmission/Type.hs 36-55 states, 104-128 messages,    *)
(*        130-132 agency. Its StBusy comment (44-51) mentions a timeout,   *)
(*        but no time limits are defined for this protocol: Codec.hs has   *)
(*        none, and [S3] says "No timeouts".                               *)
(*   [R2] .../LocalTxSubmission/Codec.hs 107-169: the tags; each state     *)
(*        decodes only its own messages.                                   *)
(*   [R3] .../LocalTxSubmission/Client.hs 94-106, Server.hs 56-80: one     *)
(*        transaction, then Await its answer; Done only from StIdle.       *)
(*   [R4] IntersectMBO/ouroboros-consensus commit ec239d57f618:            *)
(*        .../Consensus/MiniProtocol/LocalTxSubmission/Server.hs 26-38     *)
(*        answers after addLocalTxs returns, and                           *)
(*        .../Consensus/Mempool/API.hs 142-145: adding "will block until   *)
(*        the transaction fits into the mempool".                          *)
(*                                                                         *)
(* The gOuroboros code it is compared with is protocol/localtxsubmission/  *)
(* localtxsubmission.go (StateMap, NewConfig), client.go (NewClient's      *)
(* timeout, SubmitTx and its busyMutex, the handlers), server.go, and the  *)
(* send and receive checks in protocol/protocol.go.                        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend at the top of                   *)
(* specs/01-keepalive/KeepAlive.tla. New here: SelectSeq(s, Test) keeps    *)
(* the items of list s for which Test is true; PrintT (from TLC) prints a  *)
(* value when TLC starts.                                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    MaxRuns,         \* how many runs the client may start on one connection
    MaxSubmits,      \* how many transactions the callers submit in all; they are numbered 1..MaxSubmits
    MaxFlips,        \* how many times the mempool may fill up or drain (keeps the model finite)
    RogueMessages,   \* how many arbitrary messages a misbehaving peer may inject
    ClientTimeouts,  \* TRUE: gOuroboros's client timer in StBusy (30 s by default on main;
                     \* opt-in with WithTimeout, none by default, on PR #3140)
                     \* FALSE: no timeouts, as [S3] says
    StopCancelsWait, \* TRUE: Stop ends a SubmitTx that waits for the server, then closes
                     \* the protocol without a message (a reference client is a thread
                     \* that is cancelled; it cannot send in StBusy [R4])
                     \* FALSE: Stop takes busyMutex first, so it waits for the answer
    SerialCalls,     \* TRUE: SubmitTx calls take busyMutex, so one caller waits at a time
                     \* FALSE: the mutation, with the mutex removed
    ServerRestarts,  \* TRUE: the server restarts after MsgDone [S4]. FALSE: gOuroboros today
    PrintTable       \* TRUE: print the receive table when TLC starts

Roles    == {"Client", "Server"}
States   == {"StIdle", "StBusy", "StDone"}
MsgTypes == {"MsgSubmitTx", "MsgAcceptTx", "MsgRejectTx", "MsgDone"}
Txs      == 1..MaxSubmits

\* A message is a record: its type and the transaction it is about. The
\* wire carries the transaction in MsgSubmitTx only; on MsgAcceptTx and
\* MsgRejectTx the field is bookkeeping that lets the model check who gets
\* the answer. 0 means "no transaction".
Msg(t, x) == [type |-> t, tx |-> x]
Messages  == {Msg(t, x) : t \in MsgTypes, x \in 0..MaxSubmits}

Failures == {"Violation", "TimedOut"}

\* In English: "In StIdle the client may send, in StBusy the server, in
\* StDone nobody" [S2] agency table, [R1] 130-132.
Agency(s) == CASE s = "StIdle" -> "Client"
             []   s = "StBusy" -> "Server"
             []   s = "StDone" -> "Nobody"

\* In English: "From StIdle, MsgSubmitTx goes to StBusy and MsgDone to
\* StDone; from StBusy, MsgAcceptTx and MsgRejectTx go back to StIdle"
\* [S2] figure and messages, [R1] 104-128.
Transitions ==
    { <<"StIdle", "MsgSubmitTx", "StBusy">>,
      <<"StIdle", "MsgDone",     "StDone">>,
      <<"StBusy", "MsgAcceptTx", "StIdle">>,
      <<"StBusy", "MsgRejectTx", "StIdle">> }

IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]
Peer(r)       == IF r = "Client" THEN "Server" ELSE "Client"
Awaiting(r, s) == s \in {"StIdle", "StBusy"} /\ Agency(s) = Peer(r)

\* In English: "A message with no row from s aborts the connection [S1];
\* otherwise follow the row."
Judge(s, m) == IF IsLegal(s, m.type) THEN After(s, m.type) ELSE "Violation"

RunState(s) == IF s = "StDone" THEN "StIdle" ELSE s

\* THE RECEIVE TABLE the Go tests mirror (see LocalTxMonitor.tla).
ReceiveTable(r, s, t) ==
    IF s = "StDone"
        THEN IF r = "Server" /\ ServerRestarts
                 THEN Judge("StIdle", Msg(t, 0))
                 ELSE "Held"
    ELSE IF Agency(s) = r THEN "Waits"
    ELSE Judge(s, Msg(t, 0))

ASSUME PrintTable =>
         \A r \in Roles, s \in States, t \in MsgTypes :
             PrintT(<<r, s, t, ReceiveTable(r, s, t)>>)

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in, or a failure
    inbox,      \* inbox[r]: messages sent to r that r has not read yet
    queued,     \* transactions handed to the client's send queue, not yet on the wire
    waiting,    \* callers (named by their transaction) blocked on an answer
    submits,    \* transactions submitted so far
    srvTx,      \* the transaction the server is working on
    full,       \* TRUE while the node's mempool has no room
    flips,      \* how many times the mempool filled up or drained
    misrouted,  \* TRUE once an answer reached a caller other than the one it answers
    runs,       \* client runs started so far on this connection
    rogueLeft,  \* rogue messages the misbehaving peer may still inject
    stop,       \* the client's Stop: "no", "requested" (called, not yet returned), or "done"
    cancelled   \* TRUE once Stop ended a SubmitTx that was waiting for the server

vars == <<view, inbox, queued, waiting, submits, srvTx, full, flips,
          misrouted, runs, rogueLeft, stop, cancelled>>

Init ==
    /\ view = [r \in Roles |-> "StIdle"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ queued = <<>>
    /\ waiting = {}
    /\ submits = 0
    /\ srvTx = 0
    /\ full = FALSE
    /\ flips = 0
    /\ misrouted = FALSE
    /\ runs = 1
    /\ rogueLeft = RogueMessages
    /\ stop = "no"
    /\ cancelled = FALSE

\* In English: "The server holds a transaction it cannot add yet, because
\* the mempool is full [R4]."
ServerBlocked == view["Server"] = "StBusy" /\ full

Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ view["Client"] = "Closed" /\ stop = "done"
    \/ /\ view["Client"] = "StDone" /\ runs = MaxRuns
       /\ view["Server"] = "StDone" /\ inbox["Server"] = <<>>

\* In English: "Nothing more can happen but a mempool drain the model has
\* run out of. The reference client waits here, which is correct [S2]."
WaitsForever == ServerBlocked /\ flips = MaxFlips /\ RogueMessages = 0

\* --- The client. ---------------------------------------------------------

\* In English: "A caller calls SubmitTx with the next transaction. With
\* SerialCalls it must first get busyMutex, which it can only do when no
\* other caller is waiting; the client must then be in StIdle. Without it,
\* any number of callers may wait. Either way the transaction joins the
\* client's send queue and the caller waits for an answer."
ClientSubmit ==
    /\ submits < MaxSubmits
    /\ stop = "no"
    /\ view["Client"] \in {"StIdle", "StBusy"}
    /\ SerialCalls => (waiting = {} /\ view["Client"] = "StIdle")
    /\ submits' = submits + 1
    /\ queued' = Append(queued, submits + 1)
    /\ waiting' = waiting \cup {submits + 1}
    /\ UNCHANGED <<view, inbox, srvTx, full, flips, misrouted, runs, rogueLeft,
                   stop, cancelled>>

\* In English: "The client's send loop puts the oldest queued transaction on
\* the wire once the client holds agency, in StIdle."
ClientSend ==
    /\ queued /= <<>>
    /\ view["Client"] = "StIdle"
    /\ view' = [view EXCEPT !["Client"] = "StBusy"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgSubmitTx", Head(queued)))]
    /\ queued' = Tail(queued)
    /\ UNCHANGED <<waiting, submits, srvTx, full, flips, misrouted, runs, rogueLeft,
                   stop, cancelled>>

\* In English: "A waiting SubmitTx holds busyMutex. It returns, freeing
\* it, when its answer is read, or when the protocol fails (the result
\* channel is closed)."
LockHeld == waiting /= {} /\ view["Client"] \notin Failures

\* In English: "Stop is called. It may be called at any time during a run,
\* including while a SubmitTx waits for the server."
StopRequest ==
    /\ stop = "no"
    /\ view["Client"] \in States \ {"StDone"}
    /\ stop' = "requested"
    /\ UNCHANGED <<view, inbox, queued, waiting, submits, srvTx, full, flips,
                   misrouted, runs, rogueLeft, cancelled>>

\* In English: "With StopCancelsWait, Stop ends the waiting SubmitTx; it
\* returns, freeing busyMutex."
StopCancel ==
    /\ StopCancelsWait
    /\ stop = "requested"
    /\ LockHeld
    /\ waiting' = {}
    /\ cancelled' = TRUE
    /\ UNCHANGED <<view, inbox, queued, submits, srvTx, full, flips,
                   misrouted, runs, rogueLeft, stop>>

\* In English: "Stop runs once it holds busyMutex. If it cancelled a
\* waiting SubmitTx, the client may not send (the server has agency), so it
\* closes the protocol without a message. If the protocol already failed,
\* there is nothing to send. Otherwise the client is in StIdle and sends
\* MsgDone."
ClientStop ==
    /\ stop = "requested"
    /\ ~LockHeld
    /\ stop' = "done"
    /\ \/ /\ cancelled
          /\ view["Client"] \in States
          /\ view' = [view EXCEPT !["Client"] = "Closed"]
          /\ UNCHANGED inbox
       \/ /\ view["Client"] \in Failures
          /\ UNCHANGED <<view, inbox>>
       \/ /\ ~cancelled
          /\ view["Client"] = "StIdle"
          /\ queued = <<>>
          /\ view' = [view EXCEPT !["Client"] = "StDone"]
          /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0))]
    /\ UNCHANGED <<queued, waiting, submits, srvTx, full, flips, misrouted, runs,
                   rogueLeft, cancelled>>

ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ runs' = runs + 1
    /\ stop' = "no"
    /\ UNCHANGED <<inbox, queued, waiting, submits, srvTx, full, flips, misrouted, rogueLeft,
                   cancelled>>

\* --- The server. ---------------------------------------------------------

\* In English: "In StBusy, once the transaction fits, the server accepts or
\* rejects it [R4]."
ServerAnswer(t) ==
    /\ view["Server"] = "StBusy"
    /\ ~full
    /\ view' = [view EXCEPT !["Server"] = "StIdle"]
    /\ inbox' = [inbox EXCEPT !["Client"] = Append(@, Msg(t, srvTx))]
    /\ UNCHANGED <<queued, waiting, submits, srvTx, full, flips, misrouted, runs, rogueLeft,
                   stop, cancelled>>

\* In English: "The mempool fills up or drains, a bounded number of times."
MempoolFlip ==
    /\ flips < MaxFlips
    /\ full' = ~full
    /\ flips' = flips + 1
    /\ UNCHANGED <<view, inbox, queued, waiting, submits, srvTx, misrouted, runs, rogueLeft,
                   stop, cancelled>>

\* --- Reading. ------------------------------------------------------------

\* In English: "Side r reads its oldest message when it waits for its peer,
\* or when it is a restartable server whose run is over, and moves to the
\* result. A server that reads MsgSubmitTx works on that transaction. A
\* client that reads an answer in StBusy wakes one waiting caller: with
\* several waiting, which one the Go runtime wakes is not decided, so any of
\* them may get it."
Recv(r) ==
    /\ inbox[r] /= <<>>
    /\ \/ Awaiting(r, view[r])
       \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts
    /\ LET m    == Head(inbox[r])
           s    == RunState(view[r])
           next == Judge(s, m)
       IN
         /\ view' = [view EXCEPT ![r] = next]
         /\ srvTx' = IF r = "Server" /\ m.type = "MsgSubmitTx" THEN m.tx ELSE srvTx
         /\ IF r = "Client" /\ s = "StBusy" /\ next = "StIdle" /\ waiting /= {}
                THEN \E c \in waiting :
                         /\ waiting' = waiting \ {c}
                         /\ misrouted' = (misrouted \/ c /= m.tx)
                ELSE UNCHANGED <<waiting, misrouted>>
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<queued, submits, full, flips, runs, rogueLeft, stop, cancelled>>

Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, queued, waiting, submits, srvTx, full, flips, misrouted, runs,
                   stop, cancelled>>

\* --- Timeouts. -----------------------------------------------------------
\* [S3] sets none. gOuroboros's client sets Config.Timeout on StBusy. The
\* node holds its answer while the mempool is full [R4], for as long as it
\* stays full, so any finite timer can run out.
\*
\* In English: "With client timeouts, a client waiting in StBusy with
\* nothing to read gives up while the server is blocked."
Timeout ==
    /\ ClientTimeouts
    /\ view["Client"] = "StBusy"
    /\ inbox["Client"] = <<>>
    /\ ServerBlocked
    /\ view' = [view EXCEPT !["Client"] = "TimedOut"]
    /\ UNCHANGED <<inbox, queued, waiting, submits, srvTx, full, flips, misrouted, runs, rogueLeft,
                   stop, cancelled>>

Next ==
    \/ ClientSubmit \/ ClientSend \/ ClientRestart
    \/ StopRequest \/ StopCancel \/ ClientStop
    \/ \E t \in {"MsgAcceptTx", "MsgRejectTx"} : ServerAnswer(t)
    \/ MempoolFlip
    \/ \E r \in Roles : Recv(r)
    \/ Timeout
    \/ \E r \in Roles, m \in Messages : Inject(r, m)
    \/ (Ended \/ WaitsForever) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

TypeOK ==
    /\ view \in [Roles -> States \cup Failures \cup {"Closed"}]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ queued \in Seq(Txs)
    /\ waiting \subseteq Txs
    /\ submits \in 0..MaxSubmits
    /\ srvTx \in 0..MaxSubmits
    /\ full \in BOOLEAN /\ misrouted \in BOOLEAN
    /\ flips \in 0..MaxFlips
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages
    /\ stop \in {"no", "requested", "done"}
    /\ cancelled \in BOOLEAN

NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "Every answer reaches the caller whose transaction it
\* answers." The request/response correlation: answers carry no
\* transaction ID on the wire, so only the order keeps them apart.
AnswersReachTheirCallers == ~misrouted

\* In English: "While the connection is up, a message waiting for the server
\* is one the server can read: after MsgDone, the MsgSubmitTx that starts
\* the client's next run is read by a restarted server [S4], not left on a
\* server whose run is over." (Rogue configs leave it out.)
NewRunServed ==
    (inbox["Server"] /= <<>> /\ NoFailures) => ENABLED Recv("Server")

NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "At most one transaction is on the wire or with the server
\* at a time" [S2] "It MUST wait for a reply".
OneSubmitInFlight ==
    Len(SelectSeq(inbox["Server"], LAMBDA m : m.type = "MsgSubmitTx"))
        + (IF view["Server"] = "StBusy" THEN 1 ELSE 0) <= 1

\* In English: "A Stop that has been called can always take its next step
\* without the server doing anything: it never waits on the peer." With no
\* client timeout, a Stop that waits for busyMutex while the node holds a
\* submission for a full mempool waits for as long as the mempool stays
\* full.
StopNeverWaitsOnPeer ==
    stop = "requested" => ENABLED (StopCancel \/ ClientStop)

FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

-----------------------------------------------------------------------------
(* Reachability probes: each must be violated in the passing configs. *)

\* In English: "Stop never cancels a SubmitTx the server holds for a full
\* mempool."
ProbeNoCancelledHeldSubmit == ~(cancelled /\ ServerBlocked)

\* In English: "The server never waits for room in the mempool."
ProbeServerNeverBlocks == ~ServerBlocked

\* In English: "The client never starts a second run."
ProbeNoSecondRun == runs = 1

\* In English: "No caller ever waits while its transaction is still queued
\* behind another." (Reachable only without SerialCalls.)
ProbeNoQueuedBehind == ~(view["Client"] = "StBusy" /\ queued /= <<>>)
=============================================================================
