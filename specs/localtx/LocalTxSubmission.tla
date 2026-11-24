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
(* noted; specs/localtx/README.md has links. Paths shortened with ...   *)
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
(* specs/keepalive/KeepAlive.tla. New here: SelectSeq(s, Test) keeps    *)
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

\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles    == {"Client", "Server"}
\* Literally: "States is defined as the set containing "StIdle", "StBusy" and
\*   "StDone"."
States   == {"StIdle", "StBusy", "StDone"}
\* Literally: "MsgTypes is defined as the set containing "MsgSubmitTx",
\*   "MsgAcceptTx", "MsgRejectTx" and "MsgDone"."
MsgTypes == {"MsgSubmitTx", "MsgAcceptTx", "MsgRejectTx", "MsgDone"}
\* Literally: "Txs is defined as 1 through MaxSubmits."
Txs      == 1..MaxSubmits

\* A message is a record: its type and the transaction it is about. The
\* wire carries the transaction in MsgSubmitTx only; on MsgAcceptTx and
\* MsgRejectTx the field is bookkeeping that lets the model check who gets
\* the answer. 0 means "no transaction".
\* Literally: "Msg of t and x is defined as the record whose field type is t
\*   and whose field tx is x."
Msg(t, x) == [type |-> t, tx |-> x]
\* Literally: "Messages is defined as the set of Msg of t and x, for every t
\*   that is a member of MsgTypes and every x that is a member of 0 through
\*   MaxSubmits."
Messages  == {Msg(t, x) : t \in MsgTypes, x \in 0..MaxSubmits}

\* Literally: "Failures is defined as the set containing "Violation" and
\*   "TimedOut"."
Failures == {"Violation", "TimedOut"}

\* In English: "In StIdle the client may send, in StBusy the server, in
\* StDone nobody" [S2] agency table, [R1] 130-132.
\* Literally: "Agency of s is defined as: in the case s equals "StIdle",
\*   "Client"; in the case s equals "StBusy", "Server"; in the case s equals
\*   "StDone", "Nobody"."
Agency(s) == CASE s = "StIdle" -> "Client"
             []   s = "StBusy" -> "Server"
             []   s = "StDone" -> "Nobody"

\* In English: "From StIdle, MsgSubmitTx goes to StBusy and MsgDone to
\* StDone; from StBusy, MsgAcceptTx and MsgRejectTx go back to StIdle"
\* [S2] figure and messages, [R1] 104-128.
\* Literally: "Transitions is defined as the set containing these four tuples:
\*   <<"StIdle", "MsgSubmitTx", "StBusy">>, <<"StIdle", "MsgDone", "StDone">>,
\*   <<"StBusy", "MsgAcceptTx", "StIdle">>, and <<"StBusy", "MsgRejectTx",
\*   "StIdle">>."
Transitions ==
    { <<"StIdle", "MsgSubmitTx", "StBusy">>,
      <<"StIdle", "MsgDone",     "StDone">>,
      <<"StBusy", "MsgAcceptTx", "StIdle">>,
      <<"StBusy", "MsgRejectTx", "StIdle">> }

\* In English: "Message type t is legal in state s if a row starts with s, t."
\* Literally: "IsLegal of s and t is defined as: there exists a tr that is a
\*   member of Transitions such that element 1 of tr equals s and element 2 of
\*   tr equals t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
\* In English: "The state that t moves to from s."
\* Literally: "After of s and t is defined as element 3 of the tr, chosen from
\*   Transitions, such that element 1 of tr equals s and element 2 of tr equals
\*   t."
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]
\* In English: "The peer of the client is the server, and vice versa."
\* Literally: "Peer of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
Peer(r)       == IF r = "Client" THEN "Server" ELSE "Client"
\* In English: "Side r is waiting for its peer in state s."
\* Literally: "Awaiting of r and s is defined as: s is a member of the set
\*   containing "StIdle" and "StBusy", and Agency of s equals Peer of r."
Awaiting(r, s) == s \in {"StIdle", "StBusy"} /\ Agency(s) = Peer(r)

\* In English: "A message with no row from s aborts the connection [S1];
\* otherwise follow the row."
\* Literally: "Judge of s and m is defined as: if IsLegal of s and m's type,
\*   then After of s and m's type, else "Violation"."
Judge(s, m) == IF IsLegal(s, m.type) THEN After(s, m.type) ELSE "Violation"

\* In English: "A new run starts in StIdle; otherwise a run keeps its state."
\* Literally: "RunState of s is defined as: if s equals "StDone" then "StIdle",
\*   else s."
RunState(s) == IF s = "StDone" THEN "StIdle" ELSE s

\* THE RECEIVE TABLE the Go tests mirror (see LocalTxMonitor.tla).
\* Literally: "ReceiveTable of r, s and t is defined as: if s equals "StDone",
\*   then (if r equals "Server" and ServerRestarts is true, then Judge of
\*   "StIdle" and Msg of t and 0; else "Held"); else if Agency of s equals r,
\*   then "Waits"; else Judge of s and Msg of t and 0."
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

\* Literally: "vars is defined as the tuple of all thirteen variables."
vars == <<view, inbox, queued, waiting, submits, srvTx, full, flips,
          misrouted, runs, rogueLeft, stop, cancelled>>

\* In English: "At the start both sides think StIdle, nothing is in flight,
\* queued or waiting, nothing has been submitted, the mempool has room, this is
\* run 1, the rogue peer has its full allowance, and Stop has not been called."
\* Literally: "Init is defined as: view equals the function that maps every r
\*   in Roles to "StIdle", and inbox equals the function that maps every r in
\*   Roles to the empty sequence, and queued equals the empty sequence, and
\*   waiting equals the empty set, and submits equals 0, and srvTx equals 0,
\*   and full equals FALSE, and flips equals 0, and misrouted equals FALSE, and
\*   runs equals 1, and rogueLeft equals RogueMessages, and stop equals "no",
\*   and cancelled equals FALSE."
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
\* Literally: "ServerBlocked is defined as: view of "Server" equals "StBusy",
\*   and full is true."
ServerBlocked == view["Server"] = "StBusy" /\ full

\* In English: "The connection is over when someone has hung up, or the client
\* closed after Stop, or both sides are done after the last run with nothing
\* left for the server to read."
\* Literally: "Ended is defined as: there exists an r in Roles such that view
\*   of r is a member of Failures; or view of "Client" equals "Closed" and stop
\*   equals "done"; or view of "Client" equals "StDone" and runs equals
\*   MaxRuns, and view of "Server" equals "StDone" and inbox of "Server" equals
\*   the empty sequence."
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ view["Client"] = "Closed" /\ stop = "done"
    \/ /\ view["Client"] = "StDone" /\ runs = MaxRuns
       /\ view["Server"] = "StDone" /\ inbox["Server"] = <<>>

\* In English: "Nothing more can happen but a mempool drain the model has
\* run out of. The reference client waits here, which is correct [S2]."
\* Literally: "WaitsForever is defined as: ServerBlocked is true, and flips
\*   equals MaxFlips, and RogueMessages equals 0."
WaitsForever == ServerBlocked /\ flips = MaxFlips /\ RogueMessages = 0

\* --- The client. ---------------------------------------------------------

\* In English: "A caller calls SubmitTx with the next transaction. With
\* SerialCalls it must first get busyMutex, which it can only do when no
\* other caller is waiting; the client must then be in StIdle. Without it,
\* any number of callers may wait. Either way the transaction joins the
\* client's send queue and the caller waits for an answer."
\* Literally: "ClientSubmit is defined as: submits is less than MaxSubmits, and
\*   stop equals "no", and view of "Client" is a member of the set containing
\*   "StIdle" and "StBusy", and if SerialCalls is true, then (waiting equals
\*   the empty set and view of "Client" equals "StIdle"), and submits in the
\*   next state equals submits plus 1, and queued in the next state equals
\*   queued with submits plus 1 appended, and waiting in the next state equals
\*   the union of waiting and the set containing submits plus 1, and view,
\*   inbox, srvTx, full, flips, misrouted, runs, rogueLeft, stop and cancelled
\*   are unchanged."
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
\* Literally: "ClientSend is defined as: queued does not equal the empty
\*   sequence, and view of "Client" equals "StIdle", and view in the next state
\*   equals view except that its "Client" entry is "StBusy", and inbox in the
\*   next state equals inbox except that its "Server" entry is the old entry
\*   with Msg of "MsgSubmitTx" and the head of queued appended, and queued in
\*   the next state equals the tail of queued, and waiting, submits, srvTx,
\*   full, flips, misrouted, runs, rogueLeft, stop and cancelled are
\*   unchanged."
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
\* Literally: "LockHeld is defined as: waiting does not equal the empty set,
\*   and view of "Client" is not a member of Failures."
LockHeld == waiting /= {} /\ view["Client"] \notin Failures

\* In English: "Stop is called. It may be called at any time during a run,
\* including while a SubmitTx waits for the server."
\* Literally: "StopRequest is defined as: stop equals "no", and view of
\*   "Client" is a member of States without the members of the set containing
\*   "StDone", and stop in the next state equals "requested", and view, inbox,
\*   queued, waiting, submits, srvTx, full, flips, misrouted, runs, rogueLeft
\*   and cancelled are unchanged."
StopRequest ==
    /\ stop = "no"
    /\ view["Client"] \in States \ {"StDone"}
    /\ stop' = "requested"
    /\ UNCHANGED <<view, inbox, queued, waiting, submits, srvTx, full, flips,
                   misrouted, runs, rogueLeft, cancelled>>

\* In English: "With StopCancelsWait, Stop ends the waiting SubmitTx; it
\* returns, freeing busyMutex."
\* Literally: "StopCancel is defined as: StopCancelsWait is true, and stop
\*   equals "requested", and LockHeld is true, and waiting in the next state
\*   equals the empty set, and cancelled in the next state equals TRUE, and
\*   view, inbox, queued, submits, srvTx, full, flips, misrouted, runs,
\*   rogueLeft and stop are unchanged."
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
\* Literally: "ClientStop is defined as: stop equals "requested", and LockHeld
\*   is not true, and stop in the next state equals "done", and either
\*   (cancelled is true, and view of "Client" is a member of States, and view
\*   in the next state equals view except that its "Client" entry is "Closed",
\*   and inbox is unchanged), or (view of "Client" is a member of Failures, and
\*   view and inbox are unchanged), or (cancelled is not true, and view of
\*   "Client" equals "StIdle", and queued equals the empty sequence, and view
\*   in the next state equals view except that its "Client" entry is "StDone",
\*   and inbox in the next state equals inbox except that its "Server" entry is
\*   the old entry with Msg of "MsgDone" and 0 appended); and queued, waiting,
\*   submits, srvTx, full, flips, misrouted, runs, rogueLeft and cancelled are
\*   unchanged."
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

\* In English: "When the client's run is over and it may start another, it
\* does: it believes StIdle, one more run has started, and Stop may be called
\* again."
\* Literally: "ClientRestart is defined as: view of "Client" equals "StDone",
\*   and runs is less than MaxRuns, and view in the next state equals view
\*   except that its "Client" entry is "StIdle", and runs in the next state
\*   equals runs plus 1, and stop in the next state equals "no", and inbox,
\*   queued, waiting, submits, srvTx, full, flips, misrouted, rogueLeft and
\*   cancelled are unchanged."
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
\* Literally: "ServerAnswer of t is defined as: view of "Server" equals
\*   "StBusy", and full is not true, and view in the next state equals view
\*   except that its "Server" entry is "StIdle", and inbox in the next state
\*   equals inbox except that its "Client" entry is the old entry with Msg of t
\*   and srvTx appended, and queued, waiting, submits, srvTx, full, flips,
\*   misrouted, runs, rogueLeft, stop and cancelled are unchanged."
ServerAnswer(t) ==
    /\ view["Server"] = "StBusy"
    /\ ~full
    /\ view' = [view EXCEPT !["Server"] = "StIdle"]
    /\ inbox' = [inbox EXCEPT !["Client"] = Append(@, Msg(t, srvTx))]
    /\ UNCHANGED <<queued, waiting, submits, srvTx, full, flips, misrouted, runs, rogueLeft,
                   stop, cancelled>>

\* In English: "The mempool fills up or drains, a bounded number of times."
\* Literally: "MempoolFlip is defined as: flips is less than MaxFlips, and full
\*   in the next state equals: full is not true, and flips in the next state
\*   equals flips plus 1, and view, inbox, queued, waiting, submits, srvTx,
\*   misrouted, runs, rogueLeft, stop and cancelled are unchanged."
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
\* Literally: "Recv of r is defined as: inbox of r does not equal the empty
\*   sequence, and (Awaiting of r and view of r, or r equals "Server" and view
\*   of r equals "StDone" and ServerRestarts is true), and, letting m be the
\*   head of inbox of r, s be RunState of view of r, and next be Judge of s and
\*   m: view in the next state equals view except that its r entry is next; and
\*   srvTx in the next state equals (if r equals "Server" and m's type equals
\*   "MsgSubmitTx" then m's tx, else srvTx); and if r equals "Client" and s
\*   equals "StBusy" and next equals "StIdle" and waiting does not equal the
\*   empty set, then there exists a c in waiting such that waiting in the next
\*   state equals waiting without the members of the set containing c, and
\*   misrouted in the next state equals (misrouted, or c does not equal m's
\*   tx); else waiting and misrouted are unchanged; and inbox in the next state
\*   equals inbox except that its r entry is the tail of the old entry; and
\*   queued, submits, full, flips, runs, rogueLeft, stop and cancelled are
\*   unchanged."
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

\* In English: "While it has allowance left, the rogue peer can put any message
\* m into r's inbox at any time."
\* Literally: "Inject of r and m is defined as: rogueLeft is greater than 0,
\*   and inbox in the next state equals inbox except that its r entry is the
\*   old entry with m appended, and rogueLeft in the next state equals
\*   rogueLeft minus 1, and view, queued, waiting, submits, srvTx, full, flips,
\*   misrouted, runs, stop and cancelled are unchanged."
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
\* Literally: "Timeout is defined as: ClientTimeouts is true, and view of
\*   "Client" equals "StBusy", and inbox of "Client" equals the empty sequence,
\*   and ServerBlocked is true, and view in the next state equals view except
\*   that its "Client" entry is "TimedOut", and inbox, queued, waiting,
\*   submits, srvTx, full, flips, misrouted, runs, rogueLeft, stop and
\*   cancelled are unchanged."
Timeout ==
    /\ ClientTimeouts
    /\ view["Client"] = "StBusy"
    /\ inbox["Client"] = <<>>
    /\ ServerBlocked
    /\ view' = [view EXCEPT !["Client"] = "TimedOut"]
    /\ UNCHANGED <<inbox, queued, waiting, submits, srvTx, full, flips, misrouted, runs, rogueLeft,
                   stop, cancelled>>

\* In English: "A step is a client action, a Stop step, a server answer, a
\* mempool flip, a read, a timeout, a rogue injection, or, once the connection
\* is over or can only wait, nothing."
\* Literally: "Next is defined as: ClientSubmit, or ClientSend, or
\*   ClientRestart, or StopRequest, or StopCancel, or ClientStop, or there
\*   exists a t in the set containing "MsgAcceptTx" and "MsgRejectTx" such that
\*   ServerAnswer of t, or MempoolFlip, or there exists an r in Roles such that
\*   Recv of r, or Timeout, or there exists an r in Roles and an m in Messages
\*   such that Inject of r and m, or (Ended or WaitsForever) and vars is
\*   unchanged."
Next ==
    \/ ClientSubmit \/ ClientSend \/ ClientRestart
    \/ StopRequest \/ StopCancel \/ ClientStop
    \/ \E t \in {"MsgAcceptTx", "MsgRejectTx"} : ServerAnswer(t)
    \/ MempoolFlip
    \/ \E r \in Roles : Recv(r)
    \/ Timeout
    \/ \E r \in Roles, m \in Messages : Inject(r, m)
    \/ (Ended \/ WaitsForever) /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: view is a member of the set of functions
\*   from Roles to the union of States, Failures and the set containing
\*   "Closed", and inbox is a member of the set of functions from Roles to the
\*   set of sequences of members of Messages, and queued is a member of the set
\*   of sequences of members of Txs, and waiting is a subset of Txs, and
\*   submits is a member of 0 through MaxSubmits, and srvTx is a member of 0
\*   through MaxSubmits, and full is a member of BOOLEAN and misrouted is a
\*   member of BOOLEAN, and flips is a member of 0 through MaxFlips, and runs
\*   is a member of 1 through MaxRuns, and rogueLeft is a member of 0 through
\*   RogueMessages, and stop is a member of the set containing "no",
\*   "requested" and "done", and cancelled is a member of BOOLEAN."
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

\* In English: "No side has hung up."
\* Literally: "NoFailures is defined as: for all r in Roles, view of r is not a
\*   member of Failures."
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "Every answer reaches the caller whose transaction it
\* answers." The request/response correlation: answers carry no
\* transaction ID on the wire, so only the order keeps them apart.
\* Literally: "AnswersReachTheirCallers is defined as: misrouted is not true."
AnswersReachTheirCallers == ~misrouted

\* In English: "While the connection is up, a message waiting for the server
\* is one the server can read: after MsgDone, the MsgSubmitTx that starts
\* the client's next run is read by a restarted server [S4], not left on a
\* server whose run is over." (Rogue configs leave it out.)
\* Literally: "NewRunServed is defined as: if inbox of "Server" does not equal
\*   the empty sequence and NoFailures is true, then Recv of "Server" is
\*   enabled."
NewRunServed ==
    (inbox["Server"] /= <<>> /\ NoFailures) => ENABLED Recv("Server")

\* In English: "Never do both sides believe they may send."
\* Literally: "NeverBothHaveAgency is defined as: it is not the case that (view
\*   of "Client" is a member of States and Agency of view of "Client" equals
\*   "Client", and view of "Server" is a member of States and Agency of view of
\*   "Server" equals "Server")."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "At most one transaction is on the wire or with the server
\* at a time" [S2] "It MUST wait for a reply".
\* Literally: "OneSubmitInFlight is defined as: the length of the subsequence
\*   of inbox of "Server" made of every m such that m's type equals
\*   "MsgSubmitTx", plus (if view of "Server" equals "StBusy" then 1, else 0),
\*   is less than or equal to 1."
OneSubmitInFlight ==
    Len(SelectSeq(inbox["Server"], LAMBDA m : m.type = "MsgSubmitTx"))
        + (IF view["Server"] = "StBusy" THEN 1 ELSE 0) <= 1

\* In English: "A Stop that has been called can always take its next step
\* without the server doing anything: it never waits on the peer." With no
\* client timeout, a Stop that waits for busyMutex while the node holds a
\* submission for a full mempool waits for as long as the mempool stays
\* full.
\* Literally: "StopNeverWaitsOnPeer is defined as: if stop equals "requested",
\*   then (StopCancel or ClientStop) is enabled."
StopNeverWaitsOnPeer ==
    stop = "requested" => ENABLED (StopCancel \/ ClientStop)

\* In English: "A side that has hung up stays hung up."
\* Literally: "FailuresAreFinal is defined as: always, every step is a step in
\*   which, for all r in Roles, if view of r is a member of Failures, then view
\*   in the next state of r equals view of r; or a step that leaves vars
\*   unchanged."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

-----------------------------------------------------------------------------
(* Reachability probes: each must be violated in the passing configs. *)

\* In English: "Stop never cancels a SubmitTx the server holds for a full
\* mempool."
\* Literally: "ProbeNoCancelledHeldSubmit is defined as: it is not the case
\*   that (cancelled is true and ServerBlocked is true)."
ProbeNoCancelledHeldSubmit == ~(cancelled /\ ServerBlocked)

\* In English: "The server never waits for room in the mempool."
\* Literally: "ProbeServerNeverBlocks is defined as: ServerBlocked is not
\*   true."
ProbeServerNeverBlocks == ~ServerBlocked

\* In English: "The client never starts a second run."
\* Literally: "ProbeNoSecondRun is defined as: runs equals 1."
ProbeNoSecondRun == runs = 1

\* In English: "No caller ever waits while its transaction is still queued
\* behind another." (Reachable only without SerialCalls.)
\* Literally: "ProbeNoQueuedBehind is defined as: it is not the case that (view
\*   of "Client" equals "StBusy" and queued does not equal the empty
\*   sequence)."
ProbeNoQueuedBehind == ~(view["Client"] = "StBusy" /\ queued /= <<>>)
=============================================================================
