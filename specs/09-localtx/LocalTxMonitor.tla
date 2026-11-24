--------------------------- MODULE LocalTxMonitor ---------------------------
(***************************************************************************)
(* The local-tx-monitor mini-protocol (node-to-client): a local client     *)
(* acquires a snapshot of the node's mempool, asks questions about that    *)
(* snapshot, and releases it. This model covers the states and agency, the *)
(* busy state's kind (which reply is legal), the acquire and release rules *)
(* for snapshots, MsgAwaitAcquire, timeouts, MsgDone and restarts, and the *)
(* gOuroboros client's Stop.                                               *)
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
(*   [S2] miniprotocols.tex 2055-2103: local-tx-monitor states, the        *)
(*        transition figure, and the agency table.                         *)
(*   [S3] miniprotocols.tex 2105-2166: the messages and the transition     *)
(*        table. Line 2157 lists MsgReplyNextTx as the answer in           *)
(*        StBusy HasTx; the figure (2086) and [R1] say MsgReplyHasTx.      *)
(*   [S4] miniprotocols.tex 2168-2174: "No size limits", "No timeouts".    *)
(*   [S5] connection-manager.tex 489-503: a server-side mini-protocol that *)
(*        terminates cleanly is restarted in its initial state; 629-634: a *)
(*        node-to-client server runs in ResponderMode.                     *)
(*   Reference implementation:                                             *)
(*   [R1] .../LocalTxMonitor/Type.hs 70-95 states, 130-141 StBusyKind,     *)
(*        200-283 messages, 285-289 agency. MsgAwaitAcquire (217-224):     *)
(*        "await for a new snapshot different from the one currently       *)
(*        acquired ... the caller will block until a new snapshot is       *)
(*        available". StBusy (88-90): "It must respond, there's no         *)
(*        timeout".                                                        *)
(*   [R2] .../LocalTxMonitor/Codec.hs 66-69: MsgAcquire and               *)
(*        MsgAwaitAcquire are both [1] on the wire; 123-174: each busy     *)
(*        kind decodes only its own reply; 140-141: MsgGetMeasures is      *)
(*        decoded in StAcquired at every version.                          *)
(*   [R3] cardano-diffusion/protocols/lib/Cardano/Network/Protocol/        *)
(*        LocalTxMonitor/Codec.hs 41-42: the node always uses V2, so       *)
(*        MsgGetMeasures is always understood.                             *)
(*   [R4] .../LocalTxMonitor/Server.hs 117-191, Client.hs 121-166: the     *)
(*        typed peers; Done is only reachable from StIdle.                 *)
(*   [R6] .../LocalTxMonitor/Codec.hs 57, 78-86, 102-113: the encoder      *)
(*        sends MsgGetMeasures and MsgReplyGetMeasures only at             *)
(*        LocalTxMonitor_V2, which Type.hs 316-317 ties to                 *)
(*        NodeToClientV_20 and later (cardano-diffusion/api/lib/Cardano/   *)
(*        Network/NodeToClient/Version.hs 58-59: V_20 "added               *)
(*        MsgGetMeasures and MsgReplyGetMeasures").                        *)
(*   [R7] ouroboros-network/framework/lib/Ouroboros/Network/               *)
(*        InboundGovernor.hs 455-470: a responder that ended cleanly is    *)
(*        restarted (TrResponderRestarted); ouroboros-network/lib/         *)
(*        Ouroboros/Network/Diffusion.hs 402-418 runs the node-to-client   *)
(*        server under an inbound governor too.                            *)
(*   [R5] IntersectMBO/ouroboros-consensus commit ec239d57f618,            *)
(*        ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/ *)
(*        MiniProtocol/LocalTxMonitor/Server.hs 85-104: the node answers   *)
(*        MsgAwaitAcquire only once the mempool snapshot differs from the  *)
(*        held one (`check (not (snapshot `isSameSnapshot` snapshot'))`).  *)
(*                                                                         *)
(* The gOuroboros code it is compared with is protocol/localtxmonitor/     *)
(* localtxmonitor.go (StateMap, matchQuery, matchReply, NewConfig),        *)
(* client.go (NewClient timeouts, Acquire, Stop, the query calls),         *)
(* server.go (handleAcquire, the query handlers), and the send and         *)
(* receive checks in protocol/protocol.go.                                 *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend at the top of                   *)
(* specs/01-keepalive/KeepAlive.tla. Nothing new is used here except       *)
(* PrintT (from the TLC module), which prints a value when TLC starts.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC   \* numbers, lists, and PrintT

CONSTANTS
    MaxRuns,             \* how many runs the client may start on one connection
    MaxQueries,          \* how many queries the client may send in all (keeps the model finite)
    MaxChanges,          \* how many times the mempool may change (keeps the model finite)
    RogueMessages,       \* how many arbitrary messages a misbehaving peer may inject
    BusyKinds,           \* TRUE: Busy remembers its query, so only the matching reply is legal [R1][R2]
                         \* FALSE: one Busy state that takes any reply (gOuroboros before matchReply)
    AwaitWaitsForChange, \* TRUE: the server answers MsgAwaitAcquire only once the mempool changed [R5]
                         \* FALSE: gOuroboros's server, which answers at once
    ClientTimeouts,      \* TRUE: gOuroboros's client timers in StAcquiring and StBusy
                         \* FALSE: no timeouts, as [S4] and [R1] say
    StopReleases,        \* TRUE: Stop from StAcquired sends MsgRelease then MsgDone
                         \* FALSE: gOuroboros's Stop, which sends MsgDone from any state
    ClientSendsMeasures, \* TRUE: the client may send MsgGetMeasures (a reference client may)
                         \* FALSE: gOuroboros's client, which has no call for it
    ServerKnowsMeasures, \* TRUE: the server understands MsgGetMeasures [R2][R3]
                         \* FALSE: gOuroboros's server, which cannot decode it
    ServerRestarts,      \* TRUE: the server restarts after MsgDone [S5][R7]. FALSE: gOuroboros today
    ClientChecksVersion, \* TRUE: the client sends MsgGetMeasures only at NodeToClientV_20 or later [R6]
                         \* FALSE: it sends it whatever version the handshake agreed
    NegotiatedV20,       \* TRUE: the handshake agreed NodeToClientV_20 or later [R6]
                         \* FALSE: an older version, which an older node may be speaking
    PrintTable           \* TRUE: print the receive table when TLC starts

Roles == {"Client", "Server"}

\* The busy state's kind is part of the state's name [R1] StBusyKind.
BusyStates == {"StBusyNextTx", "StBusyHasTx", "StBusyGetSizes", "StBusyGetMeasures"}
States == {"StIdle", "StAcquiring", "StAcquired", "StDone"} \cup BusyStates

\* "MsgAcquire" sent in StAcquired is MsgAwaitAcquire: the two are the same
\* bytes on the wire [R2], so a receiver tells them apart only by its state.
Queries == {"MsgNextTx", "MsgHasTx", "MsgGetSizes", "MsgGetMeasures"}
Replies == {"MsgReplyNextTx", "MsgReplyHasTx", "MsgReplyGetSizes", "MsgReplyGetMeasures"}
MsgTypes == {"MsgAcquire", "MsgAcquired", "MsgRelease", "MsgDone"} \cup Queries \cup Replies

\* In English: "The busy state a query leads to, and the one reply that
\* answers it." [R1] 226-273.
BusyOf(q) == CASE q = "MsgNextTx"      -> "StBusyNextTx"
             []   q = "MsgHasTx"       -> "StBusyHasTx"
             []   q = "MsgGetSizes"    -> "StBusyGetSizes"
             []   q = "MsgGetMeasures" -> "StBusyGetMeasures"
ReplyOf(q) == CASE q = "MsgNextTx"      -> "MsgReplyNextTx"
              []   q = "MsgHasTx"       -> "MsgReplyHasTx"
              []   q = "MsgGetSizes"    -> "MsgReplyGetSizes"
              []   q = "MsgGetMeasures" -> "MsgReplyGetMeasures"
\* In English: "The query that put the protocol in busy state s."
QueryOf(s) == CHOOSE q \in Queries : BusyOf(q) = s

\* Snapshots are numbered by how many times the mempool has changed: two
\* snapshots with the same number are the same snapshot [R5] isSameSnapshot.
Snaps == 0..MaxChanges

\* A message is a record: its type, and the snapshot number, which only
\* MsgAcquired uses (it stands for the slot number it carries).
Msg(t, n) == [type |-> t, snap |-> n]
Messages == {Msg(t, n) : t \in MsgTypes, n \in Snaps}

Failures == {"Violation", "TimedOut"}

\* In English: "Who may send in each state" [S2] agency table, [R1] 285-289.
Agency(s) == CASE s \in {"StIdle", "StAcquired"}    -> "Client"
             []   s \in {"StAcquiring"} \cup BusyStates -> "Server"
             []   s = "StDone"                      -> "Nobody"

\* The protocol as <<from-state, message, to-state>> rows [S3] table, with
\* StBusy HasTx answered by MsgReplyHasTx as [R1] says. In English:
\*   "From StIdle, MsgAcquire goes to StAcquiring and MsgDone to StDone.
\*    From StAcquiring, MsgAcquired goes to StAcquired.
\*    From StAcquired, MsgAcquire (that is, MsgAwaitAcquire) goes back to
\*    StAcquiring, MsgRelease to StIdle, and each query to its busy state.
\*    From each busy state, its own reply goes back to StAcquired."
Transitions ==
    { <<"StIdle",      "MsgAcquire",  "StAcquiring">>,
      <<"StIdle",      "MsgDone",     "StDone">>,
      <<"StAcquiring", "MsgAcquired", "StAcquired">>,
      <<"StAcquired",  "MsgAcquire",  "StAcquiring">>,
      <<"StAcquired",  "MsgRelease",  "StIdle">> }
    \cup { <<"StAcquired", q, BusyOf(q)>> : q \in Queries }
    \cup { <<BusyOf(q), ReplyOf(q), "StAcquired">> : q \in Queries }

\* In English: "Message type t is legal in state s if some row starts with
\* s and t", and "After(s, t) is where that row leads".
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s."
Awaiting(r, s) == s \in States \ {"StDone"} /\ Agency(s) = Peer(r)

(***************************************************************************)
(* JUDGING A MESSAGE that side r reads in state s [S1]:                    *)
(*   - A server that does not know MsgGetMeasures cannot even decode it.   *)
(*   - Without busy kinds, any reply ends any busy state (the mutation).   *)
(*   - A message with no row from s aborts the connection.                 *)
(*   - Otherwise follow the row.                                           *)
(***************************************************************************)
Judge(r, s, m) ==
    IF r = "Server" /\ m.type = "MsgGetMeasures" /\ ~ServerKnowsMeasures
                                    THEN "Violation"     \* undecodable: hang up
    ELSE IF ~BusyKinds /\ s \in BusyStates /\ m.type \in Replies
                                    THEN "StAcquired"    \* the mutation: any reply will do
    ELSE IF ~IsLegal(s, m.type)     THEN "Violation"     \* not legal here: hang up
    ELSE After(s, m.type)                                \* otherwise: follow the row

\* In English: "A new run starts in StIdle."
RunState(s) == IF s = "StDone" THEN "StIdle" ELSE s

(***************************************************************************)
(* THE RECEIVE TABLE the Go tests mirror: the outcome for every role,      *)
(* state, and message type. "Waits": the reader holds agency and does not  *)
(* read yet (see Model 01, [S8] there). "Held": the client's run is over   *)
(* and nothing reads it. After MsgDone a server restarts in StIdle [S5].   *)
(***************************************************************************)
ReceiveTable(r, s, t) ==
    IF s = "StDone"
        THEN IF r = "Server" /\ ServerRestarts
                 THEN Judge(r, "StIdle", Msg(t, 0))
                 ELSE "Held"
    ELSE IF Agency(s) = r THEN "Waits"
    ELSE Judge(r, s, Msg(t, 0))

\* In English: "If PrintTable is on, print every row of the receive table."
ASSUME PrintTable =>
         \A r \in Roles, s \in States, t \in MsgTypes :
             PrintT(<<r, s, t, ReceiveTable(r, s, t)>>)

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in, or a failure
    inbox,      \* inbox[r]: messages sent to r that r has not read yet
    mempool,    \* the node's current mempool snapshot number
    srvSnap,    \* the snapshot the server holds (last sent in MsgAcquired)
    srvAwait,   \* TRUE while the server serves a MsgAwaitAcquire, not a MsgAcquire
    cliSnap,    \* the snapshot the client last acquired
    cliAwait,   \* TRUE while the client's outstanding acquire is an MsgAwaitAcquire
    sameSnap,   \* TRUE once an MsgAwaitAcquire was answered with the held snapshot
    result,     \* <<query, reply>> the client last handed to its caller
    queries,    \* queries sent so far
    runs,       \* client runs started so far on this connection
    rogueLeft   \* rogue messages the misbehaving peer may still inject

vars == <<view, inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
          sameSnap, result, queries, runs, rogueLeft>>

\* In English: "At the start both sides think it is StIdle, nothing is in
\* flight, the mempool is snapshot 0, and nothing has been answered."
Init ==
    /\ view = [r \in Roles |-> "StIdle"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ mempool = 0
    /\ srvSnap = 0
    /\ srvAwait = FALSE
    /\ cliSnap = 0
    /\ cliAwait = FALSE
    /\ sameSnap = FALSE
    /\ result = <<"none", "none">>
    /\ queries = 0
    /\ runs = 1
    /\ rogueLeft = RogueMessages

\* In English: "The server is waiting, as [R5] says it must, for the mempool
\* to change: it serves an MsgAwaitAcquire and the mempool is still the
\* snapshot it holds."
ServerBlocked ==
    /\ view["Server"] = "StAcquiring"
    /\ srvAwait
    /\ AwaitWaitsForChange
    /\ mempool = srvSnap

\* In English: "The connection is over when someone hung up, or both sides
\* are done and the client may start no more runs."
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ /\ view["Client"] = "StDone" /\ runs = MaxRuns
       /\ view["Server"] = "StDone" /\ inbox["Server"] = <<>>

\* In English: "Nothing more can happen but the wait for a mempool change
\* the model has run out of. The reference client blocks here, which is
\* correct [R1] MsgAwaitAcquire."
WaitsForever ==
    /\ ServerBlocked
    /\ mempool = MaxChanges
    /\ RogueMessages = 0

\* --- The client. Each send needs the client to hold agency [S1]. ----------

\* In English: "From StIdle or StAcquired the client can send MsgAcquire.
\* From StAcquired that is MsgAwaitAcquire [R2]; gOuroboros's Acquire()
\* sends the same bytes in both states."
ClientAcquire ==
    /\ view["Client"] \in {"StIdle", "StAcquired"}
    /\ cliAwait' = (view["Client"] = "StAcquired")      \* next, remember whether this is an await
    /\ view' = [view EXCEPT !["Client"] = "StAcquiring"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgAcquire", 0))]
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, sameSnap, result,
                   queries, runs, rogueLeft>>

\* In English: "The client may send MsgGetMeasures: it has a call for it,
\* and either the handshake agreed NodeToClientV_20 or later or the client
\* does not check" [R6].
MayAskMeasures == ClientSendsMeasures /\ (NegotiatedV20 \/ ~ClientChecksVersion)

\* In English: "From StAcquired, with queries left, the client can send a
\* query q (MsgGetMeasures only if it may, above). It then waits in q's busy
\* state."
ClientQuery(q) ==
    /\ view["Client"] = "StAcquired"
    /\ queries < MaxQueries
    /\ q /= "MsgGetMeasures" \/ MayAskMeasures
    /\ view' = [view EXCEPT !["Client"] = BusyOf(q)]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg(q, 0))]
    /\ queries' = queries + 1
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, runs, rogueLeft>>

\* In English: "From StAcquired the client can release the snapshot."
ClientRelease ==
    /\ view["Client"] = "StAcquired"
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgRelease", 0))]
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, queries, runs, rogueLeft>>

\* In English: "Stop. From StIdle the client sends MsgDone [R4]. From
\* StAcquired: with StopReleases it sends MsgRelease and then MsgDone; without
\* it (gOuroboros's Stop) it tries to send MsgDone, which has no row from
\* StAcquired, so its own send loop refuses it and tears the connection
\* down." Stop waits for the call in progress, so it starts only while the
\* client holds agency.
ClientStop ==
    \/ /\ view["Client"] = "StIdle"
       /\ view' = [view EXCEPT !["Client"] = "StDone"]
       /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0))]
    \/ /\ view["Client"] = "StAcquired"
       /\ StopReleases
       /\ view' = [view EXCEPT !["Client"] = "StDone"]
       /\ inbox' = [inbox EXCEPT !["Server"] =
                        @ \o <<Msg("MsgRelease", 0), Msg("MsgDone", 0)>>]
    \/ /\ view["Client"] = "StAcquired"
       /\ ~StopReleases
       /\ view' = [view EXCEPT !["Client"] = "Violation"]   \* refused by its own send loop
       /\ UNCHANGED inbox
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, queries, runs, rogueLeft>>

\* In English: "When the client's run is over and it may start another, it
\* can."
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ runs' = runs + 1
    /\ UNCHANGED <<inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, rogueLeft>>

\* --- The server. ---------------------------------------------------------

\* In English: "In StAcquiring the server can answer MsgAcquired with the
\* current snapshot, unless it serves an MsgAwaitAcquire and must wait for
\* the mempool to change [R5]."
ServerAcquired ==
    /\ view["Server"] = "StAcquiring"
    /\ ~ServerBlocked
    /\ view' = [view EXCEPT !["Server"] = "StAcquired"]
    /\ inbox' = [inbox EXCEPT !["Client"] = Append(@, Msg("MsgAcquired", mempool))]
    /\ srvSnap' = mempool
    /\ srvAwait' = FALSE
    /\ UNCHANGED <<mempool, cliSnap, cliAwait, sameSnap, result, queries,
                   runs, rogueLeft>>

\* In English: "In a busy state the server answers with that state's reply
\* [R4] ServerStBusy."
ServerReply ==
    /\ view["Server"] \in BusyStates
    /\ view' = [view EXCEPT !["Server"] = "StAcquired"]
    /\ inbox' = [inbox EXCEPT !["Client"] =
                     Append(@, Msg(ReplyOf(QueryOf(view["Server"])), 0))]
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, queries, runs, rogueLeft>>

\* --- The node's mempool. -------------------------------------------------

\* In English: "Transactions come and go: the mempool can change, a bounded
\* number of times."
MempoolChange ==
    /\ mempool < MaxChanges
    /\ mempool' = mempool + 1
    /\ UNCHANGED <<view, inbox, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, rogueLeft>>

\* --- Reading. ------------------------------------------------------------

\* In English: "Side r reads the oldest message in its inbox when it waits
\* for its peer, or when it is a restartable server whose run is over. It
\* judges the message against its state and moves to the result. A server
\* that reads MsgAcquire notes whether it came in StAcquired (an await). A
\* client that reads MsgAcquired notes the snapshot, and whether an await
\* was answered with the snapshot it already held. A client that reads a
\* reply in a busy state hands <<query, reply>> to its caller."
Recv(r) ==
    /\ inbox[r] /= <<>>
    /\ \/ Awaiting(r, view[r])
       \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts
    /\ LET m    == Head(inbox[r])
           s    == RunState(view[r])
           next == Judge(r, s, m)
       IN
         /\ view' = [view EXCEPT ![r] = next]
         /\ srvAwait' = IF r = "Server" /\ m.type = "MsgAcquire"
                            THEN s = "StAcquired" ELSE srvAwait
         /\ cliSnap' = IF r = "Client" /\ next = "StAcquired" /\ m.type = "MsgAcquired"
                           THEN m.snap ELSE cliSnap
         /\ sameSnap' = \/ sameSnap
                        \/ /\ r = "Client" /\ m.type = "MsgAcquired"
                           /\ next = "StAcquired" /\ cliAwait /\ m.snap = cliSnap
         /\ result' = IF r = "Client" /\ s \in BusyStates /\ next = "StAcquired"
                          THEN <<QueryOf(s), m.type>> ELSE result
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<mempool, srvSnap, cliAwait, queries, runs, rogueLeft>>

\* In English: "While the rogue peer has allowance left, it can put any
\* message into r's inbox."
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs>>

\* --- Timeouts. -----------------------------------------------------------
\* [S4] and [R1] set no timeouts. gOuroboros's client sets AcquireTimeout on
\* StAcquiring and QueryTimeout on StBusy. The model has no clock; it lets
\* such a timer fire while the server waits, as it should, for the mempool
\* to change: that wait has no bound, so any finite timer can run out.
\*
\* In English: "With client timeouts, a client waiting in StAcquiring or a
\* busy state, with nothing to read, gives up while the server is blocked."
Timeout ==
    /\ ClientTimeouts
    /\ view["Client"] \in {"StAcquiring"} \cup BusyStates
    /\ inbox["Client"] = <<>>
    /\ ServerBlocked
    /\ view' = [view EXCEPT !["Client"] = "TimedOut"]
    /\ UNCHANGED <<inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, rogueLeft>>

\* In English: "A step is a client call, a server answer, a mempool change,
\* a read, a timeout, a rogue injection, or, once nothing more can happen,
\* nothing changing (so that TLC does not report the end as a deadlock)."
Next ==
    \/ ClientAcquire \/ ClientRelease \/ ClientStop \/ ClientRestart
    \/ \E q \in Queries : ClientQuery(q)
    \/ ServerAcquired \/ ServerReply
    \/ MempoolChange
    \/ \E r \in Roles : Recv(r)
    \/ Timeout
    \/ \E r \in Roles, m \in Messages : Inject(r, m)
    \/ (Ended \/ WaitsForever) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

TypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ mempool \in Snaps /\ srvSnap \in Snaps /\ cliSnap \in Snaps
    /\ srvAwait \in BOOLEAN /\ cliAwait \in BOOLEAN /\ sameSnap \in BOOLEAN
    /\ result \in ({<<"none", "none">>} \cup (Queries \X Replies))
    /\ queries \in 0..MaxQueries
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages

\* In English: "No side has hung up or given up."
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "The client never hands a caller a reply to a different
\* query: whatever it last handed over is the reply of the query it sent."
\* This is the request/response correlation the busy kind exists for.
RepliesMatchQueries ==
    result /= <<"none", "none">> => result[2] = ReplyOf(result[1])

\* In English: "An MsgAwaitAcquire is never answered with the snapshot the
\* client already holds" [R1] 217-224, [R5].
AwaitGetsNewSnapshot == ~sameSnap

\* In English: "While the connection is up, a message waiting for the server
\* is one the server can read: after MsgDone, the first message of the
\* client's next run is read by a restarted server [S5][R7], not left on a
\* server whose run is over." (Rogue configs leave it out: a rogue message
\* can arrive while the server itself holds agency.)
NewRunServed ==
    (inbox["Server"] /= <<>> /\ NoFailures) => ENABLED Recv("Server")

\* In English: "The client and the server never both believe they may send."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "Whenever the server is busy with a query, the client is
\* waiting in a busy state too (or has hung up): the client cannot move on,
\* say to another query, before the answer arrives."
BusyViewsAgree ==
    view["Server"] \in BusyStates =>
        view["Client"] \in BusyStates \cup Failures

\* In English: "In every step, a side that has hung up stays hung up."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

-----------------------------------------------------------------------------
(* Reachability probes. Each claims something never happens; TLC must show *)
(* that it does in the passing configs, or a pass would be vacuous.        *)

\* In English: "The server never blocks waiting for the mempool to change."
ProbeServerNeverBlocks == ~ServerBlocked

\* In English: "No MsgAwaitAcquire is ever answered." (cliAwait stays TRUE
\* from an await until the next acquire, so an acquired client with cliAwait
\* set had its await answered.)
ProbeAwaitNeverAnswered == ~(cliAwait /\ view["Client"] = "StAcquired")

\* In English: "Nobody is ever in StBusy GetMeasures."
ProbeNoGetMeasures == \A r \in Roles : view[r] /= "StBusyGetMeasures"

\* In English: "The client never starts a second run."
ProbeNoSecondRun == runs = 1

\* In English: "Stop never releases a snapshot before MsgDone."
ProbeNoReleaseThenDone ==
    ~ \E i \in 1..(Len(inbox["Server"]) - 1) :
          /\ inbox["Server"][i].type = "MsgRelease"
          /\ inbox["Server"][i + 1].type = "MsgDone"
=============================================================================
