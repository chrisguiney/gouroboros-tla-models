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
    StopCancelsWait,     \* TRUE: Stop ends a call that waits for the server, then closes
                         \* the protocol without a message (a reference client is a thread
                         \* that is cancelled; it cannot send in StAcquiring or StBusy [R4])
                         \* FALSE: Stop takes the call lock first, so it waits for the reply
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

\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles == {"Client", "Server"}

\* The busy state's kind is part of the state's name [R1] StBusyKind.
\* Literally: "BusyStates is defined as the set containing "StBusyNextTx",
\*   "StBusyHasTx", "StBusyGetSizes" and "StBusyGetMeasures"."
BusyStates == {"StBusyNextTx", "StBusyHasTx", "StBusyGetSizes", "StBusyGetMeasures"}
\* Literally: "States is defined as the union of the set containing "StIdle",
\*   "StAcquiring", "StAcquired" and "StDone", and BusyStates."
States == {"StIdle", "StAcquiring", "StAcquired", "StDone"} \cup BusyStates

\* "MsgAcquire" sent in StAcquired is MsgAwaitAcquire: the two are the same
\* bytes on the wire [R2], so a receiver tells them apart only by its state.
\* Literally: "Queries is defined as the set containing "MsgNextTx",
\*   "MsgHasTx", "MsgGetSizes" and "MsgGetMeasures"."
Queries == {"MsgNextTx", "MsgHasTx", "MsgGetSizes", "MsgGetMeasures"}
\* Literally: "Replies is defined as the set containing "MsgReplyNextTx",
\*   "MsgReplyHasTx", "MsgReplyGetSizes" and "MsgReplyGetMeasures"."
Replies == {"MsgReplyNextTx", "MsgReplyHasTx", "MsgReplyGetSizes", "MsgReplyGetMeasures"}
\* Literally: "MsgTypes is defined as the union of the set containing
\*   "MsgAcquire", "MsgAcquired", "MsgRelease" and "MsgDone", Queries, and
\*   Replies."
MsgTypes == {"MsgAcquire", "MsgAcquired", "MsgRelease", "MsgDone"} \cup Queries \cup Replies

\* In English: "The busy state a query leads to, and the one reply that
\* answers it." [R1] 226-273.
\* Literally: "BusyOf of q is defined as: in the case q equals "MsgNextTx",
\*   "StBusyNextTx"; in the case q equals "MsgHasTx", "StBusyHasTx"; in the
\*   case q equals "MsgGetSizes", "StBusyGetSizes"; in the case q equals
\*   "MsgGetMeasures", "StBusyGetMeasures"."
BusyOf(q) == CASE q = "MsgNextTx"      -> "StBusyNextTx"
             []   q = "MsgHasTx"       -> "StBusyHasTx"
             []   q = "MsgGetSizes"    -> "StBusyGetSizes"
             []   q = "MsgGetMeasures" -> "StBusyGetMeasures"
\* Literally: "ReplyOf of q is defined as: in the case q equals "MsgNextTx",
\*   "MsgReplyNextTx"; in the case q equals "MsgHasTx", "MsgReplyHasTx"; in the
\*   case q equals "MsgGetSizes", "MsgReplyGetSizes"; in the case q equals
\*   "MsgGetMeasures", "MsgReplyGetMeasures"."
ReplyOf(q) == CASE q = "MsgNextTx"      -> "MsgReplyNextTx"
              []   q = "MsgHasTx"       -> "MsgReplyHasTx"
              []   q = "MsgGetSizes"    -> "MsgReplyGetSizes"
              []   q = "MsgGetMeasures" -> "MsgReplyGetMeasures"
\* In English: "The query that put the protocol in busy state s."
\* Literally: "QueryOf of s is defined as the q, chosen from Queries, such that
\*   BusyOf of q equals s."
QueryOf(s) == CHOOSE q \in Queries : BusyOf(q) = s

\* Snapshots are numbered by how many times the mempool has changed: two
\* snapshots with the same number are the same snapshot [R5] isSameSnapshot.
\* Literally: "Snaps is defined as 0 through MaxChanges."
Snaps == 0..MaxChanges

\* A message is a record: its type, and the snapshot number, which only
\* MsgAcquired uses (it stands for the slot number it carries).
\* Literally: "Msg of t and n is defined as the record whose field type is t
\*   and whose field snap is n."
Msg(t, n) == [type |-> t, snap |-> n]
\* Literally: "Messages is defined as the set of Msg of t and n, for every t
\*   that is a member of MsgTypes and every n that is a member of Snaps."
Messages == {Msg(t, n) : t \in MsgTypes, n \in Snaps}

\* Literally: "Failures is defined as the set containing "Violation" and
\*   "TimedOut"."
Failures == {"Violation", "TimedOut"}

\* In English: "Who may send in each state" [S2] agency table, [R1] 285-289.
\* Literally: "Agency of s is defined as: in the case s is a member of the set
\*   containing "StIdle" and "StAcquired", "Client"; in the case s is a member
\*   of the union of the set containing "StAcquiring" and BusyStates, "Server";
\*   in the case s equals "StDone", "Nobody"."
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
\* Literally: "Transitions is defined as the set containing these five tuples:
\*   <<"StIdle", "MsgAcquire", "StAcquiring">>, <<"StIdle", "MsgDone",
\*   "StDone">>, <<"StAcquiring", "MsgAcquired", "StAcquired">>,
\*   <<"StAcquired", "MsgAcquire", "StAcquiring">>, and <<"StAcquired",
\*   "MsgRelease", "StIdle">>; union the set of the tuple of "StAcquired", q
\*   and BusyOf of q, for every q that is a member of Queries; union the set of
\*   the tuple of BusyOf of q, ReplyOf of q, and "StAcquired", for every q that
\*   is a member of Queries."
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
\* Literally: "IsLegal of s and t is defined as: there exists a tr that is a
\*   member of Transitions such that element 1 of tr equals s and element 2 of
\*   tr equals t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t
\* Literally: "After of s and t is defined as element 3 of the tr, chosen from
\*   Transitions, such that element 1 of tr equals s and element 2 of tr equals
\*   t."
After(s, t)   == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

\* In English: "The peer of the client is the server, and vice versa."
\* Literally: "Peer of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s."
\* Literally: "Awaiting of r and s is defined as: s is a member of States
\*   without the members of the set containing "StDone", and Agency of s equals
\*   Peer of r."
Awaiting(r, s) == s \in States \ {"StDone"} /\ Agency(s) = Peer(r)

(***************************************************************************)
(* JUDGING A MESSAGE that side r reads in state s [S1]:                    *)
(*   - A server that does not know MsgGetMeasures cannot even decode it.   *)
(*   - Without busy kinds, any reply ends any busy state (the mutation).   *)
(*   - A message with no row from s aborts the connection.                 *)
(*   - Otherwise follow the row.                                           *)
(***************************************************************************)
\* Literally: "Judge of r, s and m is defined as: if r equals "Server" and m's
\*   type equals "MsgGetMeasures" and ServerKnowsMeasures is not true, then
\*   "Violation"; else if BusyKinds is not true and s is a member of BusyStates
\*   and m's type is a member of Replies, then "StAcquired"; else if IsLegal of
\*   s and m's type is not true, then "Violation"; else After of s and m's
\*   type."
Judge(r, s, m) ==
    IF r = "Server" /\ m.type = "MsgGetMeasures" /\ ~ServerKnowsMeasures
                                    THEN "Violation"     \* undecodable: hang up
    ELSE IF ~BusyKinds /\ s \in BusyStates /\ m.type \in Replies
                                    THEN "StAcquired"    \* the mutation: any reply will do
    ELSE IF ~IsLegal(s, m.type)     THEN "Violation"     \* not legal here: hang up
    ELSE After(s, m.type)                                \* otherwise: follow the row

\* In English: "A new run starts in StIdle."
\* Literally: "RunState of s is defined as: if s equals "StDone" then "StIdle",
\*   else s."
RunState(s) == IF s = "StDone" THEN "StIdle" ELSE s

(***************************************************************************)
(* THE RECEIVE TABLE the Go tests mirror: the outcome for every role,      *)
(* state, and message type. "Waits": the reader holds agency and does not  *)
(* read yet (see Model 01, [S8] there). "Held": the client's run is over   *)
(* and nothing reads it. After MsgDone a server restarts in StIdle [S5].   *)
(***************************************************************************)
\* Literally: "ReceiveTable of r, s and t is defined as: if s equals "StDone",
\*   then (if r equals "Server" and ServerRestarts is true, then Judge of r,
\*   "StIdle", and Msg of t and 0; else "Held"); else if Agency of s equals r,
\*   then "Waits"; else Judge of r, s, and Msg of t and 0."
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
    rogueLeft,  \* rogue messages the misbehaving peer may still inject
    lock,       \* the client's call lock (busyMutex): "free", or held by a "call" or by "stop"
    stop,       \* the client's Stop: "no", "requested" (called, not yet returned), or "done"
    cancelled   \* TRUE once Stop ended a call that was waiting for the server

\* Literally: "vars is defined as the tuple of all fifteen variables."
vars == <<view, inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
          sameSnap, result, queries, runs, rogueLeft, lock, stop, cancelled>>

\* The variables only the client's call lock and Stop touch.
\* Literally: "stopVars is defined as the tuple of lock, stop and cancelled."
stopVars == <<lock, stop, cancelled>>

\* In English: "At the start both sides think it is StIdle, nothing is in
\* flight, the mempool is snapshot 0, and nothing has been answered."
\* Literally: "Init is defined as: view equals the function that maps every r
\*   in Roles to "StIdle", and inbox equals the function that maps every r in
\*   Roles to the empty sequence, and mempool equals 0, and srvSnap equals 0,
\*   and srvAwait equals FALSE, and cliSnap equals 0, and cliAwait equals
\*   FALSE, and sameSnap equals FALSE, and result equals the tuple of "none"
\*   and "none", and queries equals 0, and runs equals 1, and rogueLeft equals
\*   RogueMessages, and lock equals "free", and stop equals "no", and cancelled
\*   equals FALSE."
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
    /\ lock = "free"
    /\ stop = "no"
    /\ cancelled = FALSE

\* In English: "The server is waiting, as [R5] says it must, for the mempool
\* to change: it serves an MsgAwaitAcquire and the mempool is still the
\* snapshot it holds."
\* Literally: "ServerBlocked is defined as: view of "Server" equals
\*   "StAcquiring", and srvAwait is true, and AwaitWaitsForChange is true, and
\*   mempool equals srvSnap."
ServerBlocked ==
    /\ view["Server"] = "StAcquiring"
    /\ srvAwait
    /\ AwaitWaitsForChange
    /\ mempool = srvSnap

\* In English: "The connection is over when someone hung up, or both sides
\* are done and the client may start no more runs."
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

\* In English: "Nothing more can happen but the wait for a mempool change
\* the model has run out of. The reference client blocks here, which is
\* correct [R1] MsgAwaitAcquire."
\* Literally: "WaitsForever is defined as: ServerBlocked is true, and mempool
\*   equals MaxChanges, and RogueMessages equals 0."
WaitsForever ==
    /\ ServerBlocked
    /\ mempool = MaxChanges
    /\ RogueMessages = 0

\* --- The client. Each send needs the client to hold agency [S1]. ----------

\* In English: "From StIdle or StAcquired the client can send MsgAcquire.
\* From StAcquired that is MsgAwaitAcquire [R2]; gOuroboros's Acquire()
\* sends the same bytes in both states."
\* Literally: "ClientAcquire is defined as: view of "Client" is a member of the
\*   set containing "StIdle" and "StAcquired", and lock equals "free" and stop
\*   equals "no", and lock in the next state equals "call", and cliAwait in the
\*   next state equals (view of "Client" equals "StAcquired"), and view in the
\*   next state equals view except that its "Client" entry is "StAcquiring",
\*   and inbox in the next state equals inbox except that its "Server" entry is
\*   the old entry with Msg of "MsgAcquire" and 0 appended, and mempool,
\*   srvSnap, srvAwait, cliSnap, sameSnap, result, queries, runs, rogueLeft,
\*   stop and cancelled are unchanged."
ClientAcquire ==
    /\ view["Client"] \in {"StIdle", "StAcquired"}
    /\ lock = "free" /\ stop = "no"
    /\ lock' = "call"
    /\ cliAwait' = (view["Client"] = "StAcquired")      \* next, remember whether this is an await
    /\ view' = [view EXCEPT !["Client"] = "StAcquiring"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgAcquire", 0))]
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, sameSnap, result,
                   queries, runs, rogueLeft, stop, cancelled>>

\* In English: "The client may send MsgGetMeasures: it has a call for it,
\* and either the handshake agreed NodeToClientV_20 or later or the client
\* does not check" [R6].
\* Literally: "MayAskMeasures is defined as: ClientSendsMeasures is true, and
\*   (NegotiatedV20 is true, or ClientChecksVersion is not true)."
MayAskMeasures == ClientSendsMeasures /\ (NegotiatedV20 \/ ~ClientChecksVersion)

\* In English: "From StAcquired, with queries left, the client can send a
\* query q (MsgGetMeasures only if it may, above). It then waits in q's busy
\* state."
\* Literally: "ClientQuery of q is defined as: view of "Client" equals
\*   "StAcquired", and queries is less than MaxQueries, and (q does not equal
\*   "MsgGetMeasures", or MayAskMeasures is true), and lock equals "free" and
\*   stop equals "no", and lock in the next state equals "call", and view in
\*   the next state equals view except that its "Client" entry is BusyOf of q,
\*   and inbox in the next state equals inbox except that its "Server" entry is
\*   the old entry with Msg of q and 0 appended, and queries in the next state
\*   equals queries plus 1, and mempool, srvSnap, srvAwait, cliSnap, cliAwait,
\*   sameSnap, result, runs, rogueLeft, stop and cancelled are unchanged."
ClientQuery(q) ==
    /\ view["Client"] = "StAcquired"
    /\ queries < MaxQueries
    /\ q /= "MsgGetMeasures" \/ MayAskMeasures
    /\ lock = "free" /\ stop = "no"
    /\ lock' = "call"
    /\ view' = [view EXCEPT !["Client"] = BusyOf(q)]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg(q, 0))]
    /\ queries' = queries + 1
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, runs, rogueLeft, stop, cancelled>>

\* In English: "From StAcquired the client can release the snapshot."
\* Literally: "ClientRelease is defined as: view of "Client" equals
\*   "StAcquired", and lock equals "free" and stop equals "no", and view in the
\*   next state equals view except that its "Client" entry is "StIdle", and
\*   inbox in the next state equals inbox except that its "Server" entry is the
\*   old entry with Msg of "MsgRelease" and 0 appended, and mempool, srvSnap,
\*   srvAwait, cliSnap, cliAwait, sameSnap, result, queries, runs, rogueLeft
\*   and stopVars are unchanged."
ClientRelease ==
    /\ view["Client"] = "StAcquired"
    /\ lock = "free" /\ stop = "no"
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgRelease", 0))]
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, queries, runs, rogueLeft, stopVars>>

\* In English: "Stop is called. It may be called at any time during a run,
\* including while another call waits for the server."
\* Literally: "StopRequest is defined as: stop equals "no", and view of
\*   "Client" is a member of States without the members of the set containing
\*   "StDone", and stop in the next state equals "requested", and view, inbox,
\*   mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap, result, queries,
\*   runs, rogueLeft, lock and cancelled are unchanged."
StopRequest ==
    /\ stop = "no"
    /\ view["Client"] \in States \ {"StDone"}
    /\ stop' = "requested"
    /\ UNCHANGED <<view, inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, rogueLeft, lock, cancelled>>

\* In English: "With StopCancelsWait, Stop ends a call that holds the lock
\* waiting for the server's answer; the call returns, freeing the lock."
\* Literally: "StopCancel is defined as: StopCancelsWait is true, and stop
\*   equals "requested", and lock equals "call", and lock in the next state
\*   equals "free", and cancelled in the next state equals TRUE, and view,
\*   inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap, result,
\*   queries, runs, rogueLeft and stop are unchanged."
StopCancel ==
    /\ StopCancelsWait
    /\ stop = "requested"
    /\ lock = "call"
    /\ lock' = "free"
    /\ cancelled' = TRUE
    /\ UNCHANGED <<view, inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, rogueLeft, stop>>

\* In English: "Stop runs once it holds the call lock. If it cancelled a
\* waiting call, the client may not send (the server has agency), so it
\* closes the protocol without a message. If the protocol already failed,
\* there is nothing to send. From StIdle the client sends MsgDone [R4]. From
\* StAcquired: with StopReleases it sends MsgRelease and then MsgDone;
\* without it (gOuroboros's Stop on main) it tries to send MsgDone, which
\* has no row from StAcquired, so its own send loop refuses it and tears the
\* connection down." Taking and freeing the lock is one step: nothing in
\* Stop waits for the server once it holds it.
\* Literally: "ClientStop is defined as: stop equals "requested", and lock
\*   equals "free", and stop in the next state equals "done", and either
\*   (cancelled is true, and view of "Client" is a member of States, and view
\*   in the next state equals view except that its "Client" entry is "Closed",
\*   and inbox is unchanged), or (view of "Client" is a member of Failures, and
\*   view and inbox are unchanged), or (cancelled is not true, and view of
\*   "Client" equals "StIdle", and view in the next state equals view except
\*   that its "Client" entry is "StDone", and inbox in the next state equals
\*   inbox except that its "Server" entry is the old entry with Msg of
\*   "MsgDone" and 0 appended), or (cancelled is not true, and view of "Client"
\*   equals "StAcquired", and StopReleases is true, and view in the next state
\*   equals view except that its "Client" entry is "StDone", and inbox in the
\*   next state equals inbox except that its "Server" entry is the old entry
\*   followed by the tuple of Msg of "MsgRelease" and 0, and Msg of "MsgDone"
\*   and 0), or (cancelled is not true, and view of "Client" equals
\*   "StAcquired", and StopReleases is not true, and view in the next state
\*   equals view except that its "Client" entry is "Violation", and inbox is
\*   unchanged); and mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
\*   result, queries, runs, rogueLeft, lock and cancelled are unchanged."
ClientStop ==
    /\ stop = "requested"
    /\ lock = "free"
    /\ stop' = "done"
    /\ \/ /\ cancelled
          /\ view["Client"] \in States
          /\ view' = [view EXCEPT !["Client"] = "Closed"]
          /\ UNCHANGED inbox
       \/ /\ view["Client"] \in Failures
          /\ UNCHANGED <<view, inbox>>
       \/ /\ ~cancelled
          /\ view["Client"] = "StIdle"
          /\ view' = [view EXCEPT !["Client"] = "StDone"]
          /\ inbox' = [inbox EXCEPT !["Server"] = Append(@, Msg("MsgDone", 0))]
       \/ /\ ~cancelled
          /\ view["Client"] = "StAcquired"
          /\ StopReleases
          /\ view' = [view EXCEPT !["Client"] = "StDone"]
          /\ inbox' = [inbox EXCEPT !["Server"] =
                           @ \o <<Msg("MsgRelease", 0), Msg("MsgDone", 0)>>]
       \/ /\ ~cancelled
          /\ view["Client"] = "StAcquired"
          /\ ~StopReleases
          /\ view' = [view EXCEPT !["Client"] = "Violation"]   \* refused by its own send loop
          /\ UNCHANGED inbox
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, queries, runs, rogueLeft, lock, cancelled>>

\* In English: "When the client's run is over and it may start another, it
\* can."
\* Literally: "ClientRestart is defined as: view of "Client" equals "StDone",
\*   and runs is less than MaxRuns, and view in the next state equals view
\*   except that its "Client" entry is "StIdle", and runs in the next state
\*   equals runs plus 1, and stop in the next state equals "no", and inbox,
\*   mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap, result, queries,
\*   rogueLeft, lock and cancelled are unchanged."
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ runs' = runs + 1
    /\ stop' = "no"
    /\ UNCHANGED <<inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, rogueLeft, lock, cancelled>>

\* --- The server. ---------------------------------------------------------

\* In English: "In StAcquiring the server can answer MsgAcquired with the
\* current snapshot, unless it serves an MsgAwaitAcquire and must wait for
\* the mempool to change [R5]."
\* Literally: "ServerAcquired is defined as: view of "Server" equals
\*   "StAcquiring", and ServerBlocked is not true, and view in the next state
\*   equals view except that its "Server" entry is "StAcquired", and inbox in
\*   the next state equals inbox except that its "Client" entry is the old
\*   entry with Msg of "MsgAcquired" and mempool appended, and srvSnap in the
\*   next state equals mempool, and srvAwait in the next state equals FALSE,
\*   and mempool, cliSnap, cliAwait, sameSnap, result, queries, runs, rogueLeft
\*   and stopVars are unchanged."
ServerAcquired ==
    /\ view["Server"] = "StAcquiring"
    /\ ~ServerBlocked
    /\ view' = [view EXCEPT !["Server"] = "StAcquired"]
    /\ inbox' = [inbox EXCEPT !["Client"] = Append(@, Msg("MsgAcquired", mempool))]
    /\ srvSnap' = mempool
    /\ srvAwait' = FALSE
    /\ UNCHANGED <<mempool, cliSnap, cliAwait, sameSnap, result, queries,
                   runs, rogueLeft, stopVars>>

\* In English: "In a busy state the server answers with that state's reply
\* [R4] ServerStBusy."
\* Literally: "ServerReply is defined as: view of "Server" is a member of
\*   BusyStates, and view in the next state equals view except that its
\*   "Server" entry is "StAcquired", and inbox in the next state equals inbox
\*   except that its "Client" entry is the old entry with Msg of (ReplyOf of
\*   QueryOf of view of "Server") and 0 appended, and mempool, srvSnap,
\*   srvAwait, cliSnap, cliAwait, sameSnap, result, queries, runs, rogueLeft
\*   and stopVars are unchanged."
ServerReply ==
    /\ view["Server"] \in BusyStates
    /\ view' = [view EXCEPT !["Server"] = "StAcquired"]
    /\ inbox' = [inbox EXCEPT !["Client"] =
                     Append(@, Msg(ReplyOf(QueryOf(view["Server"])), 0))]
    /\ UNCHANGED <<mempool, srvSnap, srvAwait, cliSnap, cliAwait, sameSnap,
                   result, queries, runs, rogueLeft, stopVars>>

\* --- The node's mempool. -------------------------------------------------

\* In English: "Transactions come and go: the mempool can change, a bounded
\* number of times."
\* Literally: "MempoolChange is defined as: mempool is less than MaxChanges,
\*   and mempool in the next state equals mempool plus 1, and view, inbox,
\*   srvSnap, srvAwait, cliSnap, cliAwait, sameSnap, result, queries, runs,
\*   rogueLeft and stopVars are unchanged."
MempoolChange ==
    /\ mempool < MaxChanges
    /\ mempool' = mempool + 1
    /\ UNCHANGED <<view, inbox, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, rogueLeft, stopVars>>

\* --- Reading. ------------------------------------------------------------

\* In English: "Side r reads the oldest message in its inbox when it waits
\* for its peer, or when it is a restartable server whose run is over. It
\* judges the message against its state and moves to the result. A server
\* that reads MsgAcquire notes whether it came in StAcquired (an await). A
\* client that reads MsgAcquired notes the snapshot, and whether an await
\* was answered with the snapshot it already held. A client that reads a
\* reply in a busy state hands <<query, reply>> to its caller. A call
\* waiting on the client returns, freeing the lock, once the client holds
\* agency again or the protocol failed."
\* Literally: "Recv of r is defined as: inbox of r does not equal the empty
\*   sequence, and (Awaiting of r and view of r, or r equals "Server" and view
\*   of r equals "StDone" and ServerRestarts is true), and, letting m be the
\*   head of inbox of r, s be RunState of view of r, and next be Judge of r, s
\*   and m: view in the next state equals view except that its r entry is next;
\*   and srvAwait in the next state equals (if r equals "Server" and m's type
\*   equals "MsgAcquire" then s equals "StAcquired", else srvAwait); and
\*   cliSnap in the next state equals (if r equals "Client" and next equals
\*   "StAcquired" and m's type equals "MsgAcquired" then m's snap, else
\*   cliSnap); and sameSnap in the next state equals sameSnap, or (r equals
\*   "Client" and m's type equals "MsgAcquired" and next equals "StAcquired"
\*   and cliAwait is true and m's snap equals cliSnap); and result in the next
\*   state equals (if r equals "Client" and s is a member of BusyStates and
\*   next equals "StAcquired" then the tuple of QueryOf of s and m's type, else
\*   result); and lock in the next state equals (if r equals "Client" and lock
\*   equals "call" and (next is a member of Failures or Agency of next equals
\*   "Client") then "free", else lock); and inbox in the next state equals
\*   inbox except that its r entry is the tail of the old entry; and mempool,
\*   srvSnap, cliAwait, queries, runs, rogueLeft, stop and cancelled are
\*   unchanged."
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
         /\ lock' = IF r = "Client" /\ lock = "call"
                        /\ (next \in Failures \/ Agency(next) = "Client")
                        THEN "free" ELSE lock
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<mempool, srvSnap, cliAwait, queries, runs, rogueLeft,
                   stop, cancelled>>

\* In English: "While the rogue peer has allowance left, it can put any
\* message into r's inbox."
\* Literally: "Inject of r and m is defined as: rogueLeft is greater than 0,
\*   and inbox in the next state equals inbox except that its r entry is the
\*   old entry with m appended, and rogueLeft in the next state equals
\*   rogueLeft minus 1, and view, mempool, srvSnap, srvAwait, cliSnap,
\*   cliAwait, sameSnap, result, queries, runs and stopVars are unchanged."
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, stopVars>>

\* --- Timeouts. -----------------------------------------------------------
\* [S4] and [R1] set no timeouts. gOuroboros's client sets AcquireTimeout on
\* StAcquiring and QueryTimeout on StBusy. The model has no clock; it lets
\* such a timer fire while the server waits, as it should, for the mempool
\* to change: that wait has no bound, so any finite timer can run out.
\*
\* In English: "With client timeouts, a client waiting in StAcquiring or a
\* busy state, with nothing to read, gives up while the server is blocked.
\* The waiting call then returns, freeing the lock."
\* Literally: "Timeout is defined as: ClientTimeouts is true, and view of
\*   "Client" is a member of the union of the set containing "StAcquiring" and
\*   BusyStates, and inbox of "Client" equals the empty sequence, and
\*   ServerBlocked is true, and view in the next state equals view except that
\*   its "Client" entry is "TimedOut", and lock in the next state equals (if
\*   lock equals "call" then "free", else lock), and inbox, mempool, srvSnap,
\*   srvAwait, cliSnap, cliAwait, sameSnap, result, queries, runs, rogueLeft,
\*   stop and cancelled are unchanged."
Timeout ==
    /\ ClientTimeouts
    /\ view["Client"] \in {"StAcquiring"} \cup BusyStates
    /\ inbox["Client"] = <<>>
    /\ ServerBlocked
    /\ view' = [view EXCEPT !["Client"] = "TimedOut"]
    /\ lock' = IF lock = "call" THEN "free" ELSE lock
    /\ UNCHANGED <<inbox, mempool, srvSnap, srvAwait, cliSnap, cliAwait,
                   sameSnap, result, queries, runs, rogueLeft, stop, cancelled>>

\* In English: "A step is a client call, a step of Stop, a server answer, a
\* mempool change, a read, a timeout, a rogue injection, or, once nothing
\* more can happen, nothing changing (so that TLC does not report the end as
\* a deadlock)."
\* Literally: "Next is defined as: ClientAcquire, or ClientRelease, or
\*   ClientRestart, or StopRequest, or StopCancel, or ClientStop, or there
\*   exists a q in Queries such that ClientQuery of q, or ServerAcquired, or
\*   ServerReply, or MempoolChange, or there exists an r in Roles such that
\*   Recv of r, or Timeout, or there exists an r in Roles and an m in Messages
\*   such that Inject of r and m, or (Ended or WaitsForever) and vars is
\*   unchanged."
Next ==
    \/ ClientAcquire \/ ClientRelease \/ ClientRestart
    \/ StopRequest \/ StopCancel \/ ClientStop
    \/ \E q \in Queries : ClientQuery(q)
    \/ ServerAcquired \/ ServerReply
    \/ MempoolChange
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
\*   set of sequences of members of Messages, and mempool, srvSnap and cliSnap
\*   are members of Snaps, and srvAwait, cliAwait and sameSnap are members of
\*   BOOLEAN, and result is a member of the union of the set containing the
\*   tuple of "none" and "none", and the Cartesian product of Queries and
\*   Replies, and queries is a member of 0 through MaxQueries, and runs is a
\*   member of 1 through MaxRuns, and rogueLeft is a member of 0 through
\*   RogueMessages, and lock is a member of the set containing "free", "call"
\*   and "stop", and stop is a member of the set containing "no", "requested"
\*   and "done", and cancelled is a member of BOOLEAN."
TypeOK ==
    /\ view \in [Roles -> States \cup Failures \cup {"Closed"}]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ mempool \in Snaps /\ srvSnap \in Snaps /\ cliSnap \in Snaps
    /\ srvAwait \in BOOLEAN /\ cliAwait \in BOOLEAN /\ sameSnap \in BOOLEAN
    /\ result \in ({<<"none", "none">>} \cup (Queries \X Replies))
    /\ queries \in 0..MaxQueries
    /\ runs \in 1..MaxRuns
    /\ rogueLeft \in 0..RogueMessages
    /\ lock \in {"free", "call", "stop"}
    /\ stop \in {"no", "requested", "done"}
    /\ cancelled \in BOOLEAN

\* In English: "No side has hung up or given up."
\* Literally: "NoFailures is defined as: for all r in Roles, view of r is not a
\*   member of Failures."
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "The client never hands a caller a reply to a different
\* query: whatever it last handed over is the reply of the query it sent."
\* This is the request/response correlation the busy kind exists for.
\* Literally: "RepliesMatchQueries is defined as: if result does not equal the
\*   tuple of "none" and "none", then element 2 of result equals ReplyOf of
\*   element 1 of result."
RepliesMatchQueries ==
    result /= <<"none", "none">> => result[2] = ReplyOf(result[1])

\* In English: "An MsgAwaitAcquire is never answered with the snapshot the
\* client already holds" [R1] 217-224, [R5].
\* Literally: "AwaitGetsNewSnapshot is defined as: sameSnap is not true."
AwaitGetsNewSnapshot == ~sameSnap

\* In English: "While the connection is up, a message waiting for the server
\* is one the server can read: after MsgDone, the first message of the
\* client's next run is read by a restarted server [S5][R7], not left on a
\* server whose run is over." (Rogue configs leave it out: a rogue message
\* can arrive while the server itself holds agency.)
\* Literally: "NewRunServed is defined as: if inbox of "Server" does not equal
\*   the empty sequence and NoFailures is true, then Recv of "Server" is
\*   enabled."
NewRunServed ==
    (inbox["Server"] /= <<>> /\ NoFailures) => ENABLED Recv("Server")

\* In English: "The client and the server never both believe they may send."
\* Literally: "NeverBothHaveAgency is defined as: it is not the case that (view
\*   of "Client" is a member of States and Agency of view of "Client" equals
\*   "Client", and view of "Server" is a member of States and Agency of view of
\*   "Server" equals "Server")."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* In English: "Whenever the server is busy with a query, the client is
\* waiting in a busy state too (or has hung up): the client cannot move on,
\* say to another query, before the answer arrives."
\* Literally: "BusyViewsAgree is defined as: if view of "Server" is a member of
\*   BusyStates, then view of "Client" is a member of the union of BusyStates,
\*   Failures, and the set containing "Closed"."
BusyViewsAgree ==
    view["Server"] \in BusyStates =>
        view["Client"] \in BusyStates \cup Failures \cup {"Closed"}

\* In English: "A Stop that has been called can always take its next step
\* without the server doing anything: it never waits on the peer." A Stop
\* that has to wait for the lock while a call waits for an answer the
\* server may withhold (an MsgAwaitAcquire with no mempool change, or a
\* query with no QueryTimeout) violates this.
\* Literally: "StopNeverWaitsOnPeer is defined as: if stop equals "requested",
\*   then (StopCancel or ClientStop) is enabled."
StopNeverWaitsOnPeer ==
    stop = "requested" => ENABLED (StopCancel \/ ClientStop)

\* In English: "In every step, a side that has hung up stays hung up."
\* Literally: "FailuresAreFinal is defined as: always, every step is a step in
\*   which, for all r in Roles, if view of r is a member of Failures, then view
\*   in the next state of r equals view of r; or a step that leaves vars
\*   unchanged."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

-----------------------------------------------------------------------------
(* Reachability probes. Each claims something never happens; TLC must show *)
(* that it does in the passing configs, or a pass would be vacuous.        *)

\* In English: "The server never blocks waiting for the mempool to change."
\* Literally: "ProbeServerNeverBlocks is defined as: ServerBlocked is not
\*   true."
ProbeServerNeverBlocks == ~ServerBlocked

\* In English: "No MsgAwaitAcquire is ever answered." (cliAwait stays TRUE
\* from an await until the next acquire, so an acquired client with cliAwait
\* set had its await answered.)
\* Literally: "ProbeAwaitNeverAnswered is defined as: it is not the case that
\*   (cliAwait is true and view of "Client" equals "StAcquired")."
ProbeAwaitNeverAnswered == ~(cliAwait /\ view["Client"] = "StAcquired")

\* In English: "Nobody is ever in StBusy GetMeasures."
\* Literally: "ProbeNoGetMeasures is defined as: for all r in Roles, view of r
\*   does not equal "StBusyGetMeasures"."
ProbeNoGetMeasures == \A r \in Roles : view[r] /= "StBusyGetMeasures"

\* In English: "The client never starts a second run."
\* Literally: "ProbeNoSecondRun is defined as: runs equals 1."
ProbeNoSecondRun == runs = 1

\* In English: "Stop never cancels a waiting MsgAwaitAcquire."
\* Literally: "ProbeNoCancelledAwait is defined as: it is not the case that
\*   (cancelled is true, and cliAwait is true, and view of "Client" equals
\*   "Closed")."
ProbeNoCancelledAwait == ~(cancelled /\ cliAwait /\ view["Client"] = "Closed")

\* In English: "Stop never releases a snapshot before MsgDone."
\* Literally: "ProbeNoReleaseThenDone is defined as: it is not the case that
\*   there exists an i in 1 through the length of inbox of "Server" minus 1
\*   such that element i of inbox of "Server"'s type equals "MsgRelease" and
\*   element i plus 1 of inbox of "Server"'s type equals "MsgDone"."
ProbeNoReleaseThenDone ==
    ~ \E i \in 1..(Len(inbox["Server"]) - 1) :
          /\ inbox["Server"][i].type = "MsgRelease"
          /\ inbox["Server"][i + 1].type = "MsgDone"
=============================================================================
