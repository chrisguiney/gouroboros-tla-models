----------------------------- MODULE Handshake -----------------------------
(***************************************************************************)
(* The handshake mini-protocol: one client proposes a table of versions,   *)
(* one server answers once, and both sides finish. This module checks the  *)
(* server's choice (highest common version, the right refusal reason, the  *)
(* query flag), the client's checks on the answer, the size limit, and the *)
(* per-state timeouts. Simultaneous open is in HandshakeSimOpen.tla.       *)
(*                                                                         *)
(* Where the specification and the reference implementation differ, the   *)
(* model follows the reference and says so.                                *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e;            *)
(* specs/05-handshake/README.md has links.                                 *)
(*   Specification (docs/network-spec/miniprotocols.tex):                  *)
(*   [S1] 27-36: one side has agency; an unexpected message aborts.        *)
(*   [S2] 449-501: states, agency, messages, transitions.                  *)
(*   [S3] 503-536, 575-606, 630-649: size limit 5760 bytes in both states; *)
(*        timeouts 10 s in both states for node-to-node, none for          *)
(*        node-to-client.                                                  *)
(*   [S4] 560-573, 619-628: negotiated data; magic must agree; query is    *)
(*        inherited from the client.                                       *)
(*   [S5] 668-702: the server's algorithm, steps 1 to 8.                   *)
(*   Reference implementation (.../framework/lib/Ouroboros/Network/       *)
(*   Protocol/Handshake/ unless noted):                                    *)
(*   [R1] Type.hs 87-131: MsgReplyVersions and MsgQueryReply are legal in  *)
(*        StConfirm; StDone has no agency.                                 *)
(*   [R2] Client.hs 119-172: what the client does with each answer.        *)
(*   [R3] Client.hs 191-222: acceptOrRefuse, the highest common version.   *)
(*   [R4] Server.hs 34-48: the server answers MsgQueryReply only after     *)
(*        acceptOrRefuse accepted, and only if the agreed data asks for a  *)
(*        query.                                                           *)
(*   [R5] Codec.hs 54-99: 5760 bytes in both states; shortWait (10 s) in   *)
(*        both states, or no limits (noTimeLimitsHandshake).               *)
(*   [R6] cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs  *)
(*        134-156 and NodeToClient/Version.hs 123-135: acceptableVersion   *)
(*        accepts only equal network magic; query = local || remote.       *)
(*   [R7] network-mux/src/Network/Mux/Ingress.hs 122-126: after the        *)
(*        handshake, a segment for mini-protocol 0 is for an unknown       *)
(*        mini-protocol, and the connection is torn down.                  *)
(*                                                                         *)
(* The gOuroboros code it is compared with: protocol/handshake/            *)
(* handshake.go (StateMapNtN, StateMapNtC), client.go (messageHandler,     *)
(* handleAcceptVersion, handleQueryReply), server.go                       *)
(* (handleProposeVersions), and the receive checks in protocol/protocol.go.*)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend in specs/01-keepalive/          *)
(* KeepAlive.tla. New here:                                                *)
(*   DOMAIN f          the set of keys of function f (like a Go map's keys)*)
(*   S \cap T          the elements in both S and T                        *)
(*   SUBSET S          every subset of S                                   *)
(*   UNION S           all the elements of all the sets in S               *)
(*   [D -> P]          every function with keys D and values in P          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Versions,           \* the version numbers in play, e.g. {1, 2}
    Magics,             \* the network magics in play, e.g. {0, 1}
    Mode,               \* "NtN" (node-to-node) or "NtC" (node-to-client)
    SilentPeer,         \* "None", or the role that never sends: "Client" or "Server"
    RogueMessages,      \* how many arbitrary messages a misbehaving peer may inject
    QueryFirst,         \* TRUE: gOuroboros today, the query flag is checked before negotiating
    StrictQueryReply,   \* TRUE: gOuroboros, a client refuses MsgQueryReply it did not ask for
    HandleReplyVersions,\* TRUE: the reference, a client in StConfirm takes MsgProposeVersions as MsgReplyVersions
    Mutation            \* "None", or a safeguard switched off to prove an invariant can fail

Roles    == {"Client", "Server"}
States   == {"StPropose", "StConfirm", "StDone"}
MsgTypes == {"MsgProposeVersions", "MsgAcceptVersion", "MsgRefuse", "MsgQueryReply"}
Reasons  == {"None", "VersionMismatch", "DecodeError", "Refused"}

\* The version data the model needs. `magic` is the network magic [S4].
\* `query` asks for the supported versions instead of a connection [S4].
\* `ok` says whether the receiver can decode the data at all [S5 step 4].
\* In English: "Params is every record of a magic, a query flag, and a
\* decodable flag."
Params == [magic : Magics, query : BOOLEAN, ok : BOOLEAN]

\* A placeholder for messages that carry no version data.
NoParams == [magic |-> CHOOSE m \in Magics : TRUE, query |-> FALSE, ok |-> TRUE]

\* A version table maps version numbers to version data [S2].
\* In English: "Tables(P) is every function from some set of versions to
\* data in P." The empty table, with no keys, is included.
Tables(P) == UNION {[D -> P] : D \in SUBSET Versions}

\* The client proposes any non-empty table. The server's own data is
\* always decodable and never asks for a query: only a client queries [S4].
ClientTables == Tables(Params) \ {<<>>}
ServerParams == {p \in Params : p.ok /\ ~p.query}
ServerTables == Tables(ServerParams) \ {<<>>}

\* In English: "The largest number in the non-empty set S."
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
\* In English: "The smallest number in the non-empty set S."
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* A message is a record; fields a type does not use hold placeholders.
\* `vmap` is the table of MsgProposeVersions and MsgQueryReply; `v` and `p`
\* the version and data of MsgAcceptVersion; `reason` that of MsgRefuse;
\* `big` marks a message over the state's size limit [S3].
Msg(t, vm, v, p, r, big) ==
    [type |-> t, vmap |-> vm, v |-> v, p |-> p, reason |-> r, big |-> big]

Messages == [type : MsgTypes, vmap : Tables(Params), v : Versions \cup {0},
             p : Params, reason : Reasons, big : BOOLEAN]

\* What a side ends with. `kind` is "None" (not finished), "Accept"
\* (version v agreed), "Refuse" (the server refused with `reason`),
\* "Query" (the supported versions were exchanged), or "Error" (the client
\* rejected the server's answer [R2]).
Res(k, v, r) == [kind |-> k, v |-> v, reason |-> r]
NoResult == Res("None", 0, "None")

Failures == {"Violation", "TimedOut"}

\* In English: "StPropose belongs to the client, StConfirm to the server,
\* StDone to nobody." [S2][R1]
Agency(s) == CASE s = "StPropose" -> "Client"
             []   s = "StConfirm" -> "Server"
             []   s = "StDone"    -> "Nobody"

\* The transitions as <<from, message, to>> [S2][R1]. MsgReplyVersions has
\* the same encoding as MsgProposeVersions [S2 479-484]; it is listed
\* under that name, legal in StConfirm, as the reference decodes it there
\* (Codec.hs 160-167).
Transitions ==
    { <<"StPropose", "MsgProposeVersions", "StConfirm">>,
      <<"StConfirm", "MsgProposeVersions", "StDone">>,   \* as MsgReplyVersions
      <<"StConfirm", "MsgAcceptVersion",   "StDone">>,
      <<"StConfirm", "MsgRefuse",          "StDone">>,
      <<"StConfirm", "MsgQueryReply",      "StDone">> }

\* In English: "Message type t is legal in state s if some row starts with
\* s and t, except that MsgReplyVersions exists only where it is handled."
IsLegal(s, t) ==
    /\ \E tr \in Transitions : tr[1] = s /\ tr[2] = t
    /\ (s = "StConfirm" /\ t = "MsgProposeVersions") => HandleReplyVersions

Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s."
Awaiting(r, s) == s \in {"StPropose", "StConfirm"} /\ Agency(s) = Peer(r)

(***************************************************************************)
(* NEGOTIATION. acceptOrRefuse [R3], the spec's steps 1 to 7 [S5]:        *)
(*   no common version: refuse, VersionMismatch;                           *)
(*   else take the highest common version v;                               *)
(*   the remote data for v does not decode: refuse, DecodeError;           *)
(*   the magics differ (acceptableVersion [R6]): refuse, Refused;          *)
(*   else accept v.                                                        *)
(* `local` is the deciding side's table, `remote` the one it received.     *)
(***************************************************************************)
\* In English: "Chosen(local, remote) is the highest version in both
\* tables; the mutation LowestCommon takes the lowest instead."
Chosen(local, remote) ==
    LET common == DOMAIN local \cap DOMAIN remote IN
    IF Mutation = "LowestCommon" THEN Min(common) ELSE Max(common)

Negotiate(local, remote) ==
    LET common == DOMAIN local \cap DOMAIN remote IN
    IF common = {} THEN Res("Refuse", 0, "VersionMismatch")          \* step 2
    ELSE LET v == Chosen(local, remote) IN                           \* step 3
         IF ~remote[v].ok
         THEN Res("Refuse", v, IF Mutation = "RefusedForDecode"
                               THEN "Refused" ELSE "DecodeError")    \* steps 4-5
         ELSE IF remote[v].magic /= local[v].magic
                 /\ Mutation /= "SkipMagicCheck"
              THEN Res("Refuse", v, "Refused")                       \* steps 6-7
         ELSE Res("Accept", v, "None")                               \* step 8

\* In English: "Some proposed version that decodes asks for a query." This
\* is the check gOuroboros makes before negotiating (server.go).
AnyQuery(remote) == \E v \in DOMAIN remote : remote[v].ok /\ remote[v].query

\* The server's answer. The reference negotiates first and answers
\* MsgQueryReply only if it accepted, and the agreed data (query = local ||
\* remote [R6]) asks for a query [R4]. gOuroboros (QueryFirst) answers
\* MsgQueryReply if any decodable proposed version asks for one.
\* In English: "If the gOuroboros rule is on and some version asks for a
\* query, reply Query; if negotiation accepted v and either side's data for
\* v asks for a query, reply Query; otherwise reply what negotiation says."
ServerDecision(local, remote) ==
    LET d == Negotiate(local, remote) IN
    IF QueryFirst /\ AnyQuery(remote) THEN Res("Query", 0, "None")
    ELSE IF d.kind = "Accept" /\ (local[d.v].query \/ remote[d.v].query)
         THEN Res("Query", 0, "None")
    ELSE d

\* In English: "The message carrying decision d from a server with table
\* local." An accept carries the server's data for v; the client only
\* checks its magic, which agreed data inherits [S4].
ReplyMsg(d, local) ==
    CASE d.kind = "Accept" -> Msg("MsgAcceptVersion", <<>>, d.v, local[d.v], "None", FALSE)
    []   d.kind = "Refuse" -> Msg("MsgRefuse", <<>>, d.v, NoParams, d.reason, FALSE)
    []   d.kind = "Query"  -> Msg("MsgQueryReply", local, 0, NoParams, "None", FALSE)

(***************************************************************************)
(* THE CLIENT'S JUDGEMENT of the answer in StConfirm [R2]:                 *)
(*   MsgAcceptVersion v p: v not proposed -> Error (NotRecognisedVersion); *)
(*     p does not decode -> Error; magic differs -> Error                  *)
(*     (InvalidServerSelection); otherwise Accept v.                       *)
(*   MsgRefuse: the handshake ends refused.                                *)
(*   MsgQueryReply: the query result. gOuroboros (StrictQueryReply) makes  *)
(*     it an Error unless the client asked for a query.                    *)
(*   MsgProposeVersions, read as MsgReplyVersions: the client negotiates   *)
(*     itself (simultaneous open).                                         *)
(***************************************************************************)
ClientJudge(table, m) ==
    CASE m.type = "MsgAcceptVersion" ->
            IF m.v \notin DOMAIN table THEN Res("Error", m.v, "None")
            ELSE IF ~m.p.ok THEN Res("Error", m.v, "None")
            ELSE IF m.p.magic /= table[m.v].magic
                    /\ Mutation /= "ClientSkipMagicCheck"
                 THEN Res("Error", m.v, "None")
            ELSE Res("Accept", m.v, "None")
    []   m.type = "MsgRefuse" -> Res("Refuse", m.v, m.reason)
    []   m.type = "MsgQueryReply" ->
            IF StrictQueryReply /\ ~\E v \in DOMAIN table : table[v].query
            THEN Res("Error", 0, "None")
            ELSE Res("Query", 0, "None")
    []   m.type = "MsgProposeVersions" -> Negotiate(table, m.vmap)

(***************************************************************************)
(* THE RECEIVE TABLE, printed by HandshakeTable.tla and mirrored by the    *)
(* gOuroboros test protocol/handshake/statemap_model_test.go. Kinds stand  *)
(* for concrete messages between two sides with the same one-version table *)
(* RefTable, which does not ask for a query.                               *)
(*   "Waits":  r holds agency, so it does not read yet.                    *)
(*   "Error":  the run ends in StDone, but the client rejects the answer.  *)
(*   A server that reads MsgProposeVersions moves to StConfirm and answers *)
(*   at once.                                                              *)
(***************************************************************************)
RefVersion == Max(Versions)
RefParams  == [magic |-> CHOOSE m \in Magics : TRUE, query |-> FALSE, ok |-> TRUE]
RefTable   == [v \in {RefVersion} |-> RefParams]

Kinds == {"MsgProposeVersions", "MsgAcceptVersion", "MsgRefuse",
          "MsgQueryReply", "Oversized"}

\* In English: "The concrete message each kind stands for." MsgQueryReply
\* is unsolicited here, since RefTable does not ask for a query.
KindMsg(k) ==
    CASE k = "MsgProposeVersions" -> Msg(k, RefTable, 0, NoParams, "None", FALSE)
    []   k = "MsgAcceptVersion"   -> Msg(k, <<>>, RefVersion, RefParams, "None", FALSE)
    []   k = "MsgRefuse"          -> Msg(k, <<>>, 0, NoParams, "VersionMismatch", FALSE)
    []   k = "MsgQueryReply"      -> Msg(k, RefTable, 0, NoParams, "None", FALSE)
    []   k = "Oversized"          -> Msg("MsgProposeVersions", RefTable, 0, NoParams, "None", TRUE)

\* In English: "What side r in state s does with message m: in StDone the
\* connection no longer runs mini-protocol 0, so anything is a violation
\* [R7]; while r holds agency the message waits; too big or not legal is a
\* violation [S1][S3]; otherwise the state it moves to, or Error for a
\* client that rejects the answer."
Judge(r, s, m, table) ==
    IF s = "StDone"            THEN "Violation"
    ELSE IF Agency(s) = r      THEN "Waits"
    ELSE IF m.big              THEN "Violation"
    ELSE IF ~IsLegal(s, m.type) THEN "Violation"
    ELSE IF r = "Client" /\ ClientJudge(table, m).kind = "Error" THEN "Error"
    ELSE (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = m.type)[3]

ReceiveTable(r, s, k) == Judge(r, s, KindMsg(k), RefTable)

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in
    inbox,      \* inbox[r]: messages sent to r not yet read
    table,      \* table[r]: side r's version table, fixed at the start
    result,     \* result[r]: how side r's handshake ended
    heard,      \* the table in the MsgProposeVersions the server answered
    rogueLeft   \* rogue messages the misbehaving peer may still inject

vars == <<view, inbox, table, result, heard, rogueLeft>>

\* In English: "Both sides start in StPropose with empty inboxes and no
\* result; the client has any non-empty table and the server any non-empty
\* table of its own."
Init ==
    /\ view = [r \in Roles |-> "StPropose"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ table \in {[Client |-> c, Server |-> s] : c \in ClientTables, s \in ServerTables}
    /\ result = [r \in Roles |-> NoResult]
    /\ heard = <<>>                     \* the server has heard nothing yet
    /\ rogueLeft = RogueMessages

Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ \A r \in Roles : view[r] = "StDone"

\* In English: "A client in StPropose that is not silent sends its table and
\* moves to StConfirm." [S2]
ClientPropose ==
    /\ SilentPeer /= "Client"
    /\ view["Client"] = "StPropose"
    /\ view' = [view EXCEPT !["Client"] = "StConfirm"]
    /\ inbox' = [inbox EXCEPT !["Server"] =
                   Append(@, Msg("MsgProposeVersions", table["Client"], 0, NoParams, "None", FALSE))]
    /\ UNCHANGED <<table, result, heard, rogueLeft>>

\* In English: "A server in StPropose that is not silent reads the oldest
\* message. Too big, or not MsgProposeVersions: violation. Otherwise it
\* decides, sends its answer, and is done." The read and the answer are one
\* step: the reference yields at once [R4], gOuroboros answers inside its
\* message handler, so a server never rests in StConfirm.
ServerRecv ==
    /\ SilentPeer /= "Server"
    /\ view["Server"] = "StPropose"
    /\ inbox["Server"] /= <<>>
    /\ LET m == Head(inbox["Server"])
           d == ServerDecision(table["Server"], m.vmap) IN
       IF m.big \/ ~IsLegal("StPropose", m.type)
       THEN /\ view' = [view EXCEPT !["Server"] = "Violation"]       \* hang up
            /\ UNCHANGED <<result, heard>>
            /\ inbox' = [inbox EXCEPT !["Server"] = Tail(@)]
       ELSE /\ view' = [view EXCEPT !["Server"] = "StDone"]          \* answered, done
            /\ result' = [result EXCEPT !["Server"] = d]
            /\ heard' = m.vmap                                       \* remember what it answered
            /\ inbox' = [inbox EXCEPT !["Server"] = Tail(@),
                                      !["Client"] = Append(@, ReplyMsg(d, table["Server"]))]
    /\ UNCHANGED <<table, rogueLeft>>

\* In English: "A client in StConfirm reads the oldest message. Too big, or
\* not legal in StConfirm: violation. Otherwise it judges the answer, is
\* done, and keeps the result."
ClientRecv ==
    /\ view["Client"] = "StConfirm"
    /\ inbox["Client"] /= <<>>
    /\ LET m == Head(inbox["Client"]) IN
       IF m.big \/ ~IsLegal("StConfirm", m.type)
       THEN /\ view' = [view EXCEPT !["Client"] = "Violation"]
            /\ UNCHANGED result
       ELSE /\ view' = [view EXCEPT !["Client"] = "StDone"]
            /\ result' = [result EXCEPT !["Client"] = ClientJudge(table["Client"], m)]
    /\ inbox' = [inbox EXCEPT !["Client"] = Tail(@)]
    /\ UNCHANGED <<table, heard, rogueLeft>>

\* In English: "A side in StDone that finds a message tears the connection
\* down: mini-protocol 0 no longer runs [R7]."
DoneRecv(r) ==
    /\ view[r] = "StDone"
    /\ inbox[r] /= <<>>
    /\ view' = [view EXCEPT ![r] = "Violation"]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<table, result, heard, rogueLeft>>

\* In English: "The rogue peer may put any message, of any size, in r's
\* inbox, while it has allowance left."
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, table, result, heard>>

\* The messages the rogue peer picks from: each kind of the receive table,
\* plus an accept for every version and data, so the client's checks on
\* MsgAcceptVersion are all exercised.
RogueSet ==
    {KindMsg(k) : k \in Kinds} \cup
    {Msg("MsgAcceptVersion", <<>>, v, p, "None", FALSE) : v \in Versions, p \in Params}

Progress == ClientPropose \/ ServerRecv \/ ClientRecv \/ \E r \in Roles : DoneRecv(r)

\* Timeouts [S3][R5]: node-to-node waits at most 10 s in each state, then
\* tears the connection down; node-to-client has no timeouts. The model has
\* no clock: a timeout fires only when nothing else can happen, which is
\* when the peer is silent.
\* In English: "In node-to-node mode, a side waiting for a peer that will
\* never send can give up."
Timeout(r) ==
    /\ Mode = "NtN"
    /\ ~Ended
    /\ Awaiting(r, view[r])
    /\ ~ENABLED Progress
    /\ view' = [view EXCEPT ![r] = "TimedOut"]
    /\ UNCHANGED <<inbox, table, result, heard, rogueLeft>>

Next ==
    \/ Progress
    \/ \E r \in Roles : Timeout(r)
    \/ \E r \in Roles, m \in RogueSet : Inject(r, m)
    \/ Ended /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

TypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ table["Client"] \in ClientTables /\ table["Server"] \in ServerTables
    /\ result \in [Roles -> [kind : {"None", "Accept", "Refuse", "Query", "Error"},
                             v : Versions \cup {0}, reason : Reasons]]
    /\ heard \in Tables(Params)
    /\ rogueLeft \in 0..RogueMessages

\* The facts the specification's algorithm [S5] is stated in, written out
\* again independently of Negotiate, about the proposal the server actually
\* answered (with honest peers, the client's table; with a rogue peer,
\* possibly the rogue's).
Common      == DOMAIN heard \cap DOMAIN table["Server"]
Highest     == Max(Common)
CData       == heard[Highest]               \* the proposer's data for Highest
SData       == table["Server"][Highest]     \* the server's data for Highest
Negotiable  == Common /= {} /\ CData.ok /\ CData.magic = SData.magic

\* In English: "No side has hung up." With honest peers this must hold.
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "No side has seen a protocol violation."
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* In English: "If the server accepted v, v is the highest version both
\* sides support [S5 step 3]."
AcceptsHighestCommon ==
    result["Server"].kind = "Accept" =>
        /\ result["Server"].v \in Common
        /\ \A w \in Common : w <= result["Server"].v

\* In English: "If the server accepted, the client's data decodes and the
\* magics agree [S4][S5 steps 4-7]."
AcceptsOnlyMatchingMagic ==
    result["Server"].kind = "Accept" => Negotiable

\* In English: "Each refusal names the right reason [S5]: VersionMismatch
\* only when nothing is common; DecodeError, for the highest common
\* version, only when the client's data for it does not decode; Refused,
\* for that version, only when it decodes and the magics differ."
RefusalReasonsRight ==
    LET r == result["Server"] IN
    r.kind = "Refuse" =>
        CASE r.reason = "VersionMismatch" -> Common = {}
        []   r.reason = "DecodeError"     -> Common /= {} /\ r.v = Highest /\ ~CData.ok
        []   r.reason = "Refused"         -> Common /= {} /\ r.v = Highest /\ CData.ok
                                             /\ CData.magic /= SData.magic
        []   OTHER                        -> FALSE

\* In English: "The server never refuses a negotiable proposal."
NoRefusalWhenNegotiable ==
    result["Server"].kind = "Refuse" => ~Negotiable

\* In English: "The server answers MsgQueryReply only when negotiation
\* would accept, and the client's data for the chosen version asks for a
\* query [R4][R6]."
QueryOnlyWhenNegotiable ==
    result["Server"].kind = "Query" => Negotiable /\ CData.query

\* In English: "When both sides are done, they agree: the same version
\* accepted, or the same refusal, or both a query."
BothSidesAgree ==
    (\A r \in Roles : view[r] = "StDone") =>
        /\ result["Client"].kind = result["Server"].kind
        /\ result["Client"].kind \in {"Accept", "Refuse"} =>
               result["Client"].v = result["Server"].v
        /\ result["Client"].reason = result["Server"].reason

\* In English: "In every step where the client accepts a MsgAcceptVersion,
\* it proposed that version, the data decodes, and the magic is its own."
\* With a rogue server this is the client's own defence [R2].
ClientAcceptsOnlyProposed ==
    [][ (/\ view["Client"] = "StConfirm"
         /\ inbox["Client"] /= <<>>
         /\ Head(inbox["Client"]).type = "MsgAcceptVersion"
         /\ result'["Client"].kind = "Accept")
        => LET m == Head(inbox["Client"]) IN
           /\ m.v \in DOMAIN table["Client"]                \* it proposed v
           /\ m.p.ok                                        \* the data decodes
           /\ m.p.magic = table["Client"][m.v].magic        \* and the magic is its own
      ]_vars

\* In English: "It is never the case that both sides believe they may send."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* THE STATES THAT CANNOT BE ENTERED.
\* In English: "In every step, for every side, a change of state is to a
\* failure or along a row of the transition table; nothing leaves StDone
\* except to a failure."
OnlyLegalMoves ==
    [][\A r \in Roles :
         view'[r] /= view[r] =>
             \/ view'[r] \in Failures
             \/ \E tr \in Transitions : tr[1] = view[r] /\ tr[3] = view'[r]
             \/ r = "Server" /\ view[r] = "StPropose" /\ view'[r] = "StDone"
      ]_vars
\* (The last line is the server's read-and-answer step: StPropose to
\* StConfirm on reading, StConfirm to StDone on answering, taken together.)

\* In English: "A side that fails stays failed."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

\* In English: "A timeout fires only in node-to-node mode."
TimeoutsOnlyNtN ==
    (\E r \in Roles : view[r] = "TimedOut") => Mode = "NtN"

-----------------------------------------------------------------------------
(* Reachability probes. Each claims something never happens; TLC must find *)
(* it does. Run with the matching *ProbeBug.cfg.                           *)

ProbeNeverAccept         == result["Server"].kind /= "Accept"
ProbeNeverQuery          == result["Server"].kind /= "Query"
ProbeNeverMismatch       == result["Server"].reason /= "VersionMismatch"
ProbeNeverDecodeError    == result["Server"].reason /= "DecodeError"
ProbeNeverRefused        == result["Server"].reason /= "Refused"
\* "The highest common version is never below some other proposed
\* version": false whenever the client proposes a version the server lacks.
ProbeNeverAcceptBelowProposed ==
    ~ /\ result["Server"].kind = "Accept"
      /\ \E w \in DOMAIN table["Client"] : w > result["Server"].v
=============================================================================
