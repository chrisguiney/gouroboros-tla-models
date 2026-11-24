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
(*   [R9] Server.hs 42-44: MsgAcceptVersion carries encodeData of the      *)
(*        agreed data, the result of acceptableVersion local remote.       *)
(*   [R10] Codec.hs 210-241 (decodeVersions): a key the version codec     *)
(*        does not recognise is skipped (235); each recognised key must be *)
(*        greater than the previous recognised key, or decoding fails      *)
(*        ("unordered version", 237-240). The codec encodes keys ascending *)
(*        (encodeVersions, 197-207).                                       *)
(*   [S7] miniprotocols.tex 572-573: "the negotiated version data is sent  *)
(*        back using MsgAcceptVersion"; 653-656: the version numbers in    *)
(*        the table "are unique and appear in ascending order".            *)
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
    AcceptOwnData,      \* TRUE: gOuroboros main, MsgAcceptVersion carries the server's own data, not the agreed data
    KeyOrderRule,       \* "Recognised": the reference, recognised keys must ascend; "Every": every key must; "None": gOuroboros main
    ClientKeyOrders,    \* the wire orders the client may use: "Ascending", "UnknownAnywhere", or "Any"
    Mutation            \* "None", or a safeguard switched off to prove an invariant can fail

\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles    == {"Client", "Server"}
\* Literally: "States is defined as the set containing "StPropose", "StConfirm"
\*   and "StDone"."
States   == {"StPropose", "StConfirm", "StDone"}
\* Literally: "MsgTypes is defined as the set containing "MsgProposeVersions",
\*   "MsgAcceptVersion", "MsgRefuse" and "MsgQueryReply"."
MsgTypes == {"MsgProposeVersions", "MsgAcceptVersion", "MsgRefuse", "MsgQueryReply"}
\* Literally: "Reasons is defined as the set containing "None",
\*   "VersionMismatch", "DecodeError" and "Refused"."
Reasons  == {"None", "VersionMismatch", "DecodeError", "Refused"}

\* The version data the model needs. `magic` is the network magic [S4].
\* `query` asks for the supported versions instead of a connection [S4].
\* `ok` says whether the receiver can decode the data at all [S5 step 4].
\* `init` is the node-to-node diffusion mode, TRUE for initiator-only [S4];
\* it stands for every field the two sides combine (diffusion mode, peer
\* sharing, Peras support [R6]). Node-to-client data has no such field.
\* In English: "Params is every record of a magic, a query flag, a
\* decodable flag, and an initiator-only flag."
\* Literally: "InitModes is defined as: if Mode equals "NtN" then BOOLEAN, else
\*   the set containing FALSE."
InitModes == IF Mode = "NtN" THEN BOOLEAN ELSE {FALSE}
\* Literally: "Params is defined as the set of records whose field magic is a
\*   member of Magics, field query is a member of BOOLEAN, field ok is a member
\*   of BOOLEAN, and field init is a member of InitModes."
Params == [magic : Magics, query : BOOLEAN, ok : BOOLEAN, init : InitModes]

\* A placeholder for messages that carry no version data.
\* Literally: "NoParams is defined as the record whose field magic is the m,
\*   chosen from Magics, such that TRUE; field query is FALSE; field ok is
\*   TRUE; and field init is FALSE."
NoParams == [magic |-> CHOOSE m \in Magics : TRUE, query |-> FALSE, ok |-> TRUE,
             init |-> FALSE]

\* The negotiated data: acceptableVersion local remote [R6][S4]. The magic
\* is the local one (the two agree, or there is no agreement); a side is
\* initiator-only if either side is (`min` of the diffusion modes); query
\* is local || remote.
\* In English: "Agree(l, r) is l's magic, query if either asks, and
\* initiator-only if either is."
\* Literally: "Agree of l and r is defined as the record whose field magic is
\*   l's magic, field query is l's query or r's query, field ok is TRUE, and
\*   field init is l's init or r's init."
Agree(l, r) == [magic |-> l.magic, query |-> l.query \/ r.query, ok |-> TRUE,
                init |-> l.init \/ r.init]

\* A version table maps version numbers to version data [S2].
\* In English: "Tables(P) is every function from some set of versions to
\* data in P." The empty table, with no keys, is included.
\* Literally: "Tables of P is defined as the union of all members of the set of
\*   the set of functions from D to P, for every D that is a member of the set
\*   of subsets of Versions."
Tables(P) == UNION {[D -> P] : D \in SUBSET Versions}

\* The client proposes any non-empty table. The server's own data is
\* always decodable and never asks for a query: only a client queries [S4].
\* Literally: "ClientTables is defined as Tables of Params without the members
\*   of the set containing the empty sequence."
ClientTables == Tables(Params) \ {<<>>}
\* Literally: "ServerParams is defined as the set of every p in Params such
\*   that p's ok is true and p's query is not true."
ServerParams == {p \in Params : p.ok /\ ~p.query}
\* Literally: "ServerTables is defined as Tables of ServerParams without the
\*   members of the set containing the empty sequence."
ServerTables == Tables(ServerParams) \ {<<>>}

\* In English: "The largest number in the non-empty set S."
\* Literally: "Max of S is defined as the x, chosen from S, such that for all y
\*   in S, y is less than or equal to x."
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
\* In English: "The smallest number in the non-empty set S."
\* Literally: "Min of S is defined as the x, chosen from S, such that for all y
\*   in S, x is less than or equal to y."
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* A message is a record; fields a type does not use hold placeholders.
\* `vmap` is the table of MsgProposeVersions and MsgQueryReply; `v` and `p`
\* the version and data of MsgAcceptVersion; `reason` that of MsgRefuse;
\* `big` marks a message over the state's size limit [S3]; `keys` lists
\* the table's keys in the order they arrived on the wire [S7][R10].
\* Literally: "MsgK of t, vm, v, p, r, big and keys is defined as the record
\*   whose field type is t, field vmap is vm, field v is v, field p is p, field
\*   reason is r, field big is big, and field keys is keys."
MsgK(t, vm, v, p, r, big, keys) ==
    [type |-> t, vmap |-> vm, v |-> v, p |-> p, reason |-> r, big |-> big, keys |-> keys]

\* A version number no receiver recognises, such as one from a newer
\* release. It is on the wire only: the reference skips it [R10], so it is
\* never in `vmap`.
\* Literally: "Unknown is defined as Max of Versions plus 1."
Unknown == Max(Versions) + 1
\* Literally: "WireKeys is defined as the union of Versions and the set
\*   containing Unknown."
WireKeys == Versions \cup {Unknown}

\* In English: "The elements of S in ascending order, as a sequence."
\* Literally: "AscSeq of S is defined as the function that maps every i in 1
\*   through the number of members of S to the x, chosen from S, such that the
\*   number of members of the set of every y in S such that y is less than x
\*   equals i minus 1."
AscSeq(S) == [i \in 1..Cardinality(S) |->
                 CHOOSE x \in S : Cardinality({y \in S : y < x}) = i - 1]
\* In English: "Every order of the elements of S, as a sequence."
\* Literally: "Perms of S is defined as the set of every f in the set of
\*   functions from 1 through the number of members of S to S such that, for
\*   all x in S, there exists an i in the domain of f such that f of i equals
\*   x."
Perms(S) == {f \in [1..Cardinality(S) -> S] : \A x \in S : \E i \in DOMAIN f : f[i] = x}

\* In English: "A message whose table, if any, is in ascending order", as
\* every encoder sends it (encodeVersions [R10]; gOuroboros sorts map keys).
\* Literally: "Msg of t, vm, v, p, r and big is defined as MsgK of t, vm, v, p,
\*   r, big and AscSeq of the domain of vm."
Msg(t, vm, v, p, r, big) == MsgK(t, vm, v, p, r, big, AscSeq(DOMAIN vm))

\* Literally: "Messages is defined as the set of records whose field type is a
\*   member of MsgTypes, field vmap is a member of Tables of Params, field v is
\*   a member of the union of Versions and the set containing 0, field p is a
\*   member of Params, field reason is a member of Reasons, field big is a
\*   member of BOOLEAN, and field keys is a member of the set of sequences of
\*   members of WireKeys."
Messages == [type : MsgTypes, vmap : Tables(Params), v : Versions \cup {0},
             p : Params, reason : Reasons, big : BOOLEAN, keys : Seq(WireKeys)]

\* In English: "The keys in sequence k ascend" (all of them), and "the
\* recognised keys in k ascend", ignoring any Unknown key [R10].
\* Literally: "AllAscend of k is defined as: for all i and j in the domain of
\*   k, if i is less than j, then k of i is less than k of j."
AllAscend(k) == \A i, j \in DOMAIN k : i < j => k[i] < k[j]
\* Literally: "RecognisedAscend of k is defined as: for all i and j in the
\*   domain of k, if i is less than j and k of i is a member of Versions and k
\*   of j is a member of Versions, then k of i is less than k of j."
RecognisedAscend(k) ==
    \A i, j \in DOMAIN k : (i < j /\ k[i] \in Versions /\ k[j] \in Versions) => k[i] < k[j]

\* In English: "The wire orders a client may send table t in: ascending;
\* or (UnknownAnywhere) with or without an Unknown key at any place and the
\* recognised keys ascending, which the reference accepts; or (Any) every
\* order, with or without the Unknown key."
\* Literally: "KeyOrders of t is defined as: letting plain be the union of
\*   Perms of the domain of t and Perms of the union of the domain of t and the
\*   set containing Unknown: in the case ClientKeyOrders equals "Ascending",
\*   the set containing AscSeq of the domain of t; in the case ClientKeyOrders
\*   equals "UnknownAnywhere", the set of every k in plain such that
\*   RecognisedAscend of k; in the case ClientKeyOrders equals "Any", plain."
KeyOrders(t) ==
    LET plain == Perms(DOMAIN t) \cup Perms(DOMAIN t \cup {Unknown}) IN
    CASE ClientKeyOrders = "Ascending"       -> {AscSeq(DOMAIN t)}
    []   ClientKeyOrders = "UnknownAnywhere" -> {k \in plain : RecognisedAscend(k)}
    []   ClientKeyOrders = "Any"             -> plain

\* In English: "The receiver rejects m's table for its key order: the
\* reference when its recognised keys do not ascend [R10]; the strict
\* variant when any keys do not ascend; gOuroboros main never."
\* Literally: "BadKeyOrder of m is defined as: in the case KeyOrderRule equals
\*   "Recognised", RecognisedAscend of m's keys is not true; in the case
\*   KeyOrderRule equals "Every", AllAscend of m's keys is not true; in the
\*   case KeyOrderRule equals "None", FALSE."
BadKeyOrder(m) ==
    CASE KeyOrderRule = "Recognised" -> ~RecognisedAscend(m.keys)
    []   KeyOrderRule = "Every"      -> ~AllAscend(m.keys)
    []   KeyOrderRule = "None"       -> FALSE

\* What a side ends with. `kind` is "None" (not finished), "Accept"
\* (version v agreed), "Refuse" (the server refused with `reason`),
\* "Query" (the supported versions were exchanged), or "Error" (the client
\* rejected the server's answer [R2]).
\* Literally: "Res of k, v and r is defined as the record whose field kind is
\*   k, field v is v, and field reason is r."
Res(k, v, r) == [kind |-> k, v |-> v, reason |-> r]
\* Literally: "NoResult is defined as Res of "None", 0 and "None"."
NoResult == Res("None", 0, "None")

\* Literally: "Failures is defined as the set containing "Violation" and
\*   "TimedOut"."
Failures == {"Violation", "TimedOut"}

\* In English: "StPropose belongs to the client, StConfirm to the server,
\* StDone to nobody." [S2][R1]
\* Literally: "Agency of s is defined as: in the case s equals "StPropose",
\*   "Client"; in the case s equals "StConfirm", "Server"; in the case s equals
\*   "StDone", "Nobody"."
Agency(s) == CASE s = "StPropose" -> "Client"
             []   s = "StConfirm" -> "Server"
             []   s = "StDone"    -> "Nobody"

\* The transitions as <<from, message, to>> [S2][R1]. MsgReplyVersions has
\* the same encoding as MsgProposeVersions [S2 479-484]; it is listed
\* under that name, legal in StConfirm, as the reference decodes it there
\* (Codec.hs 160-167).
\* Literally: "Transitions is defined as the set containing these five tuples:
\*   <<"StPropose", "MsgProposeVersions", "StConfirm">>, <<"StConfirm",
\*   "MsgProposeVersions", "StDone">>, <<"StConfirm", "MsgAcceptVersion",
\*   "StDone">>, <<"StConfirm", "MsgRefuse", "StDone">>, and <<"StConfirm",
\*   "MsgQueryReply", "StDone">>."
Transitions ==
    { <<"StPropose", "MsgProposeVersions", "StConfirm">>,
      <<"StConfirm", "MsgProposeVersions", "StDone">>,   \* as MsgReplyVersions
      <<"StConfirm", "MsgAcceptVersion",   "StDone">>,
      <<"StConfirm", "MsgRefuse",          "StDone">>,
      <<"StConfirm", "MsgQueryReply",      "StDone">> }

\* In English: "Message type t is legal in state s if some row starts with
\* s and t, except that MsgReplyVersions exists only where it is handled."
\* Literally: "IsLegal of s and t is defined as: there exists a tr in
\*   Transitions such that element 1 of tr equals s and element 2 of tr equals
\*   t; and if s equals "StConfirm" and t equals "MsgProposeVersions", then
\*   HandleReplyVersions."
IsLegal(s, t) ==
    /\ \E tr \in Transitions : tr[1] = s /\ tr[2] = t
    /\ (s = "StConfirm" /\ t = "MsgProposeVersions") => HandleReplyVersions

\* Literally: "Peer of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s."
\* Literally: "Awaiting of r and s is defined as: s is a member of the set
\*   containing "StPropose" and "StConfirm", and Agency of s equals Peer of r."
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
\* Literally: "Chosen of local and remote is defined as: letting common be the
\*   intersection of the domain of local and the domain of remote: if Mutation
\*   equals "LowestCommon" then Min of common, else Max of common."
Chosen(local, remote) ==
    LET common == DOMAIN local \cap DOMAIN remote IN
    IF Mutation = "LowestCommon" THEN Min(common) ELSE Max(common)

\* In English: "Negotiate(local, remote) is what a side with table local
\* decides about the proposal remote: refuse with VersionMismatch if no version
\* is common; otherwise, for the chosen version, refuse with DecodeError if
\* remote's data does not decode, refuse with Refused if the magics differ, and
\* accept otherwise."
\* Literally: "Negotiate of local and remote is defined as: letting common be
\*   the intersection of the domain of local and the domain of remote: if
\*   common equals the empty set then Res of "Refuse", 0 and "VersionMismatch";
\*   else, letting v be Chosen of local and remote: if remote of v's ok is not
\*   true, then Res of "Refuse", v, and (if Mutation equals "RefusedForDecode"
\*   then "Refused", else "DecodeError"); else if remote of v's magic does not
\*   equal local of v's magic and Mutation does not equal "SkipMagicCheck",
\*   then Res of "Refuse", v and "Refused"; else Res of "Accept", v and
\*   "None"."
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
\* Literally: "AnyQuery of remote is defined as: there exists a v in the domain
\*   of remote such that remote of v's ok is true and remote of v's query is
\*   true."
AnyQuery(remote) == \E v \in DOMAIN remote : remote[v].ok /\ remote[v].query

\* The server's answer. The reference negotiates first and answers
\* MsgQueryReply only if it accepted, and the agreed data (query = local ||
\* remote [R6]) asks for a query [R4]. gOuroboros (QueryFirst) answers
\* MsgQueryReply if any decodable proposed version asks for one.
\* In English: "If the gOuroboros rule is on and some version asks for a
\* query, reply Query; if negotiation accepted v and either side's data for
\* v asks for a query, reply Query; otherwise reply what negotiation says."
\* Literally: "ServerDecision of local and remote is defined as: letting d be
\*   Negotiate of local and remote: if QueryFirst is true and AnyQuery of
\*   remote, then Res of "Query", 0 and "None"; else if d's kind equals
\*   "Accept" and (local of d's v's query or remote of d's v's query), then Res
\*   of "Query", 0 and "None"; else d."
ServerDecision(local, remote) ==
    LET d == Negotiate(local, remote) IN
    IF QueryFirst /\ AnyQuery(remote) THEN Res("Query", 0, "None")
    ELSE IF d.kind = "Accept" /\ (local[d.v].query \/ remote[d.v].query)
         THEN Res("Query", 0, "None")
    ELSE d

\* In English: "The message carrying decision d from a server with table
\* local, answering table remote." An accept carries the agreed data for v
\* [S7][R9]; gOuroboros main (AcceptOwnData) sends the server's own data.
\* The client checks only its magic, which agreed data inherits [S4].
\* Literally: "AcceptData of local, remote and v is defined as: if
\*   AcceptOwnData then local of v, else Agree of local of v and remote of v."
AcceptData(local, remote, v) ==
    IF AcceptOwnData THEN local[v] ELSE Agree(local[v], remote[v])

\* In English: "The message that carries decision d."
\* Literally: "ReplyMsg of d, local and remote is defined as: in the case d's
\*   kind equals "Accept", Msg of "MsgAcceptVersion", the empty sequence, d's
\*   v, AcceptData of local, remote and d's v, "None" and FALSE; in the case
\*   d's kind equals "Refuse", Msg of "MsgRefuse", the empty sequence, d's v,
\*   NoParams, d's reason and FALSE; in the case d's kind equals "Query", Msg
\*   of "MsgQueryReply", local, 0, NoParams, "None" and FALSE."
ReplyMsg(d, local, remote) ==
    CASE d.kind = "Accept" -> Msg("MsgAcceptVersion", <<>>, d.v,
                                  AcceptData(local, remote, d.v), "None", FALSE)
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
\* In English: "How a client with table judges the server's answer m."
\* Literally: "ClientJudge of table and m is defined as: in the case m's type
\*   equals "MsgAcceptVersion": if m's v is not a member of the domain of table
\*   then Res of "Error", m's v and "None"; else if m's p's ok is not true then
\*   Res of "Error", m's v and "None"; else if m's p's magic does not equal
\*   table of m's v's magic and Mutation does not equal "ClientSkipMagicCheck",
\*   then Res of "Error", m's v and "None"; else Res of "Accept", m's v and
\*   "None". In the case m's type equals "MsgRefuse", Res of "Refuse", m's v
\*   and m's reason. In the case m's type equals "MsgQueryReply": if
\*   StrictQueryReply is true and there does not exist a v in the domain of
\*   table such that table of v's query is true, then Res of "Error", 0 and
\*   "None"; else Res of "Query", 0 and "None". In the case m's type equals
\*   "MsgProposeVersions", Negotiate of table and m's vmap."
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
\* Literally: "RefVersion is defined as Max of Versions."
RefVersion == Max(Versions)
\* In English: "The data, version and table the receive table uses."
\* Literally: "RefParams is defined as the record whose field magic is the m,
\*   chosen from Magics, such that TRUE; field query is FALSE; field ok is
\*   TRUE; and field init is FALSE."
RefParams  == [magic |-> CHOOSE m \in Magics : TRUE, query |-> FALSE, ok |-> TRUE,
               init |-> FALSE]
\* Literally: "RefTable is defined as the function that maps every v in the set
\*   containing RefVersion to RefParams."
RefTable   == [v \in {RefVersion} |-> RefParams]

\* Literally: "Kinds is defined as the set containing "MsgProposeVersions",
\*   "MsgAcceptVersion", "MsgRefuse", "MsgQueryReply" and "Oversized"."
Kinds == {"MsgProposeVersions", "MsgAcceptVersion", "MsgRefuse",
          "MsgQueryReply", "Oversized"}

\* In English: "The concrete message each kind stands for." MsgQueryReply
\* is unsolicited here, since RefTable does not ask for a query.
\* Literally: "KindMsg of k is defined as: in the case k equals
\*   "MsgProposeVersions", Msg of k, RefTable, 0, NoParams, "None" and FALSE;
\*   in the case k equals "MsgAcceptVersion", Msg of k, the empty sequence,
\*   RefVersion, RefParams, "None" and FALSE; in the case k equals "MsgRefuse",
\*   Msg of k, the empty sequence, 0, NoParams, "VersionMismatch" and FALSE; in
\*   the case k equals "MsgQueryReply", Msg of k, RefTable, 0, NoParams, "None"
\*   and FALSE; in the case k equals "Oversized", Msg of "MsgProposeVersions",
\*   RefTable, 0, NoParams, "None" and TRUE."
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
\* Literally: "Judge of r, s, m and table is defined as: if s equals "StDone"
\*   then "Violation"; else if Agency of s equals r then "Waits"; else if m's
\*   big is true then "Violation"; else if IsLegal of s and m's type is not
\*   true then "Violation"; else if r equals "Client" and ClientJudge of table
\*   and m's kind equals "Error" then "Error"; else element 3 of the tr, chosen
\*   from Transitions, such that element 1 of tr equals s and element 2 of tr
\*   equals m's type."
Judge(r, s, m, table) ==
    IF s = "StDone"            THEN "Violation"
    ELSE IF Agency(s) = r      THEN "Waits"
    ELSE IF m.big              THEN "Violation"
    ELSE IF ~IsLegal(s, m.type) THEN "Violation"
    ELSE IF r = "Client" /\ ClientJudge(table, m).kind = "Error" THEN "Error"
    ELSE (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = m.type)[3]

\* In English: "The receive table's entry for side r in state s and kind k."
\* Literally: "ReceiveTable of r, s and k is defined as Judge of r, s, KindMsg
\*   of k, and RefTable."
ReceiveTable(r, s, k) == Judge(r, s, KindMsg(k), RefTable)

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in
    inbox,      \* inbox[r]: messages sent to r not yet read
    table,      \* table[r]: side r's version table, fixed at the start
    result,     \* result[r]: how side r's handshake ended
    heard,      \* the table in the MsgProposeVersions the server answered
    rogueLeft   \* rogue messages the misbehaving peer may still inject

\* Literally: "vars is defined as the tuple of all six variables."
vars == <<view, inbox, table, result, heard, rogueLeft>>

\* In English: "Both sides start in StPropose with empty inboxes and no
\* result; the client has any non-empty table and the server any non-empty
\* table of its own."
\* Literally: "Init is defined as: view equals the function that maps every r
\*   in Roles to "StPropose", and inbox equals the function that maps every r
\*   in Roles to the empty sequence, and table is a member of the set of the
\*   record whose field Client is c and field Server is s, for every c that is
\*   a member of ClientTables and every s that is a member of ServerTables; and
\*   result equals the function that maps every r in Roles to NoResult, and
\*   heard equals the empty sequence, and rogueLeft equals RogueMessages."
Init ==
    /\ view = [r \in Roles |-> "StPropose"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ table \in {[Client |-> c, Server |-> s] : c \in ClientTables, s \in ServerTables}
    /\ result = [r \in Roles |-> NoResult]
    /\ heard = <<>>                     \* the server has heard nothing yet
    /\ rogueLeft = RogueMessages

\* In English: "The connection is over when someone has hung up, or both sides
\* are done."
\* Literally: "Ended is defined as: there exists an r in Roles such that view
\*   of r is a member of Failures, or, for all r in Roles, view of r equals
\*   "StDone"."
Ended ==
    \/ \E r \in Roles : view[r] \in Failures
    \/ \A r \in Roles : view[r] = "StDone"

\* In English: "A client in StPropose that is not silent sends its table and
\* moves to StConfirm." [S2]
\* Literally: "ClientPropose is defined as: SilentPeer does not equal "Client",
\*   and view of "Client" equals "StPropose", and view in the next state equals
\*   view except that its "Client" entry is "StConfirm", and there exists a k
\*   in KeyOrders of table of "Client" such that inbox in the next state equals
\*   inbox except that its "Server" entry is the old entry with MsgK of
\*   "MsgProposeVersions", table of "Client", 0, NoParams, "None", FALSE and k
\*   appended; and table, result, heard and rogueLeft are unchanged."
ClientPropose ==
    /\ SilentPeer /= "Client"
    /\ view["Client"] = "StPropose"
    /\ view' = [view EXCEPT !["Client"] = "StConfirm"]
    /\ \E k \in KeyOrders(table["Client"]) :                  \* the keys' wire order
         inbox' = [inbox EXCEPT !["Server"] =
                     Append(@, MsgK("MsgProposeVersions", table["Client"], 0, NoParams, "None", FALSE, k))]
    /\ UNCHANGED <<table, result, heard, rogueLeft>>

\* In English: "A server in StPropose that is not silent reads the oldest
\* message. Too big, not MsgProposeVersions, or (reference) a table with
\* its keys out of order [R10]: violation. Otherwise it
\* decides, sends its answer, and is done." The read and the answer are one
\* step: the reference yields at once [R4], gOuroboros answers inside its
\* message handler, so a server never rests in StConfirm.
\* Literally: "ServerRecv is defined as: SilentPeer does not equal "Server",
\*   and view of "Server" equals "StPropose", and inbox of "Server" does not
\*   equal the empty sequence, and, letting m be the head of inbox of "Server",
\*   and d be ServerDecision of table of "Server" and m's vmap: if m's big is
\*   true, or IsLegal of "StPropose" and m's type is not true, or BadKeyOrder
\*   of m, then (view in the next state equals view except that its "Server"
\*   entry is "Violation", and result and heard are unchanged, and inbox in the
\*   next state equals inbox except that its "Server" entry is the tail of the
\*   old entry), else (view in the next state equals view except that its
\*   "Server" entry is "StDone", and result in the next state equals result
\*   except that its "Server" entry is d, and heard in the next state equals
\*   m's vmap, and inbox in the next state equals inbox except that its
\*   "Server" entry is the tail of the old entry and its "Client" entry is the
\*   old entry with ReplyMsg of d, table of "Server" and m's vmap appended);
\*   and table and rogueLeft are unchanged."
ServerRecv ==
    /\ SilentPeer /= "Server"
    /\ view["Server"] = "StPropose"
    /\ inbox["Server"] /= <<>>
    /\ LET m == Head(inbox["Server"])
           d == ServerDecision(table["Server"], m.vmap) IN
       IF m.big \/ ~IsLegal("StPropose", m.type) \/ BadKeyOrder(m)
       THEN /\ view' = [view EXCEPT !["Server"] = "Violation"]       \* hang up
            /\ UNCHANGED <<result, heard>>
            /\ inbox' = [inbox EXCEPT !["Server"] = Tail(@)]
       ELSE /\ view' = [view EXCEPT !["Server"] = "StDone"]          \* answered, done
            /\ result' = [result EXCEPT !["Server"] = d]
            /\ heard' = m.vmap                                       \* remember what it answered
            /\ inbox' = [inbox EXCEPT !["Server"] = Tail(@),
                                      !["Client"] = Append(@, ReplyMsg(d, table["Server"], m.vmap))]
    /\ UNCHANGED <<table, rogueLeft>>

\* In English: "A client in StConfirm reads the oldest message. Too big,
\* not legal in StConfirm, or (reference) a table with its keys out of
\* order [R10]: violation. Otherwise it judges the answer, is done, and
\* keeps the result."
\* Literally: "ClientRecv is defined as: view of "Client" equals "StConfirm",
\*   and inbox of "Client" does not equal the empty sequence, and, letting m be
\*   the head of inbox of "Client": if m's big is true, or IsLegal of
\*   "StConfirm" and m's type is not true, or BadKeyOrder of m, then (view in
\*   the next state equals view except that its "Client" entry is "Violation",
\*   and result is unchanged), else (view in the next state equals view except
\*   that its "Client" entry is "StDone", and result in the next state equals
\*   result except that its "Client" entry is ClientJudge of table of "Client"
\*   and m); and inbox in the next state equals inbox except that its "Client"
\*   entry is the tail of the old entry, and table, heard and rogueLeft are
\*   unchanged."
ClientRecv ==
    /\ view["Client"] = "StConfirm"
    /\ inbox["Client"] /= <<>>
    /\ LET m == Head(inbox["Client"]) IN
       IF m.big \/ ~IsLegal("StConfirm", m.type) \/ BadKeyOrder(m)
       THEN /\ view' = [view EXCEPT !["Client"] = "Violation"]
            /\ UNCHANGED result
       ELSE /\ view' = [view EXCEPT !["Client"] = "StDone"]
            /\ result' = [result EXCEPT !["Client"] = ClientJudge(table["Client"], m)]
    /\ inbox' = [inbox EXCEPT !["Client"] = Tail(@)]
    /\ UNCHANGED <<table, heard, rogueLeft>>

\* In English: "A side in StDone that finds a message tears the connection
\* down: mini-protocol 0 no longer runs [R7]."
\* Literally: "DoneRecv of r is defined as: view of r equals "StDone", and
\*   inbox of r does not equal the empty sequence, and view in the next state
\*   equals view except that its r entry is "Violation", and inbox in the next
\*   state equals inbox except that its r entry is the tail of the old entry,
\*   and table, result, heard and rogueLeft are unchanged."
DoneRecv(r) ==
    /\ view[r] = "StDone"
    /\ inbox[r] /= <<>>
    /\ view' = [view EXCEPT ![r] = "Violation"]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<table, result, heard, rogueLeft>>

\* In English: "The rogue peer may put any message, of any size, in r's
\* inbox, while it has allowance left."
\* Literally: "Inject of r and m is defined as: rogueLeft is greater than 0,
\*   and inbox in the next state equals inbox except that its r entry is the
\*   old entry with m appended, and rogueLeft in the next state equals
\*   rogueLeft minus 1, and view, table, result and heard are unchanged."
Inject(r, m) ==
    /\ rogueLeft > 0
    /\ inbox' = [inbox EXCEPT ![r] = Append(@, m)]
    /\ rogueLeft' = rogueLeft - 1
    /\ UNCHANGED <<view, table, result, heard>>

\* The messages the rogue peer picks from: each kind of the receive table,
\* plus an accept for every version and data, so the client's checks on
\* MsgAcceptVersion are all exercised; with ClientKeyOrders "Any", also
\* each table-carrying message with every version in every wire order.
\* Literally: "FullTable is defined as the function that maps every v in
\*   Versions to RefParams."
FullTable == [v \in Versions |-> RefParams]
\* Literally: "RogueSet is defined as the union of: the set of KindMsg of k,
\*   for every k that is a member of Kinds; the set of Msg of
\*   "MsgAcceptVersion", the empty sequence, v, p, "None" and FALSE, for every
\*   v that is a member of Versions and every p that is a member of Params; and
\*   the set of MsgK of t, FullTable, 0, NoParams, "None", FALSE and k, for
\*   every t that is a member of (if ClientKeyOrders equals "Any" then the set
\*   containing "MsgProposeVersions" and "MsgQueryReply", else the empty set)
\*   and every k that is a member of KeyOrders of FullTable."
RogueSet ==
    {KindMsg(k) : k \in Kinds} \cup
    {Msg("MsgAcceptVersion", <<>>, v, p, "None", FALSE) : v \in Versions, p \in Params} \cup
    {MsgK(t, FullTable, 0, NoParams, "None", FALSE, k) :
        t \in IF ClientKeyOrders = "Any"
              THEN {"MsgProposeVersions", "MsgQueryReply"} ELSE {},
        k \in KeyOrders(FullTable)}

\* In English: "Progress is possible: some honest send or read."
\* Literally: "Progress is defined as: ClientPropose, or ServerRecv, or
\*   ClientRecv, or there exists an r in Roles such that DoneRecv of r."
Progress == ClientPropose \/ ServerRecv \/ ClientRecv \/ \E r \in Roles : DoneRecv(r)

\* Timeouts [S3][R5]: node-to-node waits at most 10 s in each state, then
\* tears the connection down; node-to-client has no timeouts. The model has
\* no clock: a timeout fires only when nothing else can happen, which is
\* when the peer is silent.
\* In English: "In node-to-node mode, a side waiting for a peer that will
\* never send can give up."
\* Literally: "Timeout of r is defined as: Mode equals "NtN", and Ended is not
\*   true, and Awaiting of r and view of r, and Progress is not enabled, and
\*   view in the next state equals view except that its r entry is "TimedOut",
\*   and inbox, table, result, heard and rogueLeft are unchanged."
Timeout(r) ==
    /\ Mode = "NtN"
    /\ ~Ended
    /\ Awaiting(r, view[r])
    /\ ~ENABLED Progress
    /\ view' = [view EXCEPT ![r] = "TimedOut"]
    /\ UNCHANGED <<inbox, table, result, heard, rogueLeft>>

\* In English: "A step is progress, or some side timing out, or the rogue peer
\* injecting some message, or, once the connection is over, nothing changing."
\* Literally: "Next is defined as: Progress, or there exists an r in Roles such
\*   that Timeout of r, or there exists an r in Roles and an m in RogueSet such
\*   that Inject of r and m, or Ended is true and vars is unchanged."
Next ==
    \/ Progress
    \/ \E r \in Roles : Timeout(r)
    \/ \E r \in Roles, m \in RogueSet : Inject(r, m)
    \/ Ended /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: view is a member of the set of functions
\*   from Roles to the union of States and Failures, and inbox is a member of
\*   the set of functions from Roles to the set of sequences of members of
\*   Messages, and table of "Client" is a member of ClientTables, and table of
\*   "Server" is a member of ServerTables, and result is a member of the set of
\*   functions from Roles to the set of records whose field kind is a member of
\*   the set containing "None", "Accept", "Refuse", "Query" and "Error", field
\*   v is a member of the union of Versions and the set containing 0, and field
\*   reason is a member of Reasons; and heard is a member of Tables of Params,
\*   and rogueLeft is a member of 0 through RogueMessages."
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
\* Literally: "Common is defined as the intersection of the domain of heard and
\*   the domain of table of "Server"."
Common      == DOMAIN heard \cap DOMAIN table["Server"]
\* Literally: "Highest is defined as Max of Common."
Highest     == Max(Common)
\* Literally: "CData is defined as heard of Highest."
CData       == heard[Highest]               \* the proposer's data for Highest
\* Literally: "SData is defined as table of "Server" of Highest."
SData       == table["Server"][Highest]     \* the server's data for Highest
\* Literally: "Negotiable is defined as: Common does not equal the empty set,
\*   and CData's ok is true, and CData's magic equals SData's magic."
Negotiable  == Common /= {} /\ CData.ok /\ CData.magic = SData.magic

\* In English: "No side has hung up." With honest peers this must hold.
\* Literally: "NoFailures is defined as: for all r in Roles, view of r is not a
\*   member of Failures."
NoFailures == \A r \in Roles : view[r] \notin Failures

\* In English: "No side has seen a protocol violation."
\* Literally: "NoViolations is defined as: for all r in Roles, view of r does
\*   not equal "Violation"."
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* In English: "If the server accepted v, v is the highest version both
\* sides support [S5 step 3]."
\* Literally: "AcceptsHighestCommon is defined as: if result of "Server"'s kind
\*   equals "Accept", then result of "Server"'s v is a member of Common, and
\*   for all w in Common, w is less than or equal to result of "Server"'s v."
AcceptsHighestCommon ==
    result["Server"].kind = "Accept" =>
        /\ result["Server"].v \in Common
        /\ \A w \in Common : w <= result["Server"].v

\* In English: "If the server accepted, the client's data decodes and the
\* magics agree [S4][S5 steps 4-7]."
\* Literally: "AcceptsOnlyMatchingMagic is defined as: if result of "Server"'s
\*   kind equals "Accept", then Negotiable."
AcceptsOnlyMatchingMagic ==
    result["Server"].kind = "Accept" => Negotiable

\* In English: "Each refusal names the right reason [S5]: VersionMismatch
\* only when nothing is common; DecodeError, for the highest common
\* version, only when the client's data for it does not decode; Refused,
\* for that version, only when it decodes and the magics differ."
\* Literally: "RefusalReasonsRight is defined as: letting r be result of
\*   "Server": if r's kind equals "Refuse", then: in the case r's reason equals
\*   "VersionMismatch", Common equals the empty set; in the case r's reason
\*   equals "DecodeError", Common does not equal the empty set and r's v equals
\*   Highest and CData's ok is not true; in the case r's reason equals
\*   "Refused", Common does not equal the empty set and r's v equals Highest
\*   and CData's ok is true and CData's magic does not equal SData's magic; in
\*   every other case, FALSE."
RefusalReasonsRight ==
    LET r == result["Server"] IN
    r.kind = "Refuse" =>
        CASE r.reason = "VersionMismatch" -> Common = {}
        []   r.reason = "DecodeError"     -> Common /= {} /\ r.v = Highest /\ ~CData.ok
        []   r.reason = "Refused"         -> Common /= {} /\ r.v = Highest /\ CData.ok
                                             /\ CData.magic /= SData.magic
        []   OTHER                        -> FALSE

\* In English: "The server never refuses a negotiable proposal."
\* Literally: "NoRefusalWhenNegotiable is defined as: if result of "Server"'s
\*   kind equals "Refuse", then Negotiable is not true."
NoRefusalWhenNegotiable ==
    result["Server"].kind = "Refuse" => ~Negotiable

\* In English: "The server answers MsgQueryReply only when negotiation
\* would accept, and the client's data for the chosen version asks for a
\* query [R4][R6]."
\* Literally: "QueryOnlyWhenNegotiable is defined as: if result of "Server"'s
\*   kind equals "Query", then Negotiable and CData's query is true."
QueryOnlyWhenNegotiable ==
    result["Server"].kind = "Query" => Negotiable /\ CData.query

\* In English: "When both sides are done, they agree: the same version
\* accepted, or the same refusal, or both a query."
\* Literally: "BothSidesAgree is defined as: if, for all r in Roles, view of r
\*   equals "StDone", then result of "Client"'s kind equals result of
\*   "Server"'s kind, and (if result of "Client"'s kind is a member of the set
\*   containing "Accept" and "Refuse", then result of "Client"'s v equals
\*   result of "Server"'s v), and result of "Client"'s reason equals result of
\*   "Server"'s reason."
BothSidesAgree ==
    (\A r \in Roles : view[r] = "StDone") =>
        /\ result["Client"].kind = result["Server"].kind
        /\ result["Client"].kind \in {"Accept", "Refuse"} =>
               result["Client"].v = result["Server"].v
        /\ result["Client"].reason = result["Server"].reason

\* In English: "In every step where the client accepts a MsgAcceptVersion,
\* it proposed that version, the data decodes, and the magic is its own."
\* With a rogue server this is the client's own defence [R2].
\* Literally: "ClientAcceptsOnlyProposed is defined as: always, for every step,
\*   if (view of "Client" equals "StConfirm", and inbox of "Client" does not
\*   equal the empty sequence, and the head of inbox of "Client"'s type equals
\*   "MsgAcceptVersion", and result in the next state of "Client"'s kind equals
\*   "Accept"), then, letting m be the head of inbox of "Client": m's v is a
\*   member of the domain of table of "Client", and m's p's ok is true, and m's
\*   p's magic equals table of "Client" of m's v's magic."
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

\* In English: "In every step where the server accepts, the
\* MsgAcceptVersion it sends carries the negotiated data: the result of
\* combining its own data for v with the client's [S7][R9]."
\* Literally: "AcceptCarriesNegotiatedData is defined as: always, for every
\*   step, if (view of "Server" equals "StPropose", and result in the next
\*   state of "Server"'s kind equals "Accept"), then, letting v be result in
\*   the next state of "Server"'s v, and out be element (the length of inbox in
\*   the next state of "Client") of inbox in the next state of "Client": out's
\*   type equals "MsgAcceptVersion", and out's p equals Agree of table of
\*   "Server" of v and heard in the next state of v."
AcceptCarriesNegotiatedData ==
    [][ (/\ view["Server"] = "StPropose"
         /\ result'["Server"].kind = "Accept")
        => LET v   == result'["Server"].v
               out == inbox'["Client"][Len(inbox'["Client"])]   \* what it just sent
           IN /\ out.type = "MsgAcceptVersion"
              /\ out.p = Agree(table["Server"][v], heard'[v])
      ]_vars

\* In English: "In every step where a side reads a message whose version
\* table arrived with its recognised keys out of order, that side hangs up
\* [R10]." A read is the only step that shortens r's inbox.
\* Literally: "Reads of r is defined as: view of r is a member of the set
\*   containing "StPropose" and "StConfirm", and inbox of r does not equal the
\*   empty sequence, and the length of inbox in the next state of r is less
\*   than the length of inbox of r."
Reads(r) ==
    /\ view[r] \in {"StPropose", "StConfirm"}
    /\ inbox[r] /= <<>>
    /\ Len(inbox'[r]) < Len(inbox[r])
\* Literally: "UnorderedMapsRejected is defined as: always, for every step, for
\*   all r in Roles, if Reads of r and RecognisedAscend of the head of inbox of
\*   r's keys is not true, then view in the next state of r equals
\*   "Violation"."
UnorderedMapsRejected ==
    [][\A r \in Roles :
         (Reads(r) /\ ~RecognisedAscend(Head(inbox[r]).keys))
         => view'[r] = "Violation"
      ]_vars

\* In English: "In every step where a side reads a table whose recognised
\* keys ascend, the order of the keys is not why it hangs up": an
\* unrecognised key anywhere is skipped, as the reference skips it [R10].
\* Checked as: such a read ends in violation only for a reason other than
\* the order (too big, or not legal in the state).
\* Literally: "UnknownKeysTolerated is defined as: always, for every step, for
\*   all r in Roles, if (Reads of r, and RecognisedAscend of the head of inbox
\*   of r's keys, and the head of inbox of r's big is not true, and IsLegal of
\*   view of r and the head of inbox of r's type), then view in the next state
\*   of r does not equal "Violation"."
UnknownKeysTolerated ==
    [][\A r \in Roles :
         (/\ Reads(r)
          /\ RecognisedAscend(Head(inbox[r]).keys)
          /\ ~Head(inbox[r]).big
          /\ IsLegal(view[r], Head(inbox[r]).type))
         => view'[r] /= "Violation"
      ]_vars

\* In English: "It is never the case that both sides believe they may send."
\* Literally: "NeverBothHaveAgency is defined as: it is not the case that (view
\*   of "Client" is a member of States and Agency of it equals "Client", and
\*   view of "Server" is a member of States and Agency of it equals "Server")."
NeverBothHaveAgency ==
    ~ /\ view["Client"] \in States /\ Agency(view["Client"]) = "Client"
      /\ view["Server"] \in States /\ Agency(view["Server"]) = "Server"

\* THE STATES THAT CANNOT BE ENTERED.
\* In English: "In every step, for every side, a change of state is to a
\* failure or along a row of the transition table; nothing leaves StDone
\* except to a failure."
\* Literally: "OnlyLegalMoves is defined as: always, for every step, for all r
\*   in Roles, if view in the next state of r does not equal view of r, then
\*   view in the next state of r is a member of Failures, or there exists a tr
\*   in Transitions such that element 1 of tr equals view of r and element 3 of
\*   tr equals view in the next state of r, or (r equals "Server" and view of r
\*   equals "StPropose" and view in the next state of r equals "StDone")."
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
\* Literally: "FailuresAreFinal is defined as: always, for every step, for all
\*   r in Roles, if view of r is a member of Failures, then view in the next
\*   state of r equals view of r."
FailuresAreFinal ==
    [][\A r \in Roles : view[r] \in Failures => view'[r] = view[r]]_vars

\* In English: "A timeout fires only in node-to-node mode."
\* Literally: "TimeoutsOnlyNtN is defined as: if there exists an r in Roles
\*   such that view of r equals "TimedOut", then Mode equals "NtN"."
TimeoutsOnlyNtN ==
    (\E r \in Roles : view[r] = "TimedOut") => Mode = "NtN"

-----------------------------------------------------------------------------
(* Reachability probes. Each claims something never happens; TLC must find *)
(* it does. Run with the matching *ProbeBug.cfg.                           *)

\* In English: "Probes, each expected to be violated: the server never accepts,
\* never answers a query, never refuses for each reason."
\* Literally: "ProbeNeverAccept is defined as: result of "Server"'s kind does
\*   not equal "Accept"."
ProbeNeverAccept         == result["Server"].kind /= "Accept"
\* Literally: "ProbeNeverQuery is defined as: result of "Server"'s kind does
\*   not equal "Query"."
ProbeNeverQuery          == result["Server"].kind /= "Query"
\* Literally: "ProbeNeverMismatch is defined as: result of "Server"'s reason
\*   does not equal "VersionMismatch"."
ProbeNeverMismatch       == result["Server"].reason /= "VersionMismatch"
\* Literally: "ProbeNeverDecodeError is defined as: result of "Server"'s reason
\*   does not equal "DecodeError"."
ProbeNeverDecodeError    == result["Server"].reason /= "DecodeError"
\* Literally: "ProbeNeverRefused is defined as: result of "Server"'s reason
\*   does not equal "Refused"."
ProbeNeverRefused        == result["Server"].reason /= "Refused"
\* "The highest common version is never below some other proposed
\* version": false whenever the client proposes a version the server lacks.
\* Literally: "ProbeNeverAcceptBelowProposed is defined as: it is not the case
\*   that (result of "Server"'s kind equals "Accept", and there exists a w in
\*   the domain of table of "Client" such that w is greater than result of
\*   "Server"'s v)."
ProbeNeverAcceptBelowProposed ==
    ~ /\ result["Server"].kind = "Accept"
      /\ \E w \in DOMAIN table["Client"] : w > result["Server"].v
=============================================================================
