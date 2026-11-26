------------------------- MODULE HandshakeVersionData -------------------------
(***************************************************************************)
(* The version data layer of the handshake: which version numbers each     *)
(* side knows, what data each version carries on the wire, which data a    *)
(* receiver decodes, and how two sides combine their data into the agreed  *)
(* data. Handshake.tla checks the message exchange with one combined flag  *)
(* standing for every field; this module checks the fields themselves:     *)
(* diffusion mode, peer sharing, query, and Peras support, for Cardano     *)
(* node-to-node and DMQ node-to-node.                                      *)
(*                                                                         *)
(* One run is one handshake: Init picks the two sides (each the reference  *)
(* or gOuroboros, or a peer that sends anything), their settings and their *)
(* version tables; Answer is the server's reply; Finish is the client's    *)
(* end. The network magic is left out (always equal): Handshake.tla checks *)
(* it.                                                                     *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network 5f356486ab3e (main, unreleased  *)
(* changes included); cardano-diffusion 1.3.0.1 (the latest release) where *)
(* said; IntersectMBO/dmq-node 67a1a1e5a579.                               *)
(*   [V1] cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs  *)
(*        86-117: the versions are 14, 15, 16, 17; 134-149:                *)
(*        acceptableVersion: diffusion mode `min` (initiator-only wins),   *)
(*        peerSharing local <> remote, query local || remote, perasSupport *)
(*        `min`; 158-167: minPerasVersion = NodeToNodeV_17; 180-236: the   *)
(*        data is [magic, initiatorOnly, peerSharing, query] plus          *)
(*        [perasSupport] from minPerasVersion on, and peerSharing decodes  *)
(*        only 0 or 1.                                                     *)
(*   [V2] cardano-diffusion changelog.d/20261008_170232_coot_tx_submission_*)
(*        leios.md: Peras moved from NodeToNodeV_16 to NodeToNodeV_17, and *)
(*        NodeToNodeV_16 "is not compatible with NodeToNodeV_16 of         *)
(*        previous releases"; CHANGELOG.md 49-53 (1.1.0.0): V16 added with *)
(*        the perasSupport field. So the release has 14, 15, 16 with Peras *)
(*        at 16, main has 14 to 17 with Peras at 17.                       *)
(*   [V3] ouroboros-network/api/lib/Ouroboros/Network/PeerSelection/      *)
(*        PeerSharing.hs 19-31: PeerSharingDisabled <> _ = Disabled.       *)
(*        DiffusionMode.hs 24-27 and PerasSupport.hs 21-23: the orders     *)
(*        InitiatorOnly < InitiatorAndResponder, Unsupported < Supported.  *)
(*   [V4] dmq-node/src/DMQ/NodeToNode/Version.hs 41-44: versions 1, 2;     *)
(*        98-116: acceptableVersion as Cardano's, but peer sharing is      *)
(*        Disabled when the agreed diffusion mode is initiator-only;       *)
(*        148-168: the data is exactly four fields, peerSharing 0 or 1.    *)
(*   [V5] ouroboros-network/framework/lib/Ouroboros/Network/Protocol/      *)
(*        Handshake/Codec.hs 210-241 (decodeVersions): a key the version   *)
(*        codec does not recognise, an integer it does not know or any     *)
(*        other term, is skipped; 168-175: MsgAcceptVersion with a version *)
(*        the client does not recognise fails to decode.                   *)
(*   [V6] .../Handshake/Client.hs 147-172: on MsgAcceptVersion the client  *)
(*        decodes the data and ends with acceptVersion vData vData', its   *)
(*        own agreement of its data with the server's; 191-218            *)
(*        (acceptOrRefuse): the highest common version, DecodeError when   *)
(*        its data does not decode.                                        *)
(*   [V7] .../Handshake/Server.hs 42-44: MsgAcceptVersion carries the      *)
(*        agreed data.                                                     *)
(*                                                                         *)
(* gOuroboros at 7cd17437: protocol/versions.go (protocolVersions,         *)
(* GetProtocolVersionMapWithPerasSupport, GetProtocolVersionMapDMQNtN),    *)
(* protocol/versiondata.go (the decoders), protocol/handshake/            *)
(* version_data.go (agreedVersionData), server.go (handleProposeVersions), *)
(* client.go (handleAcceptVersion), messages.go and collection_decode.go   *)
(* (the version map's uint16 keys).                                        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend in specs/keepalive/KeepAlive.tla*)
(* and Handshake.tla. New here:                                            *)
(*   a..b              the integers from a to b                            *)
(*   [x \in S |-> e]   the function that maps each x in S to e             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Family,             \* "CardanoNtN" or "DMQNtN"
    RefRev,             \* the reference: "Main" (5f356486ab3e) or "Released" (cardano-diffusion 1.3.0.1)
    GoPerasFrom,        \* the node-to-node version from which gOuroboros carries the Peras field: 16 today
    GoKnows17,          \* TRUE: gOuroboros knows node-to-node version 17
    GoDMQRule,          \* TRUE: gOuroboros disables DMQ peer sharing when the agreed mode is initiator-only
    GoPeerSharingRange, \* TRUE: gOuroboros decodes peer sharing 0 or 1 only, as the reference
    GoClientAgrees,     \* TRUE: the gOuroboros client ends with its agreement of its data with the server's
    GoSkipsWideKeys,    \* TRUE: gOuroboros skips a version key it cannot hold in a uint16
    Mutation            \* "None", or a safeguard switched off: "DiffusionAnd", "PerasOr", "LowestCommon"

\* In English: "The two implementations, and the peers that are not one of
\* them: a client that sends any proposal, a server that sends any accept,
\* and a gOuroboros server from before it sent the agreed data."
\* Literally: "Impls is defined as the set containing "Ref" and "Go"."
Impls == {"Ref", "Go"}

\* A version no implementation knows, in uint16 range (a newer release's).
\* Literally: "UnknownKey is defined as 100."
UnknownKey == 100
\* A key gOuroboros cannot hold in its map[uint16]: above 65535, or a term
\* that is not an unsigned integer. The reference skips it like any key it
\* does not recognise [V5].
\* Literally: "WideKey is defined as 70000."
WideKey == 70000

\* In English: "The versions implementation i knows in this family."
\* Literally: "Known of i is defined as: if Family equals "DMQNtN" then the
\*   set containing 1 and 2; else if i equals "Ref" then (if RefRev equals
\*   "Main" then 14 through 17, else 14 through 16); else 14 through 16,
\*   with 17 added if GoKnows17."
Known(i) ==
    IF Family = "DMQNtN" THEN {1, 2}                                   \* [V4]
    ELSE IF i = "Ref" THEN (IF RefRev = "Main" THEN 14..17 ELSE 14..16) \* [V1][V2]
    ELSE 14..16 \cup (IF GoKnows17 THEN {17} ELSE {})                  \* versions.go
\* Literally: "AllKeys is defined as the union of Known of "Ref", Known of
\*   "Go", and the set containing UnknownKey and WideKey."
AllKeys == Known("Ref") \cup Known("Go") \cup {UnknownKey, WideKey}

\* In English: "The first version that carries the Peras field: none in
\* DMQ; 17 in the reference main, 16 in its release [V1][V2]; GoPerasFrom
\* in gOuroboros."
\* Literally: "PerasFrom of i is defined as: if Family equals "DMQNtN" then
\*   1000; else if i equals "Ref" then (if RefRev equals "Main" then 17
\*   else 16); else GoPerasFrom."
PerasFrom(i) ==
    IF Family = "DMQNtN" THEN 1000
    ELSE IF i = "Ref" THEN (IF RefRev = "Main" THEN 17 ELSE 16)
    ELSE GoPerasFrom

\* Version data on the wire. `init` is the initiator-only flag (TRUE:
\* initiator-only); `ps` the peer sharing number (2 is out of range);
\* `peras` "absent" when the field is not sent, else "no" or "yes".
\* Literally: "Wire is defined as the set of records whose field init is a
\*   member of BOOLEAN, field ps is a member of 0 through 2, field query is
\*   a member of BOOLEAN, and field peras is a member of the set containing
\*   "absent", "no" and "yes"."
Wire == [init : BOOLEAN, ps : 0..2, query : BOOLEAN, peras : {"absent", "no", "yes"}]
\* Decoded version data, as a side holds it.
\* Literally: "Data is defined as the set of records whose field init is a
\*   member of BOOLEAN, field ps is a member of 0 through 2, field query is a
\*   member of BOOLEAN, and field peras is a member of BOOLEAN."
Data == [init : BOOLEAN, ps : 0..2, query : BOOLEAN, peras : BOOLEAN]
\* An honest side's settings; it never asks for a query here (Handshake.tla
\* checks the query reply).
\* Literally: "Settings is defined as the set of records whose field init is
\*   a member of BOOLEAN, field ps is a member of 0 through 1, and field
\*   peras is a member of BOOLEAN."
Settings == [init : BOOLEAN, ps : 0..1, peras : BOOLEAN]

\* In English: "What implementation i sends for version v with settings s:
\* the Peras field only from PerasFrom(i) on" (reference: encodeTerm and
\* getLocalPerasSupport [V1]; gOuroboros: GetProtocolVersionMapWithPerasSupport).
\* Literally: "Encode of i, v and s is defined as the record whose field init
\*   is s's init, field ps is s's ps, field query is FALSE, and field peras
\*   is, if v is at least PerasFrom of i, "yes" when s's peras and "no"
\*   otherwise, else "absent"."
Encode(i, v, s) ==
    [init |-> s.init, ps |-> s.ps, query |-> FALSE,
     peras |-> IF v >= PerasFrom(i) THEN (IF s.peras THEN "yes" ELSE "no") ELSE "absent"]

\* In English: "Implementation i decodes data w for version v when the Peras
\* field is there exactly from PerasFrom(i) on, and the peer sharing number
\* is 0 or 1 (gOuroboros only with GoPeerSharingRange)" [V1][V4].
\* Literally: "Decodes of i, v and w is defined as: (w's peras does not equal
\*   "absent") equals (v is at least PerasFrom of i), and if i equals "Ref"
\*   or GoPeerSharingRange then w's ps is a member of the set containing 0
\*   and 1."
Decodes(i, v, w) ==
    /\ (w.peras /= "absent") = (v >= PerasFrom(i))                      \* exact field count
    /\ (i = "Ref" \/ GoPeerSharingRange) => w.ps \in {0, 1}           \* decodePeerSharing
\* Literally: "Dec of w is defined as the record whose field init is w's
\*   init, field ps is w's ps, field query is w's query, and field peras is
\*   (w's peras equals "yes")."
Dec(w) == [init |-> w.init, ps |-> w.ps, query |-> w.query, peras |-> w.peras = "yes"]
\* In English: "The wire form of data d for version v, as implementation i
\* sends it."
\* Literally: "Enc of i, v and d is defined as the record whose field init
\*   is d's init, field ps is d's ps, field query is d's query, and field
\*   peras is, if v is at least PerasFrom of i, "yes" when d's peras and "no"
\*   otherwise, else "absent"."
Enc(i, v, d) ==
    [init |-> d.init, ps |-> d.ps, query |-> d.query,
     peras |-> IF v >= PerasFrom(i) THEN (IF d.peras THEN "yes" ELSE "no") ELSE "absent"]

\* Literally: "MinN of a and b is defined as: if a is at most b then a else b."
MinN(a, b) == IF a <= b THEN a ELSE b

\* In English: "The reference agreement of l and r [V1][V3][V4]:
\* initiator-only if either is; peer sharing disabled if either disables it
\* (and in DMQ also when the agreed mode is initiator-only); query if
\* either asks; Peras only if both support it."
\* Literally: "RefAgree of l and r is defined as: letting init be l's init or
\*   r's init: the record whose field init is init, field ps is (if Family
\*   equals "DMQNtN" and init then 0, else MinN of l's ps and r's ps), field
\*   query is l's query or r's query, and field peras is l's peras and r's
\*   peras."
RefAgree(l, r) ==
    LET init == l.init \/ r.init IN                                    \* min of the modes
    [init  |-> init,
     ps    |-> IF Family = "DMQNtN" /\ init THEN 0 ELSE MinN(l.ps, r.ps), \* <> / [V4]
     query |-> l.query \/ r.query,
     peras |-> l.peras /\ r.peras]                                     \* min

\* In English: "gOuroboros's agreement (agreedVersionData): the same, but
\* in DMQ peer sharing is disabled for initiator-only only with GoDMQRule;
\* the mutations combine the diffusion mode or Peras the wrong way."
\* Literally: "GoAgree of l and r is defined as: letting init be (if Mutation
\*   equals "DiffusionAnd" then l's init and r's init, else l's init or r's
\*   init): the record whose field init is init, field ps is (if Family
\*   equals "DMQNtN" and GoDMQRule and init then 0, else MinN of l's ps and
\*   r's ps), field query is l's query or r's query, and field peras is (if
\*   Mutation equals "PerasOr" then l's peras or r's peras, else l's peras
\*   and r's peras)."
GoAgree(l, r) ==
    LET init == IF Mutation = "DiffusionAnd" THEN l.init /\ r.init ELSE l.init \/ r.init IN
    [init  |-> init,
     ps    |-> IF Family = "DMQNtN" /\ GoDMQRule /\ init THEN 0 ELSE MinN(l.ps, r.ps),
     query |-> l.query \/ r.query,
     peras |-> IF Mutation = "PerasOr" THEN l.peras \/ r.peras ELSE l.peras /\ r.peras]
\* Literally: "Agree of i, l and r is defined as: if i equals "Ref" then
\*   RefAgree of l and r, else GoAgree of l and r."
Agree(i, l, r) == IF i = "Ref" THEN RefAgree(l, r) ELSE GoAgree(l, r)

\* Literally: "Max of S is defined as the x, chosen from S, such that for all
\*   y in S, y is at most x." Min likewise.
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* What a side ends with. `kind` is "None", "Accept", "Refuse", or "Error"
\* (the message did not decode, or the client rejected the answer).
\* Literally: "Res of k, v, r and d is defined as the record whose field kind
\*   is k, field v is v, field reason is r and field data is d."
Res(k, v, r, d) == [kind |-> k, v |-> v, reason |-> r, data |-> d]
\* Literally: "NoData is defined as the record whose field init is FALSE,
\*   field ps is 0, field query is FALSE and field peras is FALSE."
NoData == [init |-> FALSE, ps |-> 0, query |-> FALSE, peras |-> FALSE]
\* Literally: "NoRes is defined as Res of "None", 0, "None" and NoData."
NoRes == Res("None", 0, "None", NoData)

\* In English: "Server implementation i, with settings s and versions vs,
\* answers the proposal p (a function from wire keys to wire data). A key
\* it cannot hold breaks gOuroboros's message decode unless
\* GoSkipsWideKeys; other keys it does not know are skipped [V5]. Then
\* acceptOrRefuse [V6]: no common version, VersionMismatch; data that does
\* not decode, DecodeError; else accept the highest common version with
\* the agreement of its data and the proposal's."
\* Literally: "Serve of i, s, vs and p is defined as: if i equals "Go", and
\*   GoSkipsWideKeys is not true, and WideKey is in the domain of p, then
\*   Res of "Error", 0, "None" and NoData; else, letting common be the
\*   intersection of the domain of p, Known of i and vs: if common is empty
\*   then Res of "Refuse", 0, "VersionMismatch" and NoData; else, letting v
\*   be (Min of common under the mutation LowestCommon, else Max of
\*   common): if Decodes of i, v and p of v is not true then Res of "Refuse",
\*   v, "DecodeError" and NoData; else Res of "Accept", v, "None" and Agree of
\*   i, Dec of Encode of i, v and s, and Dec of p of v."
Serve(i, s, vs, p) ==
    IF i = "Go" /\ ~GoSkipsWideKeys /\ WideKey \in DOMAIN p
    THEN Res("Error", 0, "None", NoData)                               \* map[uint16] decode fails
    ELSE LET common == DOMAIN p \cap Known(i) \cap vs IN
         IF common = {} THEN Res("Refuse", 0, "VersionMismatch", NoData)
         ELSE LET v == IF i = "Go" /\ Mutation = "LowestCommon" THEN Min(common) ELSE Max(common) IN
              IF ~Decodes(i, v, p[v]) THEN Res("Refuse", v, "DecodeError", NoData)
              ELSE Res("Accept", v, "None", Agree(i, Dec(Encode(i, v, s)), Dec(p[v])))

\* In English: "Client implementation i, with settings s and versions vs,
\* gets MsgAcceptVersion for v with data w [V6]: a version it did not
\* propose, or data it cannot decode, is an error; else the reference ends
\* with its agreement of its own data with w, gOuroboros with w itself
\* unless GoClientAgrees."
\* Literally: "Finish of i, s, vs, v and w is defined as: if v is not a
\*   member of vs, or Decodes of i, v and w is not true, then Res of "Error",
\*   v, "None" and NoData; else Res of "Accept", v, "None" and (if i equals
\*   "Ref" or GoClientAgrees then Agree of i, Dec of Encode of i, v and s,
\*   and Dec of w; else Dec of w)."
Finish(i, s, vs, v, w) ==
    IF v \notin vs \/ ~Decodes(i, v, w) THEN Res("Error", v, "None", NoData)
    ELSE Res("Accept", v, "None",
             IF i = "Ref" \/ GoClientAgrees THEN Agree(i, Dec(Encode(i, v, s)), Dec(w))
             ELSE Dec(w))

-----------------------------------------------------------------------------

VARIABLES
    side,     \* side[r]: "Ref" or "Go", or "Rogue" (a client that sends anything) or "OldGo" (a server sending its own data)
    set,      \* set[r]: side r's settings
    vers,     \* vers[r]: the versions side r offers
    prop,     \* the proposal on the wire: a function from keys to wire data
    answer,   \* the server's answer: result plus the data it sends
    result    \* result[r]: how side r ended

\* Literally: "vars is defined as the tuple of the six variables."
vars == <<side, set, vers, prop, answer, result>>
\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles == {"Client", "Server"}

\* In English: "Each honest side offers a non-empty subset of the versions
\* it knows. A rogue client sends one data value under a non-empty set of
\* keys, which may include keys nobody knows or gOuroboros cannot hold."
\* Literally: "Offers of i is defined as the set of subsets of Known of i
\*   without the empty set."
Offers(i) == SUBSET Known(i) \ {{}}
\* Literally: "RogueProps is defined as the set of functions [k \in K |-> w]
\*   for every K that is a non-empty subset of AllKeys and every w in Wire."
RogueProps == {[k \in K |-> w] : K \in SUBSET AllKeys \ {{}}, w \in Wire}

\* In English: "Pick the two sides and the proposal. An honest client
\* proposes Encode for each version it offers."
\* Literally: "Init is defined as: side is a member of the set of records
\*   whose Client field is in Impls plus "Rogue" and Server field is in
\*   Impls plus "OldGo", the server being "Go" for a rogue client (the
\*   check computes both servers); set is a member of the functions from
\*   Roles to Settings, a rogue client's settings fixed (it sends anything); vers is a function from Roles to version sets where each
\*   honest side offers a member of Offers of its implementation (a rogue
\*   client none, OldGo as Go); prop is, for a rogue client, a member of
\*   RogueProps, else the function mapping every v in vers of "Client" to
\*   Encode of the client's implementation, v and its settings; answer is
\*   NoRes and result maps every role to NoRes."
\* In English: "The implementation side r runs; an old gOuroboros server is
\* gOuroboros for decoding and agreeing."
\* Literally: "Impl of r is defined as: if side of r equals "OldGo" then
\*   "Go", else side of r."
Impl(r) == IF side[r] = "OldGo" THEN "Go" ELSE side[r]
Init ==
    /\ side \in {sd \in [Client : Impls \cup {"Rogue"}, Server : Impls \cup {"OldGo"}] :
                  sd.Client = "Rogue" => sd.Server = "Go"}           \* a rogue's server: both computed
    /\ set \in {st \in [Roles -> Settings] :
                 side["Client"] = "Rogue" => st["Client"] = CHOOSE x \in Settings : TRUE}
    /\ vers \in {[Client |-> c, Server |-> sv] :
                   c \in (IF side["Client"] = "Rogue" THEN {{}} ELSE Offers(side["Client"])),
                   sv \in Offers(IF side["Server"] = "OldGo" THEN "Go" ELSE side["Server"])}
    /\ prop \in (IF side["Client"] = "Rogue" THEN RogueProps
                 ELSE {[v \in vers["Client"] |-> Encode(side["Client"], v, set["Client"])]})
    /\ answer = [res |-> NoRes, wire |-> Encode("Ref", 0, set["Server"])]
    /\ result = [r \in Roles |-> NoRes]

\* In English: "The server answers the proposal. It sends the agreed data
\* [V7], an old gOuroboros server its own data."
\* Literally: "Answer is defined as: the server's result is NoRes; letting d
\*   be Serve of Impl of "Server", its settings, its versions and prop:
\*   result in the next state maps "Server" to d; answer in the next state
\*   holds d and the wire data Enc of the server's implementation, d's v,
\*   and (for OldGo the decoded Encode of its own settings, else d's data);
\*   side, set, vers and prop are unchanged."
Answer ==
    /\ result["Server"].kind = "None"
    /\ LET i == Impl("Server")
           d == Serve(i, set["Server"], vers["Server"], prop) IN
       /\ result' = [result EXCEPT !["Server"] = d]
       /\ answer' = [res |-> d,
                     wire |-> Enc(i, d.v, IF side["Server"] = "OldGo"
                                          THEN Dec(Encode(i, d.v, set["Server"]))
                                          ELSE d.data)]
    /\ UNCHANGED <<side, set, vers, prop>>

\* In English: "An honest client reads an accept and ends as Finish says;
\* a refusal or error ends it with the same."
\* Literally: "ClientEnd is defined as: the server's result is not NoRes and
\*   the client's is, the client is not rogue, and result in the next state
\*   maps "Client" to Finish of the client's implementation, settings,
\*   versions, the answer's v and wire, if the answer accepted, else to the
\*   answer itself; nothing else changes."
ClientEnd ==
    /\ result["Server"].kind /= "None"
    /\ result["Client"].kind = "None"
    /\ side["Client"] /= "Rogue"
    /\ result' = [result EXCEPT !["Client"] =
                    IF answer.res.kind = "Accept"
                    THEN Finish(side["Client"], set["Client"], vers["Client"], answer.res.v, answer.wire)
                    ELSE answer.res]
    /\ UNCHANGED <<side, set, vers, prop, answer>>

\* Literally: "Done is defined as: the server's result is not NoRes, and the
\*   client's is not NoRes or the client is rogue."
Done == result["Server"].kind /= "None" /\ (result["Client"].kind /= "None" \/ side["Client"] = "Rogue")
\* Literally: "Next is defined as Answer, or ClientEnd, or Done and nothing
\*   changes."
Next == Answer \/ ClientEnd \/ (Done /\ UNCHANGED vars)
\* Literally: "Spec is defined as Init and always every step is a Next step
\*   or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* PROPERTIES                                                               *)

\* In English: "Both sides honest" (a gOuroboros server that sends its own
\* data is honest too: it is what gOuroboros releases before the agreed-data
\* fix send).
\* Literally: "Honest is defined as: the client is not rogue."
Honest == side["Client"] /= "Rogue"

\* In English: "Every agreement gOuroboros computes is the reference's, for
\* every pair of decodable data [V1][V3][V4]." It reads no variable, so it
\* is joined to Done: an invariant TLC can only evaluate as a constant is
\* reported as an error, not as a violation, and the run must end the same
\* way either way.
\* Literally: "AgreementMatchesReference is defined as: if Done, then for all
\*   l and r in Data whose ps is 0 or 1, GoAgree of l and r equals RefAgree
\*   of l and r."
AgreementMatchesReference ==
    Done => \A l, r \in {d \in Data : d.ps \in {0, 1}} : GoAgree(l, r) = RefAgree(l, r)

\* In English: "Whatever any client sends, a gOuroboros server answers as a
\* reference server with the same settings and versions would" (refused
\* where the reference refuses, ignored where it ignores [V5][V6]).
\* Literally: "ServerMatchesReference is defined as: if the client is rogue
\*   and its versions are known to both implementations, Serve of "Go"
\*   equals Serve of "Ref", for the server's settings and versions, and prop."
ServerMatchesReference ==
    (side["Client"] = "Rogue" /\ vers["Server"] \subseteq Known("Ref") \cap Known("Go"))
        => Serve("Go", set["Server"], vers["Server"], prop)
           = Serve("Ref", set["Server"], vers["Server"], prop)

\* In English: "Whatever accept a server sends, a gOuroboros client ends as
\* a reference client with the same settings and versions would [V6]."
\* Checked for every version and wire data, at every state.
\* Literally: "ClientMatchesReference is defined as: if the client's versions
\*   are known to both implementations, for all v in AllKeys and w in Wire,
\*   Finish of "Go" equals Finish of "Ref" for the client's settings and
\*   versions."
ClientMatchesReference ==
    (Honest /\ vers["Client"] \subseteq Known("Ref") \cap Known("Go"))
        => \A v \in AllKeys, w \in Wire :
              Finish("Go", set["Client"], vers["Client"], v, w)
              = Finish("Ref", set["Client"], vers["Client"], v, w)

\* In English: "Two honest sides with a version in common connect: the
\* server accepts the highest common version and the client accepts it too."
\* Literally: "HonestPairsConnect is defined as: if Honest and the client's
\*   result is not NoRes, and vers of "Client" and vers of "Server" share a
\*   version, then both results accept Max of the shared versions."
HonestPairsConnect ==
    (Honest /\ result["Client"].kind /= "None"
            /\ vers["Client"] \cap vers["Server"] /= {})
        => \A r \in Roles :
              /\ result[r].kind = "Accept"
              /\ result[r].v = Max(vers["Client"] \cap vers["Server"])

\* In English: "No side ever agrees a version the client did not propose
\* or the server does not offer."
\* Literally: "NeverAgreesUnproposed is defined as: for all r in Roles, if
\*   result of r accepted, then its v is in the domain of prop and in vers of
\*   "Server", and is the largest such version."
NeverAgreesUnproposed ==
    \A r \in Roles :
        result[r].kind = "Accept" =>
            LET common == DOMAIN prop \cap vers["Server"] IN
            /\ result[r].v \in common
            /\ result[r].v = Max(common)

\* In English: "Two honest sides that both accepted end with the same data,
\* the reference agreement of the two sides' data for the agreed version:
\* never a flag the reference would not agree [V6][V7]." An old gOuroboros
\* server's own end is not checked: it is a fixed release.
\* Literally: "BothEndAgreed is defined as: if Honest and both results
\*   accepted, then the client's data equals RefAgree of the client's and
\*   the server's decoded data for that version, and so does the server's
\*   unless it is OldGo."
BothEndAgreed ==
    (Honest /\ \A r \in Roles : result[r].kind = "Accept")
        => LET v == result["Client"].v
               agreed == RefAgree(Dec(Encode(side["Client"], v, set["Client"])),
                                  Dec(Encode(Impl("Server"), v, set["Server"]))) IN
           /\ result["Client"].data = agreed
           /\ side["Server"] /= "OldGo" => result["Server"].data = agreed

\* Literally: "TypeOK is defined as: result maps every role to a record of a
\*   kind, a v in AllKeys or 0, a reason and data in Data."
TypeOK ==
    result \in [Roles -> [kind : {"None", "Accept", "Refuse", "Error"},
                          v : AllKeys \cup {0},
                          reason : {"None", "VersionMismatch", "DecodeError"},
                          data : Data]]
=============================================================================
