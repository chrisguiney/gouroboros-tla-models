------------------------- MODULE MessagePayloadBytes -------------------------
(***************************************************************************)
(* Model `dmq`, part 7: which bytes a DMQ message's id and KES signature   *)
(* cover, when gOuroboros receives a message and when it relays it.        *)
(*                                                                         *)
(* A message on the wire is [messageId, messagePayload, kesSignature,      *)
(* opCert, coldKey]. The payload [body, kesPeriod, expiresAt] can be       *)
(* written with more than one byte string: an integer may use a wider     *)
(* head than it needs ("wide"), which the reference decoder accepts. The   *)
(* model does no hashing: bytes are a pair <<content, shape>>, and two     *)
(* hashes are equal exactly when the pairs are. A gOuroboros encoder       *)
(* always writes the minimal shape.                                        *)
(*                                                                         *)
(* Questions:                                                              *)
(*   ReceiptAsReference  for every payload the reference decodes,          *)
(*                       gOuroboros accepts the message exactly when the   *)
(*                       reference does.                                   *)
(*   RelayKeepsId        a message gOuroboros accepted and relays is       *)
(*                       accepted by a reference peer downstream.          *)
(*   OwnLegacyAccepted   gOuroboros still accepts its own legacy-shape     *)
(*                       payload, whose bytes it cannot keep.              *)
(*   IdNamesContent      the id gOuroboros computes names the payload's    *)
(*                       current fields (a caller contract once a decoded  *)
(*                       payload is edited; probe only).                   *)
(*                                                                         *)
(* Sources: dmq-node a267003c14e9, dmq-node/src/DMQ/Protocol/SigSubmission/*)
(*   [R1] Codec.hs 160-181: decodeSig cuts sigRawSignedBytes from the      *)
(*        received message between the payload's two decoder offsets.      *)
(*   [R2] Codec.hs 204-210: decodePayload reads three fields; kesPeriod    *)
(*        with cborg's decodeWord, which accepts a non-minimal head.       *)
(*   [R3] Validate.hs 60-64: validateSigId hashes those bytes.             *)
(*   [R4] Validate.hs 207-212: verifyKES over the same bytes.              *)
(*   CIPs db48da14bff1 CIP-0137/README.md 370-376: messageId is the hash   *)
(*   of the CBOR payload.                                                  *)
(*                                                                         *)
(* The gOuroboros code it is compared with: protocol/common/dmq.go         *)
(*   (ebc63eab) DmqMessagePayload MarshalCBOR / UnmarshalCBOR,             *)
(*   ComputeDmqMessageID, DmqMessage.MarshalCBOR (the carried id is sent   *)
(*   as is); protocol/common/authentication.go: the id check and the KES   *)
(*   verification over cbor.Encode(msg.Payload).                           *)
(*   [G1] main: every payload is re-encoded.                               *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* README section "Reading a formula literally".                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule,          \* "main" or "fixed"; "idOnly" is a mutation
    CallerEdits    \* TRUE lets a caller edit a decoded payload (probe)

VARIABLES shape, edited

\* In English: the two things a table cell is made of.
\* Literally: "vars is defined as the tuple of shape and edited."
vars == <<shape, edited>>

\* In English: how the received payload was written: minimally, with a
\* wider integer head than needed, or in gOuroboros' legacy four-field
\* shape that carries the id inside the payload.
\* Literally: "Shapes is defined as the set containing "minimal", "wide"
\* and "legacy"."
Shapes == {"minimal", "wide", "legacy"}

\* In English: the bytes an encoder that writes minimally produces for
\* content c.
\* Literally: "Enc of c is defined as the pair of c and "minimal"."
Enc(c) == <<c, "minimal">>

\* In English: the payload bytes on the wire for shape s; the content is
\* "c1".
\* Literally: "Wire of s is defined as the pair of "c1" and s."
Wire(s) == <<"c1", s>>

\* In English: the reference decodes the three-field payload in either
\* integer width, and not the legacy shape. [R2]
\* Literally: "RefDecodes of s is defined as: s is a member of the set
\*   containing "minimal" and "wide"."
RefDecodes(s) == s \in {"minimal", "wide"}

\* In English: the id the sender carries. A sender hashes the bytes it
\* sent; a gOuroboros sender of the legacy shape hashes the current-shape
\* encoding of the same content (ComputeDmqMessageID).
\* Literally: "CarriedId of s is defined as: if s equals "legacy" then Enc
\*   of "c1" else Wire of s."
CarriedId(s) == IF s = "legacy" THEN Enc("c1") ELSE Wire(s)

\* In English: the KES signature covers the same bytes as the id.
\* Literally: "Signed of s is defined as CarriedId of s."
Signed(s) == CarriedId(s)

\* In English: the reference accepts when it decodes the payload, and the
\* carried id and the signature are over the bytes it received. [R1] [R3]
\* [R4]
\* Literally: "RefAccepts of s is defined as: RefDecodes of s, and
\*   CarriedId of s equals Wire of s, and Signed of s equals Wire of s."
RefAccepts(s) == RefDecodes(s) /\ CarriedId(s) = Wire(s) /\ Signed(s) = Wire(s)

\* In English: the payload's current content: "c2" once a caller edited
\* the decoded fields.
\* Literally: "Content of e is defined as: if e then "c2" else "c1"."
Content(e) == IF e THEN "c2" ELSE "c1"

\* In English: the bytes gOuroboros keeps from decoding, under rule r: on
\* main none [G1]; with the fix (DecodeStoreCbor) the received bytes,
\* except for the legacy shape, whose bytes hold the id as well.
\* Literally: "Kept of r and s is defined as: if r is not "main" and s is
\*   not "legacy" then Wire of s else "none"."
Kept(r, s) == IF r # "main" /\ s # "legacy" THEN Wire(s) ELSE "none"

\* In English: the bytes gOuroboros hashes and verifies: the kept bytes,
\* or else a re-encoding of the current content.
\* Literally: "Covered of r, s and e is defined as: if Kept of r and s is
\*   not "none" then Kept of r and s else Enc of Content of e."
Covered(r, s, e) == IF Kept(r, s) # "none" THEN Kept(r, s) ELSE Enc(Content(e))

\* In English: gOuroboros accepts a received message when the carried id
\* and the signature are over the bytes it covers.
\* Literally: "GoAccepts of r and s is defined as: CarriedId of s equals
\*   Covered of r, s and FALSE, and Signed of s equals Covered of r, s and
\*   FALSE."
GoAccepts(r, s) ==
    CarriedId(s) = Covered(r, s, FALSE) /\ Signed(s) = Covered(r, s, FALSE)

\* In English: the payload bytes gOuroboros writes when it relays the
\* message: the kept bytes, except under the "idOnly" mutation, which
\* keeps them for the id but re-encodes on the wire.
\* Literally: "RelayBytes of r and s is defined as: if r is not "idOnly"
\*   and Kept of r and s is not "none" then Kept of r and s else Enc of
\*   "c1"."
RelayBytes(r, s) ==
    IF r # "idOnly" /\ Kept(r, s) # "none" THEN Kept(r, s) ELSE Enc("c1")

\* In English: a reference peer downstream accepts the relayed message:
\* the carried id and signature, forwarded unchanged, are over the relayed
\* payload bytes. [R1] [R3] [R4]
\* Literally: "DownstreamAccepts of r and s is defined as: CarriedId of s
\*   equals RelayBytes of r and s, and Signed of s equals RelayBytes of r
\*   and s."
DownstreamAccepts(r, s) ==
    CarriedId(s) = RelayBytes(r, s) /\ Signed(s) = RelayBytes(r, s)

\* In English: any shape; edited only when the configuration lets a
\* caller edit.
\* Literally: "Init is defined as: shape is a member of Shapes, and edited
\*   is a member of (if CallerEdits then BOOLEAN else the set containing
\*   FALSE)."
Init == shape \in Shapes /\ edited \in (IF CallerEdits THEN BOOLEAN ELSE {FALSE})
\* In English: a cell does not change.
\* Literally: "Next is defined as: vars is unchanged."
Next == UNCHANGED vars
\* In English: start in a cell and stay there.
\* Literally: "Spec is defined as: Init, and always either Next or vars
\*   unchanged."
Spec == Init /\ [][Next]_vars

\* In English: for a payload the reference decodes, gOuroboros accepts
\* exactly when the reference does (N57).
\* Literally: "ReceiptAsReference is defined as: RefDecodes of shape
\*   implies (GoAccepts of Rule and shape if and only if RefAccepts of
\*   shape)."
ReceiptAsReference == RefDecodes(shape) => (GoAccepts(Rule, shape) <=> RefAccepts(shape))

\* In English: what gOuroboros accepts and relays, a reference peer
\* accepts (N57; the relayed id is the carried one).
\* Literally: "RelayKeepsId is defined as: RefDecodes of shape and
\*   GoAccepts of Rule and shape imply DownstreamAccepts of Rule and
\*   shape."
RelayKeepsId == RefDecodes(shape) /\ GoAccepts(Rule, shape) => DownstreamAccepts(Rule, shape)

\* In English: gOuroboros accepts its own legacy-shape message.
\* Literally: "OwnLegacyAccepted is defined as: shape equals "legacy"
\*   implies GoAccepts of Rule and shape."
OwnLegacyAccepted == shape = "legacy" => GoAccepts(Rule, shape)

\* In English: the id gOuroboros computes for the payload names its
\* current content.
\* Literally: "IdNamesContent is defined as: element 1 of Covered of Rule,
\*   shape and edited equals Content of edited."
IdNamesContent == Covered(Rule, shape, edited)[1] = Content(edited)
=============================================================================
