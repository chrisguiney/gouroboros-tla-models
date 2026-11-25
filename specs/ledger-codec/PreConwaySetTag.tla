--------------------------- MODULE PreConwaySetTag ---------------------------
(***************************************************************************)
(* Whether a transaction's set-shaped field may carry a CBOR tag: tag 258  *)
(* (the set tag) or any other, before Conway and from Conway on.           *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   [S1] libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/   *)
(*        Decoder.hs 930-953 (decodeSet): versions 2-8 read the set with   *)
(*        decodeCollection decodeListLenOrIndef, "set tag 258 is not       *)
(*        permitted"; from version 9 the tag 258 is permitted, not         *)
(*        enforced. A list-length decoder accepts no tag of any number.    *)
(*   [S2] eras/shelley/impl/src/Cardano/Ledger/Shelley/TxWits.hs 261-273;  *)
(*        eras/alonzo/impl/src/Cardano/Ledger/Alonzo/TxWits.hs 347-357,    *)
(*        569-580, 660-700, 721-730: below version 9 the witness-set       *)
(*        fields decode with decodeList, which accepts no tag.             *)
(*   The CDDL's set<a> allows the tag from Conway; the specifications are  *)
(*   silent on earlier eras.                                               *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ledger/common/certs.go       *)
(* (PoolRegistrationCertificate.UnmarshalCBOR,                             *)
(* ValidatePreConwayCertificateTypes), ledger/common/pre_conway_sets.go    *)
(* (ValidatePreConwaySetTags, on the fix branch), and the Shelley, Alonzo  *)
(* and Babbage body and witness-set decoders that call them. Symbols are   *)
(* read as in specs/keepalive/KeepAlive.tla.                               *)
(*   [S3] Decoder.hs 1347-1354 (allowTag): from version 9 decodeSet takes  *)
(*        an optional tag 258 and fails on any other tag number.           *)
(* Checked in Go on 37968c05: a Conway witness-set field under tag 259 or  *)
(* tag 30 is refused ("unexpected tag type"); a Conway pool owner set      *)
(* under either decodes.                                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule,   \* "main": before the fix; "fixed": e9dd7145; "anyTag": e82a8a6c
    Tags    \* the tags a field may carry: a subset of {"none", "258", "other"}

\* Literally: "Rules is defined as the set containing "main", "fixed" and
\*   "anyTag"."
\* In English: the three gOuroboros behaviours a configuration can pick.
Rules == {"main", "fixed", "anyTag"}
ASSUME Rule \in Rules
ASSUME Tags \subseteq {"none", "258", "other"}

\* Literally: "Eras is defined as the set containing "Shelley", "Allegra",
\*   "Mary", "Alonzo", "Babbage" and "Conway"."
\* In English: Shelley to Babbage decode at versions 2-8, Conway at 9.
Eras == {"Shelley", "Allegra", "Mary", "Alonzo", "Babbage", "Conway"}

\* Literally: "Fields is defined as the set containing "inputs",
\*   "poolOwners", "collateral", "requiredSigners", "referenceInputs" and
\*   "witness"."
\* In English: the set-shaped fields, by how gOuroboros decodes them:
\* the spent inputs, a pool registration's owners, the three typed input
\* or signer sets of the body, and a witness-set field (keys, scripts,
\* datums, redeemers, bootstrap witnesses).
Fields == {"inputs", "poolOwners", "collateral", "requiredSigners",
           "referenceInputs", "witness"}

\* Literally: "HasField of e and f is defined as: case f equals
\*   "collateral" or "requiredSigners" gives e is not "Shelley", "Allegra"
\*   or "Mary"; f equals "referenceInputs" gives e is "Babbage" or
\*   "Conway"; otherwise TRUE."
\* In English: collateral and required signers exist from Alonzo, reference
\* inputs from Babbage.
HasField(e, f) ==
    CASE f \in {"collateral", "requiredSigners"} ->
            e \notin {"Shelley", "Allegra", "Mary"}
      [] f = "referenceInputs" -> e \in {"Babbage", "Conway"}
      [] OTHER -> TRUE

VARIABLES era, field, tag, elsewhere258
vars == <<era, field, tag, elsewhere258>>

\* Literally: "RefDecodes is defined as: tag equals "none", or era equals
\*   "Conway" and tag equals "258"."
\* In English: the reference decodes an untagged set in every era, and a
\* tag 258 set only from version 9 [S1, S2]; another tag never.
RefDecodes == tag = "none" \/ (era = "Conway" /\ tag = "258")

\* Literally: "GoMainDecodes is defined as: case tag equals "none" gives
\*   TRUE; tag equals "258" gives field is not "inputs" or era equals
\*   "Conway"; otherwise field is "poolOwners", or field is "witness" and
\*   era is not "Conway"."
\* In English: gOuroboros before the fix: tag 258 is refused only on the
\* spent inputs before Conway; another tag is refused by the typed input
\* and signer sets and the Conway witness set ("unexpected tag type") but
\* passes on pool owners and the Shelley-Babbage witness-set fields, whose
\* decoders ignore an unknown tag.
GoMainDecodes ==
    CASE tag = "none" -> TRUE
      [] tag = "258"  -> field /= "inputs" \/ era = "Conway"
      [] OTHER        -> \/ field = "poolOwners"
                         \/ field = "witness" /\ era /= "Conway"

\* Literally: "GoFixedDecodes is defined as: case tag equals "none" gives
\*   TRUE; era equals "Conway" gives GoMainDecodes; tag equals "258" gives
\*   FALSE; otherwise field is "witness" and elsewhere258 is false."
\* In English: gOuroboros on the fix. Before Conway a tag 258 on any set
\* field is refused. Another tag is refused on pool owners (any tag head
\* sets poolOwnersTagged) and by the typed sets as before, but on a
\* witness-set field only when the map's bytes hold a tag 258 head
\* somewhere: ValidatePreConwaySetTags re-reads the map only then, and the
\* re-read refuses a field headed by any tag.
GoFixedDecodes ==
    CASE tag = "none"    -> TRUE
      [] era = "Conway"  -> GoMainDecodes
      [] tag = "258"     -> FALSE
      [] OTHER           -> field = "witness" /\ ~elsewhere258

\* Literally: "GoAnyTagDecodes is defined as: case tag equals "none" gives
\*   TRUE; tag equals "258" gives era equals "Conway"; otherwise FALSE."
\* In English: gOuroboros on e82a8a6c: before Conway
\* ValidatePreConwaySetTags re-reads the map whenever its bytes hold a tag
\* head, and refuses a field headed by any tag; pool owners refuse any tag
\* before Conway and any tag but a single 258 from Conway [S3].
GoAnyTagDecodes ==
    CASE tag = "none" -> TRUE
      [] tag = "258"  -> era = "Conway"
      [] OTHER        -> FALSE

\* Literally: "GoDecodes is defined as: case Rule equals "main" gives
\*   GoMainDecodes, Rule equals "fixed" gives GoFixedDecodes, otherwise
\*   GoAnyTagDecodes."
\* In English: the gOuroboros verdict under Rule.
GoDecodes == CASE Rule = "main"  -> GoMainDecodes
              [] Rule = "fixed" -> GoFixedDecodes
              [] OTHER          -> GoAnyTagDecodes

\* Literally: "Init is defined as: era is a member of Eras, field is a
\*   member of Fields and HasField of era and field, tag is a member of
\*   Tags, and elsewhere258 is a member of BOOLEAN."
\* In English: pick an era, one of its set fields, the field's tag, and
\* whether a tag 258 head appears anywhere else in the same map's bytes.
Init == /\ era \in Eras
        /\ field \in {f \in Fields : HasField(era, f)}
        /\ tag \in Tags
        /\ elsewhere258 \in BOOLEAN

\* Literally: "Next is defined as: vars is unchanged."
\* In English: each state is one cell of the table.
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always Next or vars unchanged."
Spec == Init /\ [][Next]_vars

\* Literally: "SetTagAsReference is defined as GoDecodes if and only if
\*   RefDecodes."
\* In English: gOuroboros decodes a tagged or untagged set field exactly
\* when decodeSet or decodeList would [S1, S2].
SetTagAsReference == GoDecodes <=> RefDecodes
=============================================================================
