------------------------- MODULE PlutusConstrFields -------------------------
(***************************************************************************)
(* Whether gOuroboros accepts a Plutus Data constructor whose fields are   *)
(* not a list, against plutus's decoder, as a table over abstract inputs.  *)
(*                                                                         *)
(* An input is the constructor's tag family, the shape of the alternative  *)
(* number (only read under tag 102) and the shape of the item that holds  *)
(* the fields.                                                             *)
(*                                                                         *)
(* Sources. IntersectMBO/plutus commit bdc12f105a98,                       *)
(* plutus-core/plutus-core/src/PlutusCore/Data.hs:                         *)
(*   [R1] 286-307 decodeConstr: tags 121-127 and 1280-1400 read their      *)
(*        content with decodeListOf; tag 102 reads [Word64, fields] and    *)
(*        the fields with decodeListOf.                                    *)
(*   [R2] 271-275 decodeListOf: decodeListLenOrIndef, so a definite or an  *)
(*        indefinite list and nothing else (not even a tagged list).       *)
(*   [S1] conway.cddl constr<a0>: #6.121([* a0]) ... #6.102([uint, [* a0]]).*)
(*                                                                         *)
(* The gOuroboros code it is compared with is cbor/constructor.go          *)
(* ConstructorDecoder.UnmarshalCBOR (cbor.Value decodes every constructor *)
(* through it):                                                            *)
(*   [G1] main (parent of a37a8a90): keeps whatever item follows the tag,  *)
(*        or the second element under 102, as the fields; the alternative *)
(*        number under 102 must decode as a uint64.                        *)
(*   [G2] fix/cbor-constructor-fields-list a37a8a90 (PR #3283): the fields *)
(*        item's first byte must be major type 4 (array).                  *)
(* Checked in Go on both commits: d87901, d87a4100, d905786161, d87aa0,    *)
(* d866820301, d866820341ff, d879d81e80, d87a6161 accepted on main and     *)
(* refused on the fix; d87980, d8799f01ff, d866820380, d8669f0380ff        *)
(* accepted on both; d866822080 refused on both.                           *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)

CONSTANTS
    GoRule      \* "main" [G1] or "fix" [G2]

VARIABLE input  \* the one constructor this behaviour decodes

\* In English: "The three tag families of a constructor." [R1]
\* Literally: "Families is defined as the set containing "121-127",
\*   "1280-1400" and "102"."
Families == {"121-127", "1280-1400", "102"}

\* In English: "Shapes the fields item can take: a definite list, an
\*   indefinite list, an unsigned integer, a byte string, a map, a text
\*   string, or a list behind another tag."
\* Literally: "FieldShapes is defined as the set containing "defList",
\*   "indefList", "uint", "bytes", "map", "text" and "taggedList"."
FieldShapes == {"defList", "indefList", "uint", "bytes", "map", "text",
                "taggedList"}

\* In English: "Shapes the alternative number under tag 102 can take."
\* Literally: "AltShapes is defined as the set containing "uint" and
\*   "negint"."
AltShapes == {"uint", "negint"}

\* In English: "Every family, alternative-number shape and fields shape."
\* Literally: "Inputs is defined as the set of records whose family is a
\*   member of Families, whose alt is a member of AltShapes and whose
\*   fields is a member of FieldShapes."
Inputs == [family : Families, alt : AltShapes, fields : FieldShapes]

\* In English: "The alternative number is well formed: it is read only
\*   under tag 102, where it must be an unsigned integer." [R1]
\* Literally: "AltOK of i is defined as: the family of i is not "102", or
\*   the alt of i equals "uint"."
AltOK(i) == i.family # "102" \/ i.alt = "uint"

\* In English: "plutus accepts the constructor when its alternative number
\*   is well formed and its fields are a list." [R1] [R2]
\* Literally: "RefAccepts of i is defined as: AltOK of i, and the fields of
\*   i is a member of the set containing "defList" and "indefList"."
RefAccepts(i) == AltOK(i) /\ i.fields \in {"defList", "indefList"}

\* In English: "main accepts any fields item." [G1]
\* Literally: "GoMain of i is defined as AltOK of i."
GoMain(i) == AltOK(i)

\* In English: "The fix accepts the fields item only when it starts with
\*   an array head, which both list shapes do and a tagged list does not."
\*   [G2]
\* Literally: "GoFix of i is defined as: AltOK of i, and the fields of i is
\*   a member of the set containing "defList" and "indefList"."
GoFix(i) == AltOK(i) /\ i.fields \in {"defList", "indefList"}

\* In English: "The gOuroboros verdict, by the rule this config names."
\* Literally: "GoAccepts of i is defined as: if GoRule equals "main" then
\*   GoMain of i, else GoFix of i."
GoAccepts(i) == IF GoRule = "main" THEN GoMain(i) ELSE GoFix(i)

\* In English: "Pick any one input."
\* Literally: "Init is defined as: input is a member of Inputs."
Init == input \in Inputs

\* In English: "A table has no steps: the input stays as it is."
\* Literally: "Next is defined as: input is unchanged."
Next == UNCHANGED input

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or input
\*   stays the same."
Spec == Init /\ [][Next]_input

\* In English: "gOuroboros accepts a constructor exactly when plutus's
\*   decodeListOf would read its fields."
\* Literally: "FieldsAsDecodeListOf is defined as: GoAccepts of input
\*   equals RefAccepts of input."
FieldsAsDecodeListOf == GoAccepts(input) = RefAccepts(input)
=============================================================================
