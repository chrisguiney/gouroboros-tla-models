-------------------------- MODULE ValueSetMembers ---------------------------
(***************************************************************************)
(* Whether gOuroboros's generic cbor.Value decodes a tag 258 set whose     *)
(* members are maps with composite keys, as a table over abstract inputs.  *)
(*                                                                         *)
(* An input is where the set sits (top level or inside a map key), the     *)
(* shape of the tag's content, and the kinds of member the content holds.  *)
(*                                                                         *)
(* Sources.                                                                *)
(*   [S1] RFC 8949 section 3.1: a map key may be any data item, arrays and *)
(*        maps included; a generic decoder must keep such a map.           *)
(*   [R1] IntersectMBO/cardano-ledger 1210d37fe6bd                         *)
(*        eras/conway/impl/golden/tx.cbor field 20: proposal procedures,   *)
(*        a tag 258 set whose committee-update maps are keyed by           *)
(*        credentials (arrays); the reference decodes it.                  *)
(*   [R2] cardano-ledger-binary Decoding/Decoder.hs 1057-1080 (same       *)
(*        commit) decodeSetLikeEnforceNoDuplicates: after the tag a set   *)
(*        is a list of members, so content that is not a list is           *)
(*        refused.                                                         *)
(*                                                                         *)
(* The gOuroboros code it is compared with is cbor/value.go                *)
(* Value.unmarshalCBOR, tag branch:                                        *)
(*   [G1] main (parent of 3a442a45): tag 258 content goes to the library's *)
(*        interface decoding, which cannot hold a map keyed by an array or *)
(*        a map ("invalid map key type"); non-list content is refused.    *)
(*   [G2] fix/cbor-value-set-members 3a442a45 (PR #3284): the members are  *)
(*        walked with Value like any list, so composite keys decode; any   *)
(*        other unrecognised tag still falls back to the library.          *)
(*   [G3] fix/cbor-value-set-members 2ee1c0ab (origin/main merged): main  *)
(*        added a budget that bounds the array elements and map pairs of  *)
(*        a whole Value tree (cbor/value.go valueBudget), and charges the  *)
(*        content of every tag it hands to the library. The merged set     *)
(*        branch walked the members on a fresh budget, so sets that fit    *)
(*        one by one and overrun together were accepted.                   *)
(*   [G4] fix/cbor-value-set-members a69cd1ad: set members spend the      *)
(*        tree's budget.                                                   *)
(*   [M1] TestValueModeLimitsApplyToWholeTree (cbor/value_limits_test.go, *)
(*        origin/main): the mode's limits cover the whole tree. This is a  *)
(*        gOuroboros resource rule; the reference has no such limit, so    *)
(*        the reference comparison is made only on inputs within it.       *)
(* Checked in Go on both commits: d9010281a1820102f5 and                   *)
(* a1d9010281a1820102f505 refused on main and decoded on the fix;          *)
(* d9010201 refused on both; d9010281d903e8a1820102f5 (a tag-1000 member  *)
(* around such a map) refused on both.                                     *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    MemberKinds,  \* member kinds to try, a subset of AllKinds
    GoRule        \* "main" [G1], "fix" [G2], "mergedFresh" [G3] or
                  \* "mergedShared" [G4]

VARIABLE input    \* the one set this behaviour decodes

\* In English: "Every kind of member the model knows: an integer, a map
\*   keyed by integers, a map keyed by an array, a map keyed by a map, and
\*   an unrecognised tag around a map keyed by an array."
\* Literally: "AllKinds is defined as the set containing "uint",
\*   "mapScalarKey", "mapArrayKey", "mapMapKey" and "otherTagComposite"."
AllKinds == {"uint", "mapScalarKey", "mapArrayKey", "mapMapKey",
             "otherTagComposite"}

\* In English: "Member kinds whose map has a key that is an array or a map,
\*   at any depth." [S1]
\* Literally: "Composite is defined as the set containing "mapArrayKey",
\*   "mapMapKey" and "otherTagComposite"."
Composite == {"mapArrayKey", "mapMapKey", "otherTagComposite"}

\* In English: "Shapes the tag's content can take."
\* Literally: "Contents is defined as the set containing "defList",
\*   "indefList", "uint" and "map"."
Contents == {"defList", "indefList", "uint", "map"}

\* In English: "Every position, content shape and set of member kinds (the
\*   empty set is an empty list, or no members when the content is not a
\*   list), and whether the set's members, added to the rest of the tree,
\*   overrun the decode mode's whole-tree limits while the set alone fits."
\* Literally: "Inputs is defined as the set of records whose where is a
\*   member of the set containing "top" and "mapKey", whose content is a
\*   member of Contents, whose members is a subset of MemberKinds, and
\*   whose treeOver is TRUE or FALSE."
\* BOOLEAN is the set {TRUE, FALSE}.
Inputs == [where : {"top", "mapKey"}, content : Contents,
           members : SUBSET MemberKinds, treeOver : BOOLEAN]

\* In English: "The content is a list (definite or indefinite)."
\* Literally: "IsList of i is defined as: the content of i is a member of
\*   the set containing "defList" and "indefList"."
IsList(i) == i.content \in {"defList", "indefList"}

\* In English: "The reference keeps any well-formed set: its content must
\*   be a list, and any member is fine." [S1] [R1] [R2]
\* Literally: "RefAccepts of i is defined as IsList of i."
RefAccepts(i) == IsList(i)

\* In English: "main refuses a set holding any member with a composite
\*   key." [G1]
\* Literally: "GoMain of i is defined as: IsList of i, and the intersection
\*   of the members of i and Composite is the empty set."
GoMain(i) == IsList(i) /\ i.members \cap Composite = {}

\* In English: "The fix decodes composite keys in set members, but not
\*   behind an unrecognised tag." [G2]
\* Literally: "GoFix of i is defined as: IsList of i, and
\*   "otherTagComposite" is not a member of the members of i."
GoFix(i) == IsList(i) /\ "otherTagComposite" \notin i.members

\* In English: "main charges a tag's content to the tree budget before the
\*   library decodes it, and so does the fix once it shares the budget; the
\*   fix as first merged walks set members on a fresh budget." [G1] [G3]
\*   [G4]
\* Literally: "ChargesTree is defined as: GoRule is not "mergedFresh"."
ChargesTree == GoRule /= "mergedFresh"

\* In English: "The gOuroboros verdict, by the rule this config names: the
\*   member rule, and refusal of an input that overruns the tree when the
\*   rule charges set members to it." [G1] [G2] [G3] [G4]
\* Literally: "GoAccepts of i is defined as: if GoRule equals "main" then
\*   GoMain of i, else GoFix of i; and if ChargesTree then the treeOver of
\*   i is FALSE."
GoAccepts(i) ==
    /\ IF GoRule = "main" THEN GoMain(i) ELSE GoFix(i)
    /\ ChargesTree => ~i.treeOver   \* overrunning sets are refused

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

\* In English: "Within the tree's limits, Value decodes exactly the sets the
\*   reference decodes, composite map keys included." [M1]
\* Literally: "SetMembersAsRfc8949 is defined as: if the treeOver of input
\*   is FALSE, then GoAccepts of input equals RefAccepts of input."
SetMembersAsRfc8949 == ~input.treeOver => GoAccepts(input) = RefAccepts(input)

\* In English: "A tree whose set members overrun the whole-tree limits is
\*   refused." [M1]
\* Literally: "TreeBudgetHolds is defined as: if the treeOver of input is
\*   TRUE, then GoAccepts of input is FALSE."
TreeBudgetHolds == input.treeOver => ~GoAccepts(input)
=============================================================================
