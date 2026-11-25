---------------------------- MODULE EraHistoryDecode ----------------------------
(***************************************************************************)
(* Which GetEraHistory reply encodings gOuroboros decodes, as a table over *)
(* abstract byte shapes, against the reference's Summary decoder.          *)
(*                                                                         *)
(* An input is the reply's outer shape: a definite or indefinite array of  *)
(* some number of well-formed era summaries, a null, or an undefined, with *)
(* no tag, a tag 258, or another tag in front. Each era summary is assumed *)
(* well formed; only the outer shape varies.                               *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [R1] ouroboros-consensus ec239d57f618 ouroboros-consensus/src/        *)
(*        ouroboros-consensus/Ouroboros/Consensus/HardFork/History/        *)
(*        Summary.hs 630-679, Serialise (Summary xs): `decode` of a list   *)
(*        of era summaries, then `fail "Summary: expected at least one era *)
(*        summary"` when it is empty.                                      *)
(*   [R2] serialise (cborg) Codec.Serialise.Class, the list instance's     *)
(*        defaultDecodeList: a definite or indefinite array; no tag, null  *)
(*        or undefined is a list.                                          *)
(*                                                                         *)
(* gOuroboros protocol/localstatequery:                                    *)
(*   [G1] main before #3205 (queries.go eraHistoryReply =                  *)
(*        growingArray[EraHistoryResult]; growing_array.go 32-55): any     *)
(*        leading tags are skipped; a null or undefined decodes as an      *)
(*        empty history; an array of any length decodes.                   *)
(*   [G2] #3205 (05b6d9f2, queries.go 871-886): the same, then an empty    *)
(*        result is refused ("era history must contain at least one era    *)
(*        summary").                                                       *)
(*   [G3] fix/localstatequery-era-history-tag aad3e65a: [G2], and a reply  *)
(*        that starts with a tag is refused before decoding.               *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    GoRule,   \* "main" [G1], "fix" [G2] or "untagged" [G3]
    Tags,     \* tags that may lead the reply, a subset of {"none", "258", "other"}
    MaxEras   \* the most era summaries in an array, e.g. 2

VARIABLE input  \* the one reply shape this behaviour decodes

\* In English: "Every reply shape: an array (definite or indefinite) of 0
\*   to MaxEras eras, a null, or an undefined, each under one of Tags."
\* Literally: "Inputs is defined as the union of the set of records whose
\*   kind is "array", whose definite is a boolean, whose eras is a member
\*   of 0 to MaxEras and whose tag is a member of Tags, and the set of
\*   records whose kind is "null" or "undefined", whose definite is TRUE,
\*   whose eras is 0 and whose tag is a member of Tags."
Inputs ==
    [kind : {"array"}, definite : BOOLEAN, eras : 0..MaxEras, tag : Tags]
    \cup [kind : {"null", "undefined"}, definite : {TRUE}, eras : {0},
          tag : Tags]

\* In English: "The reference decodes an untagged array, definite or
\*   indefinite, with at least one era." [R1][R2]
\* Literally: "RefAccepts of i is defined as: the tag of i equals "none",
\*   and the kind of i equals "array", and the eras of i is at least 1."
RefAccepts(i) == i.tag = "none" /\ i.kind = "array" /\ i.eras >= 1

\* In English: "gOuroboros skips every tag; main takes any array or a
\*   null or undefined as a history [G1]; the fix refuses an empty one
\*   [G2], and a null or undefined decodes to empty."
\* aad3e65a also refuses any tag in front [G3].
\* Literally: "GoAccepts of i is defined as: if GoRule equals "main" then
\*   TRUE, else the kind of i equals "array" and the eras of i is at
\*   least 1, and, if GoRule equals "untagged", the tag of i equals
\*   "none"."
GoAccepts(i) ==
    IF GoRule = "main" THEN TRUE
    ELSE /\ i.kind = "array" /\ i.eras >= 1
         /\ (GoRule = "untagged" => i.tag = "none")

\* In English: "Pick any one input; nothing changes after that."
\* Literally: "Init is defined as: input is a member of Inputs."
Init == input \in Inputs

\* In English: "A table has no steps: the input stays as it is."
\* Literally: "Next is defined as: input is unchanged."
Next == UNCHANGED input

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or input
\*   stays the same."
Spec == Init /\ [][Next]_input

\* In English: "gOuroboros decodes exactly the replies the reference's
\*   Summary decoder decodes."
\* Literally: "EraHistoryAsSummaryDecoder is defined as: GoAccepts of input
\*   if and only if RefAccepts of input."
EraHistoryAsSummaryDecoder == GoAccepts(input) <=> RefAccepts(input)
=============================================================================
