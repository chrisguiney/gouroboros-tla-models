---------------------------- MODULE CborRational ----------------------------
(***************************************************************************)
(* Which tags gOuroboros accepts in front of a CBOR rational, against the  *)
(* reference decoders, as a table over abstract inputs.                    *)
(*                                                                         *)
(* An input is a protocol version and the list of tag numbers written      *)
(* before the two-element array [numerator, denominator]. The array itself *)
(* is always well formed here; only the tags vary.                         *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd,               *)
(* libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/ and               *)
(* libs/cardano-ledger-core/src/Cardano/Ledger/:                           *)
(*   [R1] Decoding/Decoder.hs 465-484 decodeRational (DecCBOR Rational,    *)
(*        DecCBOR.hs 210-211): from version 9 `allowTag 30`, at most one   *)
(*        tag and only 30; before 9 no tag (the list decoder refuses one). *)
(*   [R2] Decoding/Decoder.hs 1347-1354 allowTag: an optional tag, any     *)
(*        number but the expected one fails.                               *)
(*   [R3] BaseTypes.hs 386-428 BoundedRatio (UnitInterval,                 *)
(*        NonNegativeInterval, ...): Plain.decodeRationalWithTag before    *)
(*        version 12, decodeIntegralRational from 12; Plain.hs 159-189 and *)
(*        Decoding/DecCBOR.hs 271-280: both start with `assertTag 30`, so  *)
(*        exactly one tag 30 is required at every version.                 *)
(*   [S1] RFC 8949 section 3.4 and the IANA tag 30 registration: one tag   *)
(*        30 around a two-element array.                                   *)
(*                                                                         *)
(* The gOuroboros code it is compared with is cbor/tags.go                 *)
(* Rat.UnmarshalCBOR:                                                       *)
(*   [G1] main (parent of fe4f8206): SkipTags removes every leading tag    *)
(*        before the count check, then the library decodes the original    *)
(*        bytes into a list; that fails only for a tag 2 or 3 (bignum),    *)
(*        whose content must be a byte string. Checked in Go: 820102,      *)
(*        d81e820102, d81f820102, d90102820102, d81ed81e820102 accepted;   *)
(*        c2820102 refused.                                                *)
(*   [G2] fix/cbor-rat-single-tag fe4f8206 (PR #3282): at most one tag,    *)
(*        and it must be 30; no tag is also accepted, at every version.    *)
(*   [G3] fix/cbor-rat-single-tag aafec34d: exactly one tag 30, at every   *)
(*        version; the untagged 820102 is refused. Every ledger field.     *)
(*   [G4] aafec34d protocol/localstatequery plainRational: no tag or one   *)
(*        tag 30, for the plain Rationals of query results (stake          *)
(*        fractions, reward provenance d and eta), which the reference     *)
(*        writes untagged before version 9 (encodeRatio).                  *)
(*                                                                         *)
(* Every gOuroboros cbor.Rat ledger field (a0, rho, tau, d, execution      *)
(* prices, pool margin, committee quorum, voting thresholds) is a          *)
(* BoundedRatio in the reference, so [R3] is the rule those fields must    *)
(* follow; [R1] is the rule the fix cites.                                 *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Versions,   \* protocol versions to check, e.g. {9, 12}
    Tags,       \* tag numbers that may appear, e.g. {30, 31, 2, 258}
    MaxTags,    \* the most tags written before the array, e.g. 2
    GoRule,     \* "main" [G1], "fix" [G2], "bounded" [G3] or "plain" [G4]
    RefRule     \* "Rational" [R1] or "Bounded" [R3]

VARIABLE input  \* the one input this behaviour decodes: [pv, tags]

\* In English: "TagLists is every list of at most MaxTags tag numbers."
\* Literally: "TagLists is defined as the union, over every n in 0 to
\*   MaxTags, of the set of functions from 1 to n into Tags."
TagLists == UNION {[1..n -> Tags] : n \in 0..MaxTags}

\* In English: "Inputs is every protocol version paired with every tag list."
\* Literally: "Inputs is defined as the set of records whose pv is a member
\*   of Versions and whose tags is a member of TagLists."
Inputs == [pv : Versions, tags : TagLists]

\* In English: "The bare list, or one tag 30 in front of it." [R2]
\* Literally: "NoneOrOne30 of t is defined as: t equals the empty sequence,
\*   or t equals the sequence holding only 30."
NoneOrOne30(t) == t = <<>> \/ t = <<30>>

\* In English: "decodeRational accepts no tag before version 9, and at most
\*   one tag 30 from version 9." [R1]
\* Literally: "RefRational of i is defined as: if the pv of i is at least 9
\*   then NoneOrOne30 of the tags of i, else the tags of i equal the empty
\*   sequence."
RefRational(i) == IF i.pv >= 9 THEN NoneOrOne30(i.tags) ELSE i.tags = <<>>

\* In English: "A bounded ratio needs exactly one tag 30, at every version."
\*   [R3]
\* Literally: "RefBounded of i is defined as: the tags of i equal the
\*   sequence holding only 30."
RefBounded(i) == i.tags = <<30>>

\* In English: "The reference verdict, by the rule this config names."
\* Literally: "RefAccepts of i is defined as: if RefRule equals "Rational"
\*   then RefRational of i, else RefBounded of i."
RefAccepts(i) == IF RefRule = "Rational" THEN RefRational(i) ELSE RefBounded(i)

\* In English: "main accepts any tags unless one of them is a bignum tag,
\*   2 or 3, whose content the library insists is a byte string." [G1]
\* Literally: "GoMain of i is defined as: for all k in the domain of the
\*   tags of i, element k of the tags of i is not a member of the set
\*   containing 2 and 3."
GoMain(i) == \A k \in DOMAIN i.tags : i.tags[k] \notin {2, 3}

\* In English: "The fix accepts no tag or one tag 30, at any version." [G2]
\* Literally: "GoFix of i is defined as NoneOrOne30 of the tags of i."
GoFix(i) == NoneOrOne30(i.tags)

\* In English: "cbor.Rat from aafec34d accepts exactly one tag 30, at any
\*   version." [G3]
\* Literally: "GoBounded of i is defined as: the tags of i equal the
\*   sequence holding only 30."
GoBounded(i) == i.tags = <<30>>

\* In English: "The gOuroboros verdict, by the rule this config names; the
\*   query results' plain rationals [G4] take no tag or one tag 30, as the
\*   fix [G2] did."
\* Literally: "GoAccepts of i is defined as: case GoRule equals "main"
\*   gives GoMain of i, GoRule equals "bounded" gives GoBounded of i,
\*   otherwise GoFix of i."
GoAccepts(i) == CASE GoRule = "main"    -> GoMain(i)
                  [] GoRule = "bounded" -> GoBounded(i)
                  [] OTHER              -> GoFix(i)

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

\* In English: "gOuroboros accepts exactly the tags the reference rule
\*   accepts." Named for the reference decoders it follows.
\* Literally: "TagsAsReferenceRational is defined as: GoAccepts of input
\*   equals RefAccepts of input."
TagsAsReferenceRational == GoAccepts(input) = RefAccepts(input)
=============================================================================
