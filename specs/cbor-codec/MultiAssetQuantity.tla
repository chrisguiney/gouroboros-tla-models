------------------------- MODULE MultiAssetQuantity -------------------------
(***************************************************************************)
(* Whether gOuroboros accepts an asset quantity (or an output's coin)     *)
(* written as a CBOR bignum, against cardano-ledger's Mary value decoders, *)
(* as a table over abstract inputs.                                        *)
(*                                                                         *)
(* An input is a protocol version, the field the integer sits in, the     *)
(* integer's value (named, since TLC's integers stop at 2^31) and its     *)
(* encoding: a major type 0/1 head, or a tag 2/3 bignum.                   *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd,               *)
(* eras/mary/impl/src/Cardano/Ledger/Mary/Value.hs:                        *)
(*   [R1] 299-308 decodeMaryValue: a bare coin must be a uint token; the   *)
(*        coin of a [coin, multiasset] pair and every output quantity are  *)
(*        read with decodeWord64 (cborg: major type 0 only, no tag).       *)
(*   [R2] 331-352 decodeMultiAsset: before 9 zero quantities are pruned;  *)
(*        from 9 a zero quantity fails.                                    *)
(*   [R3] 369-393 decodeIntegerBounded64 (mint): major type 0 or 1 only,   *)
(*        value within Int64.                                              *)
(*   [S1] conway.cddl multiasset<positive_coin>, mint = multiasset<        *)
(*        nonZeroInt64>: integers, never bignums.                          *)
(*                                                                         *)
(* The gOuroboros code it is compared with:                                *)
(*   [G1] main (parent of 4ae0d4f9): ledger/common/common.go               *)
(*        MultiAsset[T].UnmarshalCBOR decodes into big.Int-capable         *)
(*        targets, so a bignum is read as its value; the range and zero    *)
(*        checks then apply to the value (ValidateOutputQuantities,        *)
(*        ValidateMintQuantities, CheckForZeroAssets).                     *)
(*   [G2] fix/ledger-multiasset-bignum-quantity 4ae0d4f9 (PR #3279):       *)
(*        checkMultiAssetQuantityHeads refuses any quantity whose head is  *)
(*        not major type 0 or 1.                                           *)
(*   [G3] ledger/mary/mary.go MaryTransactionOutputValue.UnmarshalCBOR     *)
(*        (both commits): a bare coin must be major type 0; the pair's     *)
(*        coin is a uint64 the library fills, and the library reads a      *)
(*        bignum that fits into it. Checked in Go on 4ae0d4f9: c24105      *)
(*        refused, 82c24105<multiasset> accepted with coin 5.              *)
(*   [G4] fix/ledger-multiasset-bignum-quantity 15156a03: [G2], and        *)
(*        MaryTransactionOutputValue.UnmarshalCBOR refuses a pair coin     *)
(*        whose head is not major type 0, as for a bare coin.              *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Versions,   \* protocol versions to check, e.g. {8, 9, 12}
    Fields,     \* fields to check, a subset of AllFields
    TryValues,  \* values to check, a subset of Values
    GoRule      \* "main" [G1], "fix" [G2] or "fixPair" [G4]

VARIABLE input  \* the one integer this behaviour decodes

\* In English: "The fields an integer can sit in: an output asset
\*   quantity, a mint quantity, a bare output coin, and the coin of a
\*   [coin, multiasset] pair."
\* Literally: "AllFields is defined as the set containing "outputAsset",
\*   "mintAsset", "coinBare" and "coinInPair"."
AllFields == {"outputAsset", "mintAsset", "coinBare", "coinInPair"}

\* In English: "Named values: 0, 5, 2^64-1, 2^63, -1, -2^63, -2^63-1, and
\*   2^64, which no head can hold."
\* Literally: "Values is defined as the set containing "zero", "five",
\*   "w64max", "i64maxPlus1", "minusOne", "i64min", "i64minMinus1" and
\*   "beyond64"."
Values == {"zero", "five", "w64max", "i64maxPlus1", "minusOne", "i64min",
           "i64minMinus1", "beyond64"}

\* In English: "The values a Word64 holds."
\* Literally: "Word64 is defined as the set containing "zero", "five",
\*   "w64max" and "i64maxPlus1"."
Word64 == {"zero", "five", "w64max", "i64maxPlus1"}

\* In English: "The values an Int64 holds."
\* Literally: "Int64 is defined as the set containing "zero", "five",
\*   "minusOne" and "i64min"."
Int64 == {"zero", "five", "minusOne", "i64min"}

\* In English: "A head (major type 0 or 1) holds every value but 2^64."
\* Literally: "Encodable of v and e is defined as: e equals "bignum", or v
\*   is not "beyond64"."
Encodable(v, e) == e = "bignum" \/ v # "beyond64"

\* In English: "Every version, field, value and encoding that can be
\*   written."
\* Literally: "Inputs is defined as the set of records r whose pv is a
\*   member of Versions, whose field is a member of Fields, whose value is
\*   a member of TryValues and whose enc is "head" or "bignum", such that
\*   Encodable of the value of r and the enc of r."
Inputs == {r \in [pv : Versions, field : Fields, value : TryValues,
                  enc : {"head", "bignum"}] : Encodable(r.value, r.enc)}

\* In English: "The value is in the field's domain: Word64 for outputs and
\*   coins, Int64 for mint; from version 9 an asset quantity is not zero."
\*   [R1] [R2] [R3]
\* Literally: "InDomain of i is defined as: (if the field of i is
\*   "mintAsset" then the value of i is a member of Int64, else the value
\*   of i is a member of Word64), and (the pv of i is less than 9, or the
\*   field of i is a coin field, or the value of i is not "zero")."
InDomain(i) ==
    /\ IF i.field = "mintAsset" THEN i.value \in Int64 ELSE i.value \in Word64
    /\ i.pv < 9 \/ i.field \in {"coinBare", "coinInPair"} \/ i.value # "zero"

\* In English: "The reference reads only heads, and only values in the
\*   field's domain." [R1] [R3] [S1]
\* Literally: "RefAccepts of i is defined as: the enc of i equals "head",
\*   and InDomain of i."
RefAccepts(i) == i.enc = "head" /\ InDomain(i)

\* In English: "Whether gOuroboros reads a bignum in this field: never for
\*   a bare coin; in a pair's coin on main and the first fix but not on
\*   15156a03; for asset quantities on main only." [G1] [G2] [G3] [G4]
\* Literally: "GoReadsBignum of i is defined as: if the field of i is
\*   "coinBare" then FALSE, else if the field of i is "coinInPair" then
\*   GoRule is "main" or "fix", else GoRule equals "main"."
GoReadsBignum(i) ==
    IF i.field = "coinBare" THEN FALSE
    ELSE IF i.field = "coinInPair" THEN GoRule \in {"main", "fix"}
    ELSE GoRule = "main"

\* In English: "gOuroboros accepts a head, or a bignum it reads, whose
\*   value is in the field's domain." [G1] [G2] [G3]
\* Literally: "GoAccepts of i is defined as: (the enc of i equals "head",
\*   or GoReadsBignum of i), and InDomain of i."
GoAccepts(i) == (i.enc = "head" \/ GoReadsBignum(i)) /\ InDomain(i)

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

\* In English: "gOuroboros accepts exactly the integers decodeWord64 and
\*   decodeIntegerBounded64 accept."
\* Literally: "QuantityAsDecodeWord64 is defined as: GoAccepts of input
\*   equals RefAccepts of input."
QuantityAsDecodeWord64 == GoAccepts(input) = RefAccepts(input)
=============================================================================
