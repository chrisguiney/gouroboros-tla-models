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
(*        Its quantity check runs only when a literal c2 or c3 byte occurs *)
(*        and reads the quantities through a Go map, so a tag 2 with a     *)
(*        non-minimal tag head (d8 02, allowed by cbor/tags.go) and a      *)
(*        bignum on an asset name that a later duplicate replaces (before  *)
(*        version 9, where duplicates are kept last-wins) pass it.         *)
(*   [G5] the fix of [G4]'s gap: every quantity of every policy is read    *)
(*        pair by pair from the wire, duplicates included, and any head    *)
(*        that is not major type 0 or 1 is refused.                        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Versions,   \* protocol versions to check, e.g. {8, 9, 12}
    Fields,     \* fields to check, a subset of AllFields
    TryValues,  \* values to check, a subset of Values
    Encodings,  \* encodings to check, a subset of AllEncodings
    GoRule      \* "main" [G1], "fix" [G2], "fixPair" [G4] or "fixWalk" [G5]

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

\* In English: "The ways an integer is written: a major type 0/1 head; a
\*   tag 2/3 bignum with a one-byte tag head (c2, c3); the same with a
\*   non-minimal two-byte tag head (d8 02, d8 03); and a bignum on an asset
\*   name that a later entry with the same name repeats with a head."
\* Literally: "AllEncodings is defined as the set containing "head",
\*   "bignum", "bignumLongTag" and "bignumBehindDup"."
AllEncodings == {"head", "bignum", "bignumLongTag", "bignumBehindDup"}

\* In English: "A head (major type 0 or 1) holds every value but 2^64; a
\*   duplicate asset name exists only in an asset map."
\* Literally: "Encodable of v, e and f is defined as: (e is not "head", or v
\*   is not "beyond64"), and (e is not "bignumBehindDup", or f is an asset
\*   field)."
Encodable(v, e, f) ==
    /\ e # "head" \/ v # "beyond64"
    /\ e # "bignumBehindDup" \/ f \in {"outputAsset", "mintAsset"}

\* In English: "Every version, field, value and encoding that can be
\*   written."
\* Literally: "Inputs is defined as the set of records r whose pv is a
\*   member of Versions, whose field is a member of Fields, whose value is
\*   a member of TryValues and whose enc is a member of Encodings, such that
\*   Encodable of the value, the enc and the field of r."
Inputs == {r \in [pv : Versions, field : Fields, value : TryValues,
                  enc : Encodings] : Encodable(r.value, r.enc, r.field)}

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
\*   field's domain; it decodes every entry of an asset map, so a bignum
\*   behind a duplicate name fails too." [R1] [R2] [R3] [S1]
\* Literally: "RefAccepts of i is defined as: the enc of i equals "head",
\*   and InDomain of i."
RefAccepts(i) == i.enc = "head" /\ InDomain(i)

\* In English: "Whether gOuroboros reads a bignum in this field: never for
\*   a bare coin; in a pair's coin on main and the first fix but not on
\*   15156a03; for asset quantities on main, and with a long tag head on
\*   every rule but fixWalk." [G1] [G2] [G3] [G4] [G5]
\* Literally: "GoReadsBignum of i is defined as: if the field of i is
\*   "coinBare" then FALSE, else if the field of i is "coinInPair" then
\*   GoRule is "main" or "fix", else if the enc of i is "bignumLongTag"
\*   then GoRule is not "fixWalk", else GoRule equals "main"."
GoReadsBignum(i) ==
    IF i.field = "coinBare" THEN FALSE
    ELSE IF i.field = "coinInPair" THEN GoRule \in {"main", "fix"}
    ELSE IF i.enc = "bignumLongTag" THEN GoRule # "fixWalk"
    ELSE GoRule = "main"

\* In English: "gOuroboros accepts a head, or a bignum it reads, whose
\*   value is in the field's domain. A bignum behind a duplicate name is
\*   never read: the asset map keeps the later head (in domain), so before
\*   version 9 every rule but fixWalk accepts it; from 9 the duplicate is
\*   refused." [G1] [G2] [G3] [G4] [G5]
\* Literally: "GoAccepts of i is defined as: if the enc of i is
\*   "bignumBehindDup", then the pv of i is less than 9 and GoRule is not
\*   "fixWalk"; else (the enc of i equals "head", or GoReadsBignum of i),
\*   and InDomain of i."
GoAccepts(i) ==
    IF i.enc = "bignumBehindDup"
        THEN i.pv < 9 /\ GoRule # "fixWalk"
        ELSE (i.enc = "head" \/ GoReadsBignum(i)) /\ InDomain(i)

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
