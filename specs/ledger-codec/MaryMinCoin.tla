----------------------------- MODULE MaryMinCoin ----------------------------
(***************************************************************************)
(* The minimum coin of a Mary transaction output, and the verdict of the   *)
(* rule that compares an output with it.                                   *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   [S1] eras/mary/impl/src/Cardano/Ledger/Mary/TxOut.hs 33, 47-76:       *)
(*        getMinCoinTxOut is scaledMinDeposit of the output's value and    *)
(*        minUTxOValue. An ada-only value has exactly minUTxOValue.        *)
(*        Otherwise the minimum is max mv (coinsPerUTxOWord *              *)
(*        (utxoEntrySizeWithoutVal + size v)), with coinsPerUTxOWord =     *)
(*        quot mv (utxoEntrySizeWithoutVal + coinSize),                    *)
(*        utxoEntrySizeWithoutVal = 6 + 14 + 7 = 27 and coinSize = 0.      *)
(*   [S2] eras/mary/impl/src/Cardano/Ledger/Mary/Value.hs 238-258,         *)
(*        285-294, 343-349, 747-762: the size of a value with assets is    *)
(*        roundupBytesToWords (representationSize) + repOverhead, with     *)
(*        repOverhead = 4 + 1 + 1 and representationSize = 12 per triple   *)
(*        + 28 per distinct policy + the bytes of the distinct asset       *)
(*        names; a word is 8 bytes. isAdaOnly is a null asset map, and a   *)
(*        pre-Conway decoder prunes zero quantities. The ada-only branch   *)
(*        of size (2) is not used by scaledMinDeposit.                     *)
(*   [S3] eras/allegra/impl/src/Cardano/Ledger/Allegra/Rules/Utxo.hs       *)
(*        270-284: validateOutputTooSmallUTxO flags an output when         *)
(*        Val.pointwise (<) v (inject (getMinCoinTxOut pp txOut)), that    *)
(*        is its coin is below the minimum and no asset has a positive     *)
(*        quantity. Mary reuses it (Mary/Rules/Utxo.hs).                   *)
(*                                                                         *)
(*                                                                         *)
(* The gOuroboros code it is compared with is MinCoinTxOut and             *)
(* UtxoValidateOutputTooSmallUtxo (ledger/mary/rules.go). Symbols are read *)
(* as in specs/keepalive/KeepAlive.tla.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule    \* "main": flat minimum; "fixed": per-output minimum;
            \* "zeroCounted": per-output minimum that counts zero quantities

\* Literally: "Rules is defined as the set containing "main", "fixed" and
\*   "zeroCounted"."
Rules == {"main", "fixed", "zeroCounted"}
ASSUME Rule \in Rules

\* Literally: "Shapes is defined as the set of records with the number of
\*   asset triples n, the number of distinct policies p and the bytes b of
\*   the distinct asset names."
\* In English: the value shapes of the Go test table: ada only; one policy
\* with one asset (empty name, and a 5-byte name); several assets of one
\* policy with names of 1, 2 and 3 bytes; several policies, one of them
\* sharing a name across policies (counted once); and the longest names.
Shapes == {
    [n |-> 0, p |-> 0, b |-> 0],
    [n |-> 1, p |-> 1, b |-> 0],
    [n |-> 1, p |-> 1, b |-> 5],
    [n |-> 3, p |-> 1, b |-> 6],
    [n |-> 2, p |-> 2, b |-> 5],
    [n |-> 4, p |-> 2, b |-> 10],
    [n |-> 2, p |-> 1, b |-> 64]}

\* Literally: "ZeroShape is the record with n = 1, p = 1 and b = 0."
\* In English: an output whose only asset has quantity zero, as a decoder
\* that keeps zero quantities would hold it.
ZeroShape == [n |-> 1, p |-> 1, b |-> 0]
AdaOnly == [n |-> 0, p |-> 0, b |-> 0]

VARIABLES mv, coin, shape, zero
vars == <<mv, coin, shape, zero>>

\* Literally: "Max(a, b) is a if a is greater than b, else b."
Max(a, b) == IF a > b THEN a ELSE b

\* Literally: "ValueSize(s) is 2 if s has no triples, else
\*   (12 n + 28 p + b + 7) div 8 + 6."
\* In English: size in words of a value with assets [S2]; roundup of the
\* representation bytes to 8-byte words, plus repOverhead.
ValueSize(s) == IF s.n = 0 THEN 2
                ELSE ((12 * s.n + 28 * s.p + s.b + 7) \div 8) + 6

\* Literally: "Scaled(m, s) is m if s has no triples, else the larger of m
\*   and (m div 27) * (27 + ValueSize(s))."
\* In English: scaledMinDeposit [S1].
Scaled(m, s) == IF s.n = 0 THEN m
                ELSE Max(m, (m \div 27) * (27 + ValueSize(s)))

\* Literally: "RefShape is ZeroShape's pruned form AdaOnly if zero, else shape."
\* In English: the reference holds no zero quantity [S2].
RefShape == IF zero THEN AdaOnly ELSE shape

\* Literally: "GoShape is the shape gOuroboros sizes."
\* In English: "zeroCounted" sizes the zero-quantity entry; the others skip it.
GoShape == IF zero /\ Rule = "zeroCounted" THEN ZeroShape ELSE RefShape

\* Literally: "RefMin is Scaled of mv and RefShape."
RefMin == Scaled(mv, RefShape)

\* Literally: "GoMin is mv on main, else Scaled of mv and GoShape."
\* In English: main returns the flat parameter for every output.
GoMin == IF Rule = "main" THEN mv ELSE Scaled(mv, GoShape)

\* Literally: "Positive is true when the output has an asset of positive
\*   quantity." Both sides agree: a zero quantity is not positive.
Positive == RefShape.n > 0

\* Literally: "RefReject is coin below RefMin and no positive asset."
\* In English: pointwise (<) [S3].
RefReject == coin < RefMin /\ ~Positive

\* Literally: "GoReject is coin below GoMin and no positive asset."
\* In English: UtxoValidateOutputTooSmallUtxo skips an output with a
\* positive asset and compares the rest with the minimum.
GoReject == coin < GoMin /\ ~Positive

\* Literally: "Init is defined as: mv is a member of {27, 1000000}, coin is
\*   a member of {0, mv - 1, mv, mv + 1}, shape is a member of Shapes and
\*   zero is a member of {FALSE, TRUE}; a zero-quantity output has no other
\*   asset."
\* In English: pick a parameter, a coin around it, and an output.
Init == /\ mv \in {27, 1000000}
        /\ coin \in {0, mv - 1, mv, mv + 1}
        /\ shape \in Shapes
        /\ zero \in BOOLEAN
        /\ zero => shape = AdaOnly

\* Literally: "Next is defined as: vars is unchanged."
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Literally: "MinCoinAsReference is defined as GoMin equals RefMin."
\* In English: MinCoinTxOut returns scaledMinDeposit of the output.
MinCoinAsReference == GoMin = RefMin

\* Literally: "VerdictAsReference is defined as GoReject equals RefReject."
\* In English: the too-small verdict is the reference's pointwise one.
VerdictAsReference == GoReject = RefReject
=============================================================================
