----------------------------- MODULE TxSizeFraming ---------------------------
(***************************************************************************)
(* The size of a Shelley, Allegra or Mary transaction, which the fee and   *)
(* the maximum-transaction-size rules measure: whether it depends on how   *)
(* the received transaction's outer CBOR array is framed.                  *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   [S1] eras/shelley/impl/src/Cardano/Ledger/Shelley/Tx.hs 155-166:      *)
(*        toCBORForSizeComputation encodes encodeListLen 3, the body, the  *)
(*        witness set, then encodeNullStrictMaybe of the auxiliary data:   *)
(*        a one-byte array header plus the three components, the missing   *)
(*        auxiliary data as one null byte.                                 *)
(*   [S2] Shelley/Tx.hs 168-177: sizeShelleyTxF is the length of that      *)
(*        encoding, not of the received bytes.                             *)
(*   [S3] eras/allegra/impl/src/Cardano/Ledger/Allegra/Tx.hs 74 and        *)
(*        eras/mary/impl/src/Cardano/Ledger/Mary/Tx.hs 71: sizeTxF is      *)
(*        sizeShelleyTxF in both eras.                                     *)
(*   [S4] Shelley/Tx.hs 186-195: the decoder reads a record of three,      *)
(*        auxiliary data as decodeNullStrictMaybe, so it never appears     *)
(*        as a fourth component.                                           *)
(*                                                                         *)
(* The gOuroboros code it is compared with is TxSize                       *)
(* (ledger/common/rules.go), which for Shelley, Allegra and Mary returns   *)
(* the length of the stored CBOR on main; TxSizeForFee returns the same.   *)
(* Symbols are read as in specs/keepalive/KeepAlive.tla.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule    \* "main": gOuroboros before the fix; "fixed": the branch

\* Literally: "Rules is defined as the set containing "main" and "fixed"."
\* In English: the two gOuroboros behaviours a configuration can pick.
Rules == {"main", "fixed"}
ASSUME Rule \in Rules

\* Literally: "Eras is defined as the set containing "Shelley", "Allegra"
\*   and "Mary"."
\* In English: the eras whose size is the Shelley measure [S3].
Eras == {"Shelley", "Allegra", "Mary"}

\* Literally: "Framings is defined as the set containing "definite", "wide"
\*   and "indefinite"."
\* In English: how the received outer array is written: header 83, header
\* 98 03 (a length in a longer form), or header 9f with a closing break ff.
Framings == {"definite", "wide", "indefinite"}

\* Literally: "Auxes is defined as the set containing "null" and "some"."
\* In English: the third component is a null byte (f6) or a map.
Auxes == {"null", "some"}

VARIABLES era, framing, aux
vars == <<era, framing, aux>>

\* In English: byte lengths of the components, small stand-ins; only that
\* they stay the same across framings matters.
BodyLen == 5
WitsLen == 2

\* Literally: "AuxLen is defined as: if aux equals "null" then 1 else 4."
\* In English: the bytes the third component occupies as received; a null
\* is the single byte f6.
AuxLen == IF aux = "null" THEN 1 ELSE 4

\* Literally: "HeaderLen(f) is defined as: 1 if f is "definite", else 2."
\* In English: bytes the array framing adds around the three components:
\* 83 alone, or 98 03, or 9f plus the closing ff.
HeaderLen(f) == IF f = "definite" THEN 1 ELSE 2

\* Literally: "RefSize is defined as 1 plus BodyLen plus WitsLen plus
\*   AuxLen."
\* In English: the reference size: a one-byte array header plus the three
\* components, whatever framing was received [S1, S2].
RefSize == 1 + BodyLen + WitsLen + AuxLen

\* Literally: "GoSize(f) is defined as: if Rule equals "main" then
\*   HeaderLen(f) plus BodyLen plus WitsLen plus AuxLen, else RefSize."
\* In English: main returns the length of the stored bytes, framing
\* included; the fix measures the parts under a one-byte header. f is the
\* framing the transaction arrived in.
GoSize(f) == IF Rule = "main"
               THEN HeaderLen(f) + BodyLen + WitsLen + AuxLen
               ELSE RefSize

\* Literally: "Init is defined as: era is a member of Eras, framing is a
\*   member of Framings, and aux is a member of Auxes."
\* In English: pick an era, a framing and an auxiliary-data shape.
Init == /\ era \in Eras
        /\ framing \in Framings
        /\ aux \in Auxes

\* Literally: "Next is defined as: vars is unchanged."
\* In English: each state is one cell of the table.
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always Next or vars unchanged."
Spec == Init /\ [][Next]_vars

\* Literally: "SizeAsReference is defined as GoSize(framing) equals
\*   RefSize."
\* In English: the size is the reference's [S1, S2, S3].
SizeAsReference == GoSize(framing) = RefSize

\* Literally: "FramingIndependent is defined as GoSize(framing) equals
\*   GoSize("definite")."
\* In English: the same transaction measures the same size whichever way
\* its outer array was framed.
FramingIndependent == GoSize(framing) = GoSize("definite")
=============================================================================
