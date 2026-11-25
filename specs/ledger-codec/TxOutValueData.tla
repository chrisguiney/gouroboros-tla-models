--------------------------- MODULE TxOutValueData ---------------------------
(***************************************************************************)
(* The value of a transaction output as a script sees it: which currency   *)
(* entries the Plutus Data map of a TxInfo output or resolved input holds, *)
(* in particular the ada entry when the coin is zero.                      *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   [S1] libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/TxInfo.hs     *)
(*        186-187: transCoinToValue (Coin c) = PV1.singleton adaSymbol     *)
(*        adaToken c, for every c, zero included.                          *)
(*   [S2] eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Plutus/TxInfo.hs      *)
(*        417-418: transValue (MaryValue c m) = transCoinToValue c <>      *)
(*        transMultiAsset m.                                               *)
(*   [S3] eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs 158: the  *)
(*        TxOut of a PlutusV2 and PlutusV3 TxInfo uses transValue.         *)
(*   Golden: eras/conway/impl/golden/translations.cbor records zero-coin   *)
(*   outputs with an ada entry of 0. The Alonzo specification (txinfo.tex, *)
(*   transValue) is silent on zero.                                        *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ToPlutusData of              *)
(* ShelleyTransactionOutput (ledger/shelley/shelley.go), MaryTransaction-  *)
(* Output (ledger/mary/mary.go), AlonzoTransactionOutput (ledger/alonzo/   *)
(* alonzo.go) and BabbageTransactionOutput (ledger/babbage/babbage.go),    *)
(* and the WithZeroAdaAsset wrapper (ledger/common/script/wrappers.go)     *)
(* that TxInfoV1 and TxInfoV2 put around their outputs. Symbols are read   *)
(* as in specs/keepalive/KeepAlive.tla.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule    \* "main": gOuroboros before the fix; "fixed": the branch

\* Literally: "Rules is defined as the set containing "main" and "fixed"."
\* In English: the two gOuroboros behaviours a configuration can pick.
Rules == {"main", "fixed"}
ASSUME Rule \in Rules

\* Literally: "Eras is defined as the set containing "Shelley", "Mary",
\*   "Alonzo" and "Babbage"."
\* In English: the four output types (Allegra's is Shelley's). An output of
\* any of them can be a resolved input of a later transaction.
Eras == {"Shelley", "Mary", "Alonzo", "Babbage"}
\* Literally: "Langs is defined as the set containing "V1", "V2" and "V3"."
\* In English: the Plutus language whose TxInfo carries the output.
Langs == {"V1", "V2", "V3"}

VARIABLES era, lang, coin, assets
vars == <<era, lang, coin, assets>>

\* Literally: "AssetEntries is defined as: if assets equals "some" then the
\*   set containing "policy" else the empty set."
\* In English: one entry per policy the output's multi-asset holds.
AssetEntries == IF assets = "some" THEN {"policy"} ELSE {}

\* Literally: "RefEntries is defined as the union of the set containing
\*   "ada" and AssetEntries."
\* In English: the reference value always has the ada entry [S1, S2, S3].
RefEntries == {"ada"} \cup AssetEntries

\* Literally: "GoAdaEntry is defined as: lang is a member of the set
\*   containing "V1" and "V2", or Rule equals "fixed", or coin is greater
\*   than 0."
\* In English: gOuroboros writes the ada entry when WithZeroAdaAsset wraps
\* the output (PlutusV1 and V2), on the fix always, and on main otherwise
\* only for a positive coin.
GoAdaEntry == lang \in {"V1", "V2"} \/ Rule = "fixed" \/ coin > 0

\* Literally: "GoEntries is defined as: the union of (if GoAdaEntry then
\*   the set containing "ada" else the empty set) and AssetEntries."
\* In English: the currency entries gOuroboros writes.
GoEntries == (IF GoAdaEntry THEN {"ada"} ELSE {}) \cup AssetEntries

\* Literally: "Init is defined as: era is a member of Eras, lang is a member
\*   of Langs, coin is a member of the set containing 0 and 1, and assets is
\*   a member of: if era equals "Shelley" then the set containing "none",
\*   else the set containing "none" and "some"."
\* In English: pick an output (Shelley outputs hold no multi-asset), a
\* coin of zero or more, and the language of the TxInfo.
Init == /\ era \in Eras
        /\ lang \in Langs
        /\ coin \in {0, 1}
        /\ assets \in (IF era = "Shelley" THEN {"none"} ELSE {"none", "some"})

\* Literally: "Next is defined as: vars is unchanged."
\* In English: each state is one cell of the table.
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always Next or vars unchanged."
Spec == Init /\ [][Next]_vars

\* Literally: "TransValueAsReference is defined as GoEntries equals
\*   RefEntries."
\* In English: the output's value has the reference's entries: an ada
\* entry whatever the coin, plus one per policy (transValue).
TransValueAsReference == GoEntries = RefEntries
=============================================================================
