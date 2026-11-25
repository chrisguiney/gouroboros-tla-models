------------------------- MODULE CostModelLanguages -------------------------
(***************************************************************************)
(* The cost models a classic (Alonzo or Babbage) parameter update may      *)
(* carry, by protocol version: which language keys are accepted, and with  *)
(* how many parameters.                                                    *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   [S1] libs/cardano-ledger-core/src/Cardano/Ledger/Plutus/              *)
(*        CostModels.hs 307-317: before protocol version 9 an update's     *)
(*        cost models decode with decodeCostModelsFailing, each key as any *)
(*        Language.                                                        *)
(*   [S2] CostModels.hs 319-338 (decodeCostModelLegacy): a language above  *)
(*        PlutusV2 fails; otherwise the array must have exactly the        *)
(*        language's initial parameter count.                              *)
(*   [S3] libs/cardano-ledger-core/internal/Cardano/Ledger/Internal/       *)
(*        Definition/Era.hs 113-125: Alonzo is versions 5-6, Babbage 7-8.  *)
(*   The Alonzo ledger specification lists PlutusV1 only; the reference    *)
(*   decoder is wider, and gOuroboros follows the reference.               *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ledger/alonzo/pparams.go and *)
(* ledger/babbage/pparams.go (ValidateProtocolParameterUpdateVersion),     *)
(* both through ledger/common/pparam_update_validation.go                  *)
(* (ValidateClassicCostModelUpdate). Symbols are read as in                *)
(* specs/keepalive/KeepAlive.tla.                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Rule    \* "main": gOuroboros before the fix; "fixed": the branch

\* Literally: "Rules is defined as the set containing "main" and "fixed"."
\* In English: the two gOuroboros behaviours a configuration can pick.
Rules == {"main", "fixed"}
ASSUME Rule \in Rules

\* Literally: "Languages is defined as 0 to 3."
\* In English: the language keys tried: 0 PlutusV1, 1 PlutusV2, 2 PlutusV3,
\* 3 a later one.
Languages == 0..3
\* Literally: "Lengths is defined as the set containing "exact" and
\*   "short"."
\* In English: an array with the language's parameter count, or one short.
Lengths == {"exact", "short"}
\* Literally: "Entries is defined as the pairs of Languages and Lengths."
\* In English: one cost model in the update: its key and its length.
Entries == Languages \X Lengths

\* Literally: "Versions is defined as the set containing 5, 6, 7 and 8."
\* In English: the protocol versions a classic update with cost models is
\* checked at: Alonzo 5-6, Babbage 7-8 [S3].
Versions == {5, 6, 7, 8}

VARIABLES pv, models
vars == <<pv, models>>

\* Literally: "RefAcceptsEntry of e is defined as: element 1 of e is at most
\*   1 and element 2 of e equals "exact"."
\* In English: decodeCostModelLegacy accepts PlutusV1 and PlutusV2 with
\* their exact parameter counts [S2].
RefAcceptsEntry(e) == e[1] <= 1 /\ e[2] = "exact"

\* Literally: "RefAccepts of ms is defined as: for all e in ms,
\*   RefAcceptsEntry of e."
\* In English: the reference decodes the update's cost models [S1].
RefAccepts(ms) == \A e \in ms : RefAcceptsEntry(e)

\* Literally: "GoAllowed of v is defined as: if v is at least 7 then the set
\*   containing 0 and 1, else if Rule equals "main" then the set containing
\*   0, else the set containing 0 and 1."
\* In English: the expected-length map gOuroboros passes: Babbage always
\* lists PlutusV1 and PlutusV2; Alonzo lists only PlutusV1 on main, both
\* on the fix.
GoAllowed(v) == IF v >= 7 THEN {0, 1}
                ELSE IF Rule = "main" THEN {0} ELSE {0, 1}

\* Literally: "GoAccepts of v and ms is defined as: for all e in ms,
\*   element 1 of e is a member of GoAllowed of v and element 2 of e equals
\*   "exact"."
\* In English: ValidateClassicCostModelUpdate: every key must be in the map
\* ("unknown cost model language") and every array the right length.
GoAccepts(v, ms) == \A e \in ms : e[1] \in GoAllowed(v) /\ e[2] = "exact"

\* Literally: "Init is defined as: pv is a member of Versions, and models is
\*   a member of the subsets of Entries with 1 or 2 members."
\* In English: pick a version and an update carrying one or two cost models.
Init == /\ pv \in Versions
        /\ models \in {ms \in SUBSET Entries : Cardinality(ms) \in {1, 2}}

\* Literally: "Next is defined as: vars is unchanged."
\* In English: each state is one cell of the table.
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always Next or vars unchanged."
Spec == Init /\ [][Next]_vars

\* Literally: "LegacyCostModelsAsReference is defined as GoAccepts of pv
\*   and models if and only if RefAccepts of models."
\* In English: gOuroboros accepts exactly the cost models
\* decodeCostModelLegacy does, in every pre-Conway version [S1, S2].
LegacyCostModelsAsReference == GoAccepts(pv, models) <=> RefAccepts(models)
=============================================================================
