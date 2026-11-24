---------------------------- MODULE ConwayLedger ----------------------------
(***************************************************************************)
(* What Conway and Dijkstra add to a single transaction's UTXO and LEDGER  *)
(* checks, beyond the Shelley-to-Babbage UTXO rule of model 17, and what   *)
(* gOuroboros decides for the same transactions.                           *)
(*                                                                         *)
(* A transaction here is abstract: only the fields Conway and Dijkstra     *)
(* look at are kept. Model 17's checks (inputs exist, outputs are big      *)
(* enough, collateral, validity interval) are assumed to pass, and the     *)
(* fee is reduced to its reference-script part.                            *)
(*                                                                         *)
(* Two families of transactions:                                          *)
(*   GateTxs: the LEDGER and UTXO gates. A stated current treasury value  *)
(*     must equal the treasury; the reference scripts the transaction     *)
(*     reads must fit the per-transaction limit and be paid for by the     *)
(*     tiered fee; from protocol version 10 a key-hash withdrawal needs a  *)
(*     DRep delegation; for protocol versions 9 and 10 a reference input   *)
(*     may not also be spent. Each gate is checked only for a phase-2-    *)
(*     valid transaction in Conway, and for every transaction in Dijkstra *)
(*     where the reference moved it out of the phase-2-valid branch.      *)
(*   BalTxs: value conservation with Conway's deposits and refunds: stake *)
(*     and DRep registration, proposal deposits and treasury donation.    *)
(*                                                                         *)
(* TableSpec starts in every protocol version, registration and           *)
(* delegation state and never moves; GoAgrees checks in each state that   *)
(* gOuroboros accepts exactly the transactions the reference accepts.     *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd. Paths are    *)
(* under eras/<era>/impl/src/Cardano/Ledger/.                              *)
(*   [C1] Conway/Rules/Ledger.hs 376-428: in the Phase2Valid branch only, *)
(*        validateTreasuryValue (464-476), validateRefScriptSize          *)
(*        (478-488), and, unless hardforkConwayBootstrapPhase (pv = 9),   *)
(*        validateWithdrawalsDelegated (497-513) against the certificate  *)
(*        state before CERTS.                                              *)
(*   [C2] Conway/Era.hs 256-257: hardforkConwayBootstrapPhase pv = (major *)
(*        pv = 9).                                                         *)
(*   [C3] Conway/Tx.hs 104-150: getConwayMinFeeTx adds tierRefScriptFee:  *)
(*        each tier of sizeIncrement bytes costs the current price per    *)
(*        byte, the price is multiplied by the multiplier after each tier, *)
(*        and the exact total is floored once.                            *)
(*   [C4] Conway/UTxO.hs 183-187: txNonDistinctRefScriptsSize reads the   *)
(*        reference scripts of reference inputs union spent inputs (a set *)
(*        union, so an input both read and spent counts once).            *)
(*   [C5] Conway/Rules/Utxo.hs 254-262: conwayUtxoTransition runs         *)
(*        babbageUtxoValidation (value conservation and the disjointness  *)
(*        rule for every transaction, valid or not).                       *)
(*   [C6] babbage/.../Babbage/Rules/Utxo.hs 204-218: reference inputs     *)
(*        disjoint from spent inputs only for 8 < pv < 11.                 *)
(*   [C7] Conway/UTxO.hs conwayProducedValue: Mary's produced value plus  *)
(*        the treasury donation; Conway/TxBody.hs 382-390                  *)
(*        conwayProposalsDeposits = number of proposals times             *)
(*        ppGovActionDeposit; Conway/TxCert.hs 863-904: deposits use      *)
(*        ppKeyDeposit and ppDRepDeposit, a stake refund the deposit the  *)
(*        state records (none when the credential is not registered), a   *)
(*        DRep refund the certificate's amount.                            *)
(*   [C8] Conway/TxBody.hs 254-257: a treasury donation of zero does not  *)
(*        decode (decodePositiveCoin).                                     *)
(*   [D1] Dijkstra/Rules/Ledger.hs 393-461: validateTreasuryValue and     *)
(*        validateAllRefScriptSize run before the Phase2Valid branch, so  *)
(*        for every transaction; Dijkstra has no withdrawal-delegation    *)
(*        rule (546-559: "WdrlNotDelegatedToDRep has been removed").      *)
(*   [D2] Dijkstra/Rules/Utxo.hs 301-447: no disjointness rule; value     *)
(*        conservation only when Phase2Valid (343-365).                    *)
(*   [D3] Dijkstra/TxCert.hs 263-272: a refund is the certificate's       *)
(*        amount, stake and DRep alike; legacy Reg and UnReg certificates *)
(*        are expunged (291-292).                                          *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 756a9a89):              *)
(*   [G1] ledger/common/rules.go 390-440 UtxoValidateCurrentTreasuryValue *)
(*        (skips an invalid transaction) and ...AnyPhase (Dijkstra).      *)
(*   [G2] ledger/conway/ref_scripts.go 38-61 UtxoValidateRefScriptSizePer *)
(*        Tx (skips an invalid transaction); 103-139 CalculateRefScriptFee*)
(*        (one floor after all tiers); ledger/common/ref_scripts.go 41-108 *)
(*        ConsumedReferenceScriptSize (spent and reference inputs, keyed  *)
(*        by input so an input counts once).                               *)
(*   [G3] ledger/conway/rules.go 3572-3622 UtxoValidateWithdrawals: skips *)
(*        an invalid transaction; requires a DRep delegation of every key- *)
(*        hash withdrawal for 10 <= pv < 12.                               *)
(*   [G4] ledger/conway/rules.go 400-419 UtxoValidateDisjointRefInputs:   *)
(*        Babbage's rule, skipped from pv 11.                              *)
(*   [G5] ledger/conway/rules.go 2388-2576 conwayValueConservationDeposits*)
(*        and 2584-2680 UtxoValidateValueNotConservedUtxo (every          *)
(*        transaction).                                                    *)
(*   [G6] ledger/dijkstra/rules.go 333-401 phase table: CurrentTreasury-  *)
(*        Value and RefScriptSizePerTx Always; ValueNotConserved and      *)
(*        Withdrawals Phase2Valid; 4157-4258 fee with the stride and      *)
(*        multiplier from the parameters; 5259-5365 RefScriptSizePerTx.   *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the README section "Reading a formula     *)
(* literally" and specs/01-keepalive/KeepAlive.tla.                        *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    Era,       \* "Conway" or "Dijkstra"
    Stride,    \* the reference-script fee tier size, in bytes
    MultN,     \* the tier price multiplier is MultN / MultD
    MultD,
    BaseN,     \* minFeeRefScriptCostPerByte is BaseN / BaseD
    BaseD,
    MaxRef,    \* the per-transaction reference-script size limit
    KeyDep,    \* ppKeyDeposit
    DRepDep,   \* ppDRepDeposit
    GovDep,    \* ppGovActionDeposit
    Mutation   \* "none", or one deliberate mistake (see the README)

\* In English: the protocol versions each era runs at: Conway 9, 10 and
\* 11; Dijkstra 12.
\* Literally: "PVs is defined as: if Era equals "Conway" then the set
\*   containing 9, 10 and 11, else the set containing 12."
PVs == IF Era = "Conway" THEN {9, 10, 11} ELSE {12}

VARIABLES
    pv,      \* the major protocol version
    reg,     \* is the withdrawing (and deregistering) stake credential registered?
    deleg    \* its DRep delegation: "none", "drep" or "abstain"

\* Literally: "vars is defined as the tuple of pv, reg and deleg."
vars == <<pv, reg, deleg>>

-----------------------------------------------------------------------------
(* The tiered reference-script fee [C3].                                   *)

\* In English: b raised to the power e, for e >= 0.
RECURSIVE Pow(_, _)
\* Literally: "Pow of b and e is defined as: if e equals 0 then 1, else b
\*   times Pow of b and e minus 1."
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

\* In English: how many tiers n bytes fill: the full ones and a last
\* partial one.
\* Literally: "Tiers of n is defined as (n plus Stride minus 1) integer-divided
\*   by Stride."
Tiers(n) == (n + Stride - 1) \div Stride

\* In English: how many of the n bytes fall in tier k (counting from 0).
\* Literally: "TierSize of n and k is defined as: if (k plus 1) times Stride is
\*   less than or equal to n then Stride, else n minus k times Stride."
TierSize(n, k) == IF (k + 1) * Stride <= n THEN Stride ELSE n - k * Stride

\* In English: the exact fee of tiers k..top, all over the common
\* denominator BaseD * MultD^top: tier k costs TierSize * BaseN * MultN^k /
\* (BaseD * MultD^k), and MultD^(top - k) brings it to the common
\* denominator.
RECURSIVE TierNum(_, _, _)
\* Literally: "TierNum of n, k and top is defined as: if k is greater than top
\*   then 0, else TierSize of n and k times BaseN times Pow of MultN and k times
\*   Pow of MultD and (top minus k), plus TierNum of n, k plus 1, and top."
TierNum(n, k, top) ==
    IF k > top THEN 0
    ELSE TierSize(n, k) * BaseN * Pow(MultN, k) * Pow(MultD, top - k)
         + TierNum(n, k + 1, top)

\* In English: the reference's tierRefScriptFee: add up every tier exactly,
\* then floor once [C3].
\* Literally: "RefFee of n is defined as: if n equals 0 then 0, else, letting top
\*   be Tiers of n minus 1: TierNum of n, 0 and top, integer-divided by (BaseD
\*   times Pow of MultD and top)."
RefFee(n) ==
    IF n = 0 THEN 0
    ELSE LET top == Tiers(n) - 1
         IN TierNum(n, 0, top) \div (BaseD * Pow(MultD, top))

\* In English: the same fee with every tier floored on its own, a mistake
\* the Go test also kills.
RECURSIVE FlooredTiers(_, _, _)
\* Literally: "FlooredTiers of n, k and top is defined as: if k is greater than
\*   top then 0, else (TierSize of n and k times BaseN times Pow of MultN and
\*   k) integer-divided by (BaseD times Pow of MultD and k), plus FlooredTiers
\*   of n, k plus 1, and top."
FlooredTiers(n, k, top) ==
    IF k > top THEN 0
    ELSE (TierSize(n, k) * BaseN * Pow(MultN, k)) \div (BaseD * Pow(MultD, k))
         + FlooredTiers(n, k + 1, top)

\* In English: gOuroboros' CalculateRefScriptFee [G2]: one floor at the
\* end, the same as the reference; the mutation floors every tier.
\* Literally: "GoRefFee of n is defined as: if n equals 0 then 0, else if
\*   Mutation equals "GoFeeFloorPerTier" then FlooredTiers of n, 0 and (Tiers
\*   of n minus 1), else RefFee of n."
GoRefFee(n) ==
    IF n = 0 THEN 0
    ELSE IF Mutation = "GoFeeFloorPerTier" THEN FlooredTiers(n, 0, Tiers(n) - 1)
    ELSE RefFee(n)

-----------------------------------------------------------------------------
(* GateTxs: the LEDGER and UTXO gates.                                     *)

\* A gate transaction is a record:
\*   valid    the IsValid flag (its scripts are declared to pass)
\*   treas    the current treasury value field: "none", "ok" (equal to the
\*            treasury) or "bad"
\*   ref      the size of the reference scripts it reads, in bytes
\*   short    it pays one lovelace less than the reference-script fee
\*   wdrl     what it withdraws from: "none", the "key" credential, or a
\*            "script" credential (registered with it; never DRep-delegated)
\*   overlap  one of its reference inputs is also a spent input
\* In English: every gate transaction, leaving out a fee that would be negative.
\* Literally: "GateTxs is defined as the set of every tx in the set of
\*   records whose valid is a member of BOOLEAN, treas a member of the set
\*   containing "none", "ok" and "bad", ref a member of 0 through MaxRef plus
\*   1, short a member of BOOLEAN, wdrl a member of the set containing
\*   "none", "key" and "script", and overlap a member of BOOLEAN, such that if
\*   tx's short then RefFee of tx's ref is greater than 0."
GateTxs ==
    {tx \in [valid : BOOLEAN, treas : {"none", "ok", "bad"},
             ref : 0..(MaxRef + 1), short : BOOLEAN,
             wdrl : {"none", "key", "script"}, overlap : BOOLEAN] :
        tx.short => RefFee(tx.ref) > 0}   \* a fee below zero cannot be written

\* In English: the fee the transaction pays.
\* Literally: "Fee of tx is defined as RefFee of tx's ref minus (if tx's short
\*   then 1, else 0)."
Fee(tx) == RefFee(tx.ref) - (IF tx.short THEN 1 ELSE 0)

\* In English: a gate that the era runs only in its phase-2-valid branch
\* is checked when the transaction is valid; one Dijkstra moved before the
\* branch is checked always [C1][D1].
\* Literally: "Gated of tx is defined as: Era equals "Dijkstra" or tx's
\*   valid."
Gated(tx) == Era = "Dijkstra" \/ tx.valid

\* In English: the reference's decision on the gates [C1]-[C6], [D1], [D2].
\* Literally: "SpecGate of tx is defined as: Fee of tx is greater than or
\*   equal to RefFee of tx's ref; and if Gated of tx then tx's treas does not
\*   equal "bad"; and if Gated of tx then tx's ref is less than or equal to
\*   MaxRef; and if Era equals "Conway" and tx's valid and pv does not equal 9
\*   and tx's wdrl equals "key", then deleg does not equal "none"; and if tx's
\*   valid and tx's wdrl does not equal "none", then reg; and if tx's overlap
\*   and Era equals "Conway", then pv is not a member of the set containing 9
\*   and 10."
SpecGate(tx) ==
    /\ Fee(tx) >= RefFee(tx.ref)                       \* FeeTooSmallUTxO [C3]
    /\ Gated(tx) => tx.treas # "bad"                   \* TreasuryValueMismatch
    /\ Gated(tx) => tx.ref <= MaxRef                   \* TxRefScriptsSizeTooBig
    /\ (Era = "Conway" /\ tx.valid /\ pv # 9 /\ tx.wdrl = "key")
           => deleg # "none"                           \* WdrlNotDelegatedToDRep
    /\ (tx.valid /\ tx.wdrl # "none") => reg           \* WithdrawalsMissingAccounts
    /\ (tx.overlap /\ Era = "Conway") => pv \notin {9, 10}  \* NonDisjointRefInputs

\* In English: gOuroboros' decision, read from [G1]-[G6], with the
\* mutations the Bug configurations put in.
\* Literally: "GoGate of tx is defined as: Fee of tx is greater than or equal
\*   to GoRefFee of tx's ref; and if (Era equals "Dijkstra" and Mutation does
\*   not equal "GoTreasuryValidOnly") or tx's valid or Mutation equals
\*   "GoTreasuryAnyPhase", then tx's treas does not equal "bad"; and if (Era
\*   equals "Dijkstra" and Mutation does not equal "GoRefSizeValidOnly") or
\*   tx's valid, then tx's ref is less than or equal to MaxRef; and if Era
\*   equals "Conway" and tx's valid and (pv is greater than or equal to 10 or
\*   Mutation equals "GoDelegAtBootstrap") and (tx's wdrl equals "key" or
\*   (tx's wdrl equals "script" and Mutation equals "GoDelegScripts")), then
\*   (deleg does not equal "none" and (deleg equals "drep" or Mutation does
\*   not equal "GoDelegDRepOnly")); and if tx's valid and tx's wdrl does not
\*   equal "none", then reg; and if tx's overlap and Era equals "Conway", then
\*   pv is greater than or equal to (if Mutation equals "GoDisjointThroughPV11"
\*   then 12, else 11)."
GoGate(tx) ==
    /\ Fee(tx) >= GoRefFee(tx.ref)
    /\ ((Era = "Dijkstra" /\ Mutation # "GoTreasuryValidOnly")
           \/ tx.valid \/ Mutation = "GoTreasuryAnyPhase")
           => tx.treas # "bad"
    /\ ((Era = "Dijkstra" /\ Mutation # "GoRefSizeValidOnly") \/ tx.valid)
           => tx.ref <= MaxRef
    /\ (/\ Era = "Conway" /\ tx.valid
        /\ (pv >= 10 \/ Mutation = "GoDelegAtBootstrap")
        /\ (tx.wdrl = "key" \/ (tx.wdrl = "script" /\ Mutation = "GoDelegScripts")))
           => (deleg # "none" /\ (deleg = "drep" \/ Mutation # "GoDelegDRepOnly"))
    /\ (tx.valid /\ tx.wdrl # "none") => reg
    /\ (tx.overlap /\ Era = "Conway")
           => pv >= (IF Mutation = "GoDisjointThroughPV11" THEN 12 ELSE 11)

-----------------------------------------------------------------------------
(* BalTxs: value conservation with Conway's deposits and refunds.          *)

\* A balance transaction spends In coins and is a record:
\*   valid   the IsValid flag
\*   cert    "none", "regStake" (register the credential with a deposit),
\*           "unregStake" (deregister it, stating the deposit as refund),
\*           "regDRep", "unregDRep" (a DRep registered with DRepDep), or
\*           "prop" (one governance proposal)
\*   don     the treasury donation, 0 (absent) or 1
\*   delta   how far its output is from balancing (0 = balanced)
\* In English: every balance transaction.
\* Literally: "BalTxs is defined as the set of records whose valid is a member
\*   of BOOLEAN, cert a member of the set containing "none", "regStake",
\*   "unregStake", "regDRep", "unregDRep" and "prop", don a member of 0
\*   through 1, and delta a member of negative 1 through 1."
BalTxs ==
    [valid : BOOLEAN,
     cert : {"none", "regStake", "unregStake", "regDRep", "unregDRep", "prop"},
     don : 0..1, delta : -1..1]

\* In English: the coins of the one input every balance transaction spends.
\* Literally: "In is defined as 10."
In == 10    \* the coins its one spent input holds

\* In English: the refund the reference counts as consumed [C7][D3].
\* Conway looks up the deposit the state records, so deregistering an
\* unregistered credential (which only an invalid transaction can carry)
\* refunds nothing; Dijkstra counts the certificate's stated amount.
\* Literally: "SpecRefund of tx is defined as: in the case tx's cert equals
\*   "unregStake", (if Era equals "Dijkstra" or reg then KeyDep, else 0); in
\*   the case tx's cert equals "unregDRep", DRepDep; in every other case, 0."
SpecRefund(tx) ==
    CASE tx.cert = "unregStake" -> IF Era = "Dijkstra" \/ reg THEN KeyDep ELSE 0
      [] tx.cert = "unregDRep"  -> DRepDep
      [] OTHER                  -> 0

\* In English: the deposits the reference counts as produced, from the
\* protocol parameters [C7].
\* Literally: "SpecDeposit of tx is defined as: in the case tx's cert equals
\*   "regStake", KeyDep; in the case tx's cert equals "regDRep", DRepDep; in
\*   the case tx's cert equals "prop", GovDep; in every other case, 0."
SpecDeposit(tx) ==
    CASE tx.cert = "regStake" -> KeyDep
      [] tx.cert = "regDRep"  -> DRepDep
      [] tx.cert = "prop"     -> GovDep
      [] OTHER                -> 0

\* In English: the output's coins: what balances the transaction by the
\* reference's count, moved by delta. The fee is left out (model 17).
\* Literally: "Out of tx is defined as In plus SpecRefund of tx minus
\*   SpecDeposit of tx minus tx's don plus tx's delta."
Out(tx) == In + SpecRefund(tx) - SpecDeposit(tx) - tx.don + tx.delta

\* In English: the reference's decision. Value is conserved: consumed (In
\* plus refund) equals produced (output, deposits, donation) [C7]; Conway
\* checks it for every transaction [C5], Dijkstra only for a valid one [D2].
\* A valid transaction's certificate must also be legal: deregister only a
\* registered credential, register only an unregistered one.
\* Literally: "SpecBal of tx is defined as: if Era equals "Conway" or tx's
\*   valid, then In plus SpecRefund of tx equals Out of tx plus SpecDeposit of
\*   tx plus tx's don; and if tx's valid, then (if tx's cert equals
\*   "unregStake" then reg) and (if tx's cert equals "regStake" then reg is not
\*   true)."
SpecBal(tx) ==
    /\ (Era = "Conway" \/ tx.valid)
           => In + SpecRefund(tx) = Out(tx) + SpecDeposit(tx) + tx.don
    /\ tx.valid => /\ tx.cert = "unregStake" => reg
                   /\ tx.cert = "regStake" => ~reg

\* In English: gOuroboros' refund [G5]: the recorded deposit of a
\* registered credential, nothing for an unregistered one (it does not
\* distinguish the eras: a valid Dijkstra transaction must state the
\* recorded deposit anyway). The mutation takes the certificate's amount in
\* Conway too.
\* Literally: "GoRefund of tx is defined as: in the case tx's cert equals
\*   "unregStake", (if reg or Mutation equals "GoRefundFromCert" then KeyDep,
\*   else 0); in the case tx's cert equals "unregDRep", DRepDep; in every
\*   other case, 0."
GoRefund(tx) ==
    CASE tx.cert = "unregStake" ->
             IF reg \/ Mutation = "GoRefundFromCert" THEN KeyDep ELSE 0
      [] tx.cert = "unregDRep" -> DRepDep
      [] OTHER                 -> 0

\* In English: gOuroboros' decision [G5][G6]: the same equation with its
\* own refund, and the donation dropped by one mutation; Dijkstra's
\* phase-2-valid wrapper, removed by another.
\* Literally: "GoBal of tx is defined as: if Era equals "Conway" or tx's valid
\*   or Mutation equals "GoValueAnyPhase", then In plus GoRefund of tx equals
\*   Out of tx plus SpecDeposit of tx plus (if Mutation equals
\*   "GoDonationIgnored" then 0, else tx's don); and if tx's valid, then (if
\*   tx's cert equals "unregStake" then reg) and (if tx's cert equals
\*   "regStake" then reg is not true)."
GoBal(tx) ==
    /\ (Era = "Conway" \/ tx.valid \/ Mutation = "GoValueAnyPhase")
           => In + GoRefund(tx)
                = Out(tx) + SpecDeposit(tx)
                  + (IF Mutation = "GoDonationIgnored" THEN 0 ELSE tx.don)
    /\ tx.valid => /\ tx.cert = "unregStake" => reg
                   /\ tx.cert = "regStake" => ~reg

-----------------------------------------------------------------------------
(* The questions.                                                          *)

\* In English: the state is one TableSpec can start in.
\* Literally: "TypeOK is defined as: pv is a member of PVs, and reg is a member
\*   of BOOLEAN, and deleg is a member of the set containing "none", "drep" and
\*   "abstain"."
TypeOK == /\ pv \in PVs
          /\ reg \in BOOLEAN
          /\ deleg \in {"none", "drep", "abstain"}

\* In English: in this state, gOuroboros accepts exactly the gate and
\* balance transactions the reference accepts.
\* Literally: "GoAgrees is defined as: for all tx in GateTxs, GoGate of tx
\*   if and only if SpecGate of tx; and for all tx in BalTxs, GoBal of tx if
\*   and only if SpecBal of tx."
GoAgrees ==
    /\ \A tx \in GateTxs : GoGate(tx) <=> SpecGate(tx)
    /\ \A tx \in BalTxs : GoBal(tx) <=> SpecBal(tx)

\* In English: the fee tiers are not trivial: some size pays a fee that
\* flooring each tier would get wrong. Without it the floor mutation could
\* not be told apart. It names pv so that TLC checks it in each state.
\* Literally: "FeeTiersMatter is defined as: pv is a member of PVs, and there
\*   exists an n in 1 through MaxRef plus 1 such that FlooredTiers of n, 0 and
\*   (Tiers of n minus 1) does not equal RefFee of n."
FeeTiersMatter ==
    pv \in PVs /\ \E n \in 1..(MaxRef + 1) : FlooredTiers(n, 0, Tiers(n) - 1) # RefFee(n)

\* Reachability probes: each must be violated (a *Bug.cfg).

\* In English: "no transaction is refused by the delegation rule alone".
\* Literally: "ProbeNoDelegRefusal is defined as: there does not exist a tx in
\*   GateTxs such that SpecGate of tx is not true and SpecGate of (tx except
\*   that its wdrl is "none") is true and tx's wdrl equals "key"."
ProbeNoDelegRefusal ==
    ~\E tx \in GateTxs :
        /\ tx.wdrl = "key"
        /\ ~SpecGate(tx)
        /\ SpecGate([tx EXCEPT !.wdrl = "none"])

\* In English: "no invalid transaction is refused by a treasury value
\* mismatch" (true in Conway, false in Dijkstra).
\* Literally: "ProbeNoInvalidTreasuryRefusal is defined as: there does not
\*   exist a tx in GateTxs such that tx's valid is not true and tx's treas
\*   equals "bad" and SpecGate of tx is not true and SpecGate of (tx except
\*   that its treas is "ok") is true."
ProbeNoInvalidTreasuryRefusal ==
    ~\E tx \in GateTxs :
        /\ ~tx.valid /\ tx.treas = "bad"
        /\ ~SpecGate(tx)
        /\ SpecGate([tx EXCEPT !.treas = "ok"])

\* In English: "no transaction reading and spending the same input is
\* accepted" (false from pv 11).
\* Literally: "ProbeNoOverlapAccepted is defined as: there does not exist a tx
\*   in GateTxs such that tx's overlap and SpecGate of tx."
ProbeNoOverlapAccepted == ~\E tx \in GateTxs : tx.overlap /\ SpecGate(tx)

-----------------------------------------------------------------------------
(* TableSpec: every protocol version, registration and delegation state.  *)

\* In English: start in any of the states; nothing moves.
\* Literally: "Init is defined as: pv is a member of PVs, and reg is a member of
\*   BOOLEAN, and deleg is a member of the set containing "none", "drep" and
\*   "abstain"."
Init == /\ pv \in PVs
        /\ reg \in BOOLEAN
        /\ deleg \in {"none", "drep", "abstain"}

\* In English: nothing ever changes; every state is checked as it starts.
\* Literally: "Next is defined as: vars is unchanged."
Next == UNCHANGED vars

\* In English: "Start in Init, and from then on nothing changes."
\* Literally: "TableSpec is defined as: Init holds at the start, and always,
\*   every step is a Next step or a step that leaves vars unchanged."
TableSpec == Init /\ [][Next]_vars
=============================================================================
