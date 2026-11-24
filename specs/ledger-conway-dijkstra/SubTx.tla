-------------------------------- MODULE SubTx --------------------------------
(***************************************************************************)
(* Dijkstra's nested transactions: a top-level transaction carries a      *)
(* list of sub-transactions, and the batch is validated and applied as    *)
(* one. This module models how the batch is checked against the UTxO      *)
(* before and after the sub-transactions, the batch-wide limits, the      *)
(* withdrawals (CIP-159 partial withdrawals and the legacy drain), direct *)
(* deposits (CIP-159), and what an applied batch does to the ledger.      *)
(*                                                                         *)
(* Two specifications:                                                     *)
(*   TableSpec: every account state is a starting state and nothing       *)
(*     moves. GoAgrees checks, in each, that gOuroboros accepts exactly   *)
(*     the batches the reference accepts, over four families (which       *)
(*     inputs each level spends and reads; the current treasury value at  *)
(*     each level; the reference-script size at each level; withdrawals   *)
(*     and direct deposits).                                               *)
(*   Spec: a ledger applies accepted batches one after another and checks *)
(*     that value is preserved, that no input is spent twice, and that a  *)
(*     phase-2-invalid batch gives up only its collateral.                *)
(*                                                                         *)
(* The pinned draft. gOuroboros' ledger/dijkstra/doc.go pins the Dijkstra *)
(* CDDL at cardano-ledger 505fa72260632fca6df33e18e18719730bf9a460 (the   *)
(* ouroboros-leios rc-2026w41 build). That commit is an ancestor of the   *)
(* reference revision used here, 1210d37fe6bd; the rules below are cited  *)
(* at 1210d37fe6bd. Sub-transactions are CIP-0118 (nested transactions),  *)
(* direct deposits and partial withdrawals CIP-0159.                      *)
(*                                                                         *)
(* Sources (cardano-ledger 1210d37fe6bd, eras/dijkstra/impl/src/Cardano/  *)
(* Ledger/Dijkstra/):                                                      *)
(*   [D1] Rules/Ledger.hs 393-461: SUBLEDGERS runs first, against the     *)
(*        original UTxO and accounts and the top's IsValid; then the top's *)
(*        treasury value and the batch's reference-script size (always), *)
(*        ENTITIES and GOV (Phase2Valid only), then UTXOW.                *)
(*   [D2] Rules/SubLedger.hs 232-297: each sub-transaction's treasury     *)
(*        value is checked whatever IsValid says; SUBENTITIES only when   *)
(*        the top is Phase2Valid.                                          *)
(*   [D3] Rules/SubLedgers.hs 132-140: the sub-transactions in order.     *)
(*   [D4] Rules/SubUtxo.hs 211-262: a sub-transaction's spent inputs must *)
(*        be non-empty and in the UTxO as the earlier sub-transactions    *)
(*        left it; it is applied only when the top is Phase2Valid.       *)
(*   [D5] Rules/Utxo.hs 301-447: the top's spent inputs non-empty; every  *)
(*        level's spent, reference and collateral inputs in the original  *)
(*        UTxO (allInputsTxBodyF); the top's spent inputs in the UTxO     *)
(*        after the sub-transactions; value conservation over the batch   *)
(*        only when Phase2Valid.                                           *)
(*   [D6] UTxO.hs 370-387 batchNonDistinctRefScriptsSize: the reference-  *)
(*        script size summed over every level; Rules/Ledger.hs 351-361    *)
(*        validateAllRefScriptSize.                                        *)
(*   [D7] Rules/Entities.hs 275-314, 366-420: withdrawals. Outside legacy *)
(*        mode the batch's withdrawals from an account may not exceed its *)
(*        original balance; in legacy mode the sub-transactions' may not, *)
(*        and the top's must drain the balance the sub-transactions left. *)
(*        Direct deposits go to accounts registered after the level's     *)
(*        certificates; missing ones fail.                                 *)
(*   [D8] Rules/SubEntities.hs: a sub-transaction's withdrawal account    *)
(*        must exist in the original and the current accounts; its        *)
(*        withdrawals then its direct deposits are applied.               *)
(*   [D9] Dijkstra.hs 156-206: legacy mode = the top level needs a Plutus *)
(*        V1, V2 or V3 script.                                             *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 756a9a89,              *)
(* ledger/dijkstra/rules.go):                                              *)
(*   [G1] 333-401 the phase table: BadInputs, InputSetEmpty,               *)
(*        CurrentTreasuryValue and RefScriptSizePerTx Always;              *)
(*        NoDuplicateInputs, BatchWithdrawals, ValueNotConserved and      *)
(*        Withdrawals Phase2Valid.                                         *)
(*   [G2] 2403-2444 UtxoValidateBadInputsUtxo: every level's spent and    *)
(*        reference inputs against the original UTxO; 2496-2533           *)
(*        InputSetEmpty per level and NoDuplicateInputs over the batch.   *)
(*   [G3] ledger/common/rules.go 412-440 ...CurrentTreasuryValueAnyPhase: *)
(*        every level's stated value.                                      *)
(*   [G4] 5259-5283, 5345-5365: the reference-script size summed over the *)
(*        top and every sub-transaction.                                   *)
(*   [G5] 2577-2698 UtxoValidateBatchWithdrawals (the aggregate against   *)
(*        the original balance; the top left out in legacy mode) and      *)
(*        4869-4924 UtxoValidateWithdrawals (each level against the       *)
(*        account state threaded through the earlier levels, the top      *)
(*        exact in legacy mode); 2911-3061 the threading.                 *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the README section "Reading a formula     *)
(* literally" and specs/keepalive/KeepAlive.tla.                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxRef,    \* the per-transaction (batch) reference-script size limit
    MaxTxs,    \* how many batches the ledger applies (Spec only)
    Mutation   \* "none", or one deliberate mistake (see the README)

\* In English: the three places an input can name. "a" and "b" hold
\* outputs in the original UTxO; "c" never does.
\* Literally: "Places is defined as the set containing "a", "b" and "c"."
Places == {"a", "b", "c"}
\* In English: the places that hold an output in the original UTxO.
\* Literally: "Live0 is defined as the set containing "a" and "b"."
Live0 == {"a", "b"}

\* In English: the sequences of length 0, 1 or 2 drawn from S: a batch has
\* at most two sub-transactions here.
\* Literally: "UpTo2 of S is defined as the union of the set containing the
\*   empty tuple, the set of the tuple of x for every x that is a member of S,
\*   and the set of the tuple of x and y for every x and y that are members
\*   of S."
UpTo2(S) == {<<>>} \cup {<<x>> : x \in S} \cup {<<x, y>> : x \in S, y \in S}

VARIABLES
    reg,       \* is the one reward account registered?
    bal,       \* its balance
    utxo,      \* Spec: utxo[i] is the coin at output i, or -1 when spent
    treasury,  \* Spec: the treasury
    fees,      \* Spec: the fee pot (collateral of invalid batches)
    n,         \* Spec: batches applied so far
    last       \* Spec: what the last applied batch did, for the invariants

\* Literally: "vars is defined as the tuple of reg, bal, utxo, treasury, fees,
\*   n and last."
vars == <<reg, bal, utxo, treasury, fees, n, last>>

-----------------------------------------------------------------------------
(* Family 1: which inputs each level spends and reads [D4][D5].            *)

\* A level spends a set of places and reads a set of places.
\* In English: every level a batch in family 1 can have.
\* Literally: "Levels is defined as the set of records whose ins is a member
\*   of the set of subsets of Places, and whose refs is a member of the set
\*   containing the empty set, the set containing "a", and the set containing
\*   "c"."
Levels == [ins : SUBSET Places, refs : {{}, {"a"}, {"c"}}]

\* In English: every batch of family 1: a top level and up to two sub-transactions, valid or not.
\* Literally: "InputBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of Levels, and subs a member of UpTo2 of
\*   Levels."
InputBatches == [valid : BOOLEAN, top : Levels, subs : UpTo2(Levels)]

\* In English: the levels of a batch: its sub-transactions, then the top.
\* Literally: "AllLevels of b is defined as the set of b's subs of k for every
\*   k that is a member of the domain of b's subs, united with the set
\*   containing b's top."
AllLevels(b) == {b.subs[k] : k \in DOMAIN b.subs} \cup {b.top}

\* In English: sub-transaction k spends something an earlier one spent.
\* Literally: "SubClash of b and k is defined as: there exists a j in 1 through
\*   k minus 1 such that the intersection of b's subs of j's ins and b's subs
\*   of k's ins does not equal the empty set."
SubClash(b, k) == \E j \in 1..(k - 1) : b.subs[j].ins \cap b.subs[k].ins # {}

\* In English: everything the sub-transactions spend.
\* Literally: "SubIns of b is defined as the union of all the sets in the set
\*   of b's subs of k's ins for every k in the domain of b's subs."
SubIns(b) == UNION {b.subs[k].ins : k \in DOMAIN b.subs}

\* In English: the reference's decision [D4][D5]. Every level spends
\* something. Every level's spent and reference inputs are in the original
\* UTxO. When the top is phase-2-valid the sub-transactions are applied in
\* turn, so each must find its inputs still unspent, and the top must find
\* its inputs unspent after all of them. When it is invalid nothing is
\* applied, so overlaps are not refused.
\* Literally: "SpecInputs of b is defined as: for all l in AllLevels of b,
\*   l's ins does not equal the empty set and the union of l's ins and l's refs
\*   is a subset of Live0; and if b's valid, then (for all k in the domain of
\*   b's subs, SubClash of b and k is not true) and the intersection of b's
\*   top's ins and SubIns of b equals the empty set."
SpecInputs(b) ==
    /\ \A l \in AllLevels(b) : /\ l.ins # {}                  \* InputSetEmpty
                               /\ l.ins \cup l.refs \subseteq Live0   \* BadInputs, utxo0
    /\ b.valid => /\ \A k \in DOMAIN b.subs : ~SubClash(b, k)   \* SubBadInputs, utxo_s
                  /\ b.top.ins \cap SubIns(b) = {}            \* BadInputs, after subs

\* In English: gOuroboros' decision [G1][G2]: InputSetEmpty and BadInputs
\* (spent and reference inputs) per level against the original UTxO, and
\* NoDuplicateInputs over every level's spent inputs when valid. The
\* mutations check only the top, skip the reference inputs, or refuse
\* duplicates in an invalid batch too.
\* Literally: "GoInputs of b is defined as: for all l in AllLevels of b, l's
\*   ins does not equal the empty set and (if l equals b's top or Mutation does
\*   not equal "GoBadInputsTopOnly", then l's ins is a subset of Live0 and (l's
\*   refs is a subset of Live0 or Mutation equals "GoRefsUnchecked")); and if
\*   b's valid or Mutation equals "GoNoDuplicatesAnyPhase", then (for all k in
\*   the domain of b's subs, SubClash of b and k is not true) and the
\*   intersection of b's top's ins and SubIns of b equals the empty set."
GoInputs(b) ==
    /\ \A l \in AllLevels(b) :
           /\ l.ins # {}
           /\ (l = b.top \/ Mutation # "GoBadInputsTopOnly")
                  => /\ l.ins \subseteq Live0
                     /\ l.refs \subseteq Live0 \/ Mutation = "GoRefsUnchecked"
    /\ (b.valid \/ Mutation = "GoNoDuplicatesAnyPhase")
           => /\ \A k \in DOMAIN b.subs : ~SubClash(b, k)
              /\ b.top.ins \cap SubIns(b) = {}

-----------------------------------------------------------------------------
(* Family 2: the current treasury value at each level [D1][D2].            *)

\* In English: every batch of family 2: what each level states as the treasury value.
\* Literally: "TreasBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of the set containing "none", "ok" and
\*   "bad", and subs a member of UpTo2 of that set."
TreasBatches ==
    [valid : BOOLEAN, top : {"none", "ok", "bad"},
     subs : UpTo2({"none", "ok", "bad"})]

\* In English: the reference checks every level's stated treasury value,
\* valid or not [D1][D2].
\* Literally: "SpecTreas of b is defined as: b's top does not equal "bad", and
\*   for all k in the domain of b's subs, b's subs of k does not equal "bad"."
SpecTreas(b) == b.top # "bad" /\ \A k \in DOMAIN b.subs : b.subs[k] # "bad"

\* In English: gOuroboros [G3]: every level, valid or not; the mutations
\* check only the top, or only a valid batch.
\* Literally: "GoTreas of b is defined as: if b's valid or Mutation does not
\*   equal "GoTreasValidOnly", then b's top does not equal "bad" and (Mutation
\*   equals "GoTreasTopOnly" or for all k in the domain of b's subs, b's subs
\*   of k does not equal "bad")."
GoTreas(b) ==
    (b.valid \/ Mutation # "GoTreasValidOnly")
        => /\ b.top # "bad"
           /\ Mutation = "GoTreasTopOnly" \/ \A k \in DOMAIN b.subs : b.subs[k] # "bad"

-----------------------------------------------------------------------------
(* Family 3: the reference-script size over the batch [D6].                *)

\* In English: every batch of family 3: how many units of reference script each level reads.
\* Literally: "RefBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of 0 through 3, and subs a member of UpTo2
\*   of 0 through 3."
RefBatches == [valid : BOOLEAN, top : 0..3, subs : UpTo2(0..3)]

\* In English: the sum of a sequence of numbers.
RECURSIVE SumSeq(_)
\* Literally: "SumSeq of s is defined as: if s equals the empty tuple then 0,
\*   else the head of s plus SumSeq of the tail of s."
SumSeq(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumSeq(Tail(s))

\* In English: the reference sums the size over every level and checks it
\* whatever IsValid says [D6][D1].
\* Literally: "SpecRef of b is defined as: b's top plus SumSeq of b's subs is
\*   less than or equal to MaxRef."
SpecRef(b) == b.top + SumSeq(b.subs) <= MaxRef

\* In English: gOuroboros [G4]; the mutation measures the top alone.
\* Literally: "GoRef of b is defined as: b's top plus (if Mutation equals
\*   "GoRefTopOnly" then 0, else SumSeq of b's subs) is less than or equal to
\*   MaxRef."
GoRef(b) == b.top + (IF Mutation = "GoRefTopOnly" THEN 0 ELSE SumSeq(b.subs))
                <= MaxRef

-----------------------------------------------------------------------------
(* Family 4: withdrawals and direct deposits [D7][D8].                     *)

\* A withdrawal batch has one sub-transaction. -1 means "no withdrawal".
\*   legacy  the top needs a Plutus V1-V3 script [D9]
\*   wt, ws  what the top and the sub-transaction withdraw from the account
\*   dd      what the sub-transaction deposits directly into the account
\* In English: every batch of family 4.
\* Literally: "WdrlBatches is defined as the set of records whose valid and
\*   legacy are members of BOOLEAN, whose wt and ws are members of negative 1
\*   through 3, and whose dd is a member of 0 through 1."
WdrlBatches ==
    [valid : BOOLEAN, legacy : BOOLEAN, wt : -1..3, ws : -1..3, dd : 0..1]

\* In English: what a withdrawal field takes, counting "none" as zero.
\* Literally: "W of x is defined as: if x equals negative 1 then 0, else x."
W(x) == IF x = -1 THEN 0 ELSE x

\* In English: the reference's decision, only for a valid batch (ENTITIES
\* and SUBENTITIES are in the Phase2Valid branch) [D7][D8]. An account
\* withdrawn from or deposited into must exist. Outside legacy mode a
\* withdrawal may be partial, but the batch may not take more than the
\* original balance. In legacy mode the sub-transaction may not take more
\* than the original balance, and the top must take exactly what is left
\* after the sub-transaction's withdrawal and direct deposit.
\* Literally: "SpecWdrl of b is defined as: if b's valid, then (if b's wt is
\*   greater than or equal to 0 or b's ws is greater than or equal to 0 or b's
\*   dd is greater than 0, then reg) and (if b's legacy is not true, then W of
\*   b's wt plus W of b's ws is less than or equal to bal) and (if b's legacy,
\*   then W of b's ws is less than or equal to bal and (if b's wt is greater
\*   than or equal to 0, then b's wt equals bal minus W of b's ws plus b's
\*   dd))."
SpecWdrl(b) ==
    b.valid =>
        /\ (b.wt >= 0 \/ b.ws >= 0 \/ b.dd > 0) => reg
        /\ ~b.legacy => W(b.wt) + W(b.ws) <= bal
        /\ b.legacy => /\ W(b.ws) <= bal
                       /\ b.wt >= 0 => b.wt = bal - W(b.ws) + b.dd

\* In English: gOuroboros [G5]: the aggregate check (the top left out in
\* legacy mode), then each level against the threaded account: the
\* sub-transaction at most the balance, then the balance less its
\* withdrawal plus its direct deposit for the top, exactly so in legacy
\* mode. The mutations drop the aggregate check, or drain the original
\* balance in legacy mode.
\* Literally: "GoWdrl of b is defined as: if b's valid then, letting cur be
\*   bal minus W of b's ws plus b's dd and drain be (if Mutation equals
\*   "GoDrainOriginal" then bal, else cur): (if b's wt is greater than or equal
\*   to 0 or b's ws is greater than or equal to 0 or b's dd is greater than 0,
\*   then reg); and (if Mutation does not equal "GoNoAggregate", then (if b's
\*   legacy then 0, else W of b's wt) plus W of b's ws is less than or equal to
\*   bal); and W of b's ws is less than or equal to bal; and (if b's wt is
\*   greater than or equal to 0, then (if b's legacy then b's wt equals drain,
\*   else b's wt is less than or equal to cur))."
GoWdrl(b) ==
    b.valid =>
        LET cur   == bal - W(b.ws) + b.dd
            drain == IF Mutation = "GoDrainOriginal" THEN bal ELSE cur
        IN /\ (b.wt >= 0 \/ b.ws >= 0 \/ b.dd > 0) => reg
           /\ Mutation # "GoNoAggregate"
                  => (IF b.legacy THEN 0 ELSE W(b.wt)) + W(b.ws) <= bal
           /\ W(b.ws) <= bal
           /\ b.wt >= 0 => IF b.legacy THEN b.wt = drain ELSE b.wt <= cur

-----------------------------------------------------------------------------
(* The table questions.                                                    *)

\* In English: in this account state, gOuroboros accepts exactly the
\* batches the reference accepts, in all four families.
\* Literally: "GoAgrees is defined as: for all b in InputBatches, GoInputs of b
\*   if and only if SpecInputs of b; and for all b in TreasBatches, GoTreas of
\*   b if and only if SpecTreas of b; and for all b in RefBatches, GoRef of b
\*   if and only if SpecRef of b; and for all b in WdrlBatches, GoWdrl of b if
\*   and only if SpecWdrl of b."
GoAgrees ==
    /\ \A b \in InputBatches : GoInputs(b) <=> SpecInputs(b)
    /\ \A b \in TreasBatches : GoTreas(b) <=> SpecTreas(b)
    /\ \A b \in RefBatches : GoRef(b) <=> SpecRef(b)
    /\ \A b \in WdrlBatches : GoWdrl(b) <=> SpecWdrl(b)

\* Table probes, each expected to be violated.
\* In English: "no phase-2-invalid batch whose sub-transactions spend the
\* same input is accepted" (false: nothing is applied).
\* It names reg so that TLC checks it in each state, not once as a constant.
\* Literally: "ProbeNoInvalidOverlap is defined as: reg is a member of BOOLEAN,
\*   and there does not exist a b in InputBatches such that b's valid is not
\*   true and the length of b's subs equals 2 and SubClash of b and 2 and
\*   SpecInputs of b."
ProbeNoInvalidOverlap ==
    reg \in BOOLEAN /\ ~\E b \in InputBatches :
        ~b.valid /\ Len(b.subs) = 2 /\ SubClash(b, 2) /\ SpecInputs(b)
\* In English: "no partial withdrawal is accepted" (false outside legacy
\* mode).
\* Literally: "ProbeNoPartialWithdrawal is defined as: there does not exist a
\*   b in WdrlBatches such that b's valid and b's wt is greater than 0 and b's
\*   wt is less than bal and b's ws equals negative 1 and SpecWdrl of b."
ProbeNoPartialWithdrawal ==
    ~\E b \in WdrlBatches :
        b.valid /\ b.wt > 0 /\ b.wt < bal /\ b.ws = -1 /\ SpecWdrl(b)
\* In English: "the legacy top never drains a direct deposit made by its
\* sub-transaction" (false).
\* Literally: "ProbeNoLegacyDrainOfDeposit is defined as: there does not exist
\*   a b in WdrlBatches such that b's valid and b's legacy and b's dd equals 1
\*   and b's wt is greater than bal and SpecWdrl of b."
ProbeNoLegacyDrainOfDeposit ==
    ~\E b \in WdrlBatches :
        b.valid /\ b.legacy /\ b.dd = 1 /\ b.wt > bal /\ SpecWdrl(b)

-----------------------------------------------------------------------------
(* TableSpec.                                                              *)

\* In English: any registration and balance; the ledger variables sit at a
\* fixed value.
\* Literally: "TableInit is defined as: reg is a member of BOOLEAN, and bal is
\*   a member of 1 through 2, and utxo equals the empty tuple, and treasury,
\*   fees and n equal 0, and last equals "none"."
TableInit == /\ reg \in BOOLEAN /\ bal \in 1..2
             /\ utxo = <<>> /\ treasury = 0 /\ fees = 0 /\ n = 0
             /\ last = "none"

\* In English: start in any TableInit state and never move.
\* Literally: "TableSpec is defined as: TableInit holds at the start, and
\*   always, every step is a step that leaves vars unchanged."
TableSpec == TableInit /\ [][UNCHANGED vars]_vars

-----------------------------------------------------------------------------
(* Spec: a ledger applying batches.                                        *)

\* Outputs are numbered: the original two are 1 and 2; batch t's level k
\* (k = 0 for the top, 1 or 2 for a sub-transaction) creates output
\* 2 + 3 * (t - 1) + k + 1.
\* In English: the numbers every output of the run can have.
\* Literally: "Outs is defined as 1 through 2 plus 3 times MaxTxs."
Outs == 1..(2 + 3 * MaxTxs)
\* In English: the number of the output batch t creates at level k.
\* Literally: "OutId of t and k is defined as 2 plus 3 times (t minus 1) plus k
\*   plus 1."
OutId(t, k) == 2 + 3 * (t - 1) + k + 1

\* In English: the outputs not yet spent.
\* Literally: "Live is defined as the set of every i in Outs such that utxo of
\*   i is greater than or equal to 0."
Live == {i \in Outs : utxo[i] >= 0}

\* In English: the coins at a set of outputs.
RECURSIVE CoinOf(_)
\* Literally: "CoinOf of S is defined as: if S equals the empty set then 0,
\*   else, letting i be the x, chosen from S, such that TRUE: utxo of i plus
\*   CoinOf of (S without the members of the set containing i)."
CoinOf(S) == IF S = {} THEN 0
             ELSE LET i == CHOOSE x \in S : TRUE IN utxo[i] + CoinOf(S \ {i})

\* In English: the total that must never change: coins in the UTxO, the
\* fee pot, the treasury and the reward account.
\* Literally: "Total is defined as CoinOf of Live plus fees plus treasury plus
\*   bal."
Total == CoinOf(Live) + fees + treasury + bal

\* In English: the total the run starts with.
\* Literally: "Start is defined as 6."
Start == 6    \* the starting total: 2 + 2 in the UTxO, 1 reward, 1 treasury

\* A ledger level spends ins, deposits dd directly into the reward
\* account, donates don to the treasury, and makes one output holding the
\* rest. To keep the state space small the top level donates and a
\* sub-transaction spends one output and deposits directly.
\* In English: the top levels a ledger batch can have.
\* Literally: "TopLevels of L is defined as the set of every l in the set of
\*   records whose ins is a member of the set of subsets of L, dd a member of
\*   the set containing 0, and don a member of 0 through 1, such that l's ins
\*   does not equal the empty set."
TopLevels(L) == {l \in [ins : SUBSET L, dd : {0}, don : 0..1] : l.ins # {}}
\* In English: the sub-transactions a ledger batch can have.
\* Literally: "SubLevels of L is defined as the set of records whose ins is a
\*   member of the set of the set containing x for every x that is a member of
\*   L, dd a member of 0 through 1, and don a member of the set containing 0."
SubLevels(L) == [ins : {{x} : x \in L}, dd : 0..1, don : {0}]

\* In English: a level's output, what is left of its inputs.
\* Literally: "LOut of l is defined as CoinOf of l's ins minus l's dd minus l's
\*   don."
LOut(l) == CoinOf(l.ins) - l.dd - l.don

\* In English: the reference's acceptance of a ledger batch: the inputs
\* rule of family 1 against the current UTxO, applied to spent inputs (the
\* mutation drops the threaded check, so sub-transactions may spend the
\* same input), and every output non-negative.
\* Literally: "LAccepts of b is defined as: for all l in AllLevels of b, LOut
\*   of l is greater than or equal to 0; and if b's valid and Mutation does
\*   not equal "SpecSubsAgainstOriginal", then (for all k in the domain of b's
\*   subs, the intersection of b's subs of k's ins and the union of all the
\*   sets in the set of b's subs of j's ins for every j in 1 through k minus 1
\*   equals the empty set) and the intersection of b's top's ins and SubIns of
\*   b equals the empty set."
LAccepts(b) ==
    /\ \A l \in AllLevels(b) : LOut(l) >= 0
    /\ (b.valid /\ Mutation # "SpecSubsAgainstOriginal")
           => /\ \A k \in DOMAIN b.subs :
                     b.subs[k].ins \cap UNION {b.subs[j].ins : j \in 1..(k - 1)} = {}
              /\ b.top.ins \cap SubIns(b) = {}

\* In English: apply a valid batch: every level in turn removes its inputs
\* and adds its output; its direct deposits go to the reward account and its
\* donation to the treasury. The donation mutation loses it.
\* Literally: "ApplyValid of b is defined as: letting t be n plus 1, ks be the
\*   domain of b's subs, spent be the union of SubIns of b and b's top's ins, lv
\*   be the tuple of b's top followed by b's subs, dds be SumSeq of the function
\*   that maps every k in the domain of lv to lv of k's dd, and dons the same
\*   for don: utxo in the next state equals the function that maps every i in
\*   Outs to: in the case i is a member of spent, negative 1; in the case i
\*   equals OutId of t and 0, LOut of b's top; in the case there exists a k in
\*   ks such that i equals OutId of t and k, LOut of b's subs of (the k, chosen
\*   from ks, such that i equals OutId of t and k); in every other case, utxo
\*   of i; and bal in the next state equals bal plus dds; and treasury in the
\*   next state equals treasury plus (if Mutation equals "SpecDonationLost"
\*   then 0, else dons); and fees is unchanged."
ApplyValid(b) ==
    LET t == n + 1
        ks == DOMAIN b.subs
        spent == SubIns(b) \cup b.top.ins
        lv == <<b.top>> \o b.subs   \* every level, top first
        dds == SumSeq([k \in DOMAIN lv |-> lv[k].dd])
        dons == SumSeq([k \in DOMAIN lv |-> lv[k].don])
    IN /\ utxo' = [i \in Outs |->
                     CASE i \in spent -> -1
                       [] i = OutId(t, 0) -> LOut(b.top)
                       [] \E k \in ks : i = OutId(t, k)
                            -> LOut(b.subs[CHOOSE k \in ks : i = OutId(t, k)])
                       [] OTHER -> utxo[i]]
       /\ bal' = bal + dds
       /\ treasury' = treasury + (IF Mutation = "SpecDonationLost" THEN 0 ELSE dons)
       /\ UNCHANGED fees

\* In English: apply a phase-2-invalid batch: only the collateral moves,
\* to the fee pot. The mutation applies the sub-transactions' inputs too.
\* Literally: "ApplyInvalid of b and coll is defined as: utxo in the next
\*   state equals the function that maps every i in Outs to: if i is a member
\*   of coll, or (Mutation equals "SpecInvalidAppliesSubs" and i is a member
\*   of SubIns of b), then negative 1, else utxo of i; and fees in the next
\*   state equals fees plus CoinOf of coll; and bal and treasury are
\*   unchanged."
ApplyInvalid(b, coll) ==
    /\ utxo' = [i \in Outs |->
                  IF i \in coll \/ (Mutation = "SpecInvalidAppliesSubs" /\ i \in SubIns(b))
                  THEN -1 ELSE utxo[i]]
    /\ fees' = fees + CoinOf(coll)
    /\ UNCHANGED <<bal, treasury>>

\* In English: the ledger starts with two outputs of two coins, one reward
\* coin, one treasury coin.
\* Literally: "Init is defined as: reg equals TRUE, bal equals 1, utxo equals
\*   the function that maps every i in Outs to (if i is a member of the set
\*   containing 1 and 2 then 2, else negative 1), treasury equals 1, fees
\*   equals 0, n equals 0, and last equals "none"."
Init == /\ reg = TRUE /\ bal = 1
        /\ utxo = [i \in Outs |-> IF i \in {1, 2} THEN 2 ELSE -1]
        /\ treasury = 1 /\ fees = 0 /\ n = 0 /\ last = "none"

\* In English: apply one accepted batch, with at most two
\* sub-transactions, valid or invalid (an invalid one names one collateral
\* output), and record what it did.
\* Literally: "Step is defined as: n is less than MaxTxs, and there exists a
\*   b in the set of records whose valid is a member of BOOLEAN, top a member
\*   of TopLevels of Live, and subs a member of UpTo2 of SubLevels of Live, such
\*   that LAccepts of b and (if b's valid then ApplyValid of b and last in the
\*   next state equals (if there exists k and j in the domain of b's subs with
\*   k less than j and the intersection of their ins not empty, or the
\*   intersection of b's top's ins and SubIns of b not empty, then "twice",
\*   else "valid"), else there exists a c in Live such that ApplyInvalid of b
\*   and the set containing c, and last in the next state equals
\*   "invalid"); and n in the next state equals n plus 1; and reg is
\*   unchanged."
Step ==
    /\ n < MaxTxs
    /\ \E b \in [valid : BOOLEAN, top : TopLevels(Live), subs : UpTo2(SubLevels(Live))] :
          /\ LAccepts(b)
          /\ IF b.valid
             THEN /\ ApplyValid(b)
                  /\ last' = IF \/ \E k, j \in DOMAIN b.subs :
                                     k < j /\ b.subs[k].ins \cap b.subs[j].ins # {}
                                \/ b.top.ins \cap SubIns(b) # {}
                             THEN "twice" ELSE "valid"
             ELSE \E c \in Live : /\ ApplyInvalid(b, {c})
                                  /\ last' = IF \E i \in SubIns(b) \ {c} : utxo'[i] = -1
                                             THEN "invalidMoved" ELSE "invalid"
    /\ n' = n + 1
    /\ UNCHANGED reg

\* In English: when every batch has been applied, stay put.
\* Literally: "Done is defined as: n equals MaxTxs and vars is unchanged."
Done == n = MaxTxs /\ UNCHANGED vars

\* In English: start in Init, then apply batches until MaxTxs of them have been applied.
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Step or Done step or a step that leaves vars unchanged."
Spec == Init /\ [][Step \/ Done]_vars

\* In English: value is neither made nor lost.
\* Literally: "ValuePreserved is defined as: Total equals Start."
ValuePreserved == Total = Start

\* In English: no applied batch spent an input twice.
\* Literally: "SpentOnce is defined as: last does not equal "twice"."
SpentOnce == last # "twice"

\* In English: an invalid batch gave up only its collateral.
\* Literally: "InvalidKeeps is defined as: last does not equal
\*   "invalidMoved"."
InvalidKeeps == last # "invalidMoved"

\* Ledger probes, each expected to be violated.
\* In English: "no phase-2-invalid batch is ever applied".
\* Literally: "ProbeNoInvalid is defined as: last does not equal "invalid"."
ProbeNoInvalid == last # "invalid"
\* In English: "no batch ever moves value into the treasury or the reward
\* account".
\* Literally: "ProbeNoTransfer is defined as: treasury plus bal equals 2."
ProbeNoTransfer == treasury + bal = 2
=============================================================================
