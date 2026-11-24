-------------------------------- MODULE Utxo --------------------------------
(***************************************************************************)
(* The UTXO rule (with UTXOW's phase-2 handling and UTXOS's state change)  *)
(* of the Shelley, Allegra, Mary, Alonzo and Babbage eras, at a small      *)
(* abstract scale, and gOuroboros' decisions for the same transactions.    *)
(*                                                                         *)
(* A transaction spends inputs, pays a fee and maybe a key deposit,        *)
(* collects a refund and a withdrawal, mints or burns one token, and makes *)
(* one output. From Alonzo it may run Plutus scripts (redeemers), and then *)
(* it names collateral; it declares whether its scripts pass (IsValid).    *)
(* From Babbage it may read reference inputs, return part of its          *)
(* collateral, and state the total collateral.                            *)
(*                                                                         *)
(* Two specifications share this module:                                   *)
(*   TableSpec: every small UTxO and slot is a starting state, and nothing *)
(*     moves. The invariant GoAgrees then checks, in each such state, that *)
(*     gOuroboros accepts exactly the transactions the reference accepts,  *)
(*     over five families of transactions (inputs, balance, outputs,       *)
(*     validity interval, collateral and phase 2).                         *)
(*   Spec: a ledger that applies accepted transactions one after another,  *)
(*     to check that the reference's rules preserve ada and tokens, that  *)
(*     a phase-2-invalid transaction consumes only its collateral, and    *)
(*     that reference inputs are read and never spent.                    *)
(*                                                                         *)
(* A Plutus script is not evaluated: whether a transaction's scripts pass  *)
(* is a field of the transaction (pass), so TLC tries both answers.        *)
(* Certificates are reduced to one stake credential's registration,      *)
(* deregistration and withdrawal (their rules are model `ledger-shelley`'s).            *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd; full table in *)
(* specs/ledger-utxo/README.md.                                         *)
(*   [S1] eras/shelley/formal-spec/utxo.tex: consumed, produced, UTXO.    *)
(*   [S2] eras/shelley-ma/formal-spec/utxo.tex: validity interval, mint,  *)
(*        value size.                                                      *)
(*   [S3] eras/alonzo/formal-spec/utxo.tex: feesOK, collateral, UTXOS.    *)
(*   [S4] eras/babbage/formal-spec/utxo.tex: reference inputs, collateral *)
(*        return, total collateral.                                        *)
(*   Reference implementation (eras/<era>/impl/src/Cardano/Ledger/):       *)
(*   [R1] Shelley/Rules/Utxo.hs 364-419 utxoInductive; 421-427 TTL        *)
(*        (ttl >= slot); 511-519 value conservation.                       *)
(*   [R2] Allegra/Rules/Utxo.hs 175-243 utxoTransition (also Mary's,     *)
(*        Mary/Rules/Utxo.hs 1-22); 249-256 inInterval; 280-293            *)
(*        OutputTooSmall with Val.pointwise (<).                          *)
(*   [R3] Mary/TxOut.hs 33 getMinCoinTxOut = scaledMinDeposit;            *)
(*        Mary/Value.hs 234-235 pointwise on coin and every asset.        *)
(*   [R4] Alonzo/Rules/Utxo.hs 291-366 collateral (only with redeemers); *)
(*        392-411 OutputTooSmall (pointwise >=); 507-576 utxoTransition,  *)
(*        538-540 BadInputs over inputs and collateral.                   *)
(*   [R5] Alonzo/Rules/Utxos.hs 147-166, 223-247: IsValid must match the *)
(*        scripts' result (ValidationTagMismatch).                        *)
(*   [R6] Babbage/Rules/Utxo.hs 183-201, 220-305 collateral with return; *)
(*        204-218 disjoint reference inputs only for 8 < pv < 11;          *)
(*        329-419 babbageUtxoValidation (BadInputs over inputs,           *)
(*        collateral and reference inputs; outputs include the return);   *)
(*        456-490 an invalid tx removes its collateral, adds the return   *)
(*        and moves collAdaBalance to fees.                                *)
(*   [R7] Babbage/Collateral.hs 30-41 collAdaBalance.                      *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit d0b95845):              *)
(*   [G1] ledger/shelley/rules.go 146-160 TTL, 163-173 inputs, 245-268   *)
(*        fee, 270-290 BadInputs (spent inputs only), 341-451 value       *)
(*        conservation, 462-488 OutputTooSmall.                            *)
(*   [G9] branch fix/ledger-bad-inputs-reference-set: BadInputs checks    *)
(*        the reference's set, spent inputs plus collateral (Alonzo on)   *)
(*        plus reference inputs (Babbage on), in each era's rules.go.     *)
(*   [G2] ledger/allegra/rules.go 145-168 validity interval.               *)
(*   [G3] ledger/mary/rules.go 154-180 OutputTooBig, 271-491 value with  *)
(*        tokens, 493-540 OutputTooSmall (exempt with a positive asset).  *)
(*   [G4] ledger/alonzo/rules.go 348-366 TooManyCollateralInputs, 444-467 *)
(*        IsValid flag, 605-738 collateral, 963-990 OutputTooSmall.        *)
(*   [G5] ledger/babbage/rules.go 537-722 collateral with return,          *)
(*        947-1007 outputs and the return, 1264-1301 disjoint reference   *)
(*        inputs (pv > 8 only).                                            *)
(*   [G6] ledger/common/witness.go 180-212 collateral key-locked;         *)
(*        ledger/common/rules.go 1228-1243 ValidatePlutusScriptResult.     *)
(*   [G7] Resolution of collateral and reference inputs outside BadInputs:*)
(*        ValidateCollateralVKeyWitnesses (ledger/common/witness.go       *)
(*        99-178) resolves every collateral input of every transaction,  *)
(*        and the script-witness rules resolve every reference input.     *)
(*   [G8] ledger/alonzo/alonzo.go 1167-1194, ledger/babbage/babbage.go    *)
(*        1540-1577 Consumed/Produced; ledger/common/block_state.go       *)
(*        185-200 ApplyTransaction.                                        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and      *)
(* specs/ledger-shelley/CertLifecycle.tla.                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    Era,          \* "Shelley", "Allegra", "Mary", "Alonzo" or "Babbage"
    MinFee,       \* the minimum fee (minfee with a = 0: a constant)
    MinUtxo,      \* the minimum coin of an output, in model units
    KeyDeposit,   \* ppKeyDeposit
    CollPct,      \* ppCollateralPercentage
    MaxColl,      \* ppMaxCollateralInputs
    StartUtxo,    \* the ledger's starting UTxO (Spec only)
    MaxTxs,       \* how many transactions the ledger applies (Spec only)
    Mutation      \* "none", or one deliberate mistake (see the README)

\* The three places an output can be. "c" starts empty in every state, so a
\* transaction naming it names an input that does not exist.
\* Literally: "Ids is defined as the set containing "a", "b" and "c"."
Ids == {"a", "b", "c"}
\* "No output here" and "no collateral return". They are records, like the
\* outputs they stand in for, because TLC cannot compare a record with a
\* string; a negative amount marks them.
\* Literally: "None is defined as the record whose field coin is negative 1,
\*   field tok is negative 1, and field lock is "none"."
None  == [coin |-> -1, tok |-> -1, lock |-> "none"]
\* Literally: "NoRet is defined as the record whose field coin is negative 1 and
\*   field tok is 0."
NoRet == [coin |-> -1, tok |-> 0]
\* Literally: "Back is defined as the record whose field coin is negative 2 and
\*   field tok is 0."
Back  == [coin |-> -2, tok |-> 0]   \* LedgerTxs: "return one coin and the tokens"

\* Era order, so "from Alonzo on" can be written AtLeast("Alonzo").
\* Literally: "EraIdx of e is defined as: in the case e equals "Shelley", 1; in
\*   the case e equals "Allegra", 2; in the case e equals "Mary", 3; in the case
\*   e equals "Alonzo", 4; in the case e equals "Babbage", 5."
EraIdx(e) == CASE e = "Shelley" -> 1 [] e = "Allegra" -> 2 [] e = "Mary" -> 3
                [] e = "Alonzo" -> 4 [] e = "Babbage" -> 5
\* Literally: "AtLeast of e is defined as: EraIdx of Era is greater than or
\*   equal to EraIdx of e."
AtLeast(e) == EraIdx(Era) >= EraIdx(e)

\* An output is a record [coin, tok, lock]: coins, a quantity of one token,
\* and what locks it, a payment "key" or a "script".

VARIABLES
    utxo,        \* utxo[i]: the output at place i, or None
    slot,        \* the current slot
    registered,  \* is the one stake credential registered?
    reward,      \* its reward balance
    fees,        \* the fee pot (Spec)
    deposits,    \* the deposit pot (Spec)
    minted,      \* tokens minted minus tokens burned so far (Spec)
    ntx,         \* transactions applied so far (Spec)
    kept,        \* outputs the last transaction had to leave alone (Spec)
    seen         \* events that have happened, for the probes (Spec)

\* Literally: "vars is defined as the tuple of utxo, slot, registered, reward,
\*   fees, deposits, minted, ntx, kept and seen."
vars == <<utxo, slot, registered, reward, fees, deposits, minted, ntx, kept, seen>>

-----------------------------------------------------------------------------
(* Sums over the UTxO.                                                     *)

\* Literally: "Live is defined as the set of every i in Ids such that utxo of i
\*   does not equal None."
Live == {i \in Ids : utxo[i] # None}     \* the places holding an output

\* In English: the coins (or tokens) held at the places in S that exist.
\* A place without an output adds nothing, as balance (txins tx <| utxo)
\* does in the reference [S1].
RECURSIVE CoinOf(_), TokOf(_)
\* Literally: "CoinOf of S is defined as: if the intersection of S and Live
\*   equals the empty set then 0, else, letting i be the x, chosen from the
\*   intersection of S and Live, such that TRUE: utxo of i's coin plus CoinOf of
\*   ((the intersection of S and Live) without the members of the set containing
\*   i)."
CoinOf(S) == IF S \cap Live = {} THEN 0
             ELSE LET i == CHOOSE x \in S \cap Live : TRUE
                  IN utxo[i].coin + CoinOf((S \cap Live) \ {i})
\* Literally: "TokOf of S is defined as: if the intersection of S and Live
\*   equals the empty set then 0, else, letting i be the x, chosen from the
\*   intersection of S and Live, such that TRUE: utxo of i's tok plus TokOf of
\*   ((the intersection of S and Live) without the members of the set containing
\*   i)."
TokOf(S)  == IF S \cap Live = {} THEN 0
             ELSE LET i == CHOOSE x \in S \cap Live : TRUE
                  IN utxo[i].tok + TokOf((S \cap Live) \ {i})

-----------------------------------------------------------------------------
(* Transactions.                                                           *)

\* A transaction is a record:
\*   ins, coll, refs  spent inputs, collateral inputs, reference inputs
\*   delta, tdelta    how far the output's coins and tokens are from what
\*                    balances the transaction (0 = balanced)
\*   fee, mint        the fee; tokens minted (+) or burned (-)
\*   cert, wdrl       "none", "reg" or "dereg" of the credential; whether
\*                    the transaction withdraws the whole reward balance
\*   olock, big       what locks the output; whether its value is larger
\*                    than the maximum value size
\*   lo, hi           validity interval bounds, 0 = absent (Shelley: hi is
\*                    the mandatory TTL)
\*   rdmrs, valid, pass  carries redeemers; IsValid; do its scripts pass
\*   ret, tcoll       collateral return ([coin, tok] or NoRet); total
\*                    collateral (-1 = absent)

\* In English: the refund and deposit a certificate moves [S1]. A
\* deregistration refunds the deposit only if the credential is registered
\* (an invalid transaction may carry one that is not; its certificates are
\* never checked).
\* Literally: "Refund of tx is defined as: if tx's cert equals "dereg" and
\*   registered then KeyDeposit, else 0."
Refund(tx)  == IF tx.cert = "dereg" /\ registered THEN KeyDeposit ELSE 0
\* Literally: "Deposit of tx is defined as: if tx's cert equals "reg" then
\*   KeyDeposit, else 0."
Deposit(tx) == IF tx.cert = "reg" THEN KeyDeposit ELSE 0
\* Literally: "Wdrl of tx is defined as: if tx's wdrl then reward, else 0."
Wdrl(tx)    == IF tx.wdrl THEN reward ELSE 0

\* In English: consumed = inputs + withdrawals + refunds [S1][R1]. Only
\* spent inputs count: not collateral, not reference inputs.
\* Literally: "Consumed of tx is defined as CoinOf of tx's ins plus Wdrl of tx
\*   plus Refund of tx."
Consumed(tx) == CoinOf(tx.ins) + Wdrl(tx) + Refund(tx)

\* In English: the output's coins and tokens. delta = 0 makes produced =
\* outputs + fee + deposits equal consumed; tdelta = 0 makes the output carry
\* exactly the spent tokens plus the minted ones [S2].
\* Literally: "OutCoin of tx is defined as Consumed of tx minus tx's fee minus
\*   Deposit of tx plus tx's delta."
OutCoin(tx) == Consumed(tx) - tx.fee - Deposit(tx) + tx.delta
\* Literally: "OutTok of tx is defined as TokOf of tx's ins plus tx's mint plus
\*   tx's tdelta."
OutTok(tx)  == TokOf(tx.ins) + tx.mint + tx.tdelta

\* In English: the coins of the collateral return, or 0 when there is none.
\* Literally: "RetCoin of tx is defined as: if tx's ret equals NoRet then 0,
\*   else tx's ret's coin."
RetCoin(tx) == IF tx.ret = NoRet THEN 0 ELSE tx.ret.coin
\* In English: the tokens of the collateral return, or 0 when there is none.
\* Literally: "RetTok of tx is defined as: if tx's ret equals NoRet then 0, else
\*   tx's ret's tok."
RetTok(tx)  == IF tx.ret = NoRet THEN 0 ELSE tx.ret.tok

\* In English: the collateral's ada balance: collateral coins less the
\* return's coins (collAdaBalance [R7]; no return before Babbage).
\* Literally: "CollBal of tx is defined as CoinOf of tx's coll minus RetCoin of
\*   tx."
CollBal(tx) == CoinOf(tx.coll) - RetCoin(tx)

\* In English: with no redeemers there is no script to run, so "the
\* scripts pass" holds; with redeemers it is the transaction's pass field.
\* Literally: "ScriptsPass of tx is defined as: tx's rdmrs is not true, or tx's
\*   pass."
ScriptsPass(tx) == ~tx.rdmrs \/ tx.pass

\* In English: the transaction can be written down: its output holds no
\* negative amount.
\* Literally: "Expressible of tx is defined as: OutCoin of tx is greater than or
\*   equal to 0, and OutTok of tx is greater than or equal to 0."
Expressible(tx) == OutCoin(tx) >= 0 /\ OutTok(tx) >= 0

-----------------------------------------------------------------------------
(* The reference: which transactions the ledger accepts.                   *)

\* In English: the slot is inside the transaction's validity window.
\* Shelley: ttl >= slot, inclusive [R1] 421-427. Allegra on: invalidBefore
\* <= slot < invalidHereafter, the upper bound exclusive [R2] 249-256.
\* Literally: "SpecInterval of tx is defined as: if Era equals "Shelley" then
\*   tx's hi is greater than or equal to slot, else (tx's lo equals 0 or tx's lo
\*   is less than or equal to slot) and (tx's hi equals 0 or slot is less than
\*   tx's hi)."
SpecInterval(tx) ==
    IF Era = "Shelley" THEN tx.hi >= slot
    ELSE /\ (tx.lo = 0 \/ tx.lo <= slot)
         /\ (tx.hi = 0 \/ slot < tx.hi)

\* In English: every input the rule reads must exist. Shelley to Mary: the
\* spent inputs [R1]. Alonzo: and the collateral [R4] 538-540. Babbage: and
\* the reference inputs [R6] 384-386.
\* Literally: "SpecReadInputs of tx is defined as the union of tx's ins, (if
\*   AtLeast of "Alonzo" then tx's coll, else the empty set), and (if AtLeast of
\*   "Babbage" then tx's refs, else the empty set)."
SpecReadInputs(tx) ==
    tx.ins \cup (IF AtLeast("Alonzo") THEN tx.coll ELSE {})
           \cup (IF AtLeast("Babbage") THEN tx.refs ELSE {})

\* In English: the minimum-output rule [R1][R2][R3][R4][R6].
\*   Shelley, Allegra: coins >= minUTxOValue.
\*   Mary: Val.pointwise (<) v (inject min) flags an output only if its coins
\*     are below the minimum AND every asset in it is below zero; an output
\*     holding any token is never too small [R3].
\*   Alonzo, Babbage: not (pointwise (>=) ...): coins below the minimum is
\*     enough. Babbage checks the collateral return as well.
\* Literally: "SpecOutputOk of tx is defined as: (in the case Era is a member of
\*   the set containing "Shelley" and "Allegra", OutCoin of tx is greater than
\*   or equal to MinUtxo; in the case Era equals "Mary", (OutCoin of tx is less
\*   than MinUtxo and OutTok of tx equals 0) is not true; in every other case,
\*   OutCoin of tx is greater than or equal to MinUtxo), and if Era equals
\*   "Babbage" and tx's ret does not equal NoRet, then tx's ret's coin is
\*   greater than or equal to MinUtxo, and if AtLeast of "Mary", then tx's big
\*   is not true."
SpecOutputOk(tx) ==
    /\ CASE Era \in {"Shelley", "Allegra"} -> OutCoin(tx) >= MinUtxo
         [] Era = "Mary" -> ~(OutCoin(tx) < MinUtxo /\ OutTok(tx) = 0)
         [] OTHER -> OutCoin(tx) >= MinUtxo
    /\ (Era = "Babbage" /\ tx.ret # NoRet) => tx.ret.coin >= MinUtxo
    /\ AtLeast("Mary") => ~tx.big                      \* maxValSize [R2][R4]

\* In English: feesOK's collateral half, only when there are redeemers
\* [R4] 291-326, [R6] 183-201, 220-245:
\*   every collateral output is locked by a key (ScriptsNotPaidUTxO);
\*   balance * 100 >= fee * collateralPercentage (InsufficientCollateral);
\*   Alonzo: no collateral output holds a token; Babbage: either nothing
\*     holds a token or the return takes back every token (NonADA);
\*   Babbage: a stated total collateral equals the balance;
\*   at least one collateral output exists (NoCollateralInputs).
\* Literally: "SpecCollateral of tx is defined as: if AtLeast of "Alonzo" and
\*   tx's rdmrs, then: for all i in the intersection of tx's coll and Live, utxo
\*   of i's lock equals "key"; and CollBal of tx times 100 is greater than or
\*   equal to tx's fee times CollPct; and if Era equals "Alonzo" then TokOf of
\*   tx's coll equals 0, else (TokOf of tx's coll equals 0 and RetTok of tx
\*   equals 0) or TokOf of tx's coll minus RetTok of tx equals 0; and if Era
\*   equals "Babbage" and tx's tcoll does not equal negative 1, then tx's tcoll
\*   equals CollBal of tx; and the intersection of tx's coll and Live does not
\*   equal the empty set."
SpecCollateral(tx) ==
    (AtLeast("Alonzo") /\ tx.rdmrs) =>
        /\ \A i \in tx.coll \cap Live : utxo[i].lock = "key"
        /\ CollBal(tx) * 100 >= tx.fee * CollPct
        /\ IF Era = "Alonzo" THEN TokOf(tx.coll) = 0
           ELSE \/ (TokOf(tx.coll) = 0 /\ RetTok(tx) = 0)
                \/ TokOf(tx.coll) - RetTok(tx) = 0
        /\ (Era = "Babbage" /\ tx.tcoll # -1) => tx.tcoll = CollBal(tx)
        /\ tx.coll \cap Live # {}

\* In English: the certificate and withdrawal are allowed (DELEG and
\* DELEGS; model `ledger-shelley`). Only a phase-2-valid transaction runs them: the
\* LEDGER rule skips DELEGS for an invalid one.
\* Literally: "SpecCerts of tx is defined as: if tx's valid, then (if tx's wdrl,
\*   then registered), and (if tx's cert equals "reg", then registered is not
\*   true), and (if tx's cert equals "dereg", then registered and reward minus
\*   Wdrl of tx equals 0)."
SpecCerts(tx) ==
    tx.valid =>
        /\ tx.wdrl => registered
        /\ tx.cert = "reg" => ~registered
        /\ tx.cert = "dereg" => registered /\ reward - Wdrl(tx) = 0

\* In English: the reference accepts the transaction.
\* Literally: "SpecAccepts of tx is defined as: SpecInterval of tx, and tx's ins
\*   does not equal the empty set, and tx's fee is greater than or equal to
\*   MinFee, and SpecReadInputs of tx is a subset of Live, and Consumed of tx
\*   plus (if Mutation equals "SpecNoRefund" then minus Refund of tx, else 0)
\*   equals OutCoin of tx plus tx's fee plus Deposit of tx, and if AtLeast of
\*   "Mary", then TokOf of tx's ins plus (if Mutation equals "SpecMintIgnored"
\*   then 0, else tx's mint) equals OutTok of tx, and SpecOutputOk of tx, and
\*   SpecCollateral of tx, and if AtLeast of "Alonzo", then the number of
\*   members of tx's coll is less than or equal to MaxColl, and if AtLeast of
\*   "Alonzo", then (tx's valid if and only if ScriptsPass of tx), and SpecCerts
\*   of tx."
SpecAccepts(tx) ==
    /\ SpecInterval(tx)                                   \* [R1][R2]
    /\ tx.ins # {}                                        \* InputSetEmptyUTxO
    /\ tx.fee >= MinFee                                   \* FeeTooSmallUTxO
    /\ SpecReadInputs(tx) \subseteq Live                  \* BadInputsUTxO
    /\ Consumed(tx) + (IF Mutation = "SpecNoRefund" THEN -Refund(tx) ELSE 0)
         = OutCoin(tx) + tx.fee + Deposit(tx)            \* ValueNotConserved: coins
    /\ AtLeast("Mary") =>                                 \* ... and tokens
         TokOf(tx.ins) + (IF Mutation = "SpecMintIgnored" THEN 0 ELSE tx.mint)
           = OutTok(tx)
    /\ SpecOutputOk(tx)                                   \* OutputTooSmall/TooBig
    /\ SpecCollateral(tx)                                 \* feesOK collateral
    /\ AtLeast("Alonzo") => Cardinality(tx.coll) <= MaxColl  \* TooManyCollateralInputs
    /\ AtLeast("Alonzo") =>                               \* UTXOS: IsValid matches
         (tx.valid <=> ScriptsPass(tx))                   \*  the scripts [R5]
    /\ SpecCerts(tx)
    \* Babbage reference inputs may overlap spent inputs: the disjointness
    \* rule applies only for 8 < pv < 11 [R6] 204-218, after Babbage.

-----------------------------------------------------------------------------
(* gOuroboros: the same transactions through its Babbage-and-earlier rule *)
(* lists.                                                                  *)

\* In English: Shelley UtxoValidateTimeToLive is ttl >= slot [G1]; from
\* Allegra the lower bound is checked when non-zero and the upper bound is
\* exclusive [G2].
\* Literally: "GoInterval of tx is defined as: if Era equals "Shelley" then (if
\*   Mutation equals "GoTtlExclusive" then tx's hi is greater than slot, else
\*   tx's hi is greater than or equal to slot), else (tx's lo does not equal 0
\*   and slot is less than tx's lo) is not true, and (tx's hi does not equal 0
\*   and (if Mutation equals "GoIntervalInclusive" then slot is greater than
\*   tx's hi, else slot is greater than or equal to tx's hi)) is not true."
GoInterval(tx) ==
    IF Era = "Shelley"
    THEN IF Mutation = "GoTtlExclusive" THEN tx.hi > slot ELSE tx.hi >= slot
    ELSE /\ ~(tx.lo # 0 /\ slot < tx.lo)
         /\ ~(tx.hi # 0 /\ (IF Mutation = "GoIntervalInclusive"
                            THEN slot > tx.hi ELSE slot >= tx.hi))

\* Mutations that put back the old BadInputs (spent inputs only) [G1], and
\* mutations that drop a witness rule's lookup [G7]. The "GoSpentOnly..."
\* ones do both, which is what the code did before [G9].
\* Literally: "GoSpentOnly is defined as: Mutation is a member of the set
\*   containing "GoBadInputsSpentOnly", "GoSpentOnlyCollUnresolved" and
\*   "GoSpentOnlyRefsUnresolved"."
GoSpentOnly   == Mutation \in {"GoBadInputsSpentOnly",
                               "GoSpentOnlyCollUnresolved",
                               "GoSpentOnlyRefsUnresolved"}
\* Literally: "GoNoCollLookup is defined as: Mutation is a member of the set
\*   containing "GoCollUnresolved" and "GoSpentOnlyCollUnresolved"."
GoNoCollLookup == Mutation \in {"GoCollUnresolved", "GoSpentOnlyCollUnresolved"}
\* Literally: "GoNoRefLookup is defined as: Mutation is a member of the set
\*   containing "GoRefsUnresolved" and "GoSpentOnlyRefsUnresolved"."
GoNoRefLookup  == Mutation \in {"GoRefsUnresolved", "GoSpentOnlyRefsUnresolved"}

\* In English: the inputs gOuroboros' BadInputs rule requires to exist.
\* Fixed [G9]: the reference's set, SpecReadInputs. Old [G1]: spent inputs
\* only, in every era.
\* Literally: "GoBadInputs of tx is defined as: if GoSpentOnly then tx's ins,
\*   else SpecReadInputs of tx."
GoBadInputs(tx) == IF GoSpentOnly THEN tx.ins ELSE SpecReadInputs(tx)

\* In English: the inputs the witness rules look up on their own [G7]: the
\* collateral-vkey-witnesses rule resolves every collateral input, and the
\* script-witness rules every reference input; either fails when the input
\* is absent. The rule checking collateral (GoCollateral) also needs the
\* collateral to exist, but only when there are redeemers.
\* Literally: "GoLookedUp of tx is defined as the union of (if AtLeast of
\*   "Alonzo" and GoNoCollLookup is not true then tx's coll, else the empty set)
\*   and (if AtLeast of "Babbage" and GoNoRefLookup is not true then tx's refs,
\*   else the empty set)."
GoLookedUp(tx) ==
    (IF AtLeast("Alonzo") /\ ~GoNoCollLookup THEN tx.coll ELSE {})
    \cup (IF AtLeast("Babbage") /\ ~GoNoRefLookup THEN tx.refs ELSE {})

\* In English: every input gOuroboros requires to exist, by any rule.
\* Literally: "GoReadInputs of tx is defined as the union of GoBadInputs of tx
\*   and GoLookedUp of tx."
GoReadInputs(tx) == GoBadInputs(tx) \cup GoLookedUp(tx)

\* In English: outputTooSmall as gOuroboros computes it. Mary skips an
\* output that holds a positive token quantity (outputHasPositiveAsset)
\* [G3]; Alonzo compares coins [G4]; Babbage includes the collateral
\* return (TransactionOutputsAndCollateralReturn) [G5].
\* Literally: "GoOutputOk of tx is defined as: (in the case Era is a member of
\*   the set containing "Shelley" and "Allegra", OutCoin of tx is greater than
\*   or equal to MinUtxo; in the case Era equals "Mary", if Mutation equals
\*   "GoMaryCoinMin" then OutCoin of tx is greater than or equal to MinUtxo,
\*   else OutTok of tx is greater than 0 or OutCoin of tx is greater than or
\*   equal to MinUtxo; in every other case, OutCoin of tx is greater than or
\*   equal to MinUtxo), and if Era equals "Babbage" and tx's ret does not equal
\*   NoRet, then tx's ret's coin is greater than or equal to MinUtxo, and if
\*   AtLeast of "Mary", then tx's big is not true."
GoOutputOk(tx) ==
    /\ CASE Era \in {"Shelley", "Allegra"} -> OutCoin(tx) >= MinUtxo
         [] Era = "Mary" -> IF Mutation = "GoMaryCoinMin"
                            THEN OutCoin(tx) >= MinUtxo
                            ELSE OutTok(tx) > 0 \/ OutCoin(tx) >= MinUtxo
         [] OTHER -> OutCoin(tx) >= MinUtxo
    /\ (Era = "Babbage" /\ tx.ret # NoRet) => tx.ret.coin >= MinUtxo
    /\ AtLeast("Mary") => ~tx.big

\* In English: the collateral rules, run only when the transaction has
\* redeemers [G4][G5][G6]. Babbage subtracts the return's coins before
\* comparing with the fee, requires the return to hold exactly the
\* collateral's tokens (MultiAsset Compare), and rejects a stated total
\* when the return holds more coins than the collateral or the total
\* differs from the balance.
\* Literally: "GoCollateral of tx is defined as: if AtLeast of "Alonzo" and tx's
\*   rdmrs, then: tx's coll does not equal the empty set; and for all i in tx's
\*   coll, i is a member of Live and utxo of i's lock equals "key"; and (if Era
\*   equals "Babbage" and Mutation does not equal "GoCollIgnoresReturn" then
\*   CollBal of tx, else CoinOf of tx's coll) times 100 is greater than or equal
\*   to tx's fee times CollPct; and if Era equals "Alonzo" then TokOf of tx's
\*   coll equals 0, else TokOf of tx's coll equals RetTok of tx; and if Era
\*   equals "Babbage" and tx's tcoll does not equal negative 1, then RetCoin of
\*   tx is less than or equal to CoinOf of tx's coll and tx's tcoll equals
\*   CollBal of tx."
GoCollateral(tx) ==
    (AtLeast("Alonzo") /\ tx.rdmrs) =>
        /\ tx.coll # {}                                        \* NoCollateralInputs
        /\ \A i \in tx.coll : i \in Live /\ utxo[i].lock = "key"   \* key-locked
        /\ (IF Era = "Babbage" /\ Mutation # "GoCollIgnoresReturn"
            THEN CollBal(tx) ELSE CoinOf(tx.coll)) * 100
             >= tx.fee * CollPct                               \* InsufficientCollateral
        /\ IF Era = "Alonzo" THEN TokOf(tx.coll) = 0           \* ContainsNonAda
           ELSE TokOf(tx.coll) = RetTok(tx)
        /\ (Era = "Babbage" /\ tx.tcoll # -1) =>               \* CollateralEqBalance
             /\ RetCoin(tx) <= CoinOf(tx.coll)
             /\ tx.tcoll = CollBal(tx)

\* In English: gOuroboros accepts the transaction.
\* Literally: "GoAccepts of tx is defined as: GoInterval of tx, and tx's ins
\*   does not equal the empty set, and tx's fee is greater than or equal to
\*   MinFee, and GoReadInputs of tx is a subset of Live, and Consumed of tx
\*   equals OutCoin of tx plus tx's fee plus Deposit of tx, and if AtLeast of
\*   "Mary", then TokOf of tx's ins plus tx's mint equals OutTok of tx, and
\*   GoOutputOk of tx, and GoCollateral of tx, and if AtLeast of "Alonzo", then
\*   the number of members of tx's coll is less than or equal to MaxColl, and if
\*   AtLeast of "Alonzo", then (if tx's valid is not true, then tx's rdmrs), and
\*   if AtLeast of "Alonzo", then (if tx's valid then ScriptsPass of tx, else
\*   ScriptsPass of tx is not true), and if Mutation equals "GoDisjointAlways"
\*   and Era equals "Babbage", then the intersection of tx's refs and tx's ins
\*   equals the empty set, and SpecCerts of tx."
GoAccepts(tx) ==
    /\ GoInterval(tx)
    /\ tx.ins # {}                                       \* InputSetEmptyUtxo
    /\ tx.fee >= MinFee                                  \* FeeTooSmallUtxo
    /\ GoReadInputs(tx) \subseteq Live                   \* BadInputs [G9], and [G7]
    /\ Consumed(tx) = OutCoin(tx) + tx.fee + Deposit(tx) \* ValueNotConserved [G1]
    /\ AtLeast("Mary") => TokOf(tx.ins) + tx.mint = OutTok(tx)  \* [G3]
    /\ GoOutputOk(tx)
    /\ GoCollateral(tx)
    /\ AtLeast("Alonzo") => Cardinality(tx.coll) <= MaxColl     \* [G4]
    /\ AtLeast("Alonzo") => (~tx.valid => tx.rdmrs)              \* IsValid flag [G4]
    /\ AtLeast("Alonzo") =>                                      \* ValidatePlutusScriptResult [G6]
         IF tx.valid THEN ScriptsPass(tx) ELSE ~ScriptsPass(tx)
    /\ (Mutation = "GoDisjointAlways" /\ Era = "Babbage") => tx.refs \cap tx.ins = {}
    /\ SpecCerts(tx)          \* DELEG and withdrawals: model `ledger-shelley`; skipped when invalid

-----------------------------------------------------------------------------
(* The families of transactions GoAgrees checks. Each varies some fields of *)
(* a base transaction that is accepted in a typical state.                 *)

\* In English: "The base transaction: spends "a", balanced, fee 1, nothing
\* else."
\* Literally: "Base is defined as the record whose field ins is the set
\*   containing "a", field coll is the empty set, field refs is the empty set,
\*   field delta is 0, field tdelta is 0, field fee is 1, field mint is 0, field
\*   cert is "none", field wdrl is FALSE, field olock is "key", field big is
\*   FALSE, field lo is 0, field hi is (if Era equals "Shelley" then 3, else 0),
\*   field rdmrs is FALSE, field valid is TRUE, field pass is TRUE, field ret is
\*   NoRet, and field tcoll is negative 1."
Base ==
    [ins |-> {"a"}, coll |-> {}, refs |-> {}, delta |-> 0, tdelta |-> 0,
     fee |-> 1, mint |-> 0, cert |-> "none", wdrl |-> FALSE,
     olock |-> "key", big |-> FALSE,
     lo |-> 0, hi |-> IF Era = "Shelley" THEN 3 ELSE 0,
     rdmrs |-> FALSE, valid |-> TRUE, pass |-> TRUE,
     ret |-> NoRet, tcoll |-> -1]

\* What each era can express: no collateral before Alonzo, no reference
\* inputs, return or total collateral before Babbage, no tokens before Mary.
\* Literally: "CollSets is defined as: if AtLeast of "Alonzo" then the set of
\*   subsets of Ids, else the set containing the empty set."
CollSets  == IF AtLeast("Alonzo") THEN SUBSET Ids ELSE {{}}
\* Literally: "RefSets is defined as: if AtLeast of "Babbage" then the set of
\*   subsets of Ids, else the set containing the empty set."
RefSets   == IF AtLeast("Babbage") THEN SUBSET Ids ELSE {{}}
\* Literally: "Bools2 is defined as: if AtLeast of "Alonzo" then BOOLEAN, else
\*   the set containing FALSE."
Bools2    == IF AtLeast("Alonzo") THEN BOOLEAN ELSE {FALSE}
\* Literally: "ValidSet is defined as: if AtLeast of "Alonzo" then BOOLEAN, else
\*   the set containing TRUE."
ValidSet  == IF AtLeast("Alonzo") THEN BOOLEAN ELSE {TRUE}
\* Literally: "Mints is defined as: if AtLeast of "Mary" then negative 1 through
\*   1, else the set containing 0."
Mints     == IF AtLeast("Mary") THEN -1..1 ELSE {0}
\* Literally: "Bigs is defined as: if AtLeast of "Mary" then BOOLEAN, else the
\*   set containing FALSE."
Bigs      == IF AtLeast("Mary") THEN BOOLEAN ELSE {FALSE}
\* Literally: "Rets is defined as: if Era equals "Babbage" then the union of the
\*   set containing NoRet and the set of records whose field coin is a member of
\*   0 through 2 and whose field tok is a member of 0 through 1, else the set
\*   containing NoRet."
Rets      == IF Era = "Babbage" THEN {NoRet} \cup [coin : 0..2, tok : 0..1]
             ELSE {NoRet}
\* Literally: "TColls is defined as: if Era equals "Babbage" then the set
\*   containing negative 1, 1, 2 and 3, else the set containing negative 1."
TColls    == IF Era = "Babbage" THEN {-1, 1, 2, 3} ELSE {-1}
\* Literally: "Los is defined as: if Era equals "Shelley" then the set
\*   containing 0, else 0 through 2."
Los       == IF Era = "Shelley" THEN {0} ELSE 0..2
\* Literally: "His is defined as: if Era equals "Shelley" then 1 through 3, else
\*   0 through 3."
His       == IF Era = "Shelley" THEN 1..3 ELSE 0..3

\* 1. Which inputs exist, and redeemers (which bring the collateral rules).
\* Literally: "FamInputs is defined as the set of Base except that its ins is i,
\*   its coll is c, its refs is r and its rdmrs is d, for every i that is a
\*   member of the set of subsets of Ids, every c that is a member of CollSets,
\*   every r that is a member of RefSets, and every d that is a member of
\*   Bools2."
FamInputs ==
    {[Base EXCEPT !.ins = i, !.coll = c, !.refs = r, !.rdmrs = d] :
        i \in SUBSET Ids, c \in CollSets, r \in RefSets, d \in Bools2}
\* 2. Balance: output coins and tokens, fee, mint, certificate, withdrawal.
\* Literally: "FamBalance is defined as the set of Base except that its delta is
\*   d, its tdelta is t, its fee is f, its mint is m, its cert is c and its wdrl
\*   is w, for every d that is a member of negative 1 through 1, every t that is
\*   a member of (if AtLeast of "Mary" then negative 1 through 1, else the set
\*   containing 0), every f that is a member of 0 through 2, every m that is a
\*   member of Mints, every c that is a member of the set containing "none",
\*   "reg" and "dereg", and every w that is a member of BOOLEAN."
FamBalance ==
    {[Base EXCEPT !.delta = d, !.tdelta = t, !.fee = f, !.mint = m,
                  !.cert = c, !.wdrl = w] :
        d \in -1..1, t \in (IF AtLeast("Mary") THEN -1..1 ELSE {0}),
        f \in 0..2, m \in Mints, c \in {"none", "reg", "dereg"}, w \in BOOLEAN}
\* 3. Outputs: small (by spending less or burning), and too big.
\* Literally: "FamOutputs is defined as the set of Base except that its ins is
\*   i, its fee is f, its mint is m and its big is b, for every i that is a
\*   member of the set containing (the set containing "a") and (the set
\*   containing "a" and "b"), every f that is a member of 1 through 3, every m
\*   that is a member of Mints, and every b that is a member of Bigs."
FamOutputs ==
    {[Base EXCEPT !.ins = i, !.fee = f, !.mint = m, !.big = b] :
        i \in {{"a"}, {"a", "b"}}, f \in 1..3, m \in Mints, b \in Bigs}
\* 4. The validity interval.
\* Literally: "FamInterval is defined as the set of Base except that its lo is l
\*   and its hi is h, for every l that is a member of Los and every h that is a
\*   member of His."
FamInterval ==
    {[Base EXCEPT !.lo = l, !.hi = h] : l \in Los, h \in His}
\* 5. Collateral and phase 2.
\* Literally: "FamPhase2 is defined as the set of Base except that its rdmrs is
\*   d, its valid is v, its pass is p, its coll is c, its ret is r, its tcoll is
\*   t and its fee is f, for every d that is a member of Bools2, every v that is
\*   a member of ValidSet, every p that is a member of Bools2, every c that is a
\*   member of CollSets, every r that is a member of Rets, every t that is a
\*   member of TColls, and every f that is a member of 1 through 2."
FamPhase2 ==
    {[Base EXCEPT !.rdmrs = d, !.valid = v, !.pass = p, !.coll = c,
                  !.ret = r, !.tcoll = t, !.fee = f] :
        d \in Bools2, v \in ValidSet, p \in Bools2, c \in CollSets,
        r \in Rets, t \in TColls, f \in 1..2}

\* In English: "Every transaction of the five families that can be written
\* down."
\* Literally: "Checked is defined as the set of every tx in the union of
\*   FamInputs, FamBalance, FamOutputs, FamInterval and FamPhase2 such that
\*   Expressible of tx."
Checked == {tx \in FamInputs \cup FamBalance \cup FamOutputs \cup FamInterval
                   \cup FamPhase2 : Expressible(tx)}

\* In English: gOuroboros accepts exactly what the reference accepts.
\* Literally: "GoAgrees is defined as: for all tx in Checked, GoAccepts of tx
\*   equals SpecAccepts of tx."
GoAgrees == \A tx \in Checked : GoAccepts(tx) = SpecAccepts(tx)

\* In English: BadInputs by itself rejects a transaction whose spent,
\* collateral or reference input is missing, exactly when the reference's
\* BadInputsUTxO does, whatever the witness rules look up. So a missing
\* collateral or reference input is reported as BadInputs, as the
\* reference reports it, and stays rejected if a witness rule stops
\* looking it up.
\* Literally: "GoBadInputsComplete is defined as: for all tx in Checked,
\*   (GoBadInputs of tx is a subset of Live) equals (SpecReadInputs of tx is a
\*   subset of Live)."
GoBadInputsComplete ==
    \A tx \in Checked : (GoBadInputs(tx) \subseteq Live) = (SpecReadInputs(tx) \subseteq Live)

-----------------------------------------------------------------------------
(* TableSpec: every small UTxO, slot and credential state; nothing moves.   *)

\* Places "a" and "b" may each hold 2 or 3 coins, a token or not, locked by
\* a key or a script; "c" is always empty. No tokens before Mary.
\* Literally: "TableOuts is defined as the set of records whose field coin is a
\*   member of the set containing 2 and 3, whose field tok is a member of (if
\*   AtLeast of "Mary" then 0 through 1, else the set containing 0), and whose
\*   field lock is a member of the set containing "key" and "script"."
TableOuts == [coin : {2, 3}, tok : IF AtLeast("Mary") THEN 0..1 ELSE {0},
              lock : {"key", "script"}]

\* In English: the table starts from one empty state, then fills place
\* "a", then "b", then picks a slot and credential state, one step each.
\* Every state on the way is a small ledger too, so GoAgrees is checked in
\* all of them. (Building the states in steps lets TLC check them on all
\* its threads: it checks a new state on the thread that made it.)
\* Literally: "TableInit is defined as: utxo equals the function that maps every
\*   i in Ids to None, and slot equals 0 and registered equals FALSE and reward
\*   equals 0, and fees equals 0 and deposits equals 0 and minted equals 0 and
\*   ntx equals 0, and kept equals the function that maps every i in the empty
\*   set to None, and seen equals the empty set."
TableInit ==
    /\ utxo = [i \in Ids |-> None]
    /\ slot = 0 /\ registered = FALSE /\ reward = 0
    /\ fees = 0 /\ deposits = 0 /\ minted = 0 /\ ntx = 0
    /\ kept = [i \in {} |-> None] /\ seen = {}

\* In English: "Each step fills one more part of the table's state: place "a",
\* then place "b", then the slot and credential."
\* Literally: "TablePick is defined as: ntx is less than 3, and ntx in the next
\*   state equals ntx plus 1, and: in the case ntx equals 0, there exists an o
\*   in the union of TableOuts and the set containing None such that utxo in the
\*   next state equals utxo except that its "a" entry is o, and slot, registered
\*   and reward are unchanged; in the case ntx equals 1, there exists an o in
\*   the union of TableOuts and the set containing None such that utxo in the
\*   next state equals utxo except that its "b" entry is o, and slot, registered
\*   and reward are unchanged; in the case ntx equals 2, there exists an e in
\*   the set containing the tuple of 1, TRUE and 0 and the tuple of 2, TRUE and
\*   1 such that slot in the next state equals element 1 of e and registered in
\*   the next state equals element 2 of e and reward in the next state equals
\*   element 3 of e, and utxo is unchanged; and fees, deposits, minted, kept and
\*   seen are unchanged."
TablePick ==
    /\ ntx < 3
    /\ ntx' = ntx + 1
    /\ CASE ntx = 0 -> \E o \in TableOuts \cup {None} :
                          utxo' = [utxo EXCEPT !["a"] = o]
                          /\ UNCHANGED <<slot, registered, reward>>
          [] ntx = 1 -> \E o \in TableOuts \cup {None} :
                          utxo' = [utxo EXCEPT !["b"] = o]
                          /\ UNCHANGED <<slot, registered, reward>>
          \* Three slot and credential states: together they reach every
          \* slot of the interval family and every registration and balance
          \* of the balance family.
          [] ntx = 2 -> \E e \in {<<1, TRUE, 0>>, <<2, TRUE, 1>>} :
                          slot' = e[1] /\ registered' = e[2] /\ reward' = e[3]
                          /\ UNCHANGED utxo
    /\ UNCHANGED <<fees, deposits, minted, kept, seen>>

\* In English: "Pick the next part of the table's state, or stay once all are
\* picked."
\* Literally: "TableNext is defined as: TablePick, or (ntx equals 3 and vars is
\*   unchanged)."
TableNext == TablePick \/ (ntx = 3 /\ UNCHANGED vars)

\* In English: "Start in TableInit, and from then on every step is a TableNext
\* step."
\* Literally: "TableSpec is defined as: TableInit holds at the start, and
\*   always, every step is a TableNext step or a step that leaves vars
\*   unchanged."
TableSpec == TableInit /\ [][TableNext]_vars

-----------------------------------------------------------------------------
(* Spec: the ledger applies accepted transactions.                         *)

\* The transactions the ledger tries: valid now (slot 0, no bounds), fee
\* 1, at most one collateral and one reference input, a return of one coin
\* and the collateral's tokens or none, and an output that balances or is
\* one coin or one token short (which only a mutated rule accepts).
\* Literally: "LedgerTxs is defined as the set of Base except that its ins is i,
\*   its coll is c, its refs is r, its mint is m, its cert is ce, its wdrl is w,
\*   its olock is l, its rdmrs is element 1 of ph, its valid is element 2 of ph,
\*   its pass is element 3 of ph, its ret is rt, its delta is (if k equals
\*   "coinShort" then negative 1, else 0), and its tdelta is (if k equals
\*   "tokenShort" then negative 1, else 0), for every i that is a member of the
\*   set of subsets of Ids, every c that is a member of the set of every s in
\*   CollSets such that the number of members of s is less than or equal to 1,
\*   every r that is a member of the set of every s in RefSets such that the
\*   number of members of s is less than or equal to 1, every m that is a member
\*   of Mints, every ce that is a member of the set containing "none", "reg" and
\*   "dereg", every w that is a member of BOOLEAN, every l that is a member of
\*   the set containing "key" and "script", every ph that is a member of (if
\*   AtLeast of "Alonzo" then the set containing the tuple of FALSE, TRUE and
\*   TRUE, the tuple of TRUE, TRUE and TRUE, and the tuple of TRUE, FALSE and
\*   FALSE, else the set containing the tuple of FALSE, TRUE and TRUE), every rt
\*   that is a member of (if Era equals "Babbage" then the set containing NoRet
\*   and Back, else the set containing NoRet), and every k that is a member of
\*   the set containing "balanced", "coinShort" and "tokenShort"."
LedgerTxs ==
      {[Base EXCEPT !.ins = i, !.coll = c, !.refs = r, !.mint = m,
                    !.cert = ce, !.wdrl = w, !.olock = l,
                    !.rdmrs = ph[1], !.valid = ph[2], !.pass = ph[3],
                    !.ret = rt, !.delta = IF k = "coinShort" THEN -1 ELSE 0,
                    !.tdelta = IF k = "tokenShort" THEN -1 ELSE 0] :
         i \in SUBSET Ids,
         c \in {s \in CollSets : Cardinality(s) <= 1},
         r \in {s \in RefSets : Cardinality(s) <= 1},
         m \in Mints,
         ce \in {"none", "reg", "dereg"}, w \in BOOLEAN,
         l \in {"key", "script"},
         ph \in IF AtLeast("Alonzo")
                THEN {<<FALSE, TRUE, TRUE>>, <<TRUE, TRUE, TRUE>>,
                      <<TRUE, FALSE, FALSE>>}
                ELSE {<<FALSE, TRUE, TRUE>>},
         rt \in IF Era = "Babbage" THEN {NoRet, Back} ELSE {NoRet},
         k \in {"balanced", "coinShort", "tokenShort"}}

\* A Back return gives back one coin and every collateral token.
\* Literally: "Concrete of tx is defined as: if tx's ret equals Back then tx
\*   except that its ret is the record whose field coin is 1 and field tok is
\*   TokOf of tx's coll, else tx."
Concrete(tx) ==
    IF tx.ret = Back
    THEN [tx EXCEPT !.ret = [coin |-> 1, tok |-> TokOf(tx.coll)]]
    ELSE tx

\* An empty place for a new output (one always exists: a transaction
\* removes at least one output before adding one).
\* Literally: "Fresh of u is defined as the i, chosen from Ids, such that u of i
\*   equals None."
Fresh(u) == CHOOSE i \in Ids : u[i] = None

\* Starting UTxOs a config can name with StartUtxo <- ... : three coins and
\* a token (from Mary) under a key at "a", two coins under a key at "b".
\* Literally: "LedgerStart is defined as the function that maps every i in Ids
\*   to: in the case i equals "a", the record whose field coin is 3, field tok
\*   is (if AtLeast of "Mary" then 1, else 0), and field lock is "key"; in the
\*   case i equals "b", the record whose field coin is 2, field tok is 0, and
\*   field lock is "key"; in every other case, None."
LedgerStart ==
    [i \in Ids |-> CASE i = "a" -> [coin |-> 3, tok |-> IF AtLeast("Mary") THEN 1 ELSE 0,
                                    lock |-> "key"]
                     [] i = "b" -> [coin |-> 2, tok |-> 0, lock |-> "key"]
                     [] OTHER -> None]

\* In English: "The ledger starts from StartUtxo at slot 0, with the credential
\* registered, holding a reward of 1, and its deposit in the pot."
\* Literally: "Init is defined as: utxo equals StartUtxo, and slot equals 0, and
\*   registered equals TRUE, and reward equals 1, and fees equals 0, and
\*   deposits equals KeyDeposit, and minted equals 0, and ntx equals 0, and kept
\*   equals the function that maps every i in the empty set to None, and seen
\*   equals the empty set."
Init ==
    /\ utxo = StartUtxo
    /\ slot = 0
    /\ registered = TRUE
    /\ reward = 1
    /\ fees = 0
    /\ deposits = KeyDeposit
    /\ minted = 0
    /\ ntx = 0
    /\ kept = [i \in {} |-> None]
    /\ seen = {}

\* In English: field f ("coin" or "tok") added up over the places in X of
\* the UTxO u.
RECURSIVE SumField(_, _, _)
\* Literally: "SumField of u, X and f is defined as: if X equals the empty set
\*   then 0, else, letting i be the x, chosen from X, such that TRUE: (if u of i
\*   equals None then 0, else u of i of f) plus SumField of u, X without the
\*   members of the set containing i, and f."
SumField(u, X, f) ==
    IF X = {} THEN 0
    ELSE LET i == CHOOSE x \in X : TRUE
         IN (IF u[i] = None THEN 0 ELSE u[i][f]) + SumField(u, X \ {i}, f)

\* The ada in the ledger at the start: the UTxO, the reward of 1 and the
\* credential's deposit; and the tokens at the start.
\* Literally: "Total is defined as SumField of StartUtxo, Ids and "coin", plus
\*   1, plus KeyDeposit."
Total    == SumField(StartUtxo, Ids, "coin") + 1 + KeyDeposit
\* Literally: "StartTok is defined as SumField of StartUtxo, Ids and "tok"."
StartTok == SumField(StartUtxo, Ids, "tok")

\* In English: a phase-2-valid transaction [S1][R1]: its inputs go, its
\* output arrives, the fee goes to the fee pot, the deposit to the deposit
\* pot, the refund and withdrawal come out of them, and the certificate
\* changes the registration. Reference inputs stay.
\* Literally: "ApplyValid of tx is defined as: letting u1 be the function that
\*   maps every i in Ids to (if i is a member of tx's ins then None, else utxo
\*   of i); out be the record whose field coin is OutCoin of tx, field tok is
\*   OutTok of tx, and field lock is tx's olock; and u2 be: if Mutation equals
\*   "SpecRefConsumed" then the function that maps every i in Ids to (if i is a
\*   member of tx's refs then None, else u1 of i), else u1: utxo in the next
\*   state equals u2 except that its Fresh of u2 entry is out, and fees in the
\*   next state equals fees plus tx's fee, and deposits in the next state equals
\*   deposits plus Deposit of tx minus Refund of tx, and reward in the next
\*   state equals reward minus Wdrl of tx, and registered in the next state
\*   equals: in the case tx's cert equals "reg", TRUE; in the case tx's cert
\*   equals "dereg", FALSE; in every other case, registered; and minted in the
\*   next state equals minted plus tx's mint, and kept in the next state equals
\*   the function that maps every i in tx's refs without the members of tx's ins
\*   to utxo of i."
ApplyValid(tx) ==
    LET u1 == [i \in Ids |-> IF i \in tx.ins THEN None ELSE utxo[i]]
        out == [coin |-> OutCoin(tx), tok |-> OutTok(tx), lock |-> tx.olock]
        u2 == IF Mutation = "SpecRefConsumed"
              THEN [i \in Ids |-> IF i \in tx.refs THEN None ELSE u1[i]]
              ELSE u1
    IN /\ utxo' = [u2 EXCEPT ![Fresh(u2)] = out]
       /\ fees' = fees + tx.fee
       /\ deposits' = deposits + Deposit(tx) - Refund(tx)
       /\ reward' = reward - Wdrl(tx)
       /\ registered' = CASE tx.cert = "reg" -> TRUE
                          [] tx.cert = "dereg" -> FALSE
                          [] OTHER -> registered
       /\ minted' = minted + tx.mint
       /\ kept' = [i \in tx.refs \ tx.ins |-> utxo[i]]

\* In English: a phase-2-invalid transaction [R6] 456-490, [S3]: only its
\* collateral goes; Babbage adds the return as a new output; the
\* collateral's ada balance goes to the fee pot. Its inputs, outputs,
\* certificates, withdrawals and mint have no effect.
\* Literally: "ApplyInvalid of tx is defined as: letting gone be: if Mutation
\*   equals "SpecInvalidSpendsInputs" then the union of tx's coll and tx's ins,
\*   else tx's coll; and u1 be the function that maps every i in Ids to (if i is
\*   a member of gone then None, else utxo of i): utxo in the next state equals:
\*   if tx's ret equals NoRet then u1, else u1 except that its Fresh of u1 entry
\*   is the record whose field coin is tx's ret's coin, field tok is tx's ret's
\*   tok, and field lock is "key"; and fees in the next state equals fees plus
\*   (if Mutation equals "SpecFeeIgnoresReturn" then CoinOf of tx's coll, else
\*   CollBal of tx), and deposits, reward, registered and minted are unchanged,
\*   and kept in the next state equals the function that maps every i in (the
\*   union of tx's ins and tx's refs) without the members of tx's coll to utxo
\*   of i."
ApplyInvalid(tx) ==
    LET gone == IF Mutation = "SpecInvalidSpendsInputs" THEN tx.coll \cup tx.ins
                ELSE tx.coll
        u1 == [i \in Ids |-> IF i \in gone THEN None ELSE utxo[i]]
    IN /\ utxo' = IF tx.ret = NoRet THEN u1
                  ELSE [u1 EXCEPT ![Fresh(u1)] =
                          [coin |-> tx.ret.coin, tok |-> tx.ret.tok, lock |-> "key"]]
       /\ fees' = fees + (IF Mutation = "SpecFeeIgnoresReturn"
                          THEN CoinOf(tx.coll) ELSE CollBal(tx))
       /\ UNCHANGED <<deposits, reward, registered, minted>>
       /\ kept' = [i \in (tx.ins \cup tx.refs) \ tx.coll |-> utxo[i]]

\* In English: "The ledger accepts and applies transaction t, valid or invalid."
\* Literally: "Apply of t is defined as: letting tx be Concrete of t: ntx is
\*   less than MaxTxs, and Expressible of tx, and SpecAccepts of tx, and if tx's
\*   valid then ApplyValid of tx, else ApplyInvalid of tx; and ntx in the next
\*   state equals ntx plus 1, and slot in the next state equals slot, and seen
\*   in the next state equals the union of seen, (if tx's valid is not true then
\*   the set containing "invalid", else the empty set), (if tx's valid is not
\*   true and tx's ret does not equal NoRet then the set containing "collateral
\*   return", else the empty set), (if tx's valid and tx's refs does not equal
\*   the empty set then the set containing "reference read", else the empty
\*   set), (if tx's valid and the intersection of tx's refs and tx's ins does
\*   not equal the empty set then the set containing "reference spent too", else
\*   the empty set), (if tx's valid and tx's mint is less than 0 then the set
\*   containing "burn", else the empty set), and (if tx's valid and tx's cert
\*   equals "dereg" then the set containing "refund", else the empty set)."
Apply(t) ==
    LET tx == Concrete(t) IN
    /\ ntx < MaxTxs
    /\ Expressible(tx)
    /\ SpecAccepts(tx)
    /\ IF tx.valid THEN ApplyValid(tx) ELSE ApplyInvalid(tx)
    /\ ntx' = ntx + 1
    /\ slot' = slot
    /\ seen' = seen
         \cup (IF ~tx.valid THEN {"invalid"} ELSE {})
         \cup (IF ~tx.valid /\ tx.ret # NoRet THEN {"collateral return"} ELSE {})
         \cup (IF tx.valid /\ tx.refs # {} THEN {"reference read"} ELSE {})
         \cup (IF tx.valid /\ tx.refs \cap tx.ins # {} THEN {"reference spent too"} ELSE {})
         \cup (IF tx.valid /\ tx.mint < 0 THEN {"burn"} ELSE {})
         \cup (IF tx.valid /\ tx.cert = "dereg" THEN {"refund"} ELSE {})

\* In English: the ledger stops after the last transaction, or earlier when
\* no transaction can be accepted (an invalid transaction can give all the
\* remaining outputs up as collateral).
\* Literally: "Done is defined as: (ntx equals MaxTxs, or (there exists a t in
\*   LedgerTxs such that Apply of t) is enabled is not true), and vars is
\*   unchanged."
Done == /\ \/ ntx = MaxTxs
           \/ ~ENABLED (\E t \in LedgerTxs : Apply(t))
        /\ UNCHANGED vars

\* In English: "Each step applies some transaction, or stops."
\* Literally: "Next is defined as: (there exists a t in LedgerTxs such that
\*   Apply of t) or Done."
Next == (\E t \in LedgerTxs : Apply(t)) \/ Done

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must always be true.                                               *)

\* In English: every variable holds the kind of value it should.
\* Literally: "TypeOK is defined as: for all i in Ids, utxo of i equals None or
\*   (utxo of i's coin is a member of Nat and utxo of i's tok is a member of Nat
\*   and utxo of i's lock is a member of the set containing "key" and "script");
\*   and registered is a member of BOOLEAN, and reward is a member of 0 through
\*   1, and fees is a member of Nat and deposits is a member of Nat and minted
\*   is a member of Int."
TypeOK ==
    /\ \A i \in Ids : utxo[i] = None \/
         (utxo[i].coin \in Nat /\ utxo[i].tok \in Nat /\ utxo[i].lock \in {"key", "script"})
    /\ registered \in BOOLEAN
    /\ reward \in 0..1
    /\ fees \in Nat /\ deposits \in Nat /\ minted \in Int

\* In English: no ada is made or lost: UTxO + fees + deposits + rewards is
\* constant [S1] (the reward pot and reserves are model `ledger-shelley`'s).
\* Literally: "ValuePreserved is defined as: SumField of utxo, Ids and "coin",
\*   plus fees plus deposits plus reward, equals Total."
ValuePreserved == SumField(utxo, Ids, "coin") + fees + deposits + reward = Total

\* In English: tokens change only by minting and burning [S2].
\* Literally: "TokensPreserved is defined as: SumField of utxo, Ids and "tok"
\*   equals StartTok plus minted."
TokensPreserved == SumField(utxo, Ids, "tok") = StartTok + minted

\* In English: the outputs the last transaction had to leave alone are
\* still there, unchanged: a valid transaction's reference inputs that it
\* did not spend, and an invalid transaction's inputs and reference inputs
\* that are not collateral [R6] 456-490.
\* Literally: "KeptUnspent is defined as: for all i in the domain of kept, utxo
\*   of i equals kept of i."
KeptUnspent == \A i \in DOMAIN kept : utxo[i] = kept[i]

-----------------------------------------------------------------------------
(* Reachability probes: each claims something never happens; a config that *)
(* checks one must FAIL.                                                   *)

\* In English: "No invalid transaction is ever applied."
\* Literally: "ProbeNoInvalidTx is defined as: "invalid" is not a member of
\*   seen."
ProbeNoInvalidTx        == "invalid" \notin seen
\* In English: "No collateral return is ever paid."
\* Literally: "ProbeNoCollateralReturn is defined as: "collateral return" is not
\*   a member of seen."
ProbeNoCollateralReturn == "collateral return" \notin seen
\* In English: "No valid transaction ever reads a reference input."
\* Literally: "ProbeNoReferenceRead is defined as: "reference read" is not a
\*   member of seen."
ProbeNoReferenceRead    == "reference read" \notin seen
\* In English: "No valid transaction ever spends one of its own reference
\* inputs."
\* Literally: "ProbeNoReferenceSpent is defined as: "reference spent too" is not
\*   a member of seen."
ProbeNoReferenceSpent   == "reference spent too" \notin seen
\* In English: "No valid transaction ever burns a token."
\* Literally: "ProbeNoBurn is defined as: "burn" is not a member of seen."
ProbeNoBurn             == "burn" \notin seen
\* In English: "No valid transaction ever refunds a deposit."
\* Literally: "ProbeNoRefund is defined as: "refund" is not a member of seen."
ProbeNoRefund           == "refund" \notin seen

\* Table probes: some transaction the reference accepts has the property.
\* In English: "The reference accepts no output below the minimum."
\* Literally: "ProbeNoTokenOutputBelowMin is defined as: it is not true that
\*   there exists a tx in Checked such that SpecAccepts of tx and OutCoin of tx
\*   is less than MinUtxo."
ProbeNoTokenOutputBelowMin ==
    ~\E tx \in Checked : SpecAccepts(tx) /\ OutCoin(tx) < MinUtxo
\* In English: "The reference accepts no transaction with redeemers."
\* Literally: "ProbeNoCollateralAccepted is defined as: it is not true that
\*   there exists a tx in Checked such that SpecAccepts of tx and tx's rdmrs."
ProbeNoCollateralAccepted ==
    ~\E tx \in Checked : SpecAccepts(tx) /\ tx.rdmrs
\* In English: "The reference accepts no transaction with redeemers, a
\* collateral return and a stated total."
\* Literally: "ProbeNoReturnAccepted is defined as: it is not true that there
\*   exists a tx in Checked such that SpecAccepts of tx and tx's rdmrs and tx's
\*   ret does not equal NoRet and tx's tcoll does not equal negative 1."
ProbeNoReturnAccepted ==
    ~\E tx \in Checked : SpecAccepts(tx) /\ tx.rdmrs /\ tx.ret # NoRet /\ tx.tcoll # -1
\* In English: "The reference accepts no transaction whose reference and spent
\* inputs overlap."
\* Literally: "ProbeNoOverlapAccepted is defined as: it is not true that there
\*   exists a tx in Checked such that SpecAccepts of tx and the intersection of
\*   tx's refs and tx's ins does not equal the empty set."
ProbeNoOverlapAccepted ==
    ~\E tx \in Checked : SpecAccepts(tx) /\ tx.refs \cap tx.ins # {}
=============================================================================
