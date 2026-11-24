----------------------------- MODULE ByronUtxo -----------------------------
(***************************************************************************)
(* The Byron UTxO rule: which transactions a Byron ledger accepts, what    *)
(* they do to the UTxO, and the minimum fee.                               *)
(*                                                                         *)
(* Three deciders look at every transaction the model can write:           *)
(*   1. the formal specification (SpecAccepts),                            *)
(*   2. the reference Haskell implementation (RefAccepts), and             *)
(*   3. gOuroboros (GoAccepts).                                            *)
(* gOuroboros keeps no ledger state: the caller (Dingo) hands it a UTxO    *)
(* view, and VerifyBlock folds the earlier transactions of the same block  *)
(* in with BlockLedgerState. The model runs the chain on gOuroboros'       *)
(* verdicts and, in every state it reaches, asks all three deciders about  *)
(* every candidate transaction.                                            *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   Specification (eras/byron/ledger/formal-spec/):                       *)
(*   [S1] utxo.tex 188-219: the UTXO rule: txins tx is a subset of dom    *)
(*        utxo, minfee <= fee, txins and txouts non-empty, every output   *)
(*        value positive; utxo' = (txins <-/ utxo) U txouts.               *)
(*   [S2] utxo.tex 126-128: minfee = a + b * txSize.                       *)
(*   [S3] utxo.tex 322-330: UTXOW: txSize <= maxTxSize, and every input   *)
(*        has a witness for its address.                                   *)
(*   Reference (eras/byron/ledger/impl/src/Cardano/Chain/):                *)
(*   [R1] UTxO/Tx.hs 56-58: txInputs and txOutputs are NonEmpty, so an    *)
(*        empty list does not decode.                                      *)
(*   [R2] UTxO/Validation.hs 177-236 validateTxAux: size <= maxTxSize     *)
(*        over the whole TxAux bytes; minFee 0 when every input address   *)
(*        is a redeem address (isRedeemUTxO), else calculateTxSizeLinear;  *)
(*        balances over S.fromList inputs (a duplicate counts once);      *)
(*        fee = balanceIn - balanceOut must not be negative; minFee <= fee.*)
(*        No check that an output is positive.                             *)
(*   [R3] UTxO/Validation.hs 257-278 validateTx/validateTxIn: every input *)
(*        in dom utxo. No duplicate-input check.                           *)
(*   [R4] UTxO/Validation.hs 367-406 updateUTxOTxWitness: witnesses are   *)
(*        checked with zip addresses witnesses, so pairs beyond the       *)
(*        shorter list are never looked at.                                *)
(*   [R5] Common/TxSizeLinear.hs 69-74, 81-86: a = round(summand), b =    *)
(*        multiplier as a rational; minFee = a + ceiling(b * size). The   *)
(*        genesis JSON path (Common/TxFeePolicy.hs 110-124) takes         *)
(*        summand `div` 1e9 instead of round.                              *)
(*   gOuroboros (commit d0b95845):                                         *)
(*   [G1] ledger/byron/byron.go ValidateAgainstUtxo 780-893: witness count *)
(*        = input count; no duplicate inputs; inputs resolve; outputs do  *)
(*        not exceed inputs; fee >= MinFee unless every input witness is  *)
(*        a redeem witness. No size limit; no non-empty check.            *)
(*   [G2] ledger/common/verify_config.go ByronTxFeePolicy.MinFee 170-180: *)
(*        ceiling((summand + multiplier * size) / 1e9).                    *)
(*   [G3] ledger/verify_block.go 1411-1460: each Byron transaction is     *)
(*        validated, then applied to the block's BlockLedgerState.        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla. New here:*)
(*   Seq(S), Len(s), s[i]  sequences, from the Sequences module            *)
(*   Range(s)              the set of the elements of s (defined below)    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    PkValue,      \* lovelace in the starting pay-to-key output
    RedeemValue,  \* lovelace in the starting redeem-address output
    MaxOut,       \* the largest output value a candidate writes
    Unit,         \* fee-policy units per lovelace (1e9 on a real network)
    SummandUnits, \* the fee policy's summand, in those units
    MultUnits,    \* the fee policy's multiplier per byte, in those units
    MaxTxSize,    \* the protocol parameter maxTxSize [S3][R2]
    MaxTxs,       \* how many transactions the model applies (keeps it finite)
    GoFixed,      \* TRUE: gOuroboros rejects empty inputs or outputs, as on
                  \*  fix/ledger-byron-nonempty-tx. FALSE: as on main.
    GoChecksSize, \* TRUE: gOuroboros checks maxTxSize. FALSE: as on main.
    Mutation      \* "none", or one deliberate mistake (see the configs)

\* An output reference is <<transaction number, output index>>. The two
\* starting outputs belong to transaction 0. Missing is a reference that is
\* never in any UTxO.
\* Literally: "PkIn is defined as the tuple of 0 and 1."
PkIn     == <<0, 1>>
\* Literally: "RedeemIn is defined as the tuple of 0 and 2."
RedeemIn == <<0, 2>>
\* Literally: "Missing is defined as the tuple of 99 and 99."
Missing  == <<99, 99>>

\* The value placed in the UTxO at the start.
\* Literally: "Total is defined as PkValue plus RedeemValue."
Total == PkValue + RedeemValue

VARIABLES
    utxo,      \* utxo[r]: the output at reference r, a record [val, redeem]
    reserves,  \* the fees collected so far (the spec's reserves gain)
    n          \* how many transactions have been applied

\* Literally: "vars is defined as the tuple of utxo, reserves and n."
vars == <<utxo, reserves, n>>

-----------------------------------------------------------------------------
(* Helpers.                                                                *)

\* In English: the set of the elements of a sequence.
\* Literally: "Range of s is defined as the set of s of i, for every i that is a
\*   member of the domain of s."
Range(s) == {s[i] : i \in DOMAIN s}

\* In English: the sum of a sequence of numbers.
RECURSIVE SumSeq(_)
\* Literally: "SumSeq of s is defined as: if s equals the empty sequence then 0,
\*   else the head of s plus SumSeq of the tail of s."
SumSeq(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumSeq(Tail(s))

\* In English: the sum of the values of the outputs at a set of references.
RECURSIVE SumRefs(_, _)
\* Literally: "SumRefs of u and R is defined as: if R equals the empty set then
\*   0, else, letting r be the x, chosen from R, such that TRUE: u of r's val
\*   plus SumRefs of u and (R without the members of the set containing r)."
SumRefs(u, R) ==
    IF R = {} THEN 0
    ELSE LET r == CHOOSE x \in R : TRUE
         IN u[r].val + SumRefs(u, R \ {r})

\* In English: every sequence of length 0, 1 or 2 over the set S.
\* Literally: "UpTo2 of S is defined as the union of the set containing the
\*   empty sequence, the set of the tuple of a, for every a that is a member of
\*   S, and the set of the tuple of a and b, for every a and b that are members
\*   of S."
UpTo2(S) == {<<>>} \cup {<<a>> : a \in S} \cup {<<a, b>> : a, b \in S}

\* In English: integer division rounding up, for non-negative numbers.
\* Literally: "CeilDiv of x and y is defined as (x plus y minus 1)
\*   integer-divided by y."
CeilDiv(x, y) == (x + y - 1) \div y

-----------------------------------------------------------------------------
(* Candidate transactions.                                                 *)

\* A transaction is its inputs (a sequence: the wire format is a list, so
\* it can repeat an input), its output values, and how many witnesses it
\* carries. Witness signatures are not modelled: both implementations check
\* them, and each witness here is valid for the input it is paired with.
\* Literally: "Candidates of u is defined as the set of records whose field ins
\*   is a member of UpTo2 of the union of the domain of u and the set containing
\*   Missing, whose field outs is a member of UpTo2 of 0 through MaxOut, and
\*   whose field wits is a member of 0 through 2."
Candidates(u) ==
    [ins  : UpTo2(DOMAIN u \cup {Missing}),
     outs : UpTo2(0..MaxOut),
     wits : 0..2]

\* In English: the serialized size of the TxAux in abstract bytes: one for
\* the envelope, one per input, output and witness. Both implementations
\* size the whole TxAux, witnesses included [R2][G1].
\* Literally: "Size of tx is defined as 1 plus the length of tx's ins plus the
\*   length of tx's outs plus tx's wits."
Size(tx) == 1 + Len(tx.ins) + Len(tx.outs) + tx.wits

\* In English: the value the inputs bring in, each distinct input once [R2].
\* Literally: "BalanceIn of u and tx is defined as SumRefs of u and Range of
\*   tx's ins."
BalanceIn(u, tx) == SumRefs(u, Range(tx.ins))
\* In English: the value the outputs carry out.
\* Literally: "BalanceOut of tx is defined as SumSeq of tx's outs."
BalanceOut(tx)   == SumSeq(tx.outs)
\* In English: what the inputs bring in less what the outputs carry out.
\* Literally: "Fee of u and tx is defined as BalanceIn of u and tx minus
\*   BalanceOut of tx."
Fee(u, tx)       == BalanceIn(u, tx) - BalanceOut(tx)

\* In English: every input is spent from a redeem address. Over an empty
\* input list this is vacuously TRUE.
\* Literally: "AllRedeem of u and tx is defined as: for all r in Range of tx's
\*   ins, u of r's redeem."
AllRedeem(u, tx) == \A r \in Range(tx.ins) : u[r].redeem

\* In English: the input list names some output twice.
\* Literally: "HasDup of tx is defined as: the length of tx's ins equals 2, and
\*   element 1 of tx's ins equals element 2 of tx's ins."
HasDup(tx) == Len(tx.ins) = 2 /\ tx.ins[1] = tx.ins[2]

\* In English: every input is in the UTxO.
\* Literally: "InputsExist of u and tx is defined as: Range of tx's ins is a
\*   subset of the domain of u."
InputsExist(u, tx) == Range(tx.ins) \subseteq DOMAIN u

-----------------------------------------------------------------------------
(* The three deciders.                                                     *)

\* The specification [S1][S2][S3]. Its inputs are a set, so a repeated
\* input is the same set; its fee coefficients are exact, so minfee <= fee
\* is compared in fee-policy units without rounding.
\* In English: the specification accepts tx against UTxO u.
\* Literally: "SpecAccepts of u and tx is defined as: Range of tx's ins does not
\*   equal the empty set, and tx's outs does not equal the empty sequence, and
\*   for all i in the domain of tx's outs, tx's outs of i is greater than 0, and
\*   InputsExist of u and tx, and Size of tx is less than or equal to MaxTxSize,
\*   and tx's wits is greater than or equal to the number of members of Range of
\*   tx's ins, and Fee of u and tx is greater than or equal to 0, and (AllRedeem
\*   of u and tx, or SummandUnits plus MultUnits times Size of tx is less than
\*   or equal to Fee of u and tx times Unit)."
SpecAccepts(u, tx) ==
    /\ Range(tx.ins) # {}                                  \* txins tx /= {}
    /\ tx.outs # <<>>                                      \* txouts tx /= {}
    /\ \A i \in DOMAIN tx.outs : tx.outs[i] > 0            \* every output 0 < c
    /\ InputsExist(u, tx)                                  \* txins tx in dom utxo
    /\ Size(tx) <= MaxTxSize                               \* txSize <= maxTxSize [S3]
    /\ tx.wits >= Cardinality(Range(tx.ins))               \* a witness per input [S3]
    /\ Fee(u, tx) >= 0
    /\ (AllRedeem(u, tx)
        \/ SummandUnits + MultUnits * Size(tx) <= Fee(u, tx) * Unit)

\* In English: the reference minimum fee [R5]: the summand rounded down to
\* lovelace (the genesis JSON path), plus the per-byte part rounded up.
\* Literally: "RefMinFee of sz is defined as (SummandUnits integer-divided by
\*   Unit) plus CeilDiv of MultUnits times sz, and Unit."
RefMinFee(sz) == (SummandUnits \div Unit) + CeilDiv(MultUnits * sz, Unit)

\* The reference [R1]-[R4]. Witnesses are zipped with inputs, so a short
\* or long witness list is not itself an error.
\* In English: the reference accepts tx against UTxO u.
\* Literally: "RefAccepts of u and tx is defined as: tx's ins does not equal the
\*   empty sequence, and tx's outs does not equal the empty sequence, and
\*   InputsExist of u and tx, and Size of tx is less than or equal to MaxTxSize,
\*   and Fee of u and tx is greater than or equal to 0, and (AllRedeem of u and
\*   tx, or Mutation equals "RefNoMinFee", or RefMinFee of Size of tx is less
\*   than or equal to Fee of u and tx)."
RefAccepts(u, tx) ==
    /\ tx.ins # <<>>                                       \* NonEmpty decode [R1]
    /\ tx.outs # <<>>                                      \* NonEmpty decode [R1]
    /\ InputsExist(u, tx)                                  \* validateTxIn [R3]
    /\ Size(tx) <= MaxTxSize                               \* TxValidationTxTooLarge [R2]
    /\ Fee(u, tx) >= 0                                     \* subLovelace must not underflow [R2]
    /\ (AllRedeem(u, tx)                                   \* isRedeemUTxO: minFee 0 [R2]
        \/ Mutation = "RefNoMinFee"
        \/ RefMinFee(Size(tx)) <= Fee(u, tx))              \* TxValidationFeeTooSmall [R2]

\* In English: the gOuroboros minimum fee [G2]: the whole sum rounded up.
\* Literally: "GoMinFee of sz is defined as CeilDiv of SummandUnits plus
\*   MultUnits times sz, and Unit."
GoMinFee(sz) == CeilDiv(SummandUnits + MultUnits * sz, Unit)

\* gOuroboros [G1], in its order.
\* In English: gOuroboros accepts tx against UTxO u.
\* Literally: "GoAccepts of u and tx is defined as: if GoFixed, then (tx's ins
\*   does not equal the empty sequence and tx's outs does not equal the empty
\*   sequence), and tx's wits equals the length of tx's ins, and HasDup of tx is
\*   not true, and InputsExist of u and tx, and if GoChecksSize, then Size of tx
\*   is less than or equal to MaxTxSize, and (Mutation equals "NoBalance" or Fee
\*   of u and tx is greater than or equal to 0), and (AllRedeem of u and tx, or
\*   Mutation equals "RedeemAny", or GoMinFee of Size of tx is less than or
\*   equal to Fee of u and tx)."
GoAccepts(u, tx) ==
    /\ GoFixed => (tx.ins # <<>> /\ tx.outs # <<>>)        \* the fix: reject empty lists
    /\ tx.wits = Len(tx.ins)                               \* "%d inputs but %d witnesses"
    /\ ~HasDup(tx)                                         \* "duplicate byron transaction input"
    /\ InputsExist(u, tx)                                  \* ResolveInputUtxo
    /\ GoChecksSize => Size(tx) <= MaxTxSize               \* not on main
    /\ (Mutation = "NoBalance" \/ Fee(u, tx) >= 0)         \* "output value exceeds input value"
    /\ (AllRedeem(u, tx)                                   \* allRedeemInputs: fee exempt
        \/ Mutation = "RedeemAny"
        \/ GoMinFee(Size(tx)) <= Fee(u, tx))               \* "fee is below minimum fee"

-----------------------------------------------------------------------------
(* The steps.                                                              *)

\* In English: the UTxO starts with one pay-to-key and one redeem output.
\* Literally: "Init is defined as: utxo equals the function that maps every r in
\*   the set containing PkIn and RedeemIn to: if r equals PkIn then the record
\*   whose field val is PkValue and field redeem is FALSE, else the record whose
\*   field val is RedeemValue and field redeem is TRUE; and reserves equals 0,
\*   and n equals 0."
Init ==
    /\ utxo = [r \in {PkIn, RedeemIn} |->
                 IF r = PkIn THEN [val |-> PkValue, redeem |-> FALSE]
                 ELSE [val |-> RedeemValue, redeem |-> TRUE]]
    /\ reserves = 0
    /\ n = 0

\* In English: the outputs transaction number k creates. They are
\* pay-to-key outputs (a redeem address is only ever in genesis).
\* Literally: "NewOutputs of k and tx is defined as the function that maps every
\*   r in the set of the tuple of k and i, for every i that is a member of the
\*   domain of tx's outs, to the record whose field val is tx's outs of element
\*   2 of r and whose field redeem is FALSE."
NewOutputs(k, tx) ==
    [r \in {<<k, i>> : i \in DOMAIN tx.outs} |->
        [val |-> tx.outs[r[2]], redeem |-> FALSE]]

\* In English: a block carrying tx is applied because gOuroboros accepted
\* it. BlockLedgerState removes the inputs and adds the outputs [G3]; the
\* fee goes to the reserves [S1].
\* Literally: "Apply of tx is defined as: n is less than MaxTxs, and GoAccepts
\*   of utxo and tx, and, letting kept be: if Mutation equals "KeepInputs" then
\*   the domain of utxo, else the domain of utxo without the members of Range of
\*   tx's ins; and made be NewOutputs of n plus 1, and tx: utxo in the next
\*   state equals the function that maps every r in the union of kept and the
\*   domain of made to: if r is a member of the domain of made then made of r,
\*   else utxo of r; and reserves in the next state equals reserves plus Fee of
\*   utxo and tx, and n in the next state equals n plus 1."
Apply(tx) ==
    /\ n < MaxTxs
    /\ GoAccepts(utxo, tx)
    /\ LET kept == IF Mutation = "KeepInputs" THEN DOMAIN utxo
                   ELSE DOMAIN utxo \ Range(tx.ins)
           made == NewOutputs(n + 1, tx)
       IN utxo' = [r \in kept \cup DOMAIN made |->
                     IF r \in DOMAIN made THEN made[r] ELSE utxo[r]]
    /\ reserves' = reserves + Fee(utxo, tx)
    /\ n' = n + 1

\* In English: nothing more happens. Keeps TLC from reporting a deadlock
\* once MaxTxs transactions are applied.
\* Literally: "Done is defined as: vars is unchanged."
Done == UNCHANGED vars

\* In English: "Each step applies some candidate transaction gOuroboros accepts,
\* or nothing happens."
\* Literally: "Next is defined as: (there exists a tx in Candidates of utxo such
\*   that Apply of tx) or Done."
Next == (\E tx \in Candidates(utxo) : Apply(tx)) \/ Done

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must hold.                                                         *)

\* In English: the variables have the shapes declared above.
\* Literally: "TypeOK is defined as: for all r in the domain of utxo, utxo of
\*   r's val is a member of Nat and utxo of r's redeem is a member of BOOLEAN,
\*   and reserves is a member of Int, and n is a member of 0 through MaxTxs."
TypeOK ==
    /\ \A r \in DOMAIN utxo : utxo[r].val \in Nat /\ utxo[r].redeem \in BOOLEAN
    /\ reserves \in Int
    /\ n \in 0..MaxTxs

\* In English: no lovelace is made or lost: the UTxO plus the collected
\* fees is always the starting value, and fees are never negative.
\* Literally: "ValuePreserved is defined as: reserves is greater than or equal
\*   to 0, and SumRefs of utxo and the domain of utxo, plus reserves, equals
\*   Total."
ValuePreserved ==
    /\ reserves >= 0
    /\ SumRefs(utxo, DOMAIN utxo) + reserves = Total

\* In English: gOuroboros never accepts a transaction the reference
\* rejects. Fails on main twice over: an empty transaction (no inputs is
\* vacuously "all redeem", so it pays no fee) and an oversized one.
\* Literally: "GoSound is defined as: for all tx in Candidates of utxo, if
\*   GoAccepts of utxo and tx, then RefAccepts of utxo and tx."
GoSound ==
    \A tx \in Candidates(utxo) : GoAccepts(utxo, tx) => RefAccepts(utxo, tx)

\* In English: gOuroboros accepts every transaction the reference accepts,
\* apart from its two known, deliberate tightenings: a repeated input and a
\* witness count different from the input count. Fails when the fee
\* summand is not a whole number of lovelace (the rounding differs [R5][G2]).
\* Literally: "GoComplete is defined as: for all tx in Candidates of utxo, if
\*   RefAccepts of utxo and tx and HasDup of tx is not true and tx's wits equals
\*   the length of tx's ins, then GoAccepts of utxo and tx."
GoComplete ==
    \A tx \in Candidates(utxo) :
        (RefAccepts(utxo, tx) /\ ~HasDup(tx) /\ tx.wits = Len(tx.ins))
            => GoAccepts(utxo, tx)

\* In English: the reference accepts only what the specification accepts,
\* except for its two known departures: a zero-valued output (the spec
\* wants every output positive) and a transaction with fewer witnesses than
\* inputs (zip never checks the unpaired inputs).
\* Literally: "RefMatchesSpec is defined as: for all tx in Candidates of utxo,
\*   if RefAccepts of utxo and tx and SpecAccepts of utxo and tx is not true,
\*   then (there exists an i in the domain of tx's outs such that tx's outs of i
\*   equals 0) or tx's wits is less than the number of members of Range of tx's
\*   ins."
RefMatchesSpec ==
    \A tx \in Candidates(utxo) :
        (RefAccepts(utxo, tx) /\ ~SpecAccepts(utxo, tx))
            => (\/ \E i \in DOMAIN tx.outs : tx.outs[i] = 0
                \/ tx.wits < Cardinality(Range(tx.ins)))

-----------------------------------------------------------------------------
(* Reachability probes: each is expected to be violated (named *Bug.cfg).  *)

\* A transaction that spends an output an earlier transaction made.
\* Literally: "ProbeChained is defined as: (there exists an r in the domain of
\*   utxo such that element 1 of r is greater than 0 and there exists a tx in
\*   Candidates of utxo such that r is a member of Range of tx's ins and
\*   GoAccepts of utxo and tx) is not true."
ProbeChained == ~(\E r \in DOMAIN utxo : r[1] > 0 /\
                   \E tx \in Candidates(utxo) :
                       r \in Range(tx.ins) /\ GoAccepts(utxo, tx))

\* A redeem-only spend below the minimum fee is accepted.
\* Literally: "ProbeRedeemExempt is defined as: (there exists a tx in Candidates
\*   of utxo such that GoAccepts of utxo and tx, and tx's ins does not equal the
\*   empty sequence, and Fee of utxo and tx is less than GoMinFee of Size of tx)
\*   is not true."
ProbeRedeemExempt ==
    ~(\E tx \in Candidates(utxo) :
         GoAccepts(utxo, tx) /\ tx.ins # <<>>
         /\ Fee(utxo, tx) < GoMinFee(Size(tx)))

\* The reference accepts a repeated input that gOuroboros rejects.
\* Literally: "ProbeDupDeviation is defined as: (there exists a tx in Candidates
\*   of utxo such that RefAccepts of utxo and tx, and HasDup of tx, and tx's
\*   wits equals 2, and GoAccepts of utxo and tx is not true) is not true."
ProbeDupDeviation ==
    ~(\E tx \in Candidates(utxo) :
         RefAccepts(utxo, tx) /\ HasDup(tx) /\ tx.wits = 2
         /\ ~GoAccepts(utxo, tx))

\* The reference accepts an input that carries no witness.
\* Literally: "ProbeUnderwitnessed is defined as: (there exists a tx in
\*   Candidates of utxo such that RefAccepts of utxo and tx, and tx's wits is
\*   less than the length of tx's ins) is not true."
ProbeUnderwitnessed ==
    ~(\E tx \in Candidates(utxo) :
         RefAccepts(utxo, tx) /\ tx.wits < Len(tx.ins))

\* The reference and gOuroboros both accept a zero-valued output the
\* specification forbids.
\* Literally: "ProbeZeroOutput is defined as: (there exists a tx in Candidates
\*   of utxo such that RefAccepts of utxo and tx, and GoAccepts of utxo and tx,
\*   and there exists an i in the domain of tx's outs such that tx's outs of i
\*   equals 0) is not true."
ProbeZeroOutput ==
    ~(\E tx \in Candidates(utxo) :
         RefAccepts(utxo, tx) /\ GoAccepts(utxo, tx)
         /\ \E i \in DOMAIN tx.outs : tx.outs[i] = 0)
=============================================================================
