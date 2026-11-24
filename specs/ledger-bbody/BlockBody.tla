------------------------------ MODULE BlockBody ------------------------------
(***************************************************************************)
(* The block-body rule (BBODY, with the LEDGERS fold it runs) of every     *)
(* Shelley-family era, at a small abstract scale, and gOuroboros'          *)
(* decision for the same blocks.                                           *)
(*                                                                         *)
(* A block is checked in three steps:                                      *)
(*   1. Its envelope: the body decodes (the invalid-transaction indexes    *)
(*      are in range, there is one witness set per body), the size the    *)
(*      header declares is the real size and within the maximum, the       *)
(*      header's body hash is right, and the header's protocol version is  *)
(*      allowed (Conway: not too high on mainnet; Dijkstra: not too low).  *)
(*   2. Its transactions, in order: each one is checked against the UTxO   *)
(*      the earlier ones left, then applied. A phase-2-invalid one (listed *)
(*      in invalid_transactions) consumes only its collateral and adds     *)
(*      only its collateral return.                                        *)
(*   3. Its totals: execution units over every transaction (Alonzo on),    *)
(*      and reference-script bytes (Conway on), measured against the       *)
(*      starting UTxO through protocol version 10 and against the starting *)
(*      UTxO plus the earlier transactions' outputs from version 11.       *)
(*                                                                         *)
(* A transaction is reduced to one spent input, one collateral input, one  *)
(* optional reference input, whether its output carries a reference        *)
(* script, and its execution units (0 or 1). Its other rules are model     *)
(* 17's, which this model does not repeat: here "valid" means only that    *)
(* every input it names exists when it is applied.                         *)
(*                                                                         *)
(* An input is named relative to the transaction: "g" is a genesis output  *)
(* carrying a reference script of size 1, "k" a genesis output with no     *)
(* script, "prev" the output of the transaction before, "prevret" its      *)
(* collateral return. "prev" of the first transaction does not exist.      *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd                *)
(* (eras/<era>/impl/src/Cardano/Ledger/<Era>/), full table in              *)
(* specs/ledger-bbody/README.md.                                        *)
(*   [R1] Shelley/Rules/Bbody.hs 228-249 bbodyTransition: size, hash,      *)
(*        then LEDGERS; 260-281 size, 283-300 hash.                        *)
(*   [R2] Shelley/Rules/Ledgers.hs 214-231: each transaction runs LEDGER   *)
(*        on the state the one before it left, with its index.             *)
(*   [R3] Alonzo/Rules/Bbody.hs 157-175 validateExUnits (sum over every    *)
(*        transaction, pointwise <=); 196-217 bbodyTransition.             *)
(*   [R4] Conway/Rules/Bbody.hs 281-286 (Conway checks, then Alonzo's);    *)
(*        303-330 HeaderProtVerTooHigh on mainnet (header major <=         *)
(*        current major + 1); 356-369 BodyRefScriptsSizeTooBig against     *)
(*        the starting UTxO; 371-383 totalRefScriptSizeInBlock (pv <= 10:  *)
(*        each tx against the start; pv >= 11: the start unioned with      *)
(*        earlier outputs, or collateral outputs of invalid txs).          *)
(*        Conway/PParams.hs 983: the Conway limit is 1 MiB.                *)
(*   [R5] Conway/UTxO.hs 183-187 txNonDistinctRefScriptsSize: the union of *)
(*        spent and reference inputs, each counted once.                   *)
(*   [R6] Dijkstra/Rules/Bbody.hs 416-456: size, hash, HeaderProtVerTooLow *)
(*        (header major >= current major), LEDGERS, units, ref scripts.    *)
(*   [R7] Alonzo/BlockBody/Internal.hs 242-275: the body decoder rejects   *)
(*        unequal body and witness counts and an out-of-range invalid      *)
(*        index; 304-311 alignedValidFlags; 209-224 the four-part hash.    *)
(*   [R8] Shelley/Chain.hs 71-80 chainChecks: declared body size <=        *)
(*        maxBBSize.                                                       *)
(*   [R9] Babbage/Rules/Utxo.hs 380-382 BadInputs covers spent,            *)
(*        collateral and reference inputs whatever IsValid says; 456-490   *)
(*        an invalid tx removes its collateral and adds its return.        *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 756a9a89):              *)
(*   [G1] ledger/verify_block.go 1272 size, 1316 hash, 1568-1600 maximum   *)
(*        body size (skipped when the maximum is 0), 1518 units.           *)
(*   [G2] ledger/verify_block.go 714-773 sumBlockExUnits (every tx).       *)
(*   [G3] ledger/verify_block.go 798-817 verifyBlockTransactions with      *)
(*        common.BlockLedgerState (ledger/common/block_state.go 185).      *)
(*   [G4] ledger/common/common.go 1452-1479 TransactionValidityFlags;      *)
(*        1279 body and witness counts; ledger/{alonzo,babbage,conway}/    *)
(*        <era>.go invalid index range (alonzo.go 111).                    *)
(*   [G5] ledger/common/ref_scripts.go 51-108, 150-167, 185-230            *)
(*        ConsumedReferenceScriptSizePerBlock; ledger/verify_block.go 1740.*)
(*   [G6] ledger/dijkstra/leios_header.go 29-42 HeaderProtVerTooLow.       *)
(*   [G7] HeaderProtVerTooHigh: absent on main; added by branch            *)
(*        fix/ledger-bbody-header-protver-too-high (GoFixed = TRUE).       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Era,            \* "Shelley" (also Allegra, Mary), "Alonzo" (also
                    \* Babbage), "Conway" or "Dijkstra"
    PV,             \* the major protocol version in force
    Mainnet,        \* TRUE: the ledger runs on mainnet
    MaxTxs,         \* the most transactions a block may hold here
    MaxInvalidLen,  \* the longest invalid_transactions list tried
    MaxBody,        \* maximum body size (one unit per tx, plus one)
    MaxEx,          \* maximum execution units per block
    MaxRef,         \* maximum reference-script bytes per block
    InChoices,      \* what a transaction's spent input may name
    CollChoices,    \* what its collateral input may name
    RefChoices,     \* what its reference input may name ("none": none)
    ScriptChoices,  \* whether its output carries a script: subset of 0..1
    ExChoices,      \* its execution units: subset of 0..1
    SizeOffs,       \* declared size: "exact", "less" or "more" than real
    HashOks,        \* whether the header's body hash is right
    WitOffs,        \* witness sets: "same", "fewer" or "more" than bodies
    HdrPVs,         \* major protocol versions a header may carry
    GoFixed,        \* TRUE: gOuroboros with HeaderProtVerTooHigh [G7]
    Mutation        \* "none", or a deliberate change to the reference

\* ---------------------------------------------------------------------
\* Eras
\* ---------------------------------------------------------------------

\* In English: "From Alonzo, blocks list their phase-2-invalid
\* transactions, transactions carry collateral, and the block's execution
\* units are bounded."
\* Literally: "AlonzoOn is defined as: Era is a member of the set
\*   containing "Alonzo", "Conway" and "Dijkstra"."
AlonzoOn == Era \in {"Alonzo", "Conway", "Dijkstra"}

\* In English: "From Conway, a block's reference-script bytes are bounded."
\* Literally: "ConwayOn is defined as: Era is a member of the set
\*   containing "Conway" and "Dijkstra"."
ConwayOn == Era \in {"Conway", "Dijkstra"}

\* In English: "From protocol version 11, a transaction's reference scripts
\* are looked up among the earlier transactions' outputs too [R4]."
\* Literally: "Accumulates is defined as: PV is greater than or equal to 11."
Accumulates == PV >= 11

\* ---------------------------------------------------------------------
\* Blocks
\* ---------------------------------------------------------------------

\* In English: "A transaction is its spent input, collateral input,
\* reference input, whether its output carries a script, and its units."
\* Literally: "TxSpace is defined as the set of records whose in is a
\*   member of InChoices, coll a member of CollChoices, ref a member of
\*   RefChoices, script a member of ScriptChoices and ex a member of
\*   ExChoices."
TxSpace == [in : InChoices, coll : CollChoices, ref : RefChoices,
            script : ScriptChoices, ex : ExChoices]

\* In English: "Every list of up to MaxTxs transactions."
\* Literally: "TxLists is defined as the union of the sets of functions
\*   from 1 through k to TxSpace, for every k that is a member of 0
\*   through MaxTxs."
TxLists == UNION {[1..k -> TxSpace] : k \in 0..MaxTxs}

\* In English: "Every invalid_transactions list of up to MaxInvalidLen
\* zero-based indexes, each at most MaxTxs, so that one index is always
\* out of range. Lists may repeat or be out of order, as the wire allows."
\* Literally: "InvalidLists is defined as the union of the sets of
\*   functions from 1 through k to 0 through MaxTxs, for every k that is a
\*   member of 0 through MaxInvalidLen."
InvalidLists == UNION {[1..k -> 0..MaxTxs] : k \in 0..MaxInvalidLen}

\* In English: "Every block: its transactions, its invalid list, and its
\* header's declared size, body hash, witness count and protocol version."
\* Literally: "Blocks is defined as the set of records whose txs is a
\*   member of TxLists, invalid a member of InvalidLists, sizeOff a member
\*   of SizeOffs, hashOk a member of HashOks, witOff a member of WitOffs and
\*   hdrPV a member of HdrPVs."
Blocks == [txs : TxLists, invalid : InvalidLists, sizeOff : SizeOffs,
           hashOk : HashOks, witOff : WitOffs, hdrPV : HdrPVs]

\* ---------------------------------------------------------------------
\* Validity flags from the invalid list
\* ---------------------------------------------------------------------

\* In English: "k copies of v (none when k is not positive)."
\* Literally: "Rep of k and v is defined as: if k is less than or equal
\*   to 0 then the empty sequence, else the function that maps every j in
\*   1 through k to v."
Rep(k, v) == IF k <= 0 THEN <<>> ELSE [j \in 1..k |-> v]

\* The reference's alignedValidFlags, word for word [R7] 304-311.
\* In English: "Walk the list: before each index x put as many valid flags
\* as the gap from the previous index, then one invalid flag; at the end
\* put the n that remain (none if n has gone negative)."
\* Literally: "Aligned is defined recursively. Aligned of prev, n and xs
\*   is defined as: if xs equals the empty sequence then Rep of n and
\*   TRUE, else, letting x be the head of xs: Rep of x minus prev minus 1
\*   and TRUE, followed by the tuple of FALSE, followed by Aligned of x,
\*   n minus (x minus prev), and the tail of xs."
RECURSIVE Aligned(_, _, _)
Aligned(prev, n, xs) ==
    IF xs = <<>> THEN Rep(n, TRUE)
    ELSE LET x == Head(xs)
         IN  Rep(x - prev - 1, TRUE) \o <<FALSE>>
                \o Aligned(x, n - (x - prev), Tail(xs))

\* In English: "Transaction i's flag (TRUE: phase-2 valid). The decoder
\* zips the flags with the transactions, so flags past the last one are
\* dropped. Before Alonzo there is no list and every transaction is valid."
\* Literally: "RefFlag of b and i is defined as: letting a be Aligned of
\*   -1, the length of b's txs, and b's invalid: if AlonzoOn is not true
\*   then TRUE, else if i is less than or equal to the length of a then
\*   element i of a, else TRUE."
RefFlag(b, i) ==
    LET a == Aligned(-1, Len(b.txs), b.invalid)
    IN  IF ~AlonzoOn THEN TRUE
        ELSE IF i <= Len(a) THEN a[i] ELSE TRUE

\* gOuroboros' TransactionValidityFlags, step by step [G4]: an index at or
\* past n is clamped to n; then pad with valid flags and cut to n. The
\* "GoSkipRepeats" mutation ignores an index not above the one before.
\* In English: "Fold the list into flags the way the Go loop does."
\* Literally: "GoFold is defined recursively. GoFold of flags, prev, n and
\*   xs is defined as: if xs equals the empty sequence then flags, else,
\*   letting idx be (if the head of xs is less than n then the head of xs,
\*   else n): if Mutation equals "GoSkipRepeats" and idx is less than or
\*   equal to prev, then GoFold of flags, prev, n and the tail of xs, else
\*   GoFold of (flags followed by Rep of idx minus prev minus 1 and TRUE,
\*   followed by the tuple of FALSE), idx, n, and the tail of xs."
RECURSIVE GoFold(_, _, _, _)
GoFold(flags, prev, n, xs) ==
    IF xs = <<>> THEN flags
    ELSE LET idx == IF Head(xs) < n THEN Head(xs) ELSE n
         IN  IF Mutation = "GoSkipRepeats" /\ idx <= prev
             THEN GoFold(flags, prev, n, Tail(xs))
             ELSE GoFold(flags \o Rep(idx - prev - 1, TRUE) \o <<FALSE>>,
                         idx, n, Tail(xs))

\* In English: "Transaction i's flag as gOuroboros computes it."
\* Literally: "GoFlag of b and i is defined as: letting f be GoFold of the
\*   empty sequence, -1, the length of b's txs, and b's invalid: if
\*   AlonzoOn is not true then TRUE, else if i is less than or equal to the
\*   length of f then element i of f, else TRUE."
GoFlag(b, i) ==
    LET f == GoFold(<<>>, -1, Len(b.txs), b.invalid)
    IN  IF ~AlonzoOn THEN TRUE
        ELSE IF i <= Len(f) THEN f[i] ELSE TRUE

\* ---------------------------------------------------------------------
\* Outputs, inputs and reference scripts
\* ---------------------------------------------------------------------

\* In English: "The outputs before the block: the genesis outputs."
\* Literally: "Start is defined as the set containing the tuple of "g"
\*   and 0 and the tuple of "k" and 0."
Start == {<<"g", 0>>, <<"k", 0>>}

\* In English: "The output that transaction i adds: its output if it is
\* valid, its collateral return if not [R9]."
\* Literally: "OutOf of b, i and flag is defined as: if flag then the
\*   tuple of "o" and i, else the tuple of "r" and i."
OutOf(b, i, flag) == IF flag THEN <<"o", i>> ELSE <<"r", i>>

\* In English: "The output that a relative name c denotes for transaction
\* i: a genesis output, or the earlier transaction's output or return."
\* Literally: "Resolve of i and c is defined as: in the case c equals "g",
\*   the tuple of "g" and 0; in the case c equals "k", the tuple of "k" and
\*   0; in the case c equals "prev", the tuple of "o" and i minus 1; in the
\*   case c equals "prevret", the tuple of "r" and i minus 1."
Resolve(i, c) == CASE c = "g"       -> <<"g", 0>>
                 []   c = "k"       -> <<"k", 0>>
                 []   c = "prev"    -> <<"o", i - 1>>
                 []   c = "prevret" -> <<"r", i - 1>>

\* In English: "Every output transaction i names and needs to exist: its
\* spent input, and from Alonzo its collateral and reference input [R9]."
\* Literally: "Needs of b and i is defined as: letting t be element i of
\*   b's txs: the union of the set containing Resolve of i and t's in,
\*   (if AlonzoOn then the set containing Resolve of i and t's coll, else
\*   the empty set), and (if t's ref does not equal "none" then the set
\*   containing Resolve of i and t's ref, else the empty set)."
Needs(b, i) ==
    LET t == b.txs[i]
    IN  {Resolve(i, t.in)}
          \cup (IF AlonzoOn THEN {Resolve(i, t.coll)} ELSE {})
          \cup (IF t.ref /= "none" THEN {Resolve(i, t.ref)} ELSE {})

\* In English: "What transaction i removes: its spent input if valid, its
\* collateral if not."
\* Literally: "Spends of b, i and flag is defined as: if flag then the set
\*   containing Resolve of i and element i of b's txs' in, else the set
\*   containing Resolve of i and element i of b's txs' coll."
Spends(b, i, flag) ==
    IF flag THEN {Resolve(i, b.txs[i].in)} ELSE {Resolve(i, b.txs[i].coll)}

\* In English: "The script size carried by output id: 1 at "g", the
\* transaction's choice at a transaction output, 0 elsewhere."
\* Literally: "ScriptAt of b and id is defined as: if id equals the tuple
\*   of "g" and 0 then 1, else if element 1 of id equals "o" and element 2
\*   of id is a member of 1 through the length of b's txs then element 2
\*   of id of b's txs' script, else 0."
ScriptAt(b, id) ==
    IF id = <<"g", 0>> THEN 1
    ELSE IF id[1] = "o" /\ id[2] \in 1..Len(b.txs)
         THEN b.txs[id[2]].script ELSE 0

\* In English: "Transaction i's reference-script bytes looked up in the
\* set S: its spent input and its reference input, counted once if they
\* are the same output; a name missing from S counts nothing [R5]."
\* Literally: "RefBytes of b, i and S is defined as: letting ids be the
\*   union of the set containing Resolve of i and element i of b's txs' in
\*   and (if its ref does not equal "none" then the set containing Resolve
\*   of i and its ref, else the empty set), and In of x be (if x is a member
\*   of S then ScriptAt of b and x, else 0): if the number of members of
\*   ids equals 1 then In of the one member of ids, else the sum of In of
\*   each of the two."
RefBytes(b, i, S) ==
    LET t   == b.txs[i]
        ids == {Resolve(i, t.in)}
                 \cup (IF t.ref /= "none" THEN {Resolve(i, t.ref)} ELSE {})
        In(x) == IF x \in S THEN ScriptAt(b, x) ELSE 0
    IN  IF Cardinality(ids) = 1
        THEN In(CHOOSE x \in ids : TRUE)
        ELSE In(Resolve(i, t.in)) + In(Resolve(i, t.ref))

\* In English: "The sum of f over the first n positions."
\* Literally: "SumTo is defined recursively. SumTo of f and n is defined
\*   as: if n equals 0 then 0, else f of n plus SumTo of f and n minus 1."
RECURSIVE SumTo(_, _)
SumTo(f, n) == IF n = 0 THEN 0 ELSE f[n] + SumTo(f, n - 1)

\* ---------------------------------------------------------------------
\* The reference, stated declaratively
\* ---------------------------------------------------------------------

\* In English: "The block's real body size: one unit per transaction plus
\* one for the empty collections."
\* Literally: "Actual of b is defined as 1 plus the length of b's txs."
Actual(b) == 1 + Len(b.txs)

\* In English: "The size the header declares."
\* Literally: "Declared of b is defined as: in the case b's sizeOff equals
\*   "exact", Actual of b; in the case it equals "less", Actual of b minus
\*   1; in the case it equals "more", Actual of b plus 1."
Declared(b) == CASE b.sizeOff = "exact" -> Actual(b)
               []   b.sizeOff = "less"  -> Actual(b) - 1
               []   b.sizeOff = "more"  -> Actual(b) + 1

\* In English: "The body decodes: one witness set per body, and every
\* invalid index names a transaction of the block [R7]."
\* Literally: "DecodeOk of b is defined as: b's witOff equals "same", and
\*   for all j in the domain of b's invalid, element j of b's invalid is
\*   less than the length of b's txs."
DecodeOk(b) ==
    /\ b.witOff = "same"
    /\ \A j \in DOMAIN b.invalid : b.invalid[j] < Len(b.txs)

\* In English: "The declared size is the real size [R1], and within the
\* maximum [R8]."
\* Literally: "SizeOk of b is defined as: Declared of b equals Actual of
\*   b, and Declared of b is less than or equal to MaxBody."
SizeOk(b) == Declared(b) = Actual(b) /\ Declared(b) <= MaxBody

\* In English: "The header's protocol version is allowed: in Conway, on
\* mainnet, at most one above the version in force [R4]; in Dijkstra, at
\* least the version in force [R6]; no rule before Conway."
\* Literally: "PVOk of b is defined as: in the case Era equals "Conway",
\*   if Mainnet then b's hdrPV is less than or equal to PV plus 1; in the
\*   case Era equals "Dijkstra", b's hdrPV is greater than or equal to PV;
\*   in every other case, TRUE."
PVOk(b) == CASE Era = "Conway"   -> (Mainnet => b.hdrPV <= PV + 1)
           []   Era = "Dijkstra" -> b.hdrPV >= PV
           []   OTHER            -> TRUE

\* In English: "What the earlier transactions left: the start, plus what
\* each earlier transaction added, minus what each removed. Every output
\* is added at most once, so the set difference is exact."
\* Literally: "Avail of b and i is defined as: the union of Start and the
\*   set of OutOf of b, j and RefFlag of b and j, for every j that is a
\*   member of 1 through i minus 1, without the members of the union of
\*   the sets Spends of b, j and RefFlag of b and j, for every j that is a
\*   member of 1 through i minus 1."
Avail(b, i) ==
    (Start \cup {OutOf(b, j, RefFlag(b, j)) : j \in 1..(i - 1)})
      \ UNION {Spends(b, j, RefFlag(b, j)) : j \in 1..(i - 1)}

\* In English: "Every transaction finds what it names among what the
\* earlier ones left [R2]."
\* Literally: "LedgerOk of b is defined as: for all i in 1 through the
\*   length of b's txs, Needs of b and i is a subset of Avail of b and i."
LedgerOk(b) == \A i \in 1..Len(b.txs) : Needs(b, i) \subseteq Avail(b, i)

\* In English: "Where transaction i's reference scripts are looked up: the
\* start through version 10; from 11, the start plus every earlier
\* transaction's output or collateral return, spent or not [R4]."
\* Literally: "MeasureSet of b and i is defined as: if Accumulates then
\*   the union of Start and the set of OutOf of b, j and RefFlag of b and
\*   j, for every j that is a member of 1 through i minus 1, else Start."
MeasureSet(b, i) ==
    IF Accumulates
    THEN Start \cup {OutOf(b, j, RefFlag(b, j)) : j \in 1..(i - 1)}
    ELSE Start

\* In English: "The block's reference-script bytes."
\* Literally: "RefTotal of b is defined as SumTo of the function that maps
\*   every i in 1 through the length of b's txs to RefBytes of b, i and
\*   MeasureSet of b and i, and the length of b's txs."
RefTotal(b) ==
    SumTo([i \in 1..Len(b.txs) |-> RefBytes(b, i, MeasureSet(b, i))],
          Len(b.txs))

\* In English: "The block's execution units: every transaction's, valid or
\* not [R3]."
\* Literally: "ExTotal of b is defined as SumTo of the function that maps
\*   every i in 1 through the length of b's txs to element i of b's txs'
\*   ex, and the length of b's txs."
ExTotal(b) == SumTo([i \in 1..Len(b.txs) |-> b.txs[i].ex], Len(b.txs))

\* In English: "The block's totals are within their maximums, in the eras
\* that bound them."
\* Literally: "TotalsOk of b is defined as: if AlonzoOn then ExTotal of b
\*   is less than or equal to MaxEx, and if ConwayOn then RefTotal of b is
\*   less than or equal to MaxRef."
TotalsOk(b) ==
    /\ AlonzoOn => ExTotal(b) <= MaxEx
    /\ ConwayOn => RefTotal(b) <= MaxRef

\* In English: "The reference accepts block b."
\* Literally: "SpecAccepts of b is defined as: DecodeOk of b, and SizeOk
\*   of b, and b's hashOk, and PVOk of b, and LedgerOk of b, and TotalsOk
\*   of b."
SpecAccepts(b) ==
    /\ DecodeOk(b) /\ SizeOk(b) /\ b.hashOk /\ PVOk(b)
    /\ LedgerOk(b) /\ TotalsOk(b)

\* ---------------------------------------------------------------------
\* gOuroboros, restated from its code
\* ---------------------------------------------------------------------

\* In English: "gOuroboros' view of what the earlier transactions left,
\* using its own flags [G3][G4]."
\* Literally: "GoAvail of b and i is defined as: the union of Start and
\*   the set of OutOf of b, j and GoFlag of b and j, for every j in 1
\*   through i minus 1, without the members of the union of the sets
\*   Spends of b, j and GoFlag of b and j, for every j in 1 through i
\*   minus 1."
GoAvail(b, i) ==
    (Start \cup {OutOf(b, j, GoFlag(b, j)) : j \in 1..(i - 1)})
      \ UNION {Spends(b, j, GoFlag(b, j)) : j \in 1..(i - 1)}

\* In English: "gOuroboros accepts block b: the decoder's checks [G4], the
\* declared size, the maximum size unless the maximum is 0 [G1], the hash,
\* the protocol-version rules it has [G6][G7], each transaction in order
\* [G3], and the totals [G2][G5]."
\* Literally: "GoAccepts of b is defined as: DecodeOk of b, and Declared
\*   of b equals Actual of b, and (MaxBody equals 0 or Actual of b is less
\*   than or equal to MaxBody), and b's hashOk, and (if Era equals
\*   "Conway" and GoFixed and Mainnet then b's hdrPV is less than or equal
\*   to PV plus 1), and (if Era equals "Dijkstra" then b's hdrPV is greater
\*   than or equal to PV), and for all i in 1 through the length of b's
\*   txs, Needs of b and i is a subset of GoAvail of b and i, and TotalsOk
\*   of b."
GoAccepts(b) ==
    /\ DecodeOk(b)
    /\ Declared(b) = Actual(b)
    /\ MaxBody = 0 \/ Actual(b) <= MaxBody
    /\ b.hashOk
    /\ (Era = "Conway" /\ GoFixed /\ Mainnet) => b.hdrPV <= PV + 1
    /\ Era = "Dijkstra" => b.hdrPV >= PV
    /\ \A i \in 1..Len(b.txs) : Needs(b, i) \subseteq GoAvail(b, i)
    /\ TotalsOk(b)

\* ---------------------------------------------------------------------
\* The reference, step by step
\* ---------------------------------------------------------------------

VARIABLES
    blk,       \* the block being checked
    phase,     \* "envelope", "ledgers", "totals", "accepted", "rejected"
    i,         \* the next transaction to apply (1-based)
    utxo,      \* the UTxO the transactions so far left
    measured,  \* where the next reference scripts are looked up [R4]
    refSum,    \* reference-script bytes so far
    why        \* why the block was rejected ("" while not rejected)

\* In English: "Every variable, for UNCHANGED and the stuttering step."
\* Literally: "vars is defined as the tuple of blk, phase, i, utxo,
\*   measured, refSum and why."
vars == <<blk, phase, i, utxo, measured, refSum, why>>

\* In English: "Transaction i's flag as the reference step uses it; the
\* "NoIndexRange" mutation lets an out-of-range list through decoding."
\* Literally: "Flag of n is defined as RefFlag of blk and n."
Flag(n) == RefFlag(blk, n)

\* In English: "Any block, before any check."
\* Literally: "Init is defined as: blk is a member of Blocks, and phase
\*   equals "envelope", and i equals 1, and utxo equals Start, and measured
\*   equals Start, and refSum equals 0, and why equals the empty string."
Init ==
    /\ blk \in Blocks
    /\ phase = "envelope"
    /\ i = 1
    /\ utxo = Start
    /\ measured = Start
    /\ refSum = 0
    /\ why = ""

\* In English: "The first failed envelope check, or "" if none failed.
\* Each mutation removes one check."
\* Literally: "EnvelopeFailure is defined as: in the case DecodeOk of blk
\*   is not true and Mutation does not equal "NoIndexRange", "Decode"; in
\*   the case blk's witOff does not equal "same", "Decode"; in the case
\*   SizeOk of blk is not true and Mutation does not equal "NoSizeCheck",
\*   "Size"; in the case blk's hashOk is not true and Mutation does not
\*   equal "NoHashCheck", "Hash"; in the case PVOk of blk is not true and
\*   Mutation does not equal "NoProtVerCheck", "ProtVer"; in every other
\*   case, the empty string."
EnvelopeFailure ==
    CASE ~DecodeOk(blk) /\ Mutation /= "NoIndexRange" -> "Decode"
    []   blk.witOff /= "same"                         -> "Decode"
    []   ~SizeOk(blk) /\ Mutation /= "NoSizeCheck"    -> "Size"
    []   ~blk.hashOk /\ Mutation /= "NoHashCheck"     -> "Hash"
    []   ~PVOk(blk) /\ Mutation /= "NoProtVerCheck"   -> "ProtVer"
    []   OTHER                                        -> ""

\* In English: "Check the envelope [R1][R4][R6][R7][R8]."
\* Literally: "Envelope is defined as: phase equals "envelope", and if
\*   EnvelopeFailure equals the empty string then phase in the next state
\*   equals "ledgers" and why is unchanged, else phase in the next state
\*   equals "rejected" and why in the next state equals EnvelopeFailure;
\*   and blk, i, utxo, measured and refSum are unchanged."
Envelope ==
    /\ phase = "envelope"
    /\ IF EnvelopeFailure = ""
       THEN phase' = "ledgers" /\ UNCHANGED why
       ELSE phase' = "rejected" /\ why' = EnvelopeFailure
    /\ UNCHANGED <<blk, i, utxo, measured, refSum>>

\* In English: "Where transaction i is checked: the UTxO the earlier ones
\* left; the "LedgerAgainstStart" mutation checks every one against the
\* start."
\* Literally: "CheckSet is defined as: if Mutation equals
\*   "LedgerAgainstStart" then Start, else utxo."
CheckSet == IF Mutation = "LedgerAgainstStart" THEN Start ELSE utxo

\* In English: "What transaction i removes; the "InvalidSpendsInputs"
\* mutation makes an invalid one spend its input too."
\* Literally: "Removed is defined as: if Mutation equals
\*   "InvalidSpendsInputs" and Flag of i is not true then the union of
\*   Spends of blk, i and FALSE and Spends of blk, i and TRUE, else Spends
\*   of blk, i and Flag of i."
Removed ==
    IF Mutation = "InvalidSpendsInputs" /\ ~Flag(i)
    THEN Spends(blk, i, FALSE) \cup Spends(blk, i, TRUE)
    ELSE Spends(blk, i, Flag(i))

\* In English: "Where transaction i's reference scripts are looked up; the
\* "RefStartAlways" mutation always uses the start."
\* Literally: "LookIn is defined as: if Mutation equals "RefStartAlways"
\*   then Start, else measured."
LookIn == IF Mutation = "RefStartAlways" THEN Start ELSE measured

\* In English: "Apply transaction i, or reject the block if it names an
\* output that is not there [R2][R9]."
\* Literally: "ApplyTx is defined as: phase equals "ledgers", and i is
\*   less than or equal to the length of blk's txs, and if Needs of blk and
\*   i is a subset of CheckSet then utxo in the next state equals the union
\*   of (utxo without the members of Removed) and the set containing OutOf
\*   of blk, i and Flag of i, and measured in the next state equals (if
\*   Accumulates then the union of measured and that set, else measured),
\*   and refSum in the next state equals refSum plus RefBytes of blk, i and
\*   LookIn, and i in the next state equals i plus 1, and phase and why
\*   are unchanged; else phase in the next state equals "rejected" and why
\*   in the next state equals "Ledgers" and utxo, measured, refSum and i
\*   are unchanged; and blk is unchanged."
ApplyTx ==
    /\ phase = "ledgers"
    /\ i <= Len(blk.txs)
    /\ IF Needs(blk, i) \subseteq CheckSet
       THEN /\ utxo' = (utxo \ Removed) \cup {OutOf(blk, i, Flag(i))}
            /\ measured' = IF Accumulates
                           THEN measured \cup {OutOf(blk, i, Flag(i))}
                           ELSE measured
            /\ refSum' = refSum + RefBytes(blk, i, LookIn)
            /\ i' = i + 1
            /\ UNCHANGED <<phase, why>>
       ELSE /\ phase' = "rejected" /\ why' = "Ledgers"
            /\ UNCHANGED <<utxo, measured, refSum, i>>
    /\ UNCHANGED blk

\* In English: "The block's units as the reference sums them; the
\* "ExValidOnly" mutation leaves out invalid transactions."
\* Literally: "ExSum is defined as: if Mutation equals "ExValidOnly" then
\*   SumTo of the function that maps every n in 1 through the length of
\*   blk's txs to (if Flag of n then element n of blk's txs' ex, else 0),
\*   and the length of blk's txs; else ExTotal of blk."
ExSum ==
    IF Mutation = "ExValidOnly"
    THEN SumTo([n \in 1..Len(blk.txs) |->
                  IF Flag(n) THEN blk.txs[n].ex ELSE 0], Len(blk.txs))
    ELSE ExTotal(blk)

\* In English: "After the last transaction, check the totals [R3][R4]."
\* Literally: "Totals is defined as: phase equals "ledgers", and i
\*   equals the length of blk's txs plus 1, and in the case AlonzoOn and
\*   ExSum is greater than MaxEx, phase in the next state equals
\*   "rejected" and why in the next state equals "ExUnits"; in the case
\*   ConwayOn and refSum is greater than MaxRef, phase in the next state
\*   equals "rejected" and why in the next state equals "RefScripts"; in
\*   every other case, phase in the next state equals "accepted" and why
\*   is unchanged; and blk, i, utxo, measured and refSum are unchanged."
Totals ==
    /\ phase = "ledgers"
    /\ i = Len(blk.txs) + 1
    /\ CASE AlonzoOn /\ ExSum > MaxEx ->
              phase' = "rejected" /\ why' = "ExUnits"
       []   ConwayOn /\ refSum > MaxRef ->
              phase' = "rejected" /\ why' = "RefScripts"
       []   OTHER -> phase' = "accepted" /\ UNCHANGED why
    /\ UNCHANGED <<blk, i, utxo, measured, refSum>>

\* In English: "A decided block stays decided."
\* Literally: "Done is defined as: phase is a member of the set containing
\*   "accepted" and "rejected", and vars is unchanged."
Done == phase \in {"accepted", "rejected"} /\ UNCHANGED vars

\* In English: "Each step checks the envelope, applies a transaction,
\* checks the totals, or keeps a decided block decided."
\* Literally: "Next is defined as: Envelope or ApplyTx or Totals or Done."
Next == Envelope \/ ApplyTx \/ Totals \/ Done

\* In English: "Start with any block and take steps."
\* Literally: "Spec is defined as: Init, and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------
\* The questions
\* ---------------------------------------------------------------------

\* In English: "The step-by-step reference accepts only blocks the
\* declarative rules accept."
\* Literally: "Sound is defined as: if phase equals "accepted", then
\*   SpecAccepts of blk."
Sound == phase = "accepted" => SpecAccepts(blk)

\* In English: "It rejects only blocks the declarative rules reject."
\* Literally: "Complete is defined as: if phase equals "rejected", then
\*   SpecAccepts of blk is not true."
Complete == phase = "rejected" => ~SpecAccepts(blk)

\* In English: "While transactions are applied, the UTxO is exactly what
\* the declarative rules say the earlier ones left: in particular an
\* invalid transaction removed only its collateral and added only its
\* return."
\* Literally: "UtxoMatches is defined as: if phase is a member of the set
\*   containing "ledgers" and "accepted", then utxo equals Avail of blk
\*   and i."
UtxoMatches == phase \in {"ledgers", "accepted"} => utxo = Avail(blk, i)

\* In English: "gOuroboros' flags are the reference's, for every decodable
\* list."
\* Literally: "FlagsAgree is defined as: if DecodeOk of blk, then for all
\*   n in 1 through the length of blk's txs, GoFlag of blk and n equals
\*   RefFlag of blk and n."
FlagsAgree ==
    DecodeOk(blk) =>
        \A n \in 1..Len(blk.txs) : GoFlag(blk, n) = RefFlag(blk, n)

\* In English: "Once the reference decides, gOuroboros decides the same."
\* Literally: "GoAgrees is defined as: if phase is a member of the set
\*   containing "accepted" and "rejected", then GoAccepts of blk if and
\*   only if phase equals "accepted"."
GoAgrees ==
    phase \in {"accepted", "rejected"} =>
        (GoAccepts(blk) <=> phase = "accepted")

\* ---------------------------------------------------------------------
\* Reachability probes: each is expected to be violated
\* ---------------------------------------------------------------------

\* In English: "No accepted block spends an output made earlier in it."
\* Literally: "ProbeNoChainedSpend is defined as: it is not true that
\*   phase equals "accepted" and there exists an n in 1 through the length
\*   of blk's txs such that element n of blk's txs' in equals "prev"."
ProbeNoChainedSpend ==
    ~(phase = "accepted" /\ \E n \in 1..Len(blk.txs) : blk.txs[n].in = "prev")

\* In English: "No accepted block holds an invalid transaction."
\* Literally: "ProbeNoInvalidAccepted is defined as: it is not true that
\*   phase equals "accepted" and there exists an n in 1 through the length
\*   of blk's txs such that Flag of n is not true."
ProbeNoInvalidAccepted ==
    ~(phase = "accepted" /\ \E n \in 1..Len(blk.txs) : ~Flag(n))

\* In English: "No accepted block has an invalid list that is out of
\* order or repeats an index."
\* Literally: "ProbeNoUnorderedList is defined as: it is not true that
\*   phase equals "accepted" and there exist j and m in the domain of
\*   blk's invalid such that j is less than m and element j of blk's
\*   invalid is greater than or equal to element m of blk's invalid."
ProbeNoUnorderedList ==
    ~(phase = "accepted" /\
      \E j, m \in DOMAIN blk.invalid :
          j < m /\ blk.invalid[j] >= blk.invalid[m])

\* In English: "No block is rejected for its reference scripts that the
\* start-only measure would have let through (version 11 counts a script
\* made earlier in the block)."
\* Literally: "ProbeNoAccumulatedReject is defined as: it is not true
\*   that why equals "RefScripts" and SumTo of the function that maps
\*   every n in 1 through the length of blk's txs to RefBytes of blk, n
\*   and Start, and the length of blk's txs, is less than or equal to
\*   MaxRef."
ProbeNoAccumulatedReject ==
    ~(why = "RefScripts" /\
      SumTo([n \in 1..Len(blk.txs) |-> RefBytes(blk, n, Start)],
            Len(blk.txs)) <= MaxRef)

\* In English: "No block is rejected for its execution units."
\* Literally: "ProbeNoExReject is defined as: why does not equal
\*   "ExUnits"."
ProbeNoExReject == why /= "ExUnits"

\* In English: "No block is rejected for its header's protocol version."
\* Literally: "ProbeNoProtVerReject is defined as: why does not equal
\*   "ProtVer"."
ProbeNoProtVerReject == why /= "ProtVer"
=============================================================================
