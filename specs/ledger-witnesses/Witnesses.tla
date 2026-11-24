----------------------------- MODULE Witnesses -----------------------------
(***************************************************************************)
(* The UTXOW witness rules of every era from Shelley to Dijkstra, at a     *)
(* small abstract scale, and gOuroboros' decisions for the same            *)
(* transactions.                                                           *)
(*                                                                         *)
(* A transaction needs some key witnesses and some scripts, and it         *)
(* supplies witnesses, scripts, redeemers and datums. The model says which *)
(* of them are needed and whether they are supplied; it does not do        *)
(* signature or hash arithmetic. A key is a name: "v1" and "v2" are vkeys, *)
(* whose hash a vkey witness supplies, and "b" is a bootstrap key, whose   *)
(* hash (an address root) a bootstrap witness supplies.                   *)
(*                                                                         *)
(* The state is the environment of a table cell: which keys have a        *)
(* witness, and the transaction's validity bounds. TableSpec walks every   *)
(* environment, and in each one the invariant GoAgrees checks, over five   *)
(* families of transactions, that gOuroboros accepts exactly what the      *)
(* reference accepts:                                                      *)
(*   1. needed key witnesses (inputs, collateral, withdrawals,             *)
(*      certificates, pool owners, required signers, voters, genesis       *)
(*      delegation, MIR quorum, update proposals) and a badly signed one;  *)
(*   2. native scripts: Shelley multisig and Allegra-on timelocks;         *)
(*   3. needed versus supplied scripts (witness set, reference input) and  *)
(*      redeemers;                                                         *)
(*   4. required and supplemental datums, inline datums;                   *)
(*   5. the script integrity hash's language views.                        *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd; the full      *)
(* table is in specs/ledger-witnesses/README.md.                        *)
(*   [R1] eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Utxow.hs      *)
(*        281-338 transitionRulesUTXOW; 377-399 failed native scripts,     *)
(*        missing and extraneous scripts; 402-421 validateVerifiedWits;    *)
(*        423-436 validateNeededWitnesses; 460-490 MIR genesis quorum.     *)
(*   [R2] eras/shelley/impl/src/Cardano/Ledger/Shelley/UTxO.hs 191-277:    *)
(*        witsVKeyNeededGenDelegs, getShelleyWitsVKeyNeededNoGovWith.      *)
(*   [R3] libs/cardano-ledger-core/src/Cardano/Ledger/Core.hs 545-552:     *)
(*        keyHashWitnessesTxWits, vkey hashes and bootstrap roots.         *)
(*   [R4] eras/shelley/impl/src/Cardano/Ledger/Shelley/Scripts.hs 307-334  *)
(*        evalMultiSig over vkey witnesses only.                           *)
(*   [R5] eras/allegra/impl/src/Cardano/Ledger/Allegra/Scripts.hs 492-521  *)
(*        evalTimelock; Allegra/Tx.hs 111-116 vkey witnesses only.         *)
(*   [R6] eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Rules/Utxow.hs        *)
(*        222-247 missingRequiredDatums; 251-275 hasExactSetOfRedeemers;   *)
(*        278-300 checkScriptIntegrityHash; 306-385 alonzoStyleWitness.    *)
(*   [R7] eras/alonzo/impl/src/Cardano/Ledger/Alonzo/UTxO.hs 246-311:      *)
(*        supplemental datums (outputs), required spending datums;         *)
(*        444-459 getAlonzoWitsVKeyNeeded (required signers).              *)
(*   [R8] eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Tx.hs 463-482         *)
(*        mkScriptIntegrity; Alonzo.hs 168-169 languages of the needed     *)
(*        Plutus scripts.                                                  *)
(*   [R9] eras/babbage/impl/src/Cardano/Ledger/Babbage/Rules/Utxow.hs      *)
(*        206-245 babbageMissingScripts, validateFailedBabbageScripts;     *)
(*        294-317 MIR; 319-401 babbageUtxowTransition (Conway uses it,     *)
(*        Conway/Rules/Utxow.hs 209).                                      *)
(*   [R10] eras/babbage/impl/src/Cardano/Ledger/Babbage/UTxO.hs 92-102     *)
(*        supplemental datums (outputs and reference inputs), 154-173     *)
(*        scripts provided by reference; Babbage/TxInfo.hs 256-262 a       *)
(*        PlutusV1 context cannot hold inline datums or, in Babbage,       *)
(*        reference inputs.                                                *)
(*   [R11] eras/conway/impl/src/Cardano/Ledger/Conway/UTxO.hs 189-221      *)
(*        getConwayWitsVKeyNeededWith: required signers and voters.        *)
(*   [R12] eras/dijkstra/impl/src/Cardano/Ledger/Dijkstra/Rules/Utxow.hs   *)
(*        510-525 pool owners need not witness a phase-2-invalid           *)
(*        transaction; Dijkstra/UTxO.hs 171, 177-196 nor a re-registration *)
(*        that changes only the BLS key.                                   *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 756a9a89):              *)
(*   [G1] ledger/common/rules.go 941-1030 ValidateRequiredVKeyWitnesses-   *)
(*        WithPoolOwners; 762-893 certificate credentials.                 *)
(*   [G2] ledger/common/verify.go 125-171 ValidateInputVKeyWitnesses;      *)
(*        288-321 UtxoValidateSignatures; ledger/common/witness.go 58-72   *)
(*        witnessKeyHashes, 99-178 ValidateCollateralVKeyWitnesses.        *)
(*   [G3] ledger/common/rules.go 1040-1088 ValidateMIRGenesisQuorum,       *)
(*        1093-1135 ValidateClassicProtocolParameterUpdates: both counted  *)
(*        vkey witnesses only; fixed on branch                             *)
(*        fix/ledger-witnesses-genesis-bootstrap.                          *)
(*   [G4] ledger/common/script.go 1272-1320, 1543-1610 native scripts;     *)
(*        ledger/common/script/native.go 40-150 (Babbage on).              *)
(*   [G5] ledger/common/rules.go 1356-1633 script requirements, 1671-1738  *)
(*        ValidateScriptWitnesses, 1762-1794 ValidateExactExtraneous-      *)
(*        Redeemers, 2068-2160 ValidateRedeemerAndScriptWitnesses.         *)
(*   [G6] ledger/common/rules.go 1796-1995 required and supplemental       *)
(*        datums; ledger/babbage/rules.go 431-495 PlutusV1 restrictions.   *)
(*   [G7] ledger/{alonzo,babbage,conway}/rules.go UtxoValidateScriptData-  *)
(*        Hash: languages of the needed Plutus scripts.                    *)
(*   [G8] ledger/dijkstra/rules.go 1749-1785 pool owner exemption.         *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the   *)
(* README section "Reading a formula literally".                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    Era,       \* "Shelley", "Allegra", "Mary", "Alonzo", "Babbage",
               \* "Conway" or "Dijkstra"
    Mutation   \* "none", or one deliberate mistake (see the README)

\* In English: the era's position in the order, so "from Alonzo on" can be
\* written AtLeast("Alonzo").
\* Literally: "EraIdx of e is defined as: in the case e equals "Shelley", 1;
\*   in the case e equals "Allegra", 2; in the case e equals "Mary", 3; in the
\*   case e equals "Alonzo", 4; in the case e equals "Babbage", 5; in the
\*   case e equals "Conway", 6; in every other case, 7."
EraIdx(e) == CASE e = "Shelley" -> 1 [] e = "Allegra" -> 2 [] e = "Mary" -> 3
               [] e = "Alonzo" -> 4 [] e = "Babbage" -> 5 [] e = "Conway" -> 6
               [] OTHER -> 7
\* In English: the model's era is e or a later one.
\* Literally: "AtLeast of e is defined as: EraIdx of Era is greater than or
\*   equal to EraIdx of e."
AtLeast(e) == EraIdx(Era) >= EraIdx(e)

\* In English: the three keys; the first two are vkeys.
\* Literally: "Keys is defined as the set containing "v1", "v2" and "b"."
Keys  == {"v1", "v2", "b"}
\* In English: the keys a vkey witness supplies.
\* Literally: "VKeys is defined as the set containing "v1" and "v2"."
VKeys == {"v1", "v2"}
\* In English: a validity bound that is absent.
\* Literally: "NoBound is defined as negative 1."
NoBound == -1

VARIABLES
    wits,  \* the keys whose witness the transaction carries
    lo,    \* the validity interval's lower bound, or NoBound
    hi     \* the validity interval's upper bound, or NoBound

\* Literally: "vars is defined as the tuple of wits, lo and hi."
vars == <<wits, lo, hi>>

-----------------------------------------------------------------------------
(* Family 1: needed key witnesses.                                         *)

\* In English: the things that can need a key witness in this era. "in" is
\* a spent input locked by the key (a Byron address for "b"), "coll" a
\* collateral input, "wdrl" a withdrawal, "deleg" a stake delegation,
\* "reg0" a registration without a deposit (which needs no witness),
\* "pool" a pool registration's operator, "owner" a pool registration with
\* operator v2 and the key as owner, "retire" a pool retirement, "signer" a
\* required signer, "voter" a DRep voter, "gdeleg" a genesis key
\* delegation, "mir" an instantaneous-rewards certificate whose one
\* genesis delegate is the key (quorum 1), and "ppup" an update proposal
\* from a genesis key delegated to the key [R2][R7][R11].
\* Literally: "KeySources is defined as the union of the set containing
\*   "in", "wdrl", "deleg", "reg0", "pool", "owner" and "retire"; (if AtLeast
\*   of "Alonzo" then the set containing "coll", else the empty set); (if
\*   AtLeast of "Alonzo" and Era does not equal "Dijkstra" then the set
\*   containing "signer", else the empty set); and (if AtLeast of "Conway"
\*   then the set containing "voter", else the set containing "gdeleg", "mir"
\*   and "ppup")."
KeySources ==
    {"in", "wdrl", "deleg", "reg0", "pool", "owner", "retire"}
    \cup (IF AtLeast("Alonzo") THEN {"coll"} ELSE {})
    \cup (IF AtLeast("Alonzo") /\ Era # "Dijkstra" THEN {"signer"} ELSE {})
    \cup (IF AtLeast("Conway") THEN {"voter"} ELSE {"gdeleg", "mir", "ppup"})

\* In English: a key cell: a source, the key it names (v1 or b), whether
\* an extra v2 witness with a wrong signature is attached, and whether the
\* transaction is phase-2 valid (varied only in Dijkstra).
\* Literally: "KeyCells is defined as the set of records whose field src is a
\*   member of KeySources, field key is a member of the set containing "v1"
\*   and "b", field bad is a member of BOOLEAN, and field valid is a member
\*   of (if Era equals "Dijkstra" then BOOLEAN, else the set containing
\*   TRUE)."
KeyCells == [src : KeySources, key : {"v1", "b"}, bad : BOOLEAN,
             valid : IF Era = "Dijkstra" THEN BOOLEAN ELSE {TRUE}]

\* In English: the keys a cell needs, witsVKeyNeeded [R2][R7][R11]. A
\* tag-0 registration needs none. A pool registration needs its operator
\* (v2) and its owners, except that Dijkstra excuses the owners of a
\* phase-2-invalid transaction [R12]. Mutations drop a requirement.
\* Literally: "KeyNeeded of c is defined as: in the case c's src equals
\*   "reg0", the empty set; in the case c's src equals "wdrl" and Mutation
\*   equals "SpecIgnoreWdrl", the empty set; in the case c's src equals
\*   "owner", the union of the set containing "v2" and (if Era does not equal
\*   "Dijkstra" or c's valid then the set containing c's key, else the empty
\*   set); in every other case, the set containing c's key."
KeyNeeded(c) ==
    CASE c.src = "reg0" -> {}
      [] c.src = "wdrl" /\ Mutation = "SpecIgnoreWdrl" -> {}
      [] c.src = "owner" ->
           {"v2"} \cup (IF Era # "Dijkstra" \/ c.valid THEN {c.key} ELSE {})
      [] OTHER -> {c.key}

\* In English: the reference accepts a key cell when every needed key is
\* among the witness key hashes, vkey hashes and bootstrap roots alike [R3],
\* and every supplied signature verifies [R1] 402-421.
\* Literally: "SpecKeyAccepts of c is defined as: KeyNeeded of c is a subset
\*   of wits, and c's bad is not true."
SpecKeyAccepts(c) == KeyNeeded(c) \subseteq wits /\ ~c.bad

\* In English: the key hashes gOuroboros counts for a cell. The old code
\* counted only vkey witnesses towards the MIR quorum and the update
\* proposal's delegates [G3].
\* Literally: "GoKeyProvided of c is defined as: if Mutation equals
\*   "GoGenesisVkeyOnly" and c's src is a member of the set containing "mir"
\*   and "ppup", then the intersection of wits and VKeys, else wits."
GoKeyProvided(c) ==
    IF Mutation = "GoGenesisVkeyOnly" /\ c.src \in {"mir", "ppup"}
    THEN wits \cap VKeys ELSE wits

\* In English: the keys gOuroboros requires [G1]; the mutation
\* "GoOwnersAlways" drops Dijkstra's owner exemption.
\* Literally: "GoKeyNeeded of c is defined as: if Mutation equals
\*   "GoOwnersAlways" and c's src equals "owner", then the set containing "v2"
\*   and c's key, else KeyNeeded of c."
GoKeyNeeded(c) ==
    IF Mutation = "GoOwnersAlways" /\ c.src = "owner"
    THEN {"v2", c.key} ELSE KeyNeeded(c)

\* In English: gOuroboros accepts a key cell [G1][G2][G3].
\* Literally: "GoKeyAccepts of c is defined as: GoKeyNeeded of c is a subset
\*   of GoKeyProvided of c, and c's bad is not true."
GoKeyAccepts(c) == GoKeyNeeded(c) \subseteq GoKeyProvided(c) /\ ~c.bad

-----------------------------------------------------------------------------
(* Family 2: native scripts.                                               *)

\* In English: the leaves of a native script: a signature by a key, a
\* start slot (invalid before) and an expiry slot (invalid hereafter).
\* Shelley's multisig has signatures only [R4].
\* Literally: "Leaves is defined as the union of the set of records whose
\*   field op is "sig", field key is a member of Keys, and field slot is 0,
\*   and (if AtLeast of "Allegra" then the set of records whose field op is a
\*   member of the set containing "start" and "expire", field key is "v1",
\*   and field slot is a member of 0 through 2, else the empty set)."
Leaves ==
    [op : {"sig"}, key : Keys, slot : {0}]
    \cup (IF AtLeast("Allegra")
          THEN [op : {"start", "expire"}, key : {"v1"}, slot : 0..2]
          ELSE {})

\* In English: the leaf lists a script can combine: none, one, or two.
\* Literally: "Subs is defined as the union of the set containing the empty
\*   sequence, the set of the tuple of l for every l that is a member of
\*   Leaves, and the set of the tuple of l1 and l2 for every l1 that is a
\*   member of Leaves and every l2 that is a member of Leaves."
Subs == {<<>>} \cup {<<l>> : l \in Leaves}
        \cup {<<l1, l2>> : l1 \in Leaves, l2 \in Leaves}

\* In English: a script is "all", "any" or "atleast m" over a leaf list (a
\* leaf on its own is "all" over that leaf).
\* Literally: "Scripts is defined as the union of the set of records whose
\*   field op is o, field m is 0 and field subs is l, for every o that is a
\*   member of the set containing "all" and "any" and every l that is a member
\*   of Subs, and the set of records whose field op is "atleast", field m is
\*   n and field subs is l, for every n that is a member of 0 through 3 and
\*   every l that is a member of Subs."
Scripts ==
    {[op |-> o, m |-> 0, subs |-> l] : o \in {"all", "any"}, l \in Subs}
    \cup {[op |-> "atleast", m |-> n, subs |-> l] : n \in 0..3, l \in Subs}

\* In English: the reference evaluates a leaf [R4][R5]. A signature counts
\* only from a vkey witness: validateMultiSig and validateTimelock read the
\* vkey witnesses, never the bootstrap ones. A start slot needs a present
\* lower bound at or after it; an expiry needs a present upper bound at or
\* before it. The Spec and Go mutations change one of these readings.
\* Literally: "EvalLeaf of l, counted, startAbsentOk and expireExclusive is
\*   defined as: in the case l's op equals "sig", l's key is a member of the
\*   intersection of wits and counted; in the case l's op equals "start", if
\*   lo equals NoBound then startAbsentOk, else l's slot is less than or
\*   equal to lo; in every other case, hi does not equal NoBound, and if
\*   expireExclusive then hi is less than l's slot, else hi is less than or
\*   equal to l's slot."
EvalLeaf(l, counted, startAbsentOk, expireExclusive) ==
    CASE l.op = "sig" -> l.key \in wits \cap counted
      [] l.op = "start" ->
           IF lo = NoBound THEN startAbsentOk ELSE l.slot <= lo
      [] OTHER ->
           /\ hi # NoBound
           /\ IF expireExclusive THEN hi < l.slot ELSE hi <= l.slot

\* In English: how many of a script's leaves hold.
\* Literally: "Count of s, counted, a and x is defined as the number of members
\*   of the set of every i in 1 through the length of s's subs such that
\*   EvalLeaf of element i of s's subs, counted, a and x."
Count(s, counted, a, x) ==
    Cardinality({i \in 1..Len(s.subs) : EvalLeaf(s.subs[i], counted, a, x)})

\* In English: a script holds: "all" when every leaf holds, "any" when one
\* does, "atleast m" when m of them do [R4][R5].
\* Literally: "Eval of s, counted, a and x is defined as: in the case s's op
\*   equals "all", Count of s, counted, a, x equals the length of s's subs;
\*   in the case s's op equals "any", Count of s, counted, a, x is greater
\*   than 0; in every other case, Count of s, counted, a, x is greater than or
\*   equal to s's m."
Eval(s, counted, a, x) ==
    CASE s.op = "all" -> Count(s, counted, a, x) = Len(s.subs)
      [] s.op = "any" -> Count(s, counted, a, x) > 0
      [] OTHER -> Count(s, counted, a, x) >= s.m

\* In English: the reference accepts a transaction whose spent input is
\* locked by native script s, supplied in the witness set or by reference.
\* Literally: "SpecNativeAccepts of s is defined as Eval of s, VKeys,
\*   (Mutation equals "SpecStartAbsentOk"), and FALSE."
SpecNativeAccepts(s) == Eval(s, VKeys, Mutation = "SpecStartAbsentOk", FALSE)

\* In English: gOuroboros' evaluation [G4]; three mutations.
\* Literally: "GoNativeAccepts of s is defined as Eval of s, (if Mutation
\*   equals "GoNativeCountsBootstrap" then Keys, else VKeys), (Mutation equals
\*   "GoStartAbsentOk"), and (Mutation equals "GoExpireExclusive")."
GoNativeAccepts(s) ==
    Eval(s, IF Mutation = "GoNativeCountsBootstrap" THEN Keys ELSE VKeys,
         Mutation = "GoStartAbsentOk", Mutation = "GoExpireExclusive")

-----------------------------------------------------------------------------
(* Family 3: needed versus supplied scripts and redeemers.                 *)

\* In English: the purposes that can need a script in this era.
\* Literally: "Purposes is defined as the union of the set containing
\*   "spend", "wdrl" and "cert", (if AtLeast of "Mary" then the set containing
\*   "mint", else the empty set), and (if AtLeast of "Conway" then the set
\*   containing "vote", else the empty set)."
Purposes == {"spend", "wdrl", "cert"}
            \cup (IF AtLeast("Mary") THEN {"mint"} ELSE {})
            \cup (IF AtLeast("Conway") THEN {"vote"} ELSE {})

\* In English: a script cell: the purpose, whether its script is native or
\* Plutus, whether the script is in the witness set and whether a reference
\* input carries it, whether an unneeded script is supplied (in the witness
\* set or by reference), and the redeemer: none, at the purpose, or at the
\* key-locked input, which is no purpose.
\* Literally: "ScriptCells is defined as the set of records whose field
\*   purpose is a member of Purposes, field kind is a member of (if AtLeast of
\*   "Alonzo" then the set containing "native" and "plutus", else the set
\*   containing "native"), field wit is a member of BOOLEAN, field ref is a
\*   member of (if AtLeast of "Babbage" then BOOLEAN, else the set containing
\*   FALSE), field extra is a member of (if AtLeast of "Babbage" then the set
\*   containing "none", "wit" and "ref", else the set containing "none" and
\*   "wit"), and field rdmr is a member of (if AtLeast of "Alonzo" then the
\*   set containing "none", "purpose" and "stray", else the set containing
\*   "none")."
ScriptCells ==
    [purpose : Purposes,
     kind : IF AtLeast("Alonzo") THEN {"native", "plutus"} ELSE {"native"},
     wit : BOOLEAN,
     ref : IF AtLeast("Babbage") THEN BOOLEAN ELSE {FALSE},
     extra : IF AtLeast("Babbage") THEN {"none", "wit", "ref"}
             ELSE {"none", "wit"},
     rdmr : IF AtLeast("Alonzo") THEN {"none", "purpose", "stray"}
            ELSE {"none"}]

\* In English: the redeemers are exactly the needed Plutus purposes [R6]
\* 251-275: a Plutus script needs its redeemer, a native one has none, and
\* a redeemer at no purpose is extra.
\* Literally: "RedeemersExact of c is defined as: if c's kind equals
\*   "plutus" then c's rdmr equals "purpose", else c's rdmr equals "none"."
RedeemersExact(c) ==
    IF c.kind = "plutus" THEN c.rdmr = "purpose" ELSE c.rdmr = "none"

\* In English: the reference accepts a script cell [R1] 389-399, [R9]
\* 206-221: missing = needed - refs - wits must be empty, and extra = wits -
\* (needed - refs) must be empty, so a needed script supplied both ways is
\* extraneous, and an unneeded witness-set script is too; an unneeded
\* reference script is just data.
\* Literally: "SpecScriptAccepts of c is defined as: (c's wit or c's ref),
\*   and (c's wit and c's ref and Mutation does not equal "SpecRefAndWitOk")
\*   is not true, and c's extra does not equal "wit", and RedeemersExact of
\*   c."
SpecScriptAccepts(c) ==
    /\ c.wit \/ c.ref
    /\ ~(c.wit /\ c.ref /\ Mutation # "SpecRefAndWitOk")
    /\ c.extra # "wit"
    /\ RedeemersExact(c)

\* In English: gOuroboros' script and redeemer rules [G5]; two mutations.
\* Literally: "GoScriptAccepts of c is defined as: (c's wit or c's ref), and
\*   (c's wit and c's ref and Mutation does not equal "GoRefAndWitOk") is not
\*   true, and (c's extra does not equal "wit" or Mutation equals
\*   "GoExtraWitOk"), and RedeemersExact of c."
GoScriptAccepts(c) ==
    /\ c.wit \/ c.ref
    /\ ~(c.wit /\ c.ref /\ Mutation # "GoRefAndWitOk")
    /\ c.extra # "wit" \/ Mutation = "GoExtraWitOk"
    /\ RedeemersExact(c)

-----------------------------------------------------------------------------
(* Family 4: datums (Alonzo on).                                           *)

\* In English: the Plutus versions in this era (V2 from Babbage, V3 from
\* Conway).
\* Literally: "Versions is defined as the union of the set containing 1, (if
\*   AtLeast of "Babbage" then the set containing 2, else the empty set), and
\*   (if AtLeast of "Conway" then the set containing 3, else the empty set)."
Versions == {1} \cup (IF AtLeast("Babbage") THEN {2} ELSE {})
                \cup (IF AtLeast("Conway") THEN {3} ELSE {})

\* In English: a datum cell: the spent input's lock (a Plutus script of
\* some version, or a native script), its datum (none, a hash, or from
\* Babbage inline), and the witness datums: the input's ("in"), an
\* output's datum hash ("out"), a reference input's ("ref", from Babbage),
\* and a stray one.
\* Literally: "DatumCells is defined as the set of records whose field lock
\*   is a member of the set containing "plutus" and "native", field ver is a
\*   member of Versions, field datum is a member of (if AtLeast of "Babbage"
\*   then the set containing "none", "hash" and "inline", else the set
\*   containing "none" and "hash"), and field wd is a member of the set of
\*   subsets of (if AtLeast of "Babbage" then the set containing "in",
\*   "out", "ref" and "stray", else the set containing "in", "out" and
\*   "stray")."
DatumCells ==
    [lock : {"plutus", "native"}, ver : Versions,
     datum : IF AtLeast("Babbage") THEN {"none", "hash", "inline"}
             ELSE {"none", "hash"},
     wd : SUBSET (IF AtLeast("Babbage") THEN {"in", "out", "ref", "stray"}
                  ELSE {"in", "out", "stray"})]

\* In English: the witness datums a cell requires: the input's, when a
\* Plutus script locks it with a datum hash [R7] 280-311.
\* Literally: "DatumRequired of c is defined as: if c's lock equals "plutus"
\*   and c's datum equals "hash" then the set containing "in", else the empty
\*   set."
DatumRequired(c) ==
    IF c.lock = "plutus" /\ c.datum = "hash" THEN {"in"} ELSE {}

\* In English: the witness datums allowed besides the required ones: an
\* output's [R7] 246-255 and, from Babbage, a reference input's [R10]
\* 92-102. The mutation "SpecAnyDatumOk" allows a stray one;
\* "GoRefNotSupplemental" forgets the reference inputs.
\* Literally: "DatumAllowed of c, refOk and anyOk is defined as the union of
\*   DatumRequired of c, the set containing "out", (if AtLeast of "Babbage"
\*   and refOk then the set containing "ref", else the empty set), and (if
\*   anyOk then the set containing "stray", else the empty set)."
DatumAllowed(c, refOk, anyOk) ==
    DatumRequired(c) \cup {"out"}
    \cup (IF AtLeast("Babbage") /\ refOk THEN {"ref"} ELSE {})
    \cup (IF anyOk THEN {"stray"} ELSE {})

\* In English: a Plutus V1 or V2 input with no datum cannot be spent; V3
\* needs none (CIP-69) [R7] 297-301.
\* Literally: "Unspendable of c and v3From is defined as: c's lock equals
\*   "plutus" and c's datum equals "none" and c's ver is less than v3From."
Unspendable(c, v3From) == c.lock = "plutus" /\ c.datum = "none" /\ c.ver < v3From

\* In English: a PlutusV1 script's context cannot hold an inline datum,
\* nor in Babbage a reference input [R10].
\* Literally: "V1Unsupported of c is defined as: c's lock equals "plutus" and
\*   c's ver equals 1 and (c's datum equals "inline" or (Era equals "Babbage"
\*   and "ref" is a member of c's wd))."
V1Unsupported(c) ==
    /\ c.lock = "plutus" /\ c.ver = 1
    /\ c.datum = "inline" \/ (Era = "Babbage" /\ "ref" \in c.wd)

\* In English: the reference accepts a datum cell [R6] 222-247.
\* Literally: "SpecDatumAccepts of c is defined as: Unspendable of c and 3 is
\*   not true, and V1Unsupported of c is not true, and DatumRequired of c is
\*   a subset of c's wd, and c's wd is a subset of DatumAllowed of c, TRUE
\*   and (Mutation equals "SpecAnyDatumOk")."
SpecDatumAccepts(c) ==
    /\ ~Unspendable(c, 3)
    /\ ~V1Unsupported(c)
    /\ DatumRequired(c) \subseteq c.wd
    /\ c.wd \subseteq DatumAllowed(c, TRUE, Mutation = "SpecAnyDatumOk")

\* In English: gOuroboros' datum rules [G6]; two mutations.
\* Literally: "GoDatumAccepts of c is defined as: Unspendable of c and (if
\*   Mutation equals "GoV2NoDatumOk" then 2, else 3) is not true, and
\*   V1Unsupported of c is not true, and DatumRequired of c is a subset of
\*   c's wd, and c's wd is a subset of DatumAllowed of c, (Mutation does not
\*   equal "GoRefNotSupplemental") and FALSE."
GoDatumAccepts(c) ==
    /\ ~Unspendable(c, IF Mutation = "GoV2NoDatumOk" THEN 2 ELSE 3)
    /\ ~V1Unsupported(c)
    /\ DatumRequired(c) \subseteq c.wd
    /\ c.wd \subseteq DatumAllowed(c, Mutation # "GoRefNotSupplemental", FALSE)

-----------------------------------------------------------------------------
(* Family 5: the script integrity hash (Alonzo on).                        *)

\* In English: an integrity cell: whether a PlutusV1 spending script runs
\* (with its redeemer), whether a supplemental datum is carried, whether
\* (from Babbage) a reference input holds an unneeded PlutusV2 script,
\* whether a hash is declared, and the language set it covers (1 is V1, 2
\* is V2; empty when no hash is declared).
\* Literally: "IntegrityCells is defined as the set of every c in the set of
\*   records whose field rd is a member of BOOLEAN, field dat is a member of
\*   BOOLEAN, field unused is a member of (if AtLeast of "Babbage" then
\*   BOOLEAN, else the set containing FALSE), field decl is a member of
\*   BOOLEAN, and field langs is a member of the set of subsets of the set
\*   containing 1 and 2, such that if c's decl is not true, then c's langs
\*   equals the empty set."
IntegrityCells ==
    {c \in [rd : BOOLEAN, dat : BOOLEAN,
            unused : IF AtLeast("Babbage") THEN BOOLEAN ELSE {FALSE},
            decl : BOOLEAN, langs : SUBSET {1, 2}] :
        ~c.decl => c.langs = {}}

\* In English: the languages whose views the reference hashes: those of
\* the needed Plutus scripts [R8], here V1 when the spending script runs.
\* The mutations count every Plutus script the transaction can reach, or
\* none at all.
\* Literally: "UsedLangs of c and allProvided is defined as the union of (if c's
\*   rd then the set containing 1, else the empty set) and (if allProvided
\*   and c's unused then the set containing 2, else the empty set)."
UsedLangs(c, allProvided) ==
    (IF c.rd THEN {1} ELSE {}) \cup (IF allProvided /\ c.unused THEN {2} ELSE {})

\* In English: with no redeemers, datums or languages there is no hash;
\* otherwise the declared hash must be the one over the used languages
\* [R8], [R6] 278-300.
\* Literally: "IntegrityOk of c and used is defined as: if c's rd is not true
\*   and c's dat is not true and used equals the empty set, then c's decl is
\*   not true, else c's decl and c's langs equals used."
IntegrityOk(c, used) ==
    IF ~c.rd /\ ~c.dat /\ used = {} THEN ~c.decl
    ELSE c.decl /\ c.langs = used

\* In English: the reference's decision.
\* Literally: "SpecIntegrityAccepts of c is defined as IntegrityOk of c and
\*   (if Mutation equals "SpecIgnoreLangs" then the empty set, else UsedLangs
\*   of c and FALSE)."
SpecIntegrityAccepts(c) ==
    IntegrityOk(c, IF Mutation = "SpecIgnoreLangs" THEN {} ELSE UsedLangs(c, FALSE))

\* In English: gOuroboros' decision [G7]; one mutation.
\* Literally: "GoIntegrityAccepts of c is defined as IntegrityOk of c and
\*   UsedLangs of c and (Mutation equals "GoLangsAllProvided")."
GoIntegrityAccepts(c) ==
    IntegrityOk(c, UsedLangs(c, Mutation = "GoLangsAllProvided"))

-----------------------------------------------------------------------------
(* The environment.                                                       *)

\* In English: the bounds a cell can have. Shelley has no lower bound, and
\* its TTL does not reach the multisig evaluator, so both stay absent.
\* Literally: "Bounds is defined as: if AtLeast of "Allegra" then the union of
\*   the set containing NoBound and 0 through 3, else the set containing
\*   NoBound."
Bounds == IF AtLeast("Allegra") THEN {NoBound} \cup 0..3 ELSE {NoBound}

\* In English: every variable holds the kind of value it should.
\* Literally: "TypeOK is defined as: wits is a subset of Keys, and lo is a
\*   member of Bounds, and hi is a member of Bounds."
TypeOK == wits \subseteq Keys /\ lo \in Bounds /\ hi \in Bounds

-----------------------------------------------------------------------------
(* The comparison.                                                         *)

\* In English: the era has Plutus scripts, datums and redeemers.
\* Literally: "PlutusEra is defined as AtLeast of "Alonzo"."
PlutusEra == AtLeast("Alonzo")

\* In English: gOuroboros accepts exactly what the reference accepts, in
\* every family of transactions.
\* Literally: "GoAgrees is defined as: for all c in KeyCells, GoKeyAccepts of
\*   c equals SpecKeyAccepts of c; and for all s in Scripts, GoNativeAccepts
\*   of s equals SpecNativeAccepts of s; and for all c in ScriptCells,
\*   GoScriptAccepts of c equals SpecScriptAccepts of c; and if PlutusEra,
\*   then for all c in DatumCells, GoDatumAccepts of c equals
\*   SpecDatumAccepts of c, and for all c in IntegrityCells,
\*   GoIntegrityAccepts of c equals SpecIntegrityAccepts of c."
GoAgrees ==
    /\ \A c \in KeyCells : GoKeyAccepts(c) = SpecKeyAccepts(c)
    /\ \A s \in Scripts : GoNativeAccepts(s) = SpecNativeAccepts(s)
    /\ \A c \in ScriptCells : GoScriptAccepts(c) = SpecScriptAccepts(c)
    /\ PlutusEra =>
         /\ \A c \in DatumCells : GoDatumAccepts(c) = SpecDatumAccepts(c)
         /\ \A c \in IntegrityCells :
              GoIntegrityAccepts(c) = SpecIntegrityAccepts(c)

-----------------------------------------------------------------------------
(* Properties of the reference itself; each has a Spec mutation that       *)
(* breaks it.                                                              *)

\* In English: an accepted transaction carries a witness for every key
\* that authorizes a withdrawal, delegation or input it names.
\* Literally: "KeysAuthorized is defined as: for all c in KeyCells, if
\*   SpecKeyAccepts of c and c's src is a member of the set containing "in",
\*   "wdrl", "deleg" and "retire", then c's key is a member of wits."
KeysAuthorized ==
    \A c \in KeyCells :
        (SpecKeyAccepts(c) /\ c.src \in {"in", "wdrl", "deleg", "retire"})
            => c.key \in wits

\* In English: an accepted one-leaf timelock is inside its bound: a start
\* leaf needs a present lower bound at or after it.
\* Literally: "TimelockSound is defined as: for all s in Scripts, if s's op
\*   equals "all" and the length of s's subs equals 1 and element 1 of s's
\*   subs's op equals "start" and SpecNativeAccepts of s, then lo does not
\*   equal NoBound and element 1 of s's subs's slot is less than or equal to
\*   lo."
TimelockSound ==
    \A s \in Scripts :
        (s.op = "all" /\ Len(s.subs) = 1 /\ s.subs[1].op = "start"
         /\ SpecNativeAccepts(s))
            => lo # NoBound /\ s.subs[1].slot <= lo

\* In English: an accepted script cell supplies its script exactly once.
\* (These families do not read the state; "TypeOK =>" makes TLC check the
\* property in each state rather than reject it as a constant formula.)
\* Literally: "ScriptsExact is defined as: if TypeOK, then for all c in
\*   ScriptCells, if SpecScriptAccepts of c, then c's wit does not equal c's
\*   ref."
ScriptsExact ==
    TypeOK => \A c \in ScriptCells : SpecScriptAccepts(c) => c.wit # c.ref

\* In English: an accepted datum cell carries no stray datum.
\* Literally: "DatumsJustified is defined as: if TypeOK and PlutusEra, then
\*   for all c in DatumCells, if SpecDatumAccepts of c, then "stray" is not a
\*   member of c's wd."
DatumsJustified ==
    TypeOK /\ PlutusEra => \A c \in DatumCells : SpecDatumAccepts(c) => "stray" \notin c.wd

\* In English: an accepted integrity cell declares the views of exactly
\* the languages it uses.
\* Literally: "IntegrityMatches is defined as: if TypeOK and PlutusEra, then
\*   for all c in IntegrityCells, if SpecIntegrityAccepts of c and c's decl, then c's
\*   langs equals UsedLangs of c and FALSE."
IntegrityMatches ==
    TypeOK /\ PlutusEra =>
        \A c \in IntegrityCells :
            (SpecIntegrityAccepts(c) /\ c.decl) => c.langs = UsedLangs(c, FALSE)

-----------------------------------------------------------------------------
(* TableSpec: every environment, one change per step.                      *)

\* In English: start with no witnesses and no bounds.
\* Literally: "Init is defined as: wits equals the empty set, and lo equals
\*   NoBound, and hi equals NoBound."
Init == wits = {} /\ lo = NoBound /\ hi = NoBound

\* In English: add a witness for one more key.
\* Literally: "AddWitness of k is defined as: k is not a member of wits, and
\*   wits in the next state equals the union of wits and the set containing
\*   k, and lo and hi are unchanged."
AddWitness(k) == k \notin wits /\ wits' = wits \cup {k} /\ UNCHANGED <<lo, hi>>

\* In English: set the lower bound.
\* Literally: "SetLo of b is defined as: lo in the next state equals b, and
\*   wits and hi are unchanged."
SetLo(b) == lo' = b /\ UNCHANGED <<wits, hi>>

\* In English: set the upper bound.
\* Literally: "SetHi of b is defined as: hi in the next state equals b, and
\*   wits and lo are unchanged."
SetHi(b) == hi' = b /\ UNCHANGED <<wits, lo>>

\* In English: each step changes one thing.
\* Literally: "Next is defined as: there exists a k in Keys such that
\*   AddWitness of k, or there exists a b in Bounds such that SetLo of b, or
\*   there exists a b in Bounds such that SetHi of b."
Next == (\E k \in Keys : AddWitness(k))
        \/ (\E b \in Bounds : SetLo(b))
        \/ (\E b \in Bounds : SetHi(b))

\* In English: start in Init, then take Next steps.
\* Literally: "TableSpec is defined as: Init, and always, every step is a Next
\*   step or a step that leaves vars unchanged."
TableSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Reachability probes: each claims something never happens; a config      *)
(* that checks one must FAIL.                                              *)

\* In English: "No key cell is ever authorized by a bootstrap witness."
\* Literally: "ProbeNoBootstrapAuthorizes is defined as: it is not true that
\*   there exists a c in KeyCells such that SpecKeyAccepts of c and c's key
\*   equals "b" and c's src does not equal "reg0"."
ProbeNoBootstrapAuthorizes ==
    ~\E c \in KeyCells : SpecKeyAccepts(c) /\ c.key = "b" /\ c.src # "reg0"
\* In English: "Dijkstra never excuses a pool owner."
\* Literally: "ProbeNoOwnerExemption is defined as: it is not true that there
\*   exists a c in KeyCells such that c's src equals "owner" and
\*   SpecKeyAccepts of c and c's key is not a member of wits."
ProbeNoOwnerExemption ==
    ~\E c \in KeyCells : c.src = "owner" /\ SpecKeyAccepts(c) /\ c.key \notin wits
\* In English: "No script with both a time leaf and a signature is ever
\* accepted."
\* Literally: "ProbeNoTimelockAccepted is defined as: it is not true that
\*   there exists an s in Scripts such that SpecNativeAccepts of s and the
\*   length of s's subs equals 2 and element 1 of s's subs's op equals "sig"
\*   and element 2 of s's subs's op equals "expire" and s's op equals "all"."
ProbeNoTimelockAccepted ==
    ~\E s \in Scripts :
        /\ SpecNativeAccepts(s) /\ s.op = "all" /\ Len(s.subs) = 2
        /\ s.subs[1].op = "sig" /\ s.subs[2].op = "expire"
\* In English: "No script is ever supplied only by a reference input."
\* Literally: "ProbeNoRefScriptAccepted is defined as: if TypeOK, then it is
\*   not true that there exists a c in ScriptCells such that SpecScriptAccepts
\*   of c and c's wit is not true."
ProbeNoRefScriptAccepted ==
    TypeOK => ~\E c \in ScriptCells : SpecScriptAccepts(c) /\ ~c.wit
\* In English: "No input with an inline datum is ever spent."
\* Literally: "ProbeNoInlineDatumAccepted is defined as: if TypeOK and
\*   PlutusEra, then it is not true that there exists a c in DatumCells such that
\*   SpecDatumAccepts of c and c's datum equals "inline"."
ProbeNoInlineDatumAccepted ==
    TypeOK /\ PlutusEra => ~\E c \in DatumCells : SpecDatumAccepts(c) /\ c.datum = "inline"
=============================================================================
