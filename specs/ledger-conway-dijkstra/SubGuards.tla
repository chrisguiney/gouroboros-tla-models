------------------------------- MODULE SubGuards -------------------------------
(***************************************************************************)
(* Dijkstra guards across a batch's levels. A level may require top-level *)
(* guards (body key 24: a credential, with a datum or not); the top level *)
(* lists its guards (key 14). The checks: every required guard is among   *)
(* the top's guards; the datum is present exactly when the guard is a     *)
(* Plutus script; a listed script guard is a needed script and a listed   *)
(* key guard a needed signature. And the script context a top-level       *)
(* guard script sees: the batch's required guards and its own datums.     *)
(*                                                                         *)
(* One specification, TableSpec: the guard credential's kind is the only  *)
(* state, and GoAgrees checks two families in each.                       *)
(*                                                                         *)
(* Sources (cardano-ledger 1210d37fe6bd, eras/dijkstra/impl/src/Cardano/  *)
(* Ledger/Dijkstra/):                                                      *)
(*   [W1] Rules/Utxow.hs 326-331: MissingRequiredGuards: the union of     *)
(*        every level's required guards less the top's guards; checked    *)
(*        whatever IsValid says (runTestOnSignal).                        *)
(*   [W2] Rules/Utxow.hs 476-508 validateGuardDatums, called for the top  *)
(*        (334) and each sub-transaction (SubUtxow.hs 274): a key guard   *)
(*        has no datum; a script guard whose script is provided has none  *)
(*        when native and one when Plutus; an unprovided script is not   *)
(*        judged. The scripts provided are the batch's                    *)
(*        (Dijkstra.hs 156-170 passes the top's to every sub).            *)
(*   [W3] UTxO.hs 237-246: each top-level script guard is a needed script *)
(*        (GuardingPurpose); TxBody.hs 1423: each key guard a required    *)
(*        signer. Rules/Utxow.hs 263-300: the batch's needed scripts must  *)
(*        equal the provided ones (missing and extraneous).               *)
(*   [W4] TxInfo.hs 829-899 transGuardingTopTxInfo: the guard script's    *)
(*        context carries, keyed by level id, the datum each level gives  *)
(*        it, and the distinct credentials every level requires.        *)
(* The formal specification (formal-ledger-specifications 60b68036c8b4)   *)
(* marks [W1] and [W2] "TODO: Fill in from the formal spec" in the        *)
(* reference; no rule for them was found in Utxow.lagda.md.              *)
(*                                                                         *)
(* gOuroboros (commit 62fa36d1, ledger/dijkstra/rules.go):                *)
(*   [G1] UtxoValidateRedeemerAndScriptWitnesses:                          *)
(*        validateDijkstraRequiredTopLevelGuards and                      *)
(*        validateDijkstraGuardDatums against the batch's scripts.        *)
(*   [G2] plutus_v4_top.go dijkstraTopTxInfoGuardDatumsV4 and             *)
(*        dijkstraBatchRequiredGuardsV4.                                  *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the README section "Reading a formula     *)
(* literally" and specs/keepalive/KeepAlive.tla.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Mutation   \* "none", or one deliberate mistake (see the README)

VARIABLES
    kind       \* the guard credential g: "key", "native" or "plutus"

\* Literally: "vars is defined as the tuple of kind."
vars == <<kind>>

\* In English: the sequences of length 0, 1 or 2 drawn from S.
\* Literally: "UpTo2 of S is defined as the union of the set containing the
\*   empty tuple, the set of the tuple of x for every x in S, and the set of
\*   the tuple of x and y for every x and y in S."
UpTo2(S) == {<<>>} \cup {<<x>> : x \in S} \cup {<<x, y>> : x \in S, y \in S}

-----------------------------------------------------------------------------
(* Family 1: required guards, guard datums and guard witnesses [W1]-[W3].  *)

\* A level requires g with no datum, with a datum, or not at all.
\* In English: what a level can require of g.
\* Literally: "Reqs is defined as the set containing "none", "nodatum" and
\*   "datum"."
Reqs == {"none", "nodatum", "datum"}

\* In English: every batch of family 1: whether the top lists g as a guard,
\* whether the top carries g's signature, where g's script is provided
\* (nowhere, in the top's witnesses, in the first sub-transaction's), and
\* what each level requires. A key credential has no script.
\* Literally: "WBatches is defined as the set of every b in the set of
\*   records whose valid, listed and wit are members of BOOLEAN, avail a
\*   member of the set containing "none", "top" and "sub", top a member of
\*   Reqs, and subs a member of UpTo2 of Reqs, such that (if b's avail
\*   equals "sub" then b's subs does not equal the empty tuple) and (if kind
\*   equals "key" then b's avail equals "none")."
WBatches ==
    {b \in [valid : BOOLEAN, listed : BOOLEAN, wit : BOOLEAN,
            avail : {"none", "top", "sub"}, top : Reqs, subs : UpTo2(Reqs)] :
        /\ b.avail = "sub" => b.subs # <<>>
        /\ kind = "key" => b.avail = "none"}

\* In English: the requirements of every level.
\* Literally: "AllReqs of b is defined as the set of b's subs of k for every
\*   k in the domain of b's subs, united with the set containing b's top."
AllReqs(b) == {b.subs[k] : k \in DOMAIN b.subs} \cup {b.top}

\* In English: the datum a requirement must carry [W2]: none for a key or
\* native script, one for a Plutus script; an unprovided script is not
\* judged.
\* Literally: "DatumOk of r and scripts is defined as: r equals "none", or
\*   (kind equals "key" and r equals "nodatum"), or (kind does not equal
\*   "key" and (not scripts, or (kind equals "native" and r equals
\*   "nodatum"), or (kind equals "plutus" and r equals "datum")))."
DatumOk(r, scripts) ==
    \/ r = "none"
    \/ kind = "key" /\ r = "nodatum"
    \/ kind # "key" /\ (\/ ~scripts
                        \/ kind = "native" /\ r = "nodatum"
                        \/ kind = "plutus" /\ r = "datum")

\* In English: the reference's decision for a batch of family 1, valid or
\* not: required guards listed at the top [W1], datums right on every level
\* against the batch's scripts [W2], g's script provided exactly when a
\* listed script guard needs it, and g's signature when it is a listed key
\* guard [W3].
\* Literally: "SpecW of b is defined as: (if there exists r in AllReqs of b
\*   with r not "none", then b's listed); and for all r in AllReqs of b,
\*   DatumOk of r and (b's avail does not equal "none"); and (b's listed and
\*   kind does not equal "key") if and only if b's avail does not equal
\*   "none"; and (if b's listed and kind equals "key", then b's wit)."
SpecW(b) ==
    /\ (\E r \in AllReqs(b) : r # "none") => b.listed
    /\ \A r \in AllReqs(b) : DatumOk(r, b.avail # "none")
    /\ (b.listed /\ kind # "key") <=> b.avail # "none"
    /\ (b.listed /\ kind = "key") => b.wit

\* In English: gOuroboros' decision [G1]. The mutations check only the top's
\* requirements against the guards, judge datums only on the top, judge a
\* level's datum against that level's own scripts, or let a key guard carry
\* a datum.
\* Literally: "GoW of b is defined as: letting reqd be (if Mutation equals
\*   "GoGuardTopOnly" then the set containing b's top, else AllReqs of b),
\*   judged be (if Mutation equals "GoGuardDatumTopOnly" then the set
\*   containing b's top, else AllReqs of b), and own of where be (if
\*   Mutation equals "GoGuardDatumLevelScripts" then b's avail equals where,
\*   else b's avail does not equal "none"): (if there exists r in reqd with r
\*   not "none", then b's listed); and (for all r in judged, DatumOk of r and
\*   own of "top", or, under "GoGuardKeyDatumOk", kind equals "key"), with
\*   each sub-transaction's requirement judged against own of "sub"; and the
\*   witness clauses of SpecW."
GoW(b) ==
    LET reqd == IF Mutation = "GoGuardTopOnly" THEN {b.top} ELSE AllReqs(b)
        own(where) == IF Mutation = "GoGuardDatumLevelScripts"
                      THEN b.avail = where ELSE b.avail # "none"
        ok(r, where) == DatumOk(r, own(where))
                        \/ (Mutation = "GoGuardKeyDatumOk" /\ kind = "key")
    IN /\ (\E r \in reqd : r # "none") => b.listed
       /\ ok(b.top, "top")
       /\ Mutation # "GoGuardDatumTopOnly" =>
              \A k \in DOMAIN b.subs : ok(b.subs[k], "sub")
       /\ (b.listed /\ kind # "key") <=> b.avail # "none"
       /\ (b.listed /\ kind = "key") => b.wit

-----------------------------------------------------------------------------
(* Family 2: the top-level guard script's context [W4].                    *)

\* Each level requires g ("g"), g with a datum ("gd"), another credential
\* h ("h", "hd"), or nothing; g is a Plutus script here.
\* In English: what a level requires in family 2.
\* Literally: "CReqs is defined as the set containing "none", "g", "gd", "h"
\*   and "hd"."
CReqs == {"none", "g", "gd", "h", "hd"}

\* In English: every batch of family 2.
\* Literally: "CBatches is defined as the set of records whose top is a member
\*   of CReqs and subs a member of UpTo2 of CReqs."
CBatches == [top : CReqs, subs : UpTo2(CReqs)]

\* In English: the batch's levels as a function from level name (0 for the
\* top, k for sub-transaction k) to its requirement.
\* Literally: "Lv of b is defined as the function that maps every k in 0
\*   through the length of b's subs to (if k equals 0 then b's top, else b's
\*   subs of k)."
Lv(b) == [k \in 0..Len(b.subs) |-> IF k = 0 THEN b.top ELSE b.subs[k]]

\* In English: the number of levels of b that require credential c, with or
\* without a datum.
\* Literally: "Requiring of b and c is defined as the number of members of
\*   the set of every k in the domain of Lv of b such that Lv of b of k is a
\*   member of the set containing c and c followed by "d"."
Requiring(b, c) == Cardinality({k \in DOMAIN Lv(b) : Lv(b)[k] \in {c, c \o "d"}})

\* In English: the reference's context [W4]: datums is the set of levels
\* that give g a datum; required counts each credential once if any level
\* requires it.
\* Literally: "SpecCtx of b is defined as the record whose datums is the set
\*   of every k in the domain of Lv of b such that Lv of b of k equals "gd",
\*   and whose required is the function that maps every c in the set
\*   containing "g" and "h" to (if Requiring of b and c is greater than 0
\*   then 1, else 0)."
SpecCtx(b) ==
    [datums |-> {k \in DOMAIN Lv(b) : Lv(b)[k] = "gd"},
     required |-> [c \in {"g", "h"} |-> IF Requiring(b, c) > 0 THEN 1 ELSE 0]]

\* In English: gOuroboros' context [G2]. The mutations take the top's datum
\* only, take another credential's datum too, or list a credential once per
\* requiring level.
\* Literally: "GoCtx of b is defined as: letting ds be the set of every k in
\*   the domain of Lv of b such that Lv of b of k equals "gd", or (Mutation
\*   equals "GoCtxAnyDatum" and Lv of b of k equals "hd"): the record whose
\*   datums is (if Mutation equals "GoCtxTopOnly" then the intersection of ds
\*   and the set containing 0, else ds), and whose required is (if Mutation
\*   equals "GoCtxNoDedup" then the function that maps every c in the set
\*   containing "g" and "h" to Requiring of b and c, else SpecCtx of b's
\*   required)."
GoCtx(b) ==
    LET ds == {k \in DOMAIN Lv(b) : \/ Lv(b)[k] = "gd"
                                    \/ Mutation = "GoCtxAnyDatum" /\ Lv(b)[k] = "hd"}
    IN [datums |-> IF Mutation = "GoCtxTopOnly" THEN ds \cap {0} ELSE ds,
        required |-> IF Mutation = "GoCtxNoDedup"
                     THEN [c \in {"g", "h"} |-> Requiring(b, c)]
                     ELSE SpecCtx(b).required]

-----------------------------------------------------------------------------
(* The table questions.                                                    *)

\* In English: gOuroboros agrees with the reference on every batch of both
\* families (family 2 is asked once, with g a Plutus script).
\* Literally: "GoAgrees is defined as: for all b in WBatches, GoW of b if and
\*   only if SpecW of b; and if kind equals "plutus", then for all b in
\*   CBatches, GoCtx of b equals SpecCtx of b."
GoAgrees ==
    /\ \A b \in WBatches : GoW(b) <=> SpecW(b)
    /\ kind = "plutus" => \A b \in CBatches : GoCtx(b) = SpecCtx(b)

\* Probes, each expected to be violated.
\* In English: "a sub-transaction never requires a guard only the top
\* provides the script for" (false for a Plutus guard).
\* Literally: "ProbeNoSubRequiresTopScript is defined as: if kind equals
\*   "plutus" then SpecW of the valid batch whose top lists g, carries no
\*   signature, provides the script and requires nothing, and whose sub-
\*   transaction requires g with a datum, is not true."
ProbeNoSubRequiresTopScript ==
    kind = "plutus" =>
        ~SpecW([valid |-> TRUE, listed |-> TRUE, wit |-> FALSE,
                avail |-> "top", top |-> "none", subs |-> <<"datum">>])
\* In English: "a guard's context never holds two datums" (false: two
\* levels each give one).
\* It names kind so that TLC checks it in each state, not once as a constant.
\* Literally: "ProbeNoTwoDatums is defined as: if kind equals "plutus", then
\*   the number of members of SpecCtx of the batch whose top and sub-
\*   transaction both give g a datum's datums does not equal 2."
ProbeNoTwoDatums ==
    kind = "plutus" =>
        Cardinality(SpecCtx([top |-> "gd", subs |-> <<"gd">>]).datums) # 2

-----------------------------------------------------------------------------
\* In English: any guard kind; nothing moves.
\* Literally: "TableInit is defined as: kind is a member of the set
\*   containing "key", "native" and "plutus"."
TableInit == kind \in {"key", "native", "plutus"}

\* In English: start in any TableInit state and never move.
\* Literally: "TableSpec is defined as: TableInit holds at the start, and
\*   always, every step leaves vars unchanged."
TableSpec == TableInit /\ [][UNCHANGED vars]_vars
=============================================================================
