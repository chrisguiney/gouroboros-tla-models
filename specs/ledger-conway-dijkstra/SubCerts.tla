------------------------------- MODULE SubCerts -------------------------------
(***************************************************************************)
(* Dijkstra's nested transactions, continued from SubTx.tla: what the     *)
(* certificates, withdrawals and direct deposits of a batch's levels do  *)
(* to the account and pool state, in order, and how the outer             *)
(* transaction aggregates them. SubTx.tla covers inputs, the treasury     *)
(* value, reference scripts and the withdrawal amounts; this module adds  *)
(* the certificates it left out.                                           *)
(*                                                                         *)
(* Two specifications:                                                     *)
(*   TableSpec: every account and pool state is a starting state and      *)
(*     nothing moves. GoAgrees checks, in each, that gOuroboros accepts   *)
(*     exactly the batches the reference accepts, over three families:    *)
(*     the entity effects of each level (withdrawals, then certificates,  *)
(*     then direct deposits), the pool deposit the batch owes, and the    *)
(*     pool-owner witnesses each level's pool registration needs.        *)
(*   Spec: a ledger applies accepted batches one after another and checks *)
(*     that the deposit pot always equals the deposits the registered     *)
(*     credential and pool owe, and that no value is made or lost.        *)
(*                                                                         *)
(* Sources (cardano-ledger 1210d37fe6bd, eras/dijkstra/impl/src/Cardano/  *)
(* Ledger/Dijkstra/):                                                      *)
(*   [E1] Rules/Ledger.hs 410-478: SUBLEDGERS first, then ENTITIES for the *)
(*        top level from the state the sub-transactions left, only when   *)
(*        the batch is phase-2 valid.                                      *)
(*   [E2] Rules/SubLedger.hs 259-299: a sub-transaction's SUBENTITIES     *)
(*        runs only when the top level is phase-2 valid.                  *)
(*   [E3] Rules/SubEntities.hs 252-282 and Rules/Entities.hs 276-314:     *)
(*        each level withdraws first, then runs its certificates in       *)
(*        order (SUBCERTS / CERTS), then pays its direct deposits into    *)
(*        accounts that exist after those certificates. A withdrawal's    *)
(*        account must exist in the original accounts and in the current *)
(*        ones; the batch's withdrawals may not exceed the original       *)
(*        balance (Entities.hs 341-389).                                   *)
(*   [E4] Rules/SubCert.hs 197-215, SubDeleg.hs, SubPool.hs: a sub-        *)
(*        transaction's certificates run the Conway DELEG and the Dijkstra *)
(*        POOL transitions unchanged. Conway Rules/Deleg.hs 236-303: a    *)
(*        registration needs an unregistered credential, a deregistration *)
(*        a registered one with a zero balance, a delegation a registered *)
(*        credential and pool.                                             *)
(*   [E5] UTxO.hs 115-137 dijkstraProducedValue and Certs: the pool       *)
(*        deposit is charged once per pool not registered in the          *)
(*        original state, over the certificates of every sub-transaction *)
(*        then the top (Shelley TxCert.hs 677-689); Rules/Utxo.hs 361-386:*)
(*        in legacy mode the top level must also balance alone, against   *)
(*        the pool state after the sub-transactions; both checks only for *)
(*        a phase-2-valid batch.                                           *)
(*   [E6] Rules/Utxow.hs 512-527 and UTxO.hs 187-203: a pool              *)
(*        registration needs its owners' witnesses unless the pool is     *)
(*        registered and its latest parameters (pending ones first)       *)
(*        equal the new ones ignoring the BLS key; never when the batch   *)
(*        is phase-2 invalid. Each sub-transaction is judged against the  *)
(*        pool state before it (SubLedger.hs 291-297, SubUtxow.hs 252-    *)
(*        254), the top against the state after every sub-transaction     *)
(*        (Ledger.hs 480-491).                                             *)
(* The formal specification (formal-ledger-specifications 60b68036c8b4,   *)
(* src/Ledger/Dijkstra/Specification/) states the same order: Ledger     *)
(* LEDGER-V and SUBLEDGERS, Entities SUBENTITIES and ENTITIES, Certs      *)
(* newCertDeposits, Utxo producedBatch and producedLegacy.                *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 62fa36d1,              *)
(* ledger/dijkstra/rules.go):                                              *)
(*   [G1] UtxoValidateCertificateDeposits, UtxoValidateWithdrawals and    *)
(*        UtxoValidateBatchWithdrawals: the levels in order through       *)
(*        common.BlockLedgerState (withdrawals, certificates, direct      *)
(*        deposits; ledger/common/block_state.go ApplyCertificate-        *)
(*        DepositLevel). UtxoValidateDelegation and                        *)
(*        UtxoValidatePoolCertificates: each level against an overlay of  *)
(*        the earlier levels' registrations. All phase-2-valid only.      *)
(*   [G2] UtxoValidateValueNotConservedUtxo over the flattened batch, one *)
(*        pool deposit per operator; UtxoValidateValueNotConserved-       *)
(*        LegacyModeUtxo against the pool state after the sub-            *)
(*        transactions.                                                    *)
(*   [G3] UtxoValidateRequiredVKeyWitnesses with                          *)
(*        common.PoolOwnersWitnessRequired, the pool state threaded       *)
(*        through the levels.                                              *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the README section "Reading a formula     *)
(* literally" and specs/keepalive/KeepAlive.tla.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxTxs,    \* how many batches the ledger applies (Spec only)
    Mutation   \* "none", or one deliberate mistake (see the README)

\* In English: the sequences of length 0, 1 or 2 drawn from S: a batch has
\* at most two sub-transactions here.
\* Literally: "UpTo2 of S is defined as the union of the set containing the
\*   empty tuple, the set of the tuple of x for every x that is a member of S,
\*   and the set of the tuple of x and y for every x and y that are members
\*   of S."
UpTo2(S) == {<<>>} \cup {<<x>> : x \in S} \cup {<<x, y>> : x \in S, y \in S}

\* In English: the sequences of length 0 or 1 drawn from S.
\* Literally: "UpTo1 of S is defined as the union of the set containing the
\*   empty tuple and the set of the tuple of x for every x that is a member
\*   of S."
UpTo1(S) == {<<>>} \cup {<<x>> : x \in S}

\* In English: the key deposit and the pool deposit, in coins. They differ
\* so that a wrong count of either shows in the pot.
\* Literally: "K is defined as 1."
K == 1
\* Literally: "P is defined as 2."
P == 2

VARIABLES
    reg,       \* is the one stake credential registered?
    bal,       \* its reward balance
    pool,      \* the one pool: "none", or the class of its current parameters
    pend,      \* the class of its pending parameters, or "none"
    pot,       \* Spec: the deposit pot
    utxo,      \* Spec: the coins in the UTxO
    n,         \* Spec: batches applied so far
    last       \* Spec: what the last applied batch did, for the probes

\* Literally: "vars is defined as the tuple of reg, bal, pool, pend, pot,
\*   utxo, n and last."
vars == <<reg, bal, pool, pend, pot, utxo, n, last>>

\* In English: the levels of a batch in the order the ledger applies them:
\* the sub-transactions, then the top [E1].
\* Literally: "Order of b is defined as b's subs followed by the tuple of b's
\*   top."
Order(b) == b.subs \o <<b.top>>

\* In English: how many positions of a sequence satisfy a condition is
\* counted with this: the positions of lv holding the value v.
\* Literally: "CountOf of lv and v is defined as the number of members of the
\*   set of every k in the domain of lv such that lv of k equals v."
CountOf(lv, v) == Cardinality({k \in DOMAIN lv : lv[k] = v})

-----------------------------------------------------------------------------
(* Family 1: entity effects of each level [E1]-[E4].                       *)

\* A level may withdraw nothing, zero or one coin from the account, carry
\* one certificate, and pay one coin into the account directly.
\*   regS    register the stake credential (key deposit)
\*   unregS  deregister it (refund the key deposit)
\*   delegS  delegate it to the pool
\*   regP    register the pool (a re-registration when it exists)
\* In English: the certificates a level can carry.
\* Literally: "Certs is defined as the set containing "none", "regS",
\*   "unregS", "delegS" and "regP"."
Certs == {"none", "regS", "unregS", "delegS", "regP"}

\* In English: every level of family 1.
\* Literally: "ELevels is defined as the set of records whose wd is a member
\*   of the set containing "none", "zero" and "one", cert a member of Certs,
\*   and dd a member of BOOLEAN."
ELevels == [wd : {"none", "zero", "one"}, cert : Certs, dd : BOOLEAN]

\* In English: every batch of family 1: a top level and up to two
\* sub-transactions, valid or not.
\* Literally: "EBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of ELevels, and subs a member of UpTo2 of
\*   ELevels."
EBatches == [valid : BOOLEAN, top : ELevels, subs : UpTo2(ELevels)]

\* In English: the coins a level withdraws.
\* Literally: "WAmt of l is defined as: if l's wd equals "one" then 1, else 0."
WAmt(l) == IF l.wd = "one" THEN 1 ELSE 0

\* In English: the coins the whole batch withdraws.
RECURSIVE WTotal(_)
\* Literally: "WTotal of lv is defined as: if lv equals the empty tuple then 0,
\*   else WAmt of the head of lv plus WTotal of the tail of lv."
WTotal(lv) == IF lv = <<>> THEN 0 ELSE WAmt(Head(lv)) + WTotal(Tail(lv))

\* In English: some level withdraws, even zero coins.
\* Literally: "WAny of lv is defined as: there exists a k in the domain of lv
\*   such that lv of k's wd does not equal "none"."
WAny(lv) == \E k \in DOMAIN lv : lv[k].wd # "none"

\* The threaded state is a record: ok (no check has failed), reg, bal, and
\* pool (is the pool registered).
\* In English: the threaded state a batch starts from: the original one.
\* Literally: "S0 is defined as the record whose ok is TRUE, reg is reg, bal is
\*   bal, and pool is (pool does not equal "none")."
S0 == [ok |-> TRUE, reg |-> reg, bal |-> bal, pool |-> pool # "none"]

\* In English: a withdrawal needs the account to exist now, and takes its
\* coins [E3].
\* Literally: "WdStep of s and l is defined as: if l's wd equals "none" then
\*   s, else s with ok replaced by (s's ok and s's reg) and bal replaced by
\*   s's bal minus WAmt of l."
WdStep(s, l) ==
    IF l.wd = "none" THEN s
    ELSE [s EXCEPT !.ok = s.ok /\ s.reg, !.bal = s.bal - WAmt(l)]

\* In English: one certificate under the Conway DELEG and POOL rules [E4].
\* Literally: "CertStep of s and c is defined as: in the case c equals "regS",
\*   s with ok replaced by (s's ok and not s's reg), reg by TRUE and bal by 0;
\*   in the case c equals "unregS", s with ok replaced by (s's ok and s's reg
\*   and s's bal equals 0) and reg by FALSE; in the case c equals "delegS", s
\*   with ok replaced by (s's ok and s's reg and s's pool); in the case c
\*   equals "regP", s with pool replaced by TRUE; in every other case, s."
CertStep(s, c) ==
    CASE c = "regS"   -> [s EXCEPT !.ok = s.ok /\ ~s.reg, !.reg = TRUE, !.bal = 0]
      [] c = "unregS" -> [s EXCEPT !.ok = s.ok /\ s.reg /\ s.bal = 0, !.reg = FALSE]
      [] c = "delegS" -> [s EXCEPT !.ok = s.ok /\ s.reg /\ s.pool]
      [] c = "regP"   -> [s EXCEPT !.pool = TRUE]
      [] OTHER        -> s

\* In English: a direct deposit needs the account to exist after the
\* level's certificates, and adds a coin [E3].
\* Literally: "DdStep of s and l is defined as: if l's dd then s with ok
\*   replaced by (s's ok and s's reg) and bal by s's bal plus 1, else s."
DdStep(s, l) ==
    IF l.dd THEN [s EXCEPT !.ok = s.ok /\ s.reg, !.bal = s.bal + 1] ELSE s

\* In English: the reference's level: withdraw, certificates, deposit [E3].
\* Literally: "SpecLevel of s and l is defined as DdStep of (CertStep of
\*   (WdStep of s and l) and l's cert) and l."
SpecLevel(s, l) == DdStep(CertStep(WdStep(s, l), l.cert), l)

\* In English: run the reference's levels in turn.
RECURSIVE SpecRun(_, _)
\* Literally: "SpecRun of lv and s is defined as: if lv equals the empty tuple
\*   then s, else SpecRun of the tail of lv and SpecLevel of s and the head of
\*   lv."
SpecRun(lv, s) == IF lv = <<>> THEN s ELSE SpecRun(Tail(lv), SpecLevel(s, Head(lv)))

\* In English: the reference's decision, only for a valid batch [E1][E2]:
\* the batch withdraws no more than the original balance, from an account
\* that existed originally, and every level's steps succeed in order.
\* Literally: "SpecEnt of b is defined as: if b's valid then, letting lv be
\*   Order of b, WTotal of lv is less than or equal to bal, and (if WAny of lv
\*   then reg), and SpecRun of lv and S0's ok."
SpecEnt(b) ==
    b.valid =>
        LET lv == Order(b)
        IN /\ WTotal(lv) <= bal
           /\ WAny(lv) => reg
           /\ SpecRun(lv, S0).ok

\* In English: gOuroboros' level [G1]. The mutations run the certificate
\* before the withdrawal, or the direct deposit before the certificate.
\* Literally: "GoLevel of s and l is defined as: in the case Mutation equals
\*   "GoEntCertsFirst", DdStep of (WdStep of (CertStep of s and l's cert) and
\*   l) and l; in the case Mutation equals "GoEntDepositFirst", CertStep of
\*   (DdStep of (WdStep of s and l) and l) and l's cert; in every other case,
\*   SpecLevel of s and l."
GoLevel(s, l) ==
    CASE Mutation = "GoEntCertsFirst"   -> DdStep(WdStep(CertStep(s, l.cert), l), l)
      [] Mutation = "GoEntDepositFirst" -> CertStep(DdStep(WdStep(s, l), l), l.cert)
      [] OTHER                          -> SpecLevel(s, l)

\* In English: run gOuroboros' levels in turn.
RECURSIVE GoRun(_, _)
\* Literally: "GoRun of lv and s is defined as: if lv equals the empty tuple
\*   then s, else GoRun of the tail of lv and GoLevel of s and the head of lv."
GoRun(lv, s) == IF lv = <<>> THEN s ELSE GoRun(Tail(lv), GoLevel(s, Head(lv)))

\* In English: gOuroboros' decision [G1]. The mutations check an invalid
\* batch too, apply the top first, judge every level against the original
\* state, or drop the original-account check on withdrawals.
\* Literally: "GoEnt of b is defined as: if b's valid or Mutation equals
\*   "GoEntAnyPhase" then, letting lv be (if Mutation equals "GoEntTopFirst"
\*   then the tuple of b's top followed by b's subs, else Order of b): WTotal of
\*   lv is less than or equal to bal, and (if WAny of lv and Mutation does not
\*   equal "GoEntCurrentOnly", then reg), and (if Mutation equals
\*   "GoEntUnthreaded" then for all k in the domain of lv, GoLevel of S0 and lv
\*   of k's ok, else GoRun of lv and S0's ok)."
GoEnt(b) ==
    (b.valid \/ Mutation = "GoEntAnyPhase") =>
        LET lv == IF Mutation = "GoEntTopFirst" THEN <<b.top>> \o b.subs ELSE Order(b)
        IN /\ WTotal(lv) <= bal
           /\ (WAny(lv) /\ Mutation # "GoEntCurrentOnly") => reg
           /\ IF Mutation = "GoEntUnthreaded"
              THEN \A k \in DOMAIN lv : GoLevel(S0, lv[k]).ok
              ELSE GoRun(lv, S0).ok

-----------------------------------------------------------------------------
(* Family 2: the pool deposit the batch owes [E5].                         *)

\* Each level registers the pool or not. dTop and dSub are the pool
\* deposits the top level and the first sub-transaction leave room for:
\* the top's outputs are its inputs less dTop deposits, the sub-
\* transaction's likewise. legacy: the top level needs a Plutus V1-V3 script.
\* In English: every batch of family 2.
\* Literally: "DBatches is defined as the set of every b in the set of records
\*   whose valid and legacy are members of BOOLEAN, top a member of the set
\*   containing "none" and "regP", subs a member of UpTo2 of that set, and
\*   dTop and dSub members of 0 through 1, such that if b's subs equals the
\*   empty tuple then b's dSub equals 0."
DBatches ==
    {b \in [valid : BOOLEAN, legacy : BOOLEAN, top : {"none", "regP"},
            subs : UpTo2({"none", "regP"}), dTop : 0..1, dSub : 0..1] :
        b.subs = <<>> => b.dSub = 0}

\* In English: the pool deposits the whole batch owes: one, when the pool is
\* not registered originally and some level registers it [E5].
\* Literally: "BatchDep of b is defined as: if pool equals "none" and CountOf
\*   of Order of b and "regP" is greater than 0, then 1, else 0."
BatchDep(b) == IF pool = "none" /\ CountOf(Order(b), "regP") > 0 THEN 1 ELSE 0

\* In English: the pool deposits the top level owes on its own in legacy
\* mode: one, when no sub-transaction registered the pool first [E5].
\* Literally: "LegacyDep of b is defined as: if pool equals "none" and CountOf
\*   of b's subs and "regP" equals 0 and b's top equals "regP", then 1, else
\*   0."
LegacyDep(b) ==
    IF pool = "none" /\ CountOf(b.subs, "regP") = 0 /\ b.top = "regP" THEN 1 ELSE 0

\* In English: the reference's decision: a valid batch balances with the
\* batch's deposits, and in legacy mode the top balances alone [E5].
\* Literally: "SpecDep of b is defined as: if b's valid, then b's dTop plus b's
\*   dSub equals BatchDep of b, and (if b's legacy then b's dTop equals
\*   LegacyDep of b)."
SpecDep(b) ==
    b.valid => /\ b.dTop + b.dSub = BatchDep(b)
               /\ b.legacy => b.dTop = LegacyDep(b)

\* In English: gOuroboros' decision [G2]. The mutations charge a deposit per
\* registering level, judge the legacy top against the original pool state,
\* or check an invalid batch too.
\* Literally: "GoDep of b is defined as: if b's valid or Mutation equals
\*   "GoDepAnyPhase" then, letting all be (if Mutation equals "GoDepPerLevel"
\*   and pool equals "none" then CountOf of Order of b and "regP", else
\*   BatchDep of b) and top be (if Mutation equals "GoDepLegacyOriginal" and
\*   pool equals "none" and b's top equals "regP" then 1, else LegacyDep of
\*   b): b's dTop plus b's dSub equals all, and (if b's legacy then b's dTop
\*   equals top)."
GoDep(b) ==
    (b.valid \/ Mutation = "GoDepAnyPhase") =>
        LET all == IF Mutation = "GoDepPerLevel" /\ pool = "none"
                   THEN CountOf(Order(b), "regP") ELSE BatchDep(b)
            top == IF Mutation = "GoDepLegacyOriginal" /\ pool = "none" /\ b.top = "regP"
                   THEN 1 ELSE LegacyDep(b)
        IN /\ b.dTop + b.dSub = all
           /\ b.legacy => b.dTop = top

-----------------------------------------------------------------------------
(* Family 3: pool-owner witnesses for each level's pool registration [E6]. *)

\* A level registers the pool with parameters of class "A", "A2" (A with
\* another BLS key) or "B" (another pledge), or not at all, and carries the
\* owner's witness or not. The operator always witnesses.
\* In English: every level of family 3.
\* Literally: "OLevels is defined as the set of records whose cert is a member
\*   of the set containing "none", "A", "A2" and "B", and own a member of
\*   BOOLEAN."
OLevels == [cert : {"none", "A", "A2", "B"}, own : BOOLEAN]

\* In English: every batch of family 3.
\* Literally: "OBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of OLevels, and subs a member of UpTo2 of
\*   OLevels."
OBatches == [valid : BOOLEAN, top : OLevels, subs : UpTo2(OLevels)]

\* In English: parameters compared without the BLS key: A2 is A.
\* Literally: "Class of c is defined as: if c equals "A2" then "A", else c."
Class(c) == IF c = "A2" THEN "A" ELSE c

\* In English: the pool's latest parameters: the pending ones if any, else
\* the current ones [E6].
\* Literally: "Latest of p is defined as: if p's pend does not equal "none"
\*   then p's pend, else p's cur."
Latest(p) == IF p.pend # "none" THEN p.pend ELSE p.cur

\* In English: the owners must witness unless the pool exists and the new
\* parameters equal its latest ones, the BLS key aside [E6].
\* Literally: "OwnReq of p and c is defined as: p's cur equals "none", or Class
\*   of c does not equal Latest of p."
OwnReq(p, c) == p.cur = "none" \/ Class(c) # Latest(p)

\* In English: a registration makes a new pool current, and gives an
\* existing pool pending parameters (Dijkstra Rules/Pool.hs 211-300).
\* Literally: "OApply of p and c is defined as: if c equals "none" then p,
\*   else if p's cur equals "none" then p with cur replaced by Class of c, else
\*   p with pend replaced by Class of c."
OApply(p, c) ==
    IF c = "none" THEN p
    ELSE IF p.cur = "none" THEN [p EXCEPT !.cur = Class(c)]
    ELSE [p EXCEPT !.pend = Class(c)]

\* In English: the reference, level by level: each registration in a valid
\* batch carries the owner's witness or does not need it, judged against
\* the pool state the earlier levels left [E6].
RECURSIVE SpecRunO(_, _, _)
\* Literally: "SpecRunO of lv, p and v is defined as: if lv equals the empty
\*   tuple then TRUE, else, letting l be the head of lv: (if l's cert does not
\*   equal "none" and v and OwnReq of p and l's cert, then l's own) and
\*   SpecRunO of the tail of lv, OApply of p and l's cert, and v."
SpecRunO(lv, p, v) ==
    IF lv = <<>> THEN TRUE
    ELSE LET l == Head(lv)
         IN /\ (l.cert # "none" /\ v /\ OwnReq(p, l.cert)) => l.own
            /\ SpecRunO(Tail(lv), OApply(p, l.cert), v)

\* In English: the original pool state, as a record.
\* Literally: "P0 is defined as the record whose cur is pool and pend is pend."
P0 == [cur |-> pool, pend |-> pend]

\* In English: the reference's decision for a batch of family 3.
\* Literally: "SpecOwn of b is defined as SpecRunO of Order of b, P0 and b's
\*   valid."
SpecOwn(b) == SpecRunO(Order(b), P0, b.valid)

\* In English: gOuroboros' parameter comparison; the mutation counts the BLS
\* key.
\* Literally: "GoClass of c is defined as: if Mutation equals "GoOwnBlsCounts"
\*   then c, else Class of c."
GoClass(c) == IF Mutation = "GoOwnBlsCounts" THEN c ELSE Class(c)

\* In English: gOuroboros' requirement [G3]; the mutation ignores pending
\* parameters.
\* Literally: "GoOwnReq of p and c is defined as: p's cur equals "none", or
\*   GoClass of c does not equal (if Mutation equals "GoOwnIgnorePending" then
\*   p's cur, else Latest of p)."
GoOwnReq(p, c) ==
    p.cur = "none"
    \/ GoClass(c) # (IF Mutation = "GoOwnIgnorePending" THEN p.cur ELSE Latest(p))

\* In English: gOuroboros' level effect; the mutation never threads.
\* Literally: "GoOApply of p and c is defined as: if Mutation equals
\*   "GoOwnUnthreaded" or c equals "none", then p, else if p's cur equals
\*   "none" then p with cur replaced by GoClass of c, else p with pend replaced
\*   by GoClass of c."
GoOApply(p, c) ==
    IF Mutation = "GoOwnUnthreaded" \/ c = "none" THEN p
    ELSE IF p.cur = "none" THEN [p EXCEPT !.cur = GoClass(c)]
    ELSE [p EXCEPT !.pend = GoClass(c)]

\* In English: gOuroboros, level by level; the mutation requires owners in
\* an invalid batch too.
RECURSIVE GoRunO(_, _, _)
\* Literally: "GoRunO of lv, p and v is defined as: if lv equals the empty
\*   tuple then TRUE, else, letting l be the head of lv: (if l's cert does not
\*   equal "none" and (v or Mutation equals "GoOwnAnyPhase") and GoOwnReq of p
\*   and l's cert, then l's own) and GoRunO of the tail of lv, GoOApply of p
\*   and l's cert, and v."
GoRunO(lv, p, v) ==
    IF lv = <<>> THEN TRUE
    ELSE LET l == Head(lv)
         IN /\ (l.cert # "none" /\ (v \/ Mutation = "GoOwnAnyPhase")
                  /\ GoOwnReq(p, l.cert)) => l.own
            /\ GoRunO(Tail(lv), GoOApply(p, l.cert), v)

\* In English: gOuroboros' decision for a batch of family 3.
\* Literally: "GoOwn of b is defined as GoRunO of Order of b, P0 and b's
\*   valid."
GoOwn(b) == GoRunO(Order(b), P0, b.valid)

-----------------------------------------------------------------------------
(* Family 4: pool retirement across levels [E4].                          *)

\* Each level registers the pool, retires it (to a valid epoch), delegates
\* the registered credential to it, or nothing. A retirement takes effect at
\* an epoch boundary, so the pool stays registered for the rest of the
\* batch (Dijkstra Rules/Pool.hs RetirePool: the pool must be in
\* psStakePools; only psRetiring changes).
\* In English: every level of family 4.
\* Literally: "RCerts is defined as the set containing "none", "regP", "retP"
\*   and "delegS"."
RCerts == {"none", "regP", "retP", "delegS"}

\* In English: every batch of family 4.
\* Literally: "RBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of RCerts, and subs a member of UpTo2 of
\*   RCerts."
RBatches == [valid : BOOLEAN, top : RCerts, subs : UpTo2(RCerts)]

\* In English: one level of family 4: a retirement or a delegation needs
\* the pool registered; a registration registers it. The mutation lets a
\* retirement unregister the pool at once.
\* Literally: "RStep of s, c and spec is defined as: in the case c equals
\*   "regP", s with pool replaced by TRUE; in the case c equals "retP", s with
\*   ok replaced by (s's ok and s's pool) and pool replaced by (s's pool and
\*   (spec or Mutation does not equal "GoRetRemovesPool")); in the case c
\*   equals "delegS", s with ok replaced by (s's ok and s's pool); in every
\*   other case, s."
RStep(s, c, spec) ==
    CASE c = "regP"   -> [s EXCEPT !.pool = TRUE]
      [] c = "retP"   -> [s EXCEPT !.ok = s.ok /\ s.pool,
                                   !.pool = s.pool /\ (spec \/ Mutation # "GoRetRemovesPool")]
      [] c = "delegS" -> [s EXCEPT !.ok = s.ok /\ s.pool]
      [] OTHER        -> s

\* In English: run the levels of family 4 in turn.
RECURSIVE RRun(_, _, _)
\* Literally: "RRun of lv, s and spec is defined as: if lv equals the empty
\*   tuple then s, else RRun of the tail of lv, RStep of s, the head of lv and
\*   spec, and spec."
RRun(lv, s, spec) == IF lv = <<>> THEN s ELSE RRun(Tail(lv), RStep(s, Head(lv), spec), spec)

\* In English: the reference's decision for family 4 (the credential is
\* registered throughout).
\* Literally: "SpecRet of b is defined as: if b's valid then RRun of Order of
\*   b, S0 and TRUE's ok."
SpecRet(b) == b.valid => RRun(Order(b), S0, TRUE).ok

\* In English: gOuroboros' decision for family 4; the mutation judges every
\* level against the original pool state.
\* Literally: "GoRet of b is defined as: if b's valid then, letting lv be
\*   Order of b: if Mutation equals "GoRetUnthreaded" then for all k in the
\*   domain of lv, RStep of S0, lv of k and FALSE's ok, else RRun of lv, S0 and
\*   FALSE's ok."
GoRet(b) ==
    b.valid =>
        LET lv == Order(b)
        IN IF Mutation = "GoRetUnthreaded"
           THEN \A k \in DOMAIN lv : RStep(S0, lv[k], FALSE).ok
           ELSE RRun(lv, S0, FALSE).ok

-----------------------------------------------------------------------------
(* Family 5: several certificates in one level [E3][E4].                   *)

\* A level withdraws one coin or not, then runs up to two certificates in
\* order (SUBCERTS / CERTS fold the list); at most one sub-transaction.
\* In English: every level of family 5.
\* Literally: "MLevels is defined as the set of records whose wd is a member
\*   of the set containing "none" and "one", and certs a member of UpTo2 of
\*   the set containing "regS", "unregS", "delegS" and "regP"."
MLevels == [wd : {"none", "one"}, certs : UpTo2({"regS", "unregS", "delegS", "regP"})]

\* In English: every batch of family 5.
\* Literally: "MBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of MLevels, and subs a member of UpTo1 of
\*   MLevels."
MBatches == [valid : BOOLEAN, top : MLevels, subs : UpTo1(MLevels)]

\* In English: a level's certificates, folded in order from a state.
RECURSIVE CertsRun(_, _)
\* Literally: "CertsRun of s and cs is defined as: if cs equals the empty tuple
\*   then s, else CertsRun of (CertStep of s and the head of cs) and the tail
\*   of cs."
CertsRun(s, cs) == IF cs = <<>> THEN s ELSE CertsRun(CertStep(s, Head(cs)), Tail(cs))

\* In English: the reference's level: the withdrawal, then every
\* certificate in order. The mutations judge each certificate against the
\* state at the level's start, or carry only the first certificate's effect
\* to later levels.
\* Literally: "MLevel of s, l and spec is defined as: letting w be WdStep of s
\*   and l: if spec or Mutation equals "none", CertsRun of w and l's certs;
\*   if Mutation equals "GoMultiLevelStart", w with ok replaced by (for all k
\*   in the domain of l's certs, CertStep of w and l's certs of k's ok) and
\*   the other fields as CertsRun of w and l's certs left them; if Mutation
\*   equals "GoMultiFirstOnly", CertsRun of w and l's certs with every field
\*   but ok taken from CertsRun of w and the first certificate alone; else
\*   CertsRun of w and l's certs."
MLevel(s, l, spec) ==
    LET w == WdStep(s, l)
        full == CertsRun(w, l.certs)
    IN CASE spec -> full
         [] Mutation = "GoMultiLevelStart" ->
                [full EXCEPT !.ok = \A k \in DOMAIN l.certs : CertStep(w, l.certs[k]).ok]
         [] Mutation = "GoMultiFirstOnly" /\ l.certs # <<>> ->
                [CertStep(w, Head(l.certs)) EXCEPT !.ok = full.ok]
         [] OTHER -> full

\* In English: run the levels of family 5 in turn.
RECURSIVE MRun(_, _, _)
\* Literally: "MRun of lv, s and spec is defined as: if lv equals the empty
\*   tuple then s, else MRun of the tail of lv, MLevel of s, the head of lv and
\*   spec, and spec."
MRun(lv, s, spec) == IF lv = <<>> THEN s ELSE MRun(Tail(lv), MLevel(s, Head(lv), spec), spec)

\* In English: the reference's decision for family 5.
\* Literally: "SpecMulti of b is defined as: if b's valid then, letting lv be
\*   Order of b: WTotal of lv is less than or equal to bal, and (if WAny of lv
\*   then reg), and MRun of lv, S0 and TRUE's ok."
SpecMulti(b) ==
    b.valid => LET lv == Order(b)
               IN /\ WTotal(lv) <= bal
                  /\ WAny(lv) => reg
                  /\ MRun(lv, S0, TRUE).ok

\* In English: gOuroboros' decision for family 5.
\* Literally: "GoMulti of b is defined as: if b's valid then, letting lv be
\*   Order of b: WTotal of lv is less than or equal to bal, and (if WAny of lv
\*   then reg), and MRun of lv, S0 and FALSE's ok."
GoMulti(b) ==
    b.valid => LET lv == Order(b)
               IN /\ WTotal(lv) <= bal
                  /\ WAny(lv) => reg
                  /\ MRun(lv, S0, FALSE).ok

-----------------------------------------------------------------------------
(* Family 6: legacy-mode withdrawals with certificates [E3].               *)

\* In legacy mode (the top level needs a Plutus V1-V3 script) the batch
\* bound covers only the sub-transactions' withdrawals, and the top's
\* withdrawal must exist in the current accounts and drain the balance the
\* sub-transactions left, before the top's certificates run; the top's
\* account need not exist originally (Entities.hs 341-412).
\* In English: the sub-transaction levels of family 6.
\* Literally: "LSub is defined as the set of records whose wd is a member of
\*   the set containing "none" and "one", cert a member of the set containing
\*   "none", "regS" and "unregS", and dd a member of BOOLEAN."
LSub == [wd : {"none", "one"}, cert : {"none", "regS", "unregS"}, dd : BOOLEAN]

\* In English: the top levels of family 6: no withdrawal, or one of 0, 1 or
\* 2 coins.
\* Literally: "LTop is defined as the set of records whose wd is a member of
\*   the set containing "none", "w0", "w1" and "w2", cert a member of the set
\*   containing "none", "regS" and "unregS", and dd a member of BOOLEAN."
LTop == [wd : {"none", "w0", "w1", "w2"}, cert : {"none", "regS", "unregS"}, dd : BOOLEAN]

\* In English: every batch of family 6.
\* Literally: "LBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of LTop, and subs a member of UpTo1 of
\*   LSub."
LBatches == [valid : BOOLEAN, top : LTop, subs : UpTo1(LSub)]

\* In English: the coins a top-level withdrawal of family 6 names.
\* Literally: "LAmt of w is defined as: in the case w equals "w1", 1; in the
\*   case "w2", 2; in every other case, 0."
LAmt(w) == CASE w = "w1" -> 1 [] w = "w2" -> 2 [] OTHER -> 0

\* In English: the legacy top level: the withdrawal drains the balance the
\* sub-transactions left (the mutation: the original balance less their
\* withdrawals, missing their direct deposits and registrations), then the
\* certificate, then the direct deposit. ob is that mutated amount.
\* Literally: "LTopStep of s, l, spec and ob is defined as: letting d be (if
\*   not spec and Mutation equals "GoLegDrainOriginal" then ob, else s's
\*   bal): if l's wd equals "none" then DdStep of (CertStep of s and l's cert)
\*   and l, else DdStep of (CertStep of (s with ok replaced by (s's ok and
\*   s's reg and LAmt of l's wd equals d) and bal by 0) and l's cert) and l."
LTopStep(s, l, spec, ob) ==
    LET d == IF ~spec /\ Mutation = "GoLegDrainOriginal" THEN ob ELSE s.bal
    IN IF l.wd = "none" THEN DdStep(CertStep(s, l.cert), l)
       ELSE DdStep(CertStep([s EXCEPT !.ok = s.ok /\ s.reg /\ LAmt(l.wd) = d,
                                      !.bal = 0], l.cert), l)

\* In English: the reference's decision for family 6; the mutation also
\* requires the top's withdrawal account to exist originally.
\* Literally: "LegacyOk of b and spec is defined as: if b's valid then,
\*   letting s be SpecRun of b's subs and S0: WTotal of b's subs is less than
\*   or equal to bal, and (if WAny of b's subs then reg), and (if not spec and
\*   Mutation equals "GoLegTopOriginal" and b's top's wd does not equal
\*   "none", then reg), and LTopStep of s, b's top, spec and (bal minus
\*   WTotal of b's subs)'s ok."
LegacyOk(b, spec) ==
    b.valid =>
        LET s == SpecRun(b.subs, S0)
        IN /\ WTotal(b.subs) <= bal
           /\ WAny(b.subs) => reg
           /\ (~spec /\ Mutation = "GoLegTopOriginal" /\ b.top.wd # "none") => reg
           /\ LTopStep(s, b.top, spec, bal - WTotal(b.subs)).ok

-----------------------------------------------------------------------------
(* Family 7: account balance intervals (CIP-159) across levels [E3].        *)

\* A level may assert an interval on the account's balance; the top may
\* also assert a starting interval. A level's interval is checked against
\* the accounts as the earlier levels left them, at the level's start
\* (before its withdrawal); the starting interval against the original
\* accounts; the account must exist in the accounts checked
\* (SubEntities.hs 264, Entities.hs 287-288, 485-517). Intervals: a lower
\* bound is inclusive, an upper bound exclusive (Scripts.hs 670-674).
\* In English: the intervals a level can assert.
\* Literally: "Ivs is defined as the set containing "none", "exact0",
\*   "exact1", "lower1" and "upper1"."
Ivs == {"none", "exact0", "exact1", "lower1", "upper1"}

\* In English: is balance x inside interval iv?
\* Literally: "InIv of iv and x is defined as: in the case iv equals
\*   "exact0", x equals 0; "exact1", x equals 1; "lower1", x is greater than
\*   or equal to 1; "upper1", x is less than 1; in every other case, TRUE."
InIv(iv, x) ==
    CASE iv = "exact0" -> x = 0
      [] iv = "exact1" -> x = 1
      [] iv = "lower1" -> x >= 1
      [] iv = "upper1" -> x < 1
      [] OTHER -> TRUE

\* In English: the levels of family 7; st is the top's starting interval
\* (always "none" on a sub-transaction).
\* Literally: "ILevels is defined as the set of records whose wd is a member
\*   of the set containing "none" and "one", cert a member of the set
\*   containing "none", "regS" and "unregS", dd a member of BOOLEAN, iv a
\*   member of Ivs, and st a member of Ivs."
ILevels == [wd : {"none", "one"}, cert : {"none", "regS", "unregS"}, dd : BOOLEAN,
            iv : Ivs, st : Ivs]

\* In English: every batch of family 7.
\* Literally: "IBatches is defined as the set of every b in the set of
\*   records whose valid is a member of BOOLEAN, top a member of ILevels and
\*   subs a member of UpTo1 of ILevels, such that for all k in the domain of
\*   b's subs, b's subs of k's st equals "none"."
IBatches == {b \in [valid : BOOLEAN, top : ILevels, subs : UpTo1(ILevels)] :
                \A k \in DOMAIN b.subs : b.subs[k].st = "none"}

\* In English: one level of family 7: the interval at the level's start,
\* then the level as in family 1. The mutation checks the interval after
\* the level's withdrawal.
\* Literally: "ILevel of s, l and spec is defined as: letting c be (if not
\*   spec and Mutation equals "GoIvAfterWithdrawal" then WdStep of s and l,
\*   else s) and t be SpecLevel of s and l: if l's iv equals "none" then t,
\*   else t with ok replaced by (t's ok and c's reg and InIv of l's iv and c's
\*   bal)."
ILevel(s, l, spec) ==
    LET c == IF ~spec /\ Mutation = "GoIvAfterWithdrawal" THEN WdStep(s, l) ELSE s
        t == SpecLevel(s, l)
    IN IF l.iv = "none" THEN t
       ELSE [t EXCEPT !.ok = t.ok /\ c.reg /\ InIv(l.iv, c.bal)]

\* In English: run the levels of family 7 in turn; the mutation judges
\* every level's interval against the original state.
RECURSIVE IRun(_, _, _)
\* Literally: "IRun of lv, s and spec is defined as: if lv equals the empty
\*   tuple then s, else IRun of the tail of lv, (if not spec and Mutation
\*   equals "GoIvOriginal" then SpecLevel of s and the head of lv with ok
\*   replaced by its ok and the interval of the head of lv checked against
\*   S0, else ILevel of s, the head of lv and spec), and spec."
IRun(lv, s, spec) ==
    IF lv = <<>> THEN s
    ELSE LET l == Head(lv)
             nx == IF ~spec /\ Mutation = "GoIvOriginal"
                  THEN LET t == SpecLevel(s, l)
                       IN [t EXCEPT !.ok = t.ok /\ (l.iv = "none" \/ (S0.reg /\ InIv(l.iv, S0.bal)))]
                  ELSE ILevel(s, l, spec)
         IN IRun(Tail(lv), nx, spec)

\* In English: the decision for family 7 (spec: the reference's), with the
\* batch bound of family 1 and the top's starting interval against the
\* original account.
\* Literally: "IntervalsOk of b and spec is defined as: if b's valid then,
\*   letting lv be Order of b: WTotal of lv is less than or equal to bal, and
\*   (if WAny of lv then reg), and (if b's top's st does not equal "none" then
\*   reg and InIv of b's top's st and bal), and IRun of lv, S0 and spec's ok."
IntervalsOk(b, spec) ==
    b.valid =>
        LET lv == Order(b)
        IN /\ WTotal(lv) <= bal
           /\ WAny(lv) => reg
           /\ b.top.st # "none" => reg /\ InIv(b.top.st, bal)
           /\ IRun(lv, S0, spec).ok

-----------------------------------------------------------------------------
(* The table questions.                                                    *)

\* In English: families 1 and 2 read only whether the pool is registered,
\* so they are asked in the states with class A and nothing pending.
\* Literally: "Plain is defined as: pend equals "none" and pool does not
\*   equal "B"."
Plain == pend = "none" /\ pool # "B"

\* In English: in this state, gOuroboros accepts exactly the batches the
\* reference accepts, in all seven families. Family 4 is asked with the
\* credential registered, families 6 and 7 with no pool.
\* Literally: "GoAgrees is defined as: (if Plain, then for all b in EBatches,
\*   GoEnt of b if and only if SpecEnt of b, for all b in DBatches, GoDep of
\*   b if and only if SpecDep of b, and for all b in MBatches, GoMulti of b if
\*   and only if SpecMulti of b); and (if Plain and reg, then for all b in
\*   RBatches, GoRet of b if and only if SpecRet of b); and (if Plain and pool
\*   equals "none", then for all b in LBatches, LegacyOk of b and FALSE if
\*   and only if LegacyOk of b and TRUE, and for all b in IBatches,
\*   IntervalsOk of b and FALSE if and only if IntervalsOk of b and TRUE); and
\*   for all b in OBatches, GoOwn of b if and only if SpecOwn of b."
GoAgrees ==
    /\ Plain => /\ \A b \in EBatches : GoEnt(b) <=> SpecEnt(b)
                /\ \A b \in DBatches : GoDep(b) <=> SpecDep(b)
                /\ \A b \in MBatches : GoMulti(b) <=> SpecMulti(b)
    /\ (Plain /\ reg) => \A b \in RBatches : GoRet(b) <=> SpecRet(b)
    /\ (Plain /\ pool = "none") =>
           /\ \A b \in LBatches : LegacyOk(b, FALSE) <=> LegacyOk(b, TRUE)
           /\ \A b \in IBatches : IntervalsOk(b, FALSE) <=> IntervalsOk(b, TRUE)
    /\ \A b \in OBatches : GoOwn(b) <=> SpecOwn(b)

\* Table probes, each expected to be violated.
\* In English: "no single level withdraws the whole balance and then
\* deregisters" (false: withdrawals come before certificates).
\* Literally: "ProbeNoDrainThenDereg is defined as: there does not exist an l
\*   in ELevels such that l's wd equals "one" and l's cert equals "unregS" and
\*   SpecEnt of the record whose valid is TRUE, top is l and subs is the empty
\*   tuple."
ProbeNoDrainThenDereg ==
    ~\E l \in ELevels :
        /\ l.wd = "one" /\ l.cert = "unregS"
        /\ SpecEnt([valid |-> TRUE, top |-> l, subs |-> <<>>])
\* In English: "a top-level BLS-only re-registration of a pool a sub-
\* transaction registered always needs the owners" (false).
\* Literally: "ProbeNoOwnerExemptAfterSub is defined as: if pool equals
\*   "none", then SpecOwn of the batch whose valid is TRUE, whose sub-
\*   transaction registers A with the owner's witness, and whose top
\*   registers A2 without it, is not true."
ProbeNoOwnerExemptAfterSub ==
    pool = "none" =>
        ~SpecOwn([valid |-> TRUE,
                  subs |-> <<[cert |-> "A", own |-> TRUE]>>,
                  top |-> [cert |-> "A2", own |-> FALSE]])

\* In English: "a legacy top never withdraws from an account a sub-
\* transaction registered" (false: legacy mode checks the top against the
\* current accounts only).
\* Literally: "ProbeNoLegacyTopFromNewAccount is defined as: if not reg and
\*   pool equals "none", then LegacyOk of the valid batch whose sub-
\*   transaction registers the credential and whose top withdraws 0, and TRUE,
\*   is not true."
ProbeNoLegacyTopFromNewAccount ==
    (~reg /\ pool = "none") =>
        ~LegacyOk([valid |-> TRUE,
                   subs |-> <<[wd |-> "none", cert |-> "regS", dd |-> FALSE]>>,
                   top |-> [wd |-> "w0", cert |-> "none", dd |-> FALSE]], TRUE)
\* In English: "no level deregisters and re-registers the credential"
\* (false).
\* Literally: "ProbeNoReRegInLevel is defined as: if reg and bal equals 0 and
\*   Plain, then SpecMulti of the valid batch whose top deregisters then
\*   registers is not true."
ProbeNoReRegInLevel ==
    (reg /\ bal = 0 /\ Plain) =>
        ~SpecMulti([valid |-> TRUE, subs |-> <<>>,
                    top |-> [wd |-> "none", certs |-> <<"unregS", "regS">>]])

-----------------------------------------------------------------------------
(* TableSpec.                                                              *)

\* In English: any registration, balance and pool state; the ledger
\* variables sit at a fixed value.
\* Literally: "TableInit is defined as: reg is a member of BOOLEAN, bal is a
\*   member of (if reg then 0 through 1, else the set containing 0), pool is a
\*   member of the set containing "none", "A" and "B", pend is a member of (if
\*   pool equals "none" then the set containing "none", else the set
\*   containing "none", "A" and "B"), pot, utxo and n equal 0, and last equals
\*   "none"."
TableInit ==
    /\ reg \in BOOLEAN
    /\ bal \in IF reg THEN 0..1 ELSE {0}
    /\ pool \in {"none", "A", "B"}
    /\ pend \in IF pool = "none" THEN {"none"} ELSE {"none", "A", "B"}
    /\ pot = 0 /\ utxo = 0 /\ n = 0 /\ last = "none"

\* In English: start in any TableInit state and never move.
\* Literally: "TableSpec is defined as: TableInit holds at the start, and
\*   always, every step is a step that leaves vars unchanged."
TableSpec == TableInit /\ [][UNCHANGED vars]_vars

-----------------------------------------------------------------------------
(* Spec: a ledger applying batches.                                        *)

\* In English: the total the run starts with, all in the UTxO.
\* Literally: "Start is defined as 6."
Start == 6

\* In English: the levels a ledger batch can have: withdraw one coin or
\* not, any certificate, a direct deposit or not. A batch has at most one
\* sub-transaction here, to keep the state space small.
\* Literally: "LLevels is defined as the set of records whose wd is a member of
\*   the set containing "none" and "one", cert a member of Certs, and dd a
\*   member of BOOLEAN."
LLevels == [wd : {"none", "one"}, cert : Certs, dd : BOOLEAN]

\* In English: the pool deposits a ledger batch puts in the pot. The
\* mutation charges one per registering level.
\* Literally: "PoolDep of lv is defined as: if pool does not equal "none" then
\*   0, else if Mutation equals "SpecPoolDepositPerLevel" then CountOf of the
\*   certs of lv and "regP", else (if CountOf of the certs of lv and "regP" is
\*   greater than 0 then 1, else 0)."
PoolDep(lv) ==
    LET certs == [k \in DOMAIN lv |-> lv[k].cert]
    IN IF pool # "none" THEN 0
       ELSE IF Mutation = "SpecPoolDepositPerLevel" THEN CountOf(certs, "regP")
       ELSE IF CountOf(certs, "regP") > 0 THEN 1 ELSE 0

\* In English: the ledger starts with nothing registered and every coin in
\* the UTxO.
\* Literally: "Init is defined as: reg equals FALSE, bal equals 0, pool and
\*   pend equal "none", pot equals 0, utxo equals Start, n equals 0, and last
\*   equals "none"."
Init == /\ reg = FALSE /\ bal = 0 /\ pool = "none" /\ pend = "none"
        /\ pot = 0 /\ utxo = Start /\ n = 0 /\ last = "none"

\* In English: apply one valid batch the reference accepts and the UTxO can
\* pay for: the account and pool end as the levels left them; key deposits
\* and refunds and the pool deposit move between the UTxO and the pot;
\* withdrawals move coins from the account to the UTxO, direct deposits
\* back. The mutation forgets to take a direct deposit from the UTxO.
\* Literally: "Step is defined as: n is less than MaxTxs, and there exists a b
\*   in the set of records whose valid is TRUE, top is a member of LLevels and
\*   subs a member of UpTo1 of LLevels, such that SpecEnt of b and, letting lv
\*   be Order of b, f be SpecRun of lv and S0, certs be the function that maps
\*   every k in the domain of lv to lv of k's cert, keys be K times (CountOf of
\*   certs and "regS" minus CountOf of certs and "unregS"), dep be keys plus P
\*   times PoolDep of lv, and dds be the number of k in the domain of lv with
\*   lv of k's dd: utxo in the next state equals utxo plus WTotal of lv minus
\*   dep minus (if Mutation equals "SpecDirectDepositFree" then 0, else dds),
\*   and that is at least 0; reg in the next state equals f's reg; bal in the
\*   next state equals f's bal; pool in the next state equals (if f's pool
\*   then "A" else "none"); pot in the next state equals pot plus dep; last in
\*   the next state names the batch's shape; n in the next state equals n
\*   plus 1; and pend is unchanged."
Step ==
    /\ n < MaxTxs
    /\ \E b \in [valid : {TRUE}, top : LLevels, subs : UpTo1(LLevels)] :
          /\ SpecEnt(b)
          /\ LET lv == Order(b)
                 f == SpecRun(lv, S0)
                 certs == [k \in DOMAIN lv |-> lv[k].cert]
                 keys == K * (CountOf(certs, "regS") - CountOf(certs, "unregS"))
                 dep == keys + P * PoolDep(lv)
                 dds == Cardinality({k \in DOMAIN lv : lv[k].dd})
             IN /\ utxo' = utxo + WTotal(lv) - dep
                              - (IF Mutation = "SpecDirectDepositFree" THEN 0 ELSE dds)
                /\ utxo' >= 0
                /\ reg' = f.reg
                /\ bal' = f.bal
                /\ pool' = IF f.pool THEN "A" ELSE "none"
                /\ pot' = pot + dep
                /\ last' = CASE CountOf([k \in DOMAIN b.subs |-> b.subs[k].cert], "regS") > 0
                                  /\ b.top.cert = "unregS" -> "transient"
                             [] CountOf(certs, "regP") >= 2 -> "poolTwice"
                             [] OTHER -> "valid"
    /\ n' = n + 1
    /\ UNCHANGED pend

\* In English: when every batch has been applied, stay put.
\* Literally: "Done is defined as: n equals MaxTxs and vars is unchanged."
Done == n = MaxTxs /\ UNCHANGED vars

\* In English: start in Init, then apply batches until MaxTxs of them have
\* been applied.
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Step or Done step or a step that leaves vars unchanged."
Spec == Init /\ [][Step \/ Done]_vars

\* In English: the pot holds exactly the deposits of what is registered.
\* Literally: "DepositsMatch is defined as: pot equals (if reg then K else 0)
\*   plus (if pool does not equal "none" then P else 0)."
DepositsMatch == pot = (IF reg THEN K ELSE 0) + (IF pool # "none" THEN P ELSE 0)

\* In English: value is neither made nor lost.
\* Literally: "ValuePreserved is defined as: utxo plus bal plus pot equals
\*   Start."
ValuePreserved == utxo + bal + pot = Start

\* Ledger probes, each expected to be violated.
\* In English: "no batch registers the credential in a sub-transaction and
\* deregisters it at the top" (false).
\* Literally: "ProbeNoTransient is defined as: last does not equal
\*   "transient"."
ProbeNoTransient == last # "transient"
\* In English: "no batch registers the pool at two levels" (false).
\* Literally: "ProbeNoPoolTwice is defined as: last does not equal
\*   "poolTwice"."
ProbeNoPoolTwice == last # "poolTwice"
=============================================================================
