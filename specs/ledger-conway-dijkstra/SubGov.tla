-------------------------------- MODULE SubGov --------------------------------
(***************************************************************************)
(* Dijkstra's nested transactions, continued from SubCerts.tla: the       *)
(* governance part of each level. Proposals and votes of a level, and the *)
(* DRep and committee certificates, judged against the state the earlier  *)
(* levels left.                                                            *)
(*                                                                         *)
(* One specification, TableSpec: every starting state is an initial state *)
(* and nothing moves. GoAgrees checks, in each, that gOuroboros accepts   *)
(* exactly the batches the reference accepts, over two families:          *)
(*   Family 1: each level registers something or not, proposes an Info    *)
(*     action or not, and casts one vote (DRep, committee or pool) on an  *)
(*     action that exists originally or on the sub-transaction's          *)
(*     proposal. A vote names an action by its transaction id, which      *)
(*     covers the vote, so a level can name only an earlier level's       *)
(*     proposal: the top the sub-transaction's, never the reverse.        *)
(*   Family 2: DRep certificates (register, deregister, update) and       *)
(*     committee certificates (authorize a hot key, resign) for a seated  *)
(*     member C1 and for C2, whom an UpdateCommittee proposal of an       *)
(*     earlier level would add.                                           *)
(*                                                                         *)
(* Sources (cardano-ledger 1210d37fe6bd):                                 *)
(*   [V1] eras/dijkstra/.../Rules/SubLedger.hs 259-299: a sub-transaction *)
(*        runs SUBENTITIES (its certificates), then SUBGOV with GovEnv     *)
(*        carrying its own transaction id and the certificate state after *)
(*        those certificates, then the proposals it leaves are the next   *)
(*        level's; SUBENTITIES gets the committee proposals of the        *)
(*        current state. Only when the batch is phase-2 valid.            *)
(*   [V2] eras/dijkstra/.../Rules/Ledger.hs 430-478: the top's ENTITIES   *)
(*        and GOV, from the state after every sub-transaction.            *)
(*   [V3] eras/conway/.../Rules/Gov.hs 460-620 conwayGovTransition:       *)
(*        proposals first (return account registered in the certificate  *)
(*        state), then votes, which may name an action of the same       *)
(*        transaction; a voter is a registered DRep, an authorized        *)
(*        committee hot key, or a registered pool.                        *)
(*   [V4] eras/conway/.../Rules/GovCert.hs conwayGovCertTransition: a     *)
(*        DRep registration needs an unregistered DRep, deregistration and *)
(*        update a registered one; a committee authorization or           *)
(*        resignation needs a cold credential that has not resigned and   *)
(*        is a current member or would be added by a pending              *)
(*        UpdateCommittee proposal (isPotentialFutureMember).             *)
(* The formal specification (formal-ledger-specifications 60b68036c8b4,   *)
(* src/Ledger/Dijkstra/Specification/Ledger.lagda.md SUBLEDGER-V,         *)
(* LEDGER-V) runs the top's CERTS and GOVS from the post-SUBLEDGERS state *)
(* the same way.                                                           *)
(*                                                                         *)
(* gOuroboros (commit 62fa36d1, ledger/dijkstra/rules.go):                *)
(*   [G1] validateDijkstraGovernanceLevels: each level's Conway GOV and   *)
(*        GOVCERT rules against dijkstraGovernanceStateView, which records *)
(*        the earlier levels' proposals, registrations and committee      *)
(*        changes after each level.                                       *)
(*   [G2] dijkstraGovernanceStateView.CommitteeCredentialMember: tracked  *)
(*        committee changes, then the wrapped state. It does not look at  *)
(*        the earlier levels' UpdateCommittee proposals (the Mutation     *)
(*        "GoComMain" models it; DRIFT L21).                              *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the README section "Reading a formula     *)
(* literally" and specs/keepalive/KeepAlive.tla.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Mutation   \* "none", or one deliberate mistake (see the README)

VARIABLES
    reg,       \* is the stake credential (the proposals' return account) registered?
    dreg,      \* is the DRep registered?
    cc,        \* family 1: has the seated member authorized its hot key?
    pool,      \* is the pool registered?
    c1         \* family 2: the seated member C1: "member", "auth" or "resigned"

\* Literally: "vars is defined as the tuple of reg, dreg, cc, pool and c1."
vars == <<reg, dreg, cc, pool, c1>>

\* In English: the sequences of length 0 or 1 drawn from S.
\* Literally: "UpTo1 of S is defined as the union of the set containing the
\*   empty tuple and the set of the tuple of x for every x that is a member
\*   of S."
UpTo1(S) == {<<>>} \cup {<<x>> : x \in S}

\* In English: the sequences of length 0, 1 or 2 drawn from S.
\* Literally: "UpTo2 of S is defined as the union of UpTo1 of S and the set of
\*   the tuple of x and y for every x and y that are members of S."
UpTo2(S) == UpTo1(S) \cup {<<x, y>> : x \in S, y \in S}

\* In English: a batch's levels with each one's name, in the order the
\* ledger applies them: the sub-transaction, then the top [V1][V2].
\* Literally: "Named of b is defined as the function that maps every k in the
\*   domain of b's subs to the record whose l is b's subs of k and me is "sub",
\*   followed by the tuple of the record whose l is b's top and me is "top"."
Named(b) ==
    [k \in DOMAIN b.subs |-> [l |-> b.subs[k], me |-> "sub"]]
        \o <<[l |-> b.top, me |-> "top"]>>

-----------------------------------------------------------------------------
(* Family 1: proposals and votes [V1]-[V3].                                *)

\* In English: the votes a level can cast: none, or a voter type on a
\* target action.
\* Literally: "Votes is defined as the union of the set containing the record
\*   whose voter is "none" and target is "orig", and the set of records whose
\*   voter is a member of the set containing "drep", "cc" and "spo" and whose
\*   target is a member of the set containing "orig" and "sub"."
Votes == {[voter |-> "none", target |-> "orig"]}
         \cup [voter : {"drep", "cc", "spo"}, target : {"orig", "sub"}]

\* In English: every level of family 1.
\* Literally: "GLevels is defined as the set of records whose cert is a member
\*   of the set containing "none", "regS", "regD", "authCC" and "regP", prop a
\*   member of BOOLEAN, and vote a member of Votes."
GLevels == [cert : {"none", "regS", "regD", "authCC", "regP"},
            prop : BOOLEAN, vote : Votes]

\* In English: every batch of family 1: a top and at most one
\* sub-transaction, which cannot name its own proposal.
\* Literally: "GBatches is defined as the set of every b in the set of
\*   records whose valid is a member of BOOLEAN, top a member of GLevels, and
\*   subs a member of UpTo1 of GLevels, such that for all k in the domain of
\*   b's subs, b's subs of k's vote's target does not equal "sub"."
GBatches ==
    {b \in [valid : BOOLEAN, top : GLevels, subs : UpTo1(GLevels)] :
        \A k \in DOMAIN b.subs : b.subs[k].vote.target # "sub"}

\* The threaded state: ok, reg, dreg, cc, pool, and props (the names of the
\* levels whose proposal exists so far).
\* In English: the state a batch starts from.
\* Literally: "G0 is defined as the record whose ok is TRUE, reg is reg, dreg
\*   is dreg, cc is cc, pool is pool and props is the empty set."
G0 == [ok |-> TRUE, reg |-> reg, dreg |-> dreg, cc |-> cc, pool |-> pool,
       props |-> {}]

\* In English: one certificate [V4] and Conway DELEG/POOL.
\* Literally: "GCert of s and c is defined as: in the case c equals "regS", s
\*   with ok replaced by (s's ok and not s's reg) and reg by TRUE; in the case c
\*   equals "regD", s with ok replaced by (s's ok and not s's dreg) and dreg by
\*   TRUE; in the case c equals "authCC", s with cc replaced by TRUE; in the
\*   case c equals "regP", s with pool replaced by TRUE; in every other case,
\*   s."
GCert(s, c) ==
    CASE c = "regS"   -> [s EXCEPT !.ok = s.ok /\ ~s.reg, !.reg = TRUE]
      [] c = "regD"   -> [s EXCEPT !.ok = s.ok /\ ~s.dreg, !.dreg = TRUE]
      [] c = "authCC" -> [s EXCEPT !.cc = TRUE]
      [] c = "regP"   -> [s EXCEPT !.pool = TRUE]
      [] OTHER        -> s

\* In English: a proposal needs a registered return account and then exists.
\* Literally: "GProp of s, l and me is defined as: if l's prop then s with ok
\*   replaced by (s's ok and s's reg) and props by s's props united with the
\*   set containing me, else s."
GProp(s, l, me) ==
    IF l.prop THEN [s EXCEPT !.ok = s.ok /\ s.reg, !.props = s.props \cup {me}]
    ELSE s

\* In English: is this voter type known in state s?
\* Literally: "Known of s and v is defined as: in the case v equals "drep",
\*   s's dreg; in the case v equals "cc", s's cc; in every other case, s's
\*   pool."
Known(s, v) == CASE v = "drep" -> s.dreg [] v = "cc" -> s.cc [] OTHER -> s.pool

\* In English: a vote needs a known voter and an existing action.
\* Literally: "GVote of s and l is defined as: if l's vote's voter equals
\*   "none" then s, else s with ok replaced by (s's ok and Known of s and l's
\*   vote's voter and (l's vote's target equals "orig" or l's vote's target
\*   is a member of s's props))."
GVote(s, l) ==
    IF l.vote.voter = "none" THEN s
    ELSE [s EXCEPT !.ok = s.ok /\ Known(s, l.vote.voter)
                          /\ (l.vote.target = "orig" \/ l.vote.target \in s.props)]

\* In English: the reference's level: certificates, then proposals, then
\* votes, all against the certificate state after the level's
\* certificates [V1][V3].
\* Literally: "SpecGLevel of s and n is defined as GVote of (GProp of (GCert of
\*   s and n's l's cert), n's l and n's me) and n's l."
SpecGLevel(s, n) == GVote(GProp(GCert(s, n.l.cert), n.l, n.me), n.l)

\* In English: run the reference's levels in turn.
RECURSIVE SpecGRun(_, _)
\* Literally: "SpecGRun of ns and s is defined as: if ns equals the empty tuple
\*   then s, else SpecGRun of the tail of ns and SpecGLevel of s and the head
\*   of ns."
SpecGRun(ns, s) == IF ns = <<>> THEN s ELSE SpecGRun(Tail(ns), SpecGLevel(s, Head(ns)))

\* In English: the reference's decision: nothing is checked for an invalid
\* batch; a valid one passes every level.
\* Literally: "SpecGov of b is defined as: if b's valid then SpecGRun of Named
\*   of b and G0's ok."
SpecGov(b) == b.valid => SpecGRun(Named(b), G0).ok

\* In English: gOuroboros' level [G1]. The mutation checks voters and
\* return accounts before the level's certificates.
\* Literally: "GoGLevel of s and n is defined as: if Mutation equals
\*   "GoGovBeforeCerts" then GCert of (GVote of (GProp of s, n's l and n's me)
\*   and n's l) and n's l's cert, else SpecGLevel of s and n."
GoGLevel(s, n) ==
    IF Mutation = "GoGovBeforeCerts"
    THEN GCert(GVote(GProp(s, n.l, n.me), n.l), n.l.cert)
    ELSE SpecGLevel(s, n)

\* In English: run gOuroboros' levels in turn.
RECURSIVE GoGRun(_, _)
\* Literally: "GoGRun of ns and s is defined as: if ns equals the empty tuple
\*   then s, else GoGRun of the tail of ns and GoGLevel of s and the head of
\*   ns."
GoGRun(ns, s) == IF ns = <<>> THEN s ELSE GoGRun(Tail(ns), GoGLevel(s, Head(ns)))

\* In English: gOuroboros' decision. The mutations check an invalid batch,
\* or judge every level against the original state.
\* Literally: "GoGov of b is defined as: if b's valid or Mutation equals
\*   "GoGovAnyPhase" then, letting ns be Named of b: if Mutation equals
\*   "GoGovUnthreaded" then for all k in the domain of ns, GoGLevel of G0 and
\*   ns of k's ok, else GoGRun of ns and G0's ok."
GoGov(b) ==
    (b.valid \/ Mutation = "GoGovAnyPhase") =>
        LET ns == Named(b)
        IN IF Mutation = "GoGovUnthreaded"
           THEN \A k \in DOMAIN ns : GoGLevel(G0, ns[k]).ok
           ELSE GoGRun(ns, G0).ok

-----------------------------------------------------------------------------
(* Family 2: DRep and committee certificates [V4].                         *)

\* In English: the certificates of family 2; pc: the level proposes an
\* UpdateCommittee action that would add C2.
\* Literally: "CLevels is defined as the set of records whose cert is a member
\*   of the set containing "none", "regD", "unregD", "updD", "authC1",
\*   "resignC1", "authC2" and "resignC2", and pc a member of BOOLEAN."
CLevels == [cert : {"none", "regD", "unregD", "updD",
                    "authC1", "resignC1", "authC2", "resignC2"},
            pc : BOOLEAN]

\* In English: every batch of family 2.
\* Literally: "CBatches is defined as the set of records whose valid is a
\*   member of BOOLEAN, top a member of CLevels, and subs a member of UpTo2 of
\*   CLevels."
CBatches == [valid : BOOLEAN, top : CLevels, subs : UpTo2(CLevels)]

\* The threaded state: ok, dreg, c1, c2 ("none", "auth" or "resigned") and
\* c2prop (an earlier level proposed adding C2).
\* In English: the state a batch of family 2 starts from: C2 not proposed.
\* Literally: "C0 is defined as the record whose ok is TRUE, dreg is dreg, c1
\*   is c1, c2 is "none" and c2prop is FALSE."
C0 == [ok |-> TRUE, dreg |-> dreg, c1 |-> c1, c2 |-> "none", c2prop |-> FALSE]

\* In English: may C2 act? The reference: it is a potential member once a
\* pending proposal would add it; gOuroboros main never sees it.
\* Literally: "C2Member of s and spec is defined as: s's c2prop and (spec or
\*   Mutation does not equal "GoComMain")."
C2Member(s, spec) == s.c2prop /\ (spec \/ Mutation # "GoComMain")

\* In English: one certificate of family 2 [V4]. spec says whether this is
\* the reference's step; the mutations change gOuroboros' step only.
\* Literally: "CCert of s, c and spec is defined as: in the case c equals
\*   "regD", s with ok replaced by (s's ok and not s's dreg) and dreg by TRUE;
\*   in the case "unregD", s with ok replaced by (s's ok and s's dreg) and dreg
\*   by FALSE; in the case "updD", s with ok replaced by (s's ok and s's dreg);
\*   in the case "authC1" or "resignC1", s with ok replaced by (s's ok and s's
\*   c1 does not equal "resigned" (or, for a resignation under the mutation
\*   "GoComResignAgain", anything)) and c1 by "auth" or "resigned"; likewise
\*   for C2, which also needs C2Member of s and spec; in every other case,
\*   s."
CCert(s, c, spec) ==
    LET again == ~spec /\ Mutation = "GoComResignAgain"
    IN CASE c = "regD"     -> [s EXCEPT !.ok = s.ok /\ ~s.dreg, !.dreg = TRUE]
         [] c = "unregD"   -> [s EXCEPT !.ok = s.ok /\ s.dreg, !.dreg = FALSE]
         [] c = "updD"     -> [s EXCEPT !.ok = s.ok /\ s.dreg]
         [] c = "authC1"   -> [s EXCEPT !.ok = s.ok /\ s.c1 # "resigned", !.c1 = "auth"]
         [] c = "resignC1" -> [s EXCEPT !.ok = s.ok /\ (s.c1 # "resigned" \/ again),
                                        !.c1 = "resigned"]
         [] c = "authC2"   -> [s EXCEPT !.ok = s.ok /\ C2Member(s, spec) /\ s.c2 # "resigned",
                                        !.c2 = "auth"]
         [] c = "resignC2" -> [s EXCEPT !.ok = s.ok /\ C2Member(s, spec)
                                               /\ (s.c2 # "resigned" \/ again),
                                        !.c2 = "resigned"]
         [] OTHER          -> s

\* In English: a level's certificates, then its proposal [V1]. The mutation
\* lets the level's own proposal count for its certificates.
\* Literally: "CLevel of s, l and spec is defined as: if not spec and
\*   Mutation equals "GoComSameLevel" then CCert of (s with c2prop replaced
\*   by (s's c2prop or l's pc)), l's cert and spec, else (letting t be CCert of
\*   s, l's cert and spec) t with c2prop replaced by (t's c2prop or l's pc)."
CLevel(s, l, spec) ==
    IF ~spec /\ Mutation = "GoComSameLevel"
    THEN CCert([s EXCEPT !.c2prop = s.c2prop \/ l.pc], l.cert, spec)
    ELSE LET t == CCert(s, l.cert, spec) IN [t EXCEPT !.c2prop = t.c2prop \/ l.pc]

\* In English: run the levels in turn.
RECURSIVE CRun(_, _, _)
\* Literally: "CRun of lv, s and spec is defined as: if lv equals the empty
\*   tuple then s, else CRun of the tail of lv, CLevel of s, the head of lv and
\*   spec, and spec."
CRun(lv, s, spec) ==
    IF lv = <<>> THEN s ELSE CRun(Tail(lv), CLevel(s, Head(lv), spec), spec)

\* In English: the reference's decision for a batch of family 2.
\* Literally: "SpecCom of b is defined as: if b's valid then CRun of b's subs
\*   followed by the tuple of b's top, C0 and TRUE's ok."
SpecCom(b) == b.valid => CRun(b.subs \o <<b.top>>, C0, TRUE).ok

\* In English: gOuroboros' decision; the mutation judges every level against
\* the original state.
\* Literally: "GoCom of b is defined as: if b's valid then, letting lv be
\*   b's subs followed by the tuple of b's top: if Mutation equals
\*   "GoComUnthreaded" then for all k in the domain of lv, CLevel of C0, lv of k
\*   and FALSE's ok, else CRun of lv, C0 and FALSE's ok."
GoCom(b) ==
    b.valid =>
        LET lv == b.subs \o <<b.top>>
        IN IF Mutation = "GoComUnthreaded"
           THEN \A k \in DOMAIN lv : CLevel(C0, lv[k], FALSE).ok
           ELSE CRun(lv, C0, FALSE).ok

-----------------------------------------------------------------------------
(* The table questions.                                                    *)

\* In English: family 1 reads reg, dreg, cc and pool; family 2 dreg and c1.
\* Each family is asked in the states where the other family's variables
\* sit at one value, to keep the table small.
\* Literally: "GoAgrees is defined as: (if c1 equals "member", then for all b
\*   in GBatches, GoGov of b if and only if SpecGov of b); and (if reg and not
\*   cc and not pool, then for all b in CBatches, GoCom of b if and only if
\*   SpecCom of b)."
GoAgrees ==
    /\ c1 = "member" => \A b \in GBatches : GoGov(b) <=> SpecGov(b)
    /\ (reg /\ ~cc /\ ~pool) => \A b \in CBatches : GoCom(b) <=> SpecCom(b)

\* Table probes, each expected to be violated.
\* In English: "the top never votes on the sub-transaction's proposal".
\* Literally: "ProbeNoVoteOnSubProposal is defined as: if reg and dreg, then
\*   SpecGov of the valid batch whose sub-transaction proposes and whose top
\*   votes as the DRep on the sub-transaction's proposal is not true."
ProbeNoVoteOnSubProposal ==
    (reg /\ dreg /\ c1 = "member") =>
        ~SpecGov([valid |-> TRUE,
                  subs |-> <<[cert |-> "none", prop |-> TRUE,
                              vote |-> [voter |-> "none", target |-> "orig"]]>>,
                  top |-> [cert |-> "none", prop |-> FALSE,
                           vote |-> [voter |-> "drep", target |-> "sub"]]])
\* In English: "C2 never authorizes a hot key in a batch" (false: after an
\* earlier level proposes it).
\* Literally: "ProbeNoProposedMemberAuth is defined as: if reg and not cc and
\*   not pool, then SpecCom of the valid batch whose sub-transaction proposes
\*   C2 and whose top authorizes C2's hot key is not true."
ProbeNoProposedMemberAuth ==
    (reg /\ ~cc /\ ~pool) =>
        ~SpecCom([valid |-> TRUE,
                  subs |-> <<[cert |-> "none", pc |-> TRUE]>>,
                  top |-> [cert |-> "authC2", pc |-> FALSE]])

-----------------------------------------------------------------------------
(* TableSpec.                                                              *)

\* In English: any registration state.
\* Literally: "TableInit is defined as: reg, dreg, cc and pool are members of
\*   BOOLEAN, and c1 is a member of the set containing "member", "auth" and
\*   "resigned"."
TableInit == /\ reg \in BOOLEAN /\ dreg \in BOOLEAN /\ cc \in BOOLEAN
             /\ pool \in BOOLEAN /\ c1 \in {"member", "auth", "resigned"}

\* In English: start in any TableInit state and never move.
\* Literally: "TableSpec is defined as: TableInit holds at the start, and
\*   always, every step is a step that leaves vars unchanged."
TableSpec == TableInit /\ [][UNCHANGED vars]_vars
=============================================================================
