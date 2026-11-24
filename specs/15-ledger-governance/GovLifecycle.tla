---------------------------- MODULE GovLifecycle ----------------------------
(***************************************************************************)
(* The life of a Conway governance action: it is proposed with a deposit, *)
(* voted on, ratified at an epoch boundary in priority order, enacted, or *)
(* left to expire; enacting one action removes its rivals, and every      *)
(* removed action gets its deposit back.                                   *)
(*                                                                         *)
(* gOuroboros implements only the first step of this, the GOV checks a     *)
(* transaction must pass (ledger/conway/rules.go: UtxoValidateProposal-    *)
(* Ancestry, UtxoValidateVotingOnExpiredGovAction and their siblings).     *)
(* Ratification, enactment, expiry and deposit refunds belong to whoever   *)
(* keeps the ledger state (Dingo, or ouroboros-mock in the conformance     *)
(* tests). The model checks the lifecycle the reference defines, and the   *)
(* one place gOuroboros feeds it: the ancestry check at submission, and    *)
(* the GovActionById answer that check relies on.                          *)
(*                                                                         *)
(* Sources (README.md has links). Spec: IntersectMBO/formal-ledger-        *)
(* specifications 77acd80a, src/Ledger/Conway/Specification/. Reference:   *)
(* IntersectMBO/cardano-ledger 1210d37f, eras/conway/impl/src/Cardano/     *)
(* Ledger/Conway/ (paths below are relative to that).                      *)
(*   [G1] Gov.lagda.md 511-528; Rules/Gov.hs 561-566 with                  *)
(*        Governance/Proposals.hs 305-334: a proposal's predecessor must   *)
(*        be the purpose's root or a live proposal of the same purpose.    *)
(*   [G2] Gov.lagda.md 503-509; Rules/Gov.hs 356-362: a vote is refused    *)
(*        once the current epoch is past the action's expiresAfter.        *)
(*   [G3] Rules/Gov.hs 401-418: expiresAfter = proposal epoch + lifetime.  *)
(*   [R1] Ratify.lagda.md 605-629; Rules/Ratify.hs 336-361: in order, an  *)
(*        action is enacted when accepted, its predecessor is the current *)
(*        root, and nothing delaying was enacted before it in this pass;  *)
(*        an action not enacted expires when expiresAfter < epoch.         *)
(*   [R2] Ratify.lagda.md 614-621; Rules/Ratify.hs 284-291: delaying       *)
(*        actions are NoConfidence, UpdateCommittee, NewConstitution and  *)
(*        HardForkInitiation.                                              *)
(*   [R3] Governance/Internal.hs 540-550; Gov.lagda.md 206-211: actions    *)
(*        are ratified sorted by priority, oldest first within a priority.*)
(*   [R4] Governance/DRepPulser.hs 409-430; Governance.hs 474-518:         *)
(*        ratification runs over the proposals and votes as they were at  *)
(*        the previous boundary, with reCurrentEpoch = the epoch that is  *)
(*        now ending and rsDelayed = False at the start.                  *)
(*   [E1] Rules/Epoch.hs 300-339; Governance/Proposals.hs 499-563: at the *)
(*        boundary, expired actions are removed with their descendants,   *)
(*        then each enacted action becomes its purpose's root and its     *)
(*        siblings are removed with their descendants.                    *)
(*   [E2] Rules/Epoch.hs 183-195, 331-333: every removed action's deposit  *)
(*        goes back to its return account (or the treasury).               *)
(*   [E3] Epoch.lagda.md 609-660: the spec instead removes enacted and    *)
(*        expired actions and then every "orphan" whose predecessor is no *)
(*        longer the root or a remaining proposal.                         *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla. New     *)
(* here:                                                                   *)
(*   RECURSIVE F(_)   declares an operator that calls itself (TLC         *)
(*                    evaluates it like a recursive Go function)          *)
(*   s \o t           the list s followed by the list t                   *)
(*   Cardinality(S)   how many things are in the set S                    *)
(*   SelectSeq(s, P)  the items of list s for which P is true             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

\* The knobs. The passing configs set every behaviour switch to TRUE (what
\* the reference does); each *Bug config turns one off.
CONSTANTS
    N,                \* how many governance actions can be proposed (ids 1..N)
    MaxEpoch,         \* the last epoch the model reaches
    Lifetime,         \* govActionLifetime, in epochs [G3]
    CheckAncestry,    \* TRUE: GOV refuses a bad predecessor [G1]
    LiveOnlyLookup,   \* TRUE: the state answers GovActionById only for live
                      \*   proposals and the current roots (see README)
    ThreadRoot,       \* TRUE: ratification compares with the root as updated
                      \*   by earlier enactments in the same pass [R1]
    Delay,            \* TRUE: a delaying enactment stops the rest of the pass [R1]
    PruneAfterExpiry  \* TRUE: rivals are found in the tree left after expired
                      \*   actions are removed [E1]

ASSUME N \in Nat /\ MaxEpoch \in Nat /\ Lifetime \in Nat

Ids == 1..N
None == 0                         \* "no predecessor" / "nothing enacted yet"

\* Three kinds of action are enough to show every rule: a delaying one with
\* a purpose (HF = HardForkInitiation), a non-delaying one with a purpose
\* (PP = ParameterChange), and one with no purpose at all
\* (TW = TreasuryWithdrawals). The other four kinds behave like one of these.
Kinds == {"HF", "PP", "TW"}
Purposes == {"HF", "PP"}

\* In English: the reference's actionPriority; lower is ratified first [R3].
Priority(k) == CASE k = "HF" -> 3 [] k = "PP" -> 4 [] k = "TW" -> 5

\* In English: only HardForkInitiation of our three kinds is delaying [R2].
Delaying(k) == k = "HF"

VARIABLES
    epoch,     \* the current epoch
    nextId,    \* the id the next proposal gets; ids are handed out in order
    kind,      \* kind[i]: the action's kind
    prev,      \* prev[i]: the predecessor it names, or None
    expires,   \* expires[i]: its expiresAfter epoch [G3]
    status,    \* "none", "live", "enacted", "expired" or "pruned"
    accepted,  \* the actions whose votes are enough to pass (votes abstracted)
    everEnacted, \* every action ever enacted, kept so a careless lookup can find it
    root,      \* root[p]: the last enacted action of purpose p, or None
    snap,      \* the actions ratification will look at next boundary [R4]
    snapAcc,   \* which of those had enough votes when the snapshot was taken
    refunds,   \* refunds[i]: how many times i's deposit was paid back
    log,       \* every enactment, in order, with what the tree looked like
    agree,     \* FALSE once the spec's orphan removal and the reference's
               \*   tree pruning disagreed about what is left [E3]
    sawDelay   \* TRUE once a delay stopped an action that would have passed

vars == <<epoch, nextId, kind, prev, expires, status, accepted, everEnacted,
          root, snap, snapAcc, refunds, log, agree, sawDelay>>

\* In English: the actions that are still waiting for a decision.
Live == {i \in Ids : status[i] = "live"}

\* In English: a predecessor p is acceptable for a new action of purpose k
\* when p is that purpose's root, or a live action of the same purpose [G1].
\* With LiveOnlyLookup off, the ledger state also answers for an action that
\* was enacted long ago and is no longer the root, and the check, which
\* trusts that answer, lets it through.
ParentOk(k, p) ==
    \/ p = root[k]                                      \* the current root
    \/ p \in Live /\ kind[p] = k                        \* a live rival chain
    \/ ~LiveOnlyLookup /\ p \in everEnacted /\ kind[p] = k \* a stale answer

Init ==
    /\ epoch = 0
    /\ nextId = 1
    /\ kind = [i \in Ids |-> "TW"]
    /\ prev = [i \in Ids |-> None]
    /\ expires = [i \in Ids |-> 0]
    /\ status = [i \in Ids |-> "none"]
    /\ accepted = {}
    /\ everEnacted = {}
    /\ root = [p \in Purposes |-> None]
    /\ snap = {}
    /\ snapAcc = {}
    /\ refunds = [i \in Ids |-> 0]
    /\ log = <<>>
    /\ agree = TRUE
    /\ sawDelay = FALSE

(***************************************************************************)
(* GOV: proposing an action [G1][G3].                                      *)
(***************************************************************************)
\* In English: a transaction proposes action number nextId, of kind k,
\* naming predecessor p. A TreasuryWithdrawals names none. With the ancestry
\* check on, p must pass ParentOk; with it off, p may be any earlier action.
Propose ==
    /\ nextId <= N                                   \* ids left to hand out
    /\ epoch < MaxEpoch                              \* not past the horizon
    /\ \E k \in Kinds, p \in {None} \cup 1..(nextId - 1) :
        /\ IF k = "TW" THEN p = None                 \* no purpose, no predecessor
           ELSE CheckAncestry => ParentOk(k, p)      \* the GOV ancestry check
        /\ kind' = [kind EXCEPT ![nextId] = k]
        /\ prev' = [prev EXCEPT ![nextId] = p]
    /\ expires' = [expires EXCEPT ![nextId] = epoch + Lifetime]
    /\ status' = [status EXCEPT ![nextId] = "live"]   \* deposit now held
    /\ nextId' = nextId + 1
    /\ UNCHANGED <<epoch, accepted, everEnacted, root, snap, snapAcc,
                   refunds, log, agree, sawDelay>>

(***************************************************************************)
(* GOV: voting [G2]. Who may vote on what is a pure table; it is tested in *)
(* Go (README). Here a vote just makes an action "accepted".               *)
(***************************************************************************)
\* In English: enough yes votes arrive for live action i, which is allowed
\* only while the epoch is not past i's expiresAfter.
Vote ==
    \E i \in Live :
        /\ i \notin accepted
        /\ epoch <= expires[i]                       \* [G2] not expired
        /\ accepted' = accepted \cup {i}
        /\ UNCHANGED <<epoch, nextId, kind, prev, expires, status,
                       everEnacted, root, snap, snapAcc, refunds, log,
                       agree, sawDelay>>

(***************************************************************************)
(* RATIFY [R1]-[R4]: one pass over the snapshot, in priority order.        *)
(***************************************************************************)
\* In English: the order an action is ratified in, priority first, then
\* the order it was proposed in (ids are handed out in proposal order).
Rank(i) == Priority(kind[i]) * (N + 1) + i

\* In English: the set S as a list sorted by Rank.
RECURSIVE Sorted(_)
Sorted(S) ==
    IF S = {} THEN <<>>
    ELSE LET m == CHOOSE i \in S : \A j \in S : Rank(i) <= Rank(j)
         IN <<m>> \o Sorted(S \ {m})

\* In English: walk the sorted list. r is the ratifier's own copy of the
\* roots (its EnactState), d says whether a delaying action has been
\* enacted in this pass, en lists what was enacted, ex collects what
\* expired, and blk records whether a delay stopped an action that would
\* otherwise have been enacted. An action is enacted when it is accepted,
\* names the current root (TreasuryWithdrawals name nothing), and no delay
\* is in force; otherwise it expires if its expiresAfter is before the
\* epoch now ending.
RECURSIVE Ratify(_, _, _, _, _, _)
Ratify(seq, r, d, en, ex, blk) ==
    IF seq = <<>> THEN [enacted |-> en, expired |-> ex, blocked |-> blk]
    ELSE
      LET i == Head(seq)
          k == kind[i]
          prevOk == k = "TW" \/ prev[i] = r[k]               \* verifyPrev
          held == Delay /\ d                                 \* delayed
      IN IF i \in snapAcc /\ prevOk /\ ~held
         THEN Ratify(Tail(seq),
                     IF k = "TW" \/ ~ThreadRoot THEN r ELSE [r EXCEPT ![k] = i],
                     Delaying(k),                            \* rsDelayed .~
                     Append(en, i), ex, blk)
         ELSE Ratify(Tail(seq), r, d, en,
                     IF expires[i] < epoch THEN ex \cup {i} ELSE ex,
                     blk \/ (i \in snapAcc /\ prevOk /\ held))

(***************************************************************************)
(* EPOCH [E1][E2]: applying the result to the current proposals.           *)
(***************************************************************************)
\* In English: S together with every action in L that descends from S by
\* predecessor links (children, grandchildren, ...).
RECURSIVE Closure(_, _)
Closure(S, L) ==
    LET more == {j \in L : prev[j] \in S} \ S
    IN IF more = {} THEN S ELSE Closure(S \cup more, L)

\* In English: apply the enactments in order, as proposalsApplyEnactment
\* does. L is the tree left after removing expired actions, L0 the tree
\* before that. For each enacted action i of purpose k: its rivals are the
\* other children of the current root of k, removed with their descendants;
\* i leaves the tree and becomes the root. Each step logs what the tree's
\* root was and whether i was still in the tree.
RECURSIVE Enact(_, _, _, _, _, _)
Enact(seq, L, L0, rt, pruned, lg) ==
    IF seq = <<>> THEN [live |-> L, root |-> rt, pruned |-> pruned, log |-> lg]
    ELSE
      LET i == Head(seq)
          k == kind[i]
          entry == [id |-> i, prev |-> prev[i],
                    root |-> IF k = "TW" THEN None ELSE rt[k],
                    inTree |-> i \in L, epoch |-> epoch,
                    delaying |-> Delaying(k)]
          from == IF PruneAfterExpiry THEN L ELSE L0
          rivals == IF k = "TW" THEN {}
                    ELSE {j \in from : kind[j] = k /\ prev[j] = rt[k] /\ j # i}
          gone == Closure(rivals, from)
      IN Enact(Tail(seq), (L \ gone) \ {i}, (L0 \ gone) \ {i},
               IF k = "TW" THEN rt ELSE [rt EXCEPT ![k] = i],
               Append(pruned, gone), Append(lg, entry))

\* In English: the spec's way [E3]. Repeatedly drop every action of a
\* purpose whose predecessor is neither the root nor a remaining action of
\* the same purpose, until nothing changes.
RECURSIVE Orphans(_, _)
Orphans(L, rt) ==
    LET o == {j \in L : kind[j] \in Purposes
                        /\ ~(prev[j] = rt[kind[j]]
                             \/ (prev[j] \in L /\ kind[prev[j]] = kind[j]))}
    IN IF o = {} THEN {} ELSE o \cup Orphans(L \ o, rt)

\* In English: how many of the sets in the list ps contain j.
TimesIn(j, ps) == Cardinality({x \in 1..Len(ps) : j \in ps[x]})

\* In English: the epoch boundary. Ratify the snapshot; remove expired
\* actions and their descendants; enact the ratified ones in order, removing
\* their rivals; refund every removed action once per time it was removed;
\* move to the next epoch and take a new snapshot of the actions and votes.
EpochBoundary ==
    /\ epoch < MaxEpoch
    /\ LET res == Ratify(Sorted(snap), root, FALSE, <<>>, {}, FALSE)
           enSet == {res.enacted[x] : x \in 1..Len(res.enacted)}
           expGone == Closure(res.expired, Live)             \* [E1] step 1
           out == Enact(res.enacted, Live \ expGone, Live, root, <<>>, log)
           specLive == LET left == (Live \ enSet) \ res.expired
                       IN left \ Orphans(left, out.root)     \* [E3]
           removals == <<expGone, enSet>> \o out.pruned
       IN
       /\ status' = [i \in Ids |->
                       IF i \in enSet THEN "enacted"
                       ELSE IF i \in res.expired THEN "expired"
                       ELSE IF status[i] = "live" /\ i \notin out.live
                            THEN "pruned"
                       ELSE status[i]]
       /\ refunds' = [i \in Ids |-> refunds[i] + TimesIn(i, removals)] \* [E2]
       /\ root' = out.root
       /\ everEnacted' = everEnacted \cup enSet
       /\ log' = out.log
       /\ agree' = (agree /\ specLive = out.live)
       /\ sawDelay' = (sawDelay \/ res.blocked)
       /\ snap' = out.live                                   \* [R4]
       /\ snapAcc' = accepted \cap out.live
       /\ accepted' = accepted \cap out.live
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<nextId, kind, prev, expires>>

\* In English: at the horizon nothing more happens; stepping in place keeps
\* TLC from calling that a deadlock, while a stuck state earlier still is.
Done ==
    /\ epoch = MaxEpoch
    /\ UNCHANGED vars

Next == Propose \/ Vote \/ EpochBoundary \/ Done

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
\* In English: every variable holds the kind of value it should.
TypeOK ==
    /\ epoch \in 0..MaxEpoch
    /\ nextId \in 1..(N + 1)
    /\ status \in [Ids -> {"none", "live", "enacted", "expired", "pruned"}]
    /\ root \in [Purposes -> {None} \cup Ids]
    /\ refunds \in [Ids -> Nat]

\* In English: every live action with a purpose hangs off the tree: its
\* predecessor is the purpose's root or another live action of the same
\* purpose. This is what the GOV ancestry check is for [G1].
TreeWellFormed ==
    \A j \in Live :
        kind[j] \in Purposes =>
            \/ prev[j] = root[kind[j]]
            \/ prev[j] \in Live /\ kind[prev[j]] = kind[j]

\* In English: when an action is enacted, the predecessor it names is the
\* last enacted action of its purpose, and it was still in the tree. The
\* reference asserts both in proposalsApplyEnactment [E1].
EnactedPrevMatchesRoot ==
    \A x \in 1..Len(log) : log[x].prev = log[x].root /\ log[x].inTree

\* In English: within one boundary, nothing is enacted after a delaying
\* action, so at most one delaying action is enacted per epoch [R1].
DelayingIsLast ==
    \A x, y \in 1..Len(log) :
        (x < y /\ log[x].epoch = log[y].epoch) => ~log[x].delaying

\* In English: a deposit is paid back exactly once, when and only when its
\* action leaves the proposals [E2].
DepositsReturnedOnce ==
    \A i \in Ids :
        /\ refunds[i] <= 1
        /\ (refunds[i] = 1) <=> (status[i] \in {"enacted", "expired", "pruned"})

\* In English: the spec's orphan removal leaves the same actions as the
\* reference's tree pruning [E3].
SpecAgrees == agree

(***************************************************************************)
(* Reachability probes: each claims something never happens. Each is       *)
(* expected to be violated, which shows the passing run is not vacuous.    *)
(***************************************************************************)
NeverEnacted == Len(log) = 0
NeverExpired == \A i \in Ids : status[i] # "expired"
NeverPruned == \A i \in Ids : status[i] # "pruned"
NeverDelayed == ~sawDelay
\* In English: no action is enacted in the same boundary as its predecessor.
NeverChained ==
    \A x, y \in 1..Len(log) :
        (x < y /\ log[x].epoch = log[y].epoch) => log[y].prev # log[x].id
=============================================================================
