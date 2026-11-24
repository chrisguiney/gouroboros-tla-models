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
(*   [G4] Gov.lagda.md 503-509; Rules/Gov.hs 361-362 (checkVotesAreValid):  *)
(*        a vote names an action in proposalsActionsMap, the live          *)
(*        proposals; an enacted root is not in it (GovActionsDoNotExist).  *)
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
    LiveOnlyLookup,   \* TRUE: the state does not answer GovActionById for an
                      \*   action enacted before the current root (see README)
    RootNotLive,      \* TRUE: the state does not answer GovActionById for a
                      \*   purpose's current root either; only live proposals
                      \*   are found, as the reference's proposalsActionsMap
    ThreadRoot,       \* TRUE: ratification compares with the root as updated
                      \*   by earlier enactments in the same pass [R1]
    Delay,            \* TRUE: a delaying enactment stops the rest of the pass [R1]
    PruneAfterExpiry  \* TRUE: rivals are found in the tree left after expired
                      \*   actions are removed [E1]

ASSUME N \in Nat /\ MaxEpoch \in Nat /\ Lifetime \in Nat

\* In English: "The ids an action can have."
\* Literally: "Ids is defined as 1 through N."
Ids == 1..N
\* Literally: "None is defined as 0."
None == 0                         \* "no predecessor" / "nothing enacted yet"

\* Three kinds of action are enough to show every rule: a delaying one with
\* a purpose (HF = HardForkInitiation), a non-delaying one with a purpose
\* (PP = ParameterChange), and one with no purpose at all
\* (TW = TreasuryWithdrawals). The other four kinds behave like one of these.
\* Literally: "Kinds is defined as the set containing "HF", "PP" and "TW"."
Kinds == {"HF", "PP", "TW"}
\* Literally: "Purposes is defined as the set containing "HF" and "PP"."
Purposes == {"HF", "PP"}

\* In English: the reference's actionPriority; lower is ratified first [R3].
\* Literally: "Priority of k is defined as: in the case k equals "HF", 3; in the
\*   case k equals "PP", 4; in the case k equals "TW", 5."
Priority(k) == CASE k = "HF" -> 3 [] k = "PP" -> 4 [] k = "TW" -> 5

\* In English: only HardForkInitiation of our three kinds is delaying [R2].
\* Literally: "Delaying of k is defined as: k equals "HF"."
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
    sawDelay,  \* TRUE once a delay stopped an action that would have passed
    deadVote   \* TRUE once a vote was accepted on an action that is not live

\* Literally: "vars is defined as the tuple of epoch, nextId, kind, prev,
\*   expires, status, accepted, everEnacted, root, snap, snapAcc, refunds, log,
\*   agree, sawDelay and deadVote."
vars == <<epoch, nextId, kind, prev, expires, status, accepted, everEnacted,
          root, snap, snapAcc, refunds, log, agree, sawDelay, deadVote>>

\* In English: the actions that are still waiting for a decision.
\* Literally: "Live is defined as the set of every i in Ids such that status of
\*   i equals "live"."
Live == {i \in Ids : status[i] = "live"}

\* In English: a predecessor p is acceptable for a new action of purpose k
\* when p is that purpose's root, or a live action of the same purpose [G1].
\* With LiveOnlyLookup off, the ledger state also answers for an action that
\* was enacted long ago and is no longer the root, and the check, which
\* trusts that answer, lets it through.
\* Literally: "ParentOk of k and p is defined as: p equals root of k; or p is a
\*   member of Live and kind of p equals k; or LiveOnlyLookup is not true and p
\*   is a member of everEnacted and kind of p equals k."
ParentOk(k, p) ==
    \/ p = root[k]                                      \* the current root
    \/ p \in Live /\ kind[p] = k                        \* a live rival chain
    \/ ~LiveOnlyLookup /\ p \in everEnacted /\ kind[p] = k \* a stale answer

\* In English: the actions GovActionById answers for. The reference's
\* GovActionsDoNotExist check looks a voted-on id up in the live proposals
\* only [G4]; an enacted root is not among them. gOuroboros'
\* UtxoValidateUnknownGovActionIds accepts any id the state answers for.
\* Literally: "Found is defined as the union of Live, (if RootNotLive then the
\*   empty set, else the set of root of q, for every q that is a member of
\*   Purposes, without the members of the set containing None), and (if
\*   LiveOnlyLookup then the empty set, else everEnacted)."
Found ==
    Live
    \cup (IF RootNotLive THEN {} ELSE {root[q] : q \in Purposes} \ {None})
    \cup (IF LiveOnlyLookup THEN {} ELSE everEnacted)

\* In English: "Nothing proposed, nothing enacted, epoch 0."
\* Literally: "Init is defined as: epoch equals 0, and nextId equals 1, and kind
\*   equals the function that maps every i in Ids to "TW", and prev equals the
\*   function that maps every i in Ids to None, and expires equals the function
\*   that maps every i in Ids to 0, and status equals the function that maps
\*   every i in Ids to "none", and accepted equals the empty set, and
\*   everEnacted equals the empty set, and root equals the function that maps
\*   every p in Purposes to None, and snap equals the empty set, and snapAcc
\*   equals the empty set, and refunds equals the function that maps every i in
\*   Ids to 0, and log equals the empty sequence, and agree equals TRUE, and
\*   sawDelay equals FALSE, and deadVote equals FALSE."
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
    /\ deadVote = FALSE

(***************************************************************************)
(* GOV: proposing an action [G1][G3].                                      *)
(***************************************************************************)
\* In English: a transaction proposes action number nextId, of kind k,
\* naming predecessor p. A TreasuryWithdrawals names none. With the ancestry
\* check on, p must pass ParentOk; with it off, p may be any earlier action.
\* Literally: "Propose is defined as: nextId is less than or equal to N, and
\*   epoch is less than MaxEpoch, and there exists a k in Kinds and a p in the
\*   union of the set containing None and 1 through (nextId minus 1) such that
\*   (if k equals "TW" then p equals None, else if CheckAncestry, then ParentOk
\*   of k and p) and kind in the next state equals kind except that its nextId
\*   entry is k and prev in the next state equals prev except that its nextId
\*   entry is p; and expires in the next state equals expires except that its
\*   nextId entry is epoch plus Lifetime, and status in the next state equals
\*   status except that its nextId entry is "live", and nextId in the next state
\*   equals nextId plus 1, and epoch, accepted, everEnacted, root, snap,
\*   snapAcc, refunds, log, agree, sawDelay and deadVote are unchanged."
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
                   refunds, log, agree, sawDelay, deadVote>>

(***************************************************************************)
(* GOV: voting [G2]. Who may vote on what is a pure table; it is tested in *)
(* Go (README). Here a vote just makes an action "accepted".               *)
(***************************************************************************)
\* In English: enough yes votes arrive for action i. GOV lets a vote
\* through when the state finds i [G4] and the epoch is not past i's
\* expiresAfter [G2]. A vote that gets through on an action that is not
\* live is recorded in deadVote.
\* Literally: "Vote is defined as: there exists an i in Found such that i is not
\*   a member of accepted, and epoch is less than or equal to expires of i, and
\*   accepted in the next state equals the union of accepted and the set
\*   containing i, and deadVote in the next state equals (deadVote or i is not a
\*   member of Live), and epoch, nextId, kind, prev, expires, status,
\*   everEnacted, root, snap, snapAcc, refunds, log, agree and sawDelay are
\*   unchanged."
Vote ==
    \E i \in Found :
        /\ i \notin accepted
        /\ epoch <= expires[i]                       \* [G2] not expired
        /\ accepted' = accepted \cup {i}
        /\ deadVote' = (deadVote \/ i \notin Live)
        /\ UNCHANGED <<epoch, nextId, kind, prev, expires, status,
                       everEnacted, root, snap, snapAcc, refunds, log,
                       agree, sawDelay>>

(***************************************************************************)
(* RATIFY [R1]-[R4]: one pass over the snapshot, in priority order.        *)
(***************************************************************************)
\* In English: the order an action is ratified in, priority first, then
\* the order it was proposed in (ids are handed out in proposal order).
\* Literally: "Rank of i is defined as Priority of kind of i, times (N plus 1),
\*   plus i."
Rank(i) == Priority(kind[i]) * (N + 1) + i

\* In English: the set S as a list sorted by Rank.
RECURSIVE Sorted(_)
\* Literally: "Sorted of S is defined as: if S equals the empty set then the
\*   empty sequence, else, letting m be the i, chosen from S, such that for all
\*   j in S, Rank of i is less than or equal to Rank of j: the tuple of m
\*   followed by Sorted of (S without the members of the set containing m)."
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
\* Literally: "Ratify of seq, r, d, en, ex and blk is defined as: if seq equals
\*   the empty sequence then the record whose field enacted is en, field expired
\*   is ex and field blocked is blk; else, letting i be the head of seq, k be
\*   kind of i, prevOk be k equals "TW" or prev of i equals r of k, and held be
\*   Delay and d: if i is a member of snapAcc and prevOk and held is not true,
\*   then Ratify of the tail of seq, (if k equals "TW" or ThreadRoot is not true
\*   then r, else r except that its k entry is i), Delaying of k, en with i
\*   appended, ex, and blk; else Ratify of the tail of seq, r, d, en, (if
\*   expires of i is less than epoch then the union of ex and the set containing
\*   i, else ex), and (blk or (i is a member of snapAcc and prevOk and held))."
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
\* Literally: "Closure of S and L is defined as: letting more be the set of
\*   every j in L such that prev of j is a member of S, without the members of
\*   S: if more equals the empty set then S, else Closure of the union of S and
\*   more, and L."
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
\* Literally: "Enact of seq, L, L0, rt, pruned and lg is defined as: if seq
\*   equals the empty sequence then the record whose field live is L, field root
\*   is rt, field pruned is pruned and field log is lg; else, letting i be the
\*   head of seq; k be kind of i; entry be the record whose field id is i, field
\*   prev is prev of i, field root is (if k equals "TW" then None, else rt of
\*   k), field inTree is (i is a member of L), field epoch is epoch, and field
\*   delaying is Delaying of k; from be: if PruneAfterExpiry then L, else L0;
\*   rivals be: if k equals "TW" then the empty set, else the set of every j in
\*   from such that kind of j equals k and prev of j equals rt of k and j does
\*   not equal i; and gone be Closure of rivals and from: Enact of the tail of
\*   seq, (L without the members of gone) without the members of the set
\*   containing i, (L0 without the members of gone) without the members of the
\*   set containing i, (if k equals "TW" then rt, else rt except that its k
\*   entry is i), pruned with gone appended, and lg with entry appended."
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
\* Literally: "Orphans of L and rt is defined as: letting o be the set of every
\*   j in L such that kind of j is a member of Purposes and (prev of j equals rt
\*   of kind of j, or (prev of j is a member of L and kind of prev of j equals
\*   kind of j)) is not true: if o equals the empty set then the empty set, else
\*   the union of o and Orphans of (L without the members of o) and rt."
Orphans(L, rt) ==
    LET o == {j \in L : kind[j] \in Purposes
                        /\ ~(prev[j] = rt[kind[j]]
                             \/ (prev[j] \in L /\ kind[prev[j]] = kind[j]))}
    IN IF o = {} THEN {} ELSE o \cup Orphans(L \ o, rt)

\* In English: how many of the sets in the list ps contain j.
\* Literally: "TimesIn of j and ps is defined as the number of members of the
\*   set of every x in 1 through the length of ps such that j is a member of ps
\*   of x."
TimesIn(j, ps) == Cardinality({x \in 1..Len(ps) : j \in ps[x]})

\* In English: the epoch boundary. Ratify the snapshot; remove expired
\* actions and their descendants; enact the ratified ones in order, removing
\* their rivals; refund every removed action once per time it was removed;
\* move to the next epoch and take a new snapshot of the actions and votes.
\* Literally: "EpochBoundary is defined as: epoch is less than MaxEpoch, and,
\*   letting res be Ratify of Sorted of snap, root, FALSE, the empty sequence,
\*   the empty set, and FALSE; enSet be the set of res's enacted of x, for every
\*   x that is a member of 1 through the length of res's enacted; expGone be
\*   Closure of res's expired and Live; out be Enact of res's enacted, Live
\*   without the members of expGone, Live, root, the empty sequence, and log;
\*   specLive be, letting left be (Live without the members of enSet) without
\*   the members of res's expired: left without the members of Orphans of left
\*   and out's root; and removals be the tuple of expGone and enSet followed by
\*   out's pruned: status in the next state equals the function that maps every
\*   i in Ids to: if i is a member of enSet then "enacted", else if i is a
\*   member of res's expired then "expired", else if status of i equals "live"
\*   and i is not a member of out's live then "pruned", else status of i; and
\*   refunds in the next state equals the function that maps every i in Ids to
\*   refunds of i plus TimesIn of i and removals, and root in the next state
\*   equals out's root, and everEnacted in the next state equals the union of
\*   everEnacted and enSet, and log in the next state equals out's log, and
\*   agree in the next state equals (agree and specLive equals out's live), and
\*   sawDelay in the next state equals (sawDelay or res's blocked), and snap in
\*   the next state equals out's live, and snapAcc in the next state equals the
\*   intersection of accepted and out's live, and accepted in the next state
\*   equals the intersection of accepted and out's live; and epoch in the next
\*   state equals epoch plus 1, and nextId, kind, prev, expires and deadVote are
\*   unchanged."
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
    /\ UNCHANGED <<nextId, kind, prev, expires, deadVote>>

\* In English: at the horizon nothing more happens; stepping in place keeps
\* TLC from calling that a deadlock, while a stuck state earlier still is.
\* Literally: "Done is defined as: epoch equals MaxEpoch, and vars is
\*   unchanged."
Done ==
    /\ epoch = MaxEpoch
    /\ UNCHANGED vars

\* In English: "Each step proposes, votes, crosses an epoch boundary, or stops."
\* Literally: "Next is defined as: Propose or Vote or EpochBoundary or Done."
Next == Propose \/ Vote \/ EpochBoundary \/ Done

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
\* In English: every variable holds the kind of value it should.
\* Literally: "TypeOK is defined as: epoch is a member of 0 through MaxEpoch,
\*   and nextId is a member of 1 through (N plus 1), and status is a member of
\*   the set of functions from Ids to the set containing "none", "live",
\*   "enacted", "expired" and "pruned", and root is a member of the set of
\*   functions from Purposes to the union of the set containing None and Ids,
\*   and refunds is a member of the set of functions from Ids to Nat, and
\*   deadVote is a member of BOOLEAN."
TypeOK ==
    /\ epoch \in 0..MaxEpoch
    /\ nextId \in 1..(N + 1)
    /\ status \in [Ids -> {"none", "live", "enacted", "expired", "pruned"}]
    /\ root \in [Purposes -> {None} \cup Ids]
    /\ refunds \in [Ids -> Nat]
    /\ deadVote \in BOOLEAN

\* In English: every live action with a purpose hangs off the tree: its
\* predecessor is the purpose's root or another live action of the same
\* purpose. This is what the GOV ancestry check is for [G1].
\* Literally: "TreeWellFormed is defined as: for all j in Live, if kind of j is
\*   a member of Purposes, then prev of j equals root of kind of j, or prev of j
\*   is a member of Live and kind of prev of j equals kind of j."
TreeWellFormed ==
    \A j \in Live :
        kind[j] \in Purposes =>
            \/ prev[j] = root[kind[j]]
            \/ prev[j] \in Live /\ kind[prev[j]] = kind[j]

\* In English: when an action is enacted, the predecessor it names is the
\* last enacted action of its purpose, and it was still in the tree. The
\* reference asserts both in proposalsApplyEnactment [E1].
\* Literally: "EnactedPrevMatchesRoot is defined as: for all x in 1 through the
\*   length of log, log of x's prev equals log of x's root and log of x's
\*   inTree."
EnactedPrevMatchesRoot ==
    \A x \in 1..Len(log) : log[x].prev = log[x].root /\ log[x].inTree

\* In English: within one boundary, nothing is enacted after a delaying
\* action, so at most one delaying action is enacted per epoch [R1].
\* Literally: "DelayingIsLast is defined as: for all x and y in 1 through the
\*   length of log, if x is less than y and log of x's epoch equals log of y's
\*   epoch, then log of x's delaying is not true."
DelayingIsLast ==
    \A x, y \in 1..Len(log) :
        (x < y /\ log[x].epoch = log[y].epoch) => ~log[x].delaying

\* In English: a deposit is paid back exactly once, when and only when its
\* action leaves the proposals [E2].
\* Literally: "DepositsReturnedOnce is defined as: for all i in Ids, refunds of
\*   i is less than or equal to 1, and (refunds of i equals 1) if and only if
\*   (status of i is a member of the set containing "enacted", "expired" and
\*   "pruned")."
DepositsReturnedOnce ==
    \A i \in Ids :
        /\ refunds[i] <= 1
        /\ (refunds[i] = 1) <=> (status[i] \in {"enacted", "expired", "pruned"})

\* In English: no vote is accepted on an action that was enacted, expired
\* or pruned: GOV refuses a vote naming anything but a live proposal [G4].
\* Literally: "VotesOnlyLive is defined as: deadVote is not true."
VotesOnlyLive == ~deadVote

\* In English: the spec's orphan removal leaves the same actions as the
\* reference's tree pruning [E3].
\* Literally: "SpecAgrees is defined as agree."
SpecAgrees == agree

(***************************************************************************)
(* Reachability probes: each claims something never happens. Each is       *)
(* expected to be violated, which shows the passing run is not vacuous.    *)
(***************************************************************************)
\* In English: "Nothing is ever enacted."
\* Literally: "NeverEnacted is defined as: the length of log equals 0."
NeverEnacted == Len(log) = 0
\* In English: "No action ever expires."
\* Literally: "NeverExpired is defined as: for all i in Ids, status of i does
\*   not equal "expired"."
NeverExpired == \A i \in Ids : status[i] # "expired"
\* In English: "No action is ever pruned."
\* Literally: "NeverPruned is defined as: for all i in Ids, status of i does not
\*   equal "pruned"."
NeverPruned == \A i \in Ids : status[i] # "pruned"
\* In English: "A delay never stops an action that would have passed."
\* Literally: "NeverDelayed is defined as: sawDelay is not true."
NeverDelayed == ~sawDelay
\* In English: no action is enacted in the same boundary as its predecessor.
\* Literally: "NeverChained is defined as: for all x and y in 1 through the
\*   length of log, if x is less than y and log of x's epoch equals log of y's
\*   epoch, then log of y's prev does not equal log of x's id."
NeverChained ==
    \A x, y \in 1..Len(log) :
        (x < y /\ log[x].epoch = log[y].epoch) => log[y].prev # log[x].id
=============================================================================
