--------------------------- MODULE ChainSelection ---------------------------
(***************************************************************************)
(* Praos chain selection: one node holds a selected chain and is offered  *)
(* candidate forks. It switches when the candidate is preferred and the   *)
(* switch rolls back at most k blocks. Every block a candidate adds has   *)
(* passed header validation's slot and operational-certificate counter    *)
(* checks against the candidate's own prefix.                             *)
(*                                                                         *)
(* The model runs the reference rule and the gOuroboros rule side by side *)
(* on every offer and asks whether they ever decide differently.          *)
(*                                                                         *)
(* Sources (README.md has links). ouroboros-consensus commit ec239d57,    *)
(* cardano-ledger commit 1210d37f.                                         *)
(*   [R1] ouroboros-consensus-protocol/.../Protocol/Praos/Common.hs        *)
(*        138-180: comparePraos. Same issuer and slot: higher issue number *)
(*        wins. Otherwise the lower VRF wins, if the VRF is "armed":       *)
(*        always, or (restricted) only for tips at most maxDist slots      *)
(*        apart. 283: preferCandidate is comparePraos.                    *)
(*   [R2] ouroboros-consensus/.../Protocol/Abstract.hs 392-398: the block  *)
(*        number is compared first; the tiebreaker only at equal height.  *)
(*   [R3] ouroboros-consensus-cardano/.../Shelley/Ledger/Config.hs 86-93:  *)
(*        Unrestricted before Conway, RestrictedVRFTiebreaker 5 from it.  *)
(*   [R5] docs/tech-reports/report/chapters/storage/chainselection.tex    *)
(*        94-98: candidates must intersect the current chain within k     *)
(*        blocks of its tip, or adopting them would roll back more than k. *)
(*   [R6] ouroboros-consensus-protocol/.../Protocol/PolyPraos.hs 1062-1069 *)
(*        and 1080-1087: counter m (0 for a registered pool with no entry)*)
(*        must satisfy m <= n and, in Praos, n <= m + 1.                  *)
(*   [R7] cardano-ledger libs/cardano-protocol-tpraos/.../Rules/OCert.hs  *)
(*        101-107: TPraos checks m <= n only.                             *)
(*   [R8] ouroboros-consensus/.../HeaderValidation.hs 378-423: slot must  *)
(*        be at least the minimum next slot (previous + 1 for Shelley).   *)
(*                                                                         *)
(* gOuroboros: consensus/selection.go (Compare, IsDeepFork),              *)
(* consensus/selection_preference.go (PreferCandidate,                     *)
(* PreferCandidateWithDensity), consensus/validate.go                      *)
(* (validateOpCertSequence, validateSlotOrdering).                        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla.         *)
(* New here:                                                               *)
(*   s \o t           the list s followed by the list t                   *)
(*   SubSeq(s, a, b)  items a..b of list s (empty when b < a)             *)
(*   Cardinality(S)   how many things are in set S (from FiniteSets)      *)
(*   UNION {S1, S2}   every thing in any of the sets                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets   \* Integers: Compare returns -1

CONSTANTS
    K,          \* the security parameter: the most blocks a switch may roll back
    MaxLen,     \* the longest chain the model builds (keeps it finite)
    MaxSlot,    \* slots run 1..MaxSlot
    IssueNos,   \* the operational-certificate issue numbers a block may carry
    Restricted, \* TRUE: the Conway VRF restriction of [R3] is in force
    MaxDist,    \* its distance; 5 in Cardano [R3], smaller here to fit the slots
    CPraos,     \* TRUE: Praos counter rule (upper bound too); FALSE: TPraos [R7]
    Routing,    \* how gOuroboros is called; see GoSwitch
    Window,     \* the Genesis window in slots, used only by Routing "GoDensity"
    Mutation    \* "none", or the name of one rule changed in the gOuroboros side

\* Two pools. Their cold keys are what "issuer" means.
Issuers == {"a", "b"}
Slots   == 1..MaxSlot

\* In English: a block is its slot, the pool that issued it, and the issue
\* number of the operational certificate it carries.
Blocks == [slot : Slots, issuer : Issuers, ino : IssueNos]

\* In English: the VRF output is fixed by the issuer and the slot (it is a
\* function of the VRF key, the slot and the epoch nonce [R1, comment at
\* 212-215]). The two pools take turns having the lower value, so both
\* orders happen. Lower is better.
VrfOf(b) == IF (b.issuer = "a") = (b.slot % 2 = 1) THEN 1 ELSE 2

Last(c) == c[Len(c)]
Max(S)  == CHOOSE x \in S : \A y \in S : y <= x
Dist(s, t) == IF s >= t THEN s - t ELSE t - s

\* In English: the counter recorded for pool i after chain c is the issue
\* number of i's latest block on c, or 0 when c has none (a registered pool
\* with no entry starts at 0 [R6]).
Counter(c, i) ==
    LET mine == {j \in 1..Len(c) : c[j].issuer = i}
    IN  IF mine = {} THEN 0 ELSE c[Max(mine)].ino

\* In English: the counter rule as the reference states it [R6][R7]: the
\* issue number never goes down and, in Praos, goes up by at most one.
SpecCounterOk(m, n) == m <= n /\ (CPraos => n <= m + 1)

\* In English: the rule gOuroboros applies (validateOpCertSequence). The
\* "NoUpperBound" mutation drops its CPraos-only "skipped ahead" check.
GoCounterOk(m, n) ==
    /\ m <= n                                         \* "rolled back"
    /\ (CPraos /\ Mutation # "NoUpperBound") => n <= m + 1  \* "skipped ahead"

\* In English: block b may follow chain c when its slot is later than c's
\* tip [R8] and its issue number passes the counter rule against c.
ValidNext(c, b) ==
    /\ Len(c) = 0 \/ b.slot > Last(c).slot
    /\ GoCounterOk(Counter(c, b.issuer), b.ino)

\* In English: the blocks that may follow chain c.
NextBlocks(c) == {b \in Blocks : ValidNext(c, b)}

\* In English: every one- or two-block suffix that may follow chain c,
\* as long as the result is no longer than MaxLen.
Suffixes(c) ==
    {s \in UNION { {<<b>> : b \in NextBlocks(c)},
                   UNION { {<<b1, b2>> : b2 \in NextBlocks(Append(c, b1))}
                           : b1 \in NextBlocks(c) } } :
        Len(c) + Len(s) <= MaxLen}

(***************************************************************************)
(* The reference rule [R1][R2].                                            *)
(***************************************************************************)

\* In English: the reference prefers cand to ours when it is longer; at
\* equal height, when the tips share slot and issuer and cand's issue number
\* is higher; otherwise when the VRF is armed and cand's VRF is lower.
RefPrefer(ours, cand, restricted) ==
    IF Len(cand) # Len(ours) THEN Len(cand) > Len(ours)
    ELSE LET o == Last(ours)
             c == Last(cand)
         IN  IF o.slot = c.slot /\ o.issuer = c.issuer /\ o.ino # c.ino
             THEN c.ino > o.ino                               \* issue number armed
             ELSE /\ (~restricted \/ Dist(o.slot, c.slot) <= MaxDist) \* VRF armed
                  /\ VrfOf(c) < VrfOf(o)

\* In English: the reference switches only to a preferred candidate that
\* intersects the current chain within k blocks of its tip [R5].
RefSwitch(ours, cand, i) ==
    Len(ours) - i <= K /\ RefPrefer(ours, cand, Restricted)

(***************************************************************************)
(* The gOuroboros rule, as written in selection.go and                     *)
(* selection_preference.go. Each Mutation changes one line of it.          *)
(***************************************************************************)

\* In English: Compare's issue-number guard: same slot and same issuer.
IssueArmed(x, y) ==
    /\ Mutation = "AnySlot"   \/ x.slot = y.slot
    /\ Mutation = "AnyIssuer" \/ x.issuer = y.issuer

\* In English: Compare prefers the higher issue number.
IssueBetter(p, q) == IF Mutation = "LowerIssueNo" THEN p < q ELSE p > q

\* In English: Compare(a, b): 1 if a ranks above b, -1 if below, 0 if tied.
\* Height first, then the issue number when armed, then the lower VRF.
GoCompare(a, b) ==
    IF Len(a) # Len(b) THEN IF Len(a) > Len(b) THEN 1 ELSE -1
    ELSE LET x == Last(a)
             y == Last(b)
         IN  IF IssueArmed(x, y) /\ x.ino # y.ino
             THEN IF IssueBetter(x.ino, y.ino) THEN 1 ELSE -1
             ELSE IF VrfOf(x) < VrfOf(y) THEN 1
                  ELSE IF VrfOf(x) > VrfOf(y) THEN -1 ELSE 0

\* In English: PreferCandidate's Conway guard: equal-height tips too far
\* apart never switch.
TooFar(s, t) ==
    IF Mutation = "DistanceGE" THEN Dist(s, t) >= MaxDist ELSE Dist(s, t) > MaxDist

\* In English: PreferCandidate(current, candidate).
GoPreferCandidate(ours, cand) ==
    IF /\ Len(ours) > 0
       /\ Restricted
       /\ Len(ours) = Len(cand)
       /\ TooFar(Last(ours).slot, Last(cand).slot)
    THEN FALSE
    ELSE GoCompare(cand, ours) > 0

\* In English: the slot of the fork point (0 for the start of the chain).
ForkSlot(c, i) == IF i = 0 THEN 0 ELSE c[i].slot

\* In English: BlocksInWindow: the blocks of c whose slot is after the fork
\* slot f and at most Window slots after it.
InWindow(c, f) ==
    Cardinality({j \in 1..Len(c) : c[j].slot > f /\ c[j].slot - f <= Window})

\* In English: PreferCandidateWithDensity: a fork more than k blocks deep
\* (IsDeepFork) is decided by the window count when the counts differ;
\* everything else by PreferCandidate.
GoDensitySwitch(ours, cand, i) ==
    LET f == ForkSlot(ours, i)
    IN  IF Len(ours) - i > K /\ InWindow(cand, f) # InWindow(ours, f)
        THEN InWindow(cand, f) > InWindow(ours, f)
        ELSE GoPreferCandidate(ours, cand)

\* In English: how a caller uses gOuroboros.
\*   "GoPlain":   the caller drops forks deeper than k, then asks
\*                PreferCandidate. The k bound is the caller's: no
\*                gOuroboros entry point that takes no fork point can apply it.
\*   "GoDensity": the caller asks PreferCandidateWithDensity, which routes
\*                deep forks to the density rule instead of refusing them.
GoSwitch(ours, cand, i) ==
    IF Routing = "GoDensity" THEN GoDensitySwitch(ours, cand, i)
    ELSE Len(ours) - i <= K /\ GoPreferCandidate(ours, cand)

\* In English: the node follows the reference ("Ref") or gOuroboros.
Adopt(ours, cand, i) ==
    IF Routing = "Ref" THEN RefSwitch(ours, cand, i) ELSE GoSwitch(ours, cand, i)

\* In English: why a switch happened, for the probes.
Reason(ours, cand) ==
    IF Len(cand) # Len(ours) THEN "longer"
    ELSE IF /\ Last(cand).slot = Last(ours).slot
            /\ Last(cand).issuer = Last(ours).issuer
         THEN "ocert"
         ELSE "vrf"

VARIABLES
    chain,         \* the selected chain, oldest block first
    agree,         \* did the two rules decide the last offer the same way?
    lastRollback,  \* how many blocks the last switch rolled back
    lastReason,    \* why the last offer switched ("none" if it did not)
    blockedByDist  \* was the last offer refused only by the Conway distance rule?

vars == <<chain, agree, lastRollback, lastReason, blockedByDist>>

TypeOK ==
    /\ chain \in Seq(Blocks) /\ Len(chain) <= MaxLen
    /\ agree \in BOOLEAN
    /\ lastRollback \in 0..MaxLen
    /\ lastReason \in {"none", "longer", "ocert", "vrf"}
    /\ blockedByDist \in BOOLEAN

\* In English: the node starts at the genesis point with no blocks.
Init ==
    /\ chain = <<>>
    /\ agree = TRUE
    /\ lastRollback = 0
    /\ lastReason = "none"
    /\ blockedByDist = FALSE

\* In English: a peer offers the fork that keeps the first i blocks of the
\* selection and adds suffix s. Both rules decide it; the node acts on Adopt.
Offer(i, s) ==
    LET cand == SubSeq(chain, 1, i) \o s
        sw   == Adopt(chain, cand, i)
    IN  /\ agree' = (RefSwitch(chain, cand, i) = GoSwitch(chain, cand, i))
        /\ chain' = IF sw THEN cand ELSE chain               \* switch, or keep
        /\ lastRollback' = IF sw THEN Len(chain) - i ELSE 0
        /\ lastReason' = IF sw THEN Reason(chain, cand) ELSE "none"
        /\ blockedByDist' =                     \* refused, yet unrestricted would switch
               (~sw /\ Len(chain) - i <= K /\ RefPrefer(chain, cand, FALSE))

\* In English: some peer offers some fork from some point of the selection.
\* An offer is always possible (one block at slot 1 from genesis), so the
\* model never deadlocks and needs no terminal step.
Next ==
    \E i \in 0..Len(chain) :
        \E s \in Suffixes(SubSeq(chain, 1, i)) : Offer(i, s)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* What must always be true.                                               *)
(***************************************************************************)

\* In English: gOuroboros and the reference decide every offer the same way.
DecisionsAgree == agree

\* In English: no switch rolls back more than k blocks [R5].
NoRollbackBeyondK == lastRollback <= K

\* In English: every block of the selection passes the reference counter
\* rule against the blocks before it [R6][R7].
OpCertCountersOnChain ==
    \A j \in 1..Len(chain) :
        SpecCounterOk(Counter(SubSeq(chain, 1, j - 1), chain[j].issuer),
                      chain[j].ino)

\* In English: slots strictly increase along the selection [R8].
SlotsIncrease == \A j \in 2..Len(chain) : chain[j].slot > chain[j - 1].slot

(***************************************************************************)
(* Reachability probes: each claims something never happens. TLC must     *)
(* show that it does, or the invariants above could pass vacuously.        *)
(***************************************************************************)

\* Probe: a replacement hot key never wins on its issue number.
NeverSwitchedByOCert == lastReason # "ocert"

\* Probe: the VRF never decides a switch.
NeverSwitchedByVRF == lastReason # "vrf"

\* Probe: the Conway distance rule never refuses a switch.
NeverBlockedByDistance == ~blockedByDist
=============================================================================
