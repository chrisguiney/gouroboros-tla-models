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
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.         *)
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
\* Literally: "Issuers is defined as the set containing "a" and "b"."
Issuers == {"a", "b"}
\* Literally: "Slots is defined as 1 through MaxSlot."
Slots   == 1..MaxSlot

\* In English: a block is its slot, the pool that issued it, and the issue
\* number of the operational certificate it carries.
\* Literally: "Blocks is defined as the set of records whose field slot is a
\*   member of Slots, whose field issuer is a member of Issuers, and whose field
\*   ino is a member of IssueNos."
Blocks == [slot : Slots, issuer : Issuers, ino : IssueNos]

\* In English: the VRF output is fixed by the issuer and the slot (it is a
\* function of the VRF key, the slot and the epoch nonce [R1, comment at
\* 212-215]). The two pools take turns having the lower value, so both
\* orders happen. Lower is better.
\* Literally: "VrfOf of b is defined as: if (b's issuer equals "a") equals (b's
\*   slot modulo 2 equals 1) then 1, else 2."
VrfOf(b) == IF (b.issuer = "a") = (b.slot % 2 = 1) THEN 1 ELSE 2

\* In English: the last block of chain c.
\* Literally: "Last of c is defined as c of the length of c."
Last(c) == c[Len(c)]
\* In English: the largest number in S.
\* Literally: "Max of S is defined as the x, chosen from S, such that for all y
\*   in S, y is less than or equal to x."
Max(S)  == CHOOSE x \in S : \A y \in S : y <= x
\* In English: how far apart slots s and t are.
\* Literally: "Dist of s and t is defined as: if s is greater than or equal to t
\*   then s minus t, else t minus s."
Dist(s, t) == IF s >= t THEN s - t ELSE t - s

\* In English: the counter recorded for pool i after chain c is the issue
\* number of i's latest block on c, or 0 when c has none (a registered pool
\* with no entry starts at 0 [R6]).
\* Literally: "Counter of c and i is defined as: letting mine be the set of
\*   every j in 1 through the length of c such that c of j's issuer equals i:
\*   if mine equals the empty set then 0, else c of Max of mine's ino."
Counter(c, i) ==
    LET mine == {j \in 1..Len(c) : c[j].issuer = i}
    IN  IF mine = {} THEN 0 ELSE c[Max(mine)].ino

\* In English: the counter rule as the reference states it [R6][R7]: the
\* issue number never goes down and, in Praos, goes up by at most one.
\* Literally: "SpecCounterOk of m and n is defined as: m is less than or equal
\*   to n, and if CPraos, then n is less than or equal to m plus 1."
SpecCounterOk(m, n) == m <= n /\ (CPraos => n <= m + 1)

\* In English: the rule gOuroboros applies (validateOpCertSequence). The
\* "NoUpperBound" mutation drops its CPraos-only "skipped ahead" check.
\* Literally: "GoCounterOk of m and n is defined as: m is less than or equal to
\*   n, and if CPraos and Mutation does not equal "NoUpperBound", then n is less
\*   than or equal to m plus 1."
GoCounterOk(m, n) ==
    /\ m <= n                                         \* "rolled back"
    /\ (CPraos /\ Mutation # "NoUpperBound") => n <= m + 1  \* "skipped ahead"

\* In English: block b may follow chain c when its slot is later than c's
\* tip [R8] and its issue number passes the counter rule against c.
\* Literally: "ValidNext of c and b is defined as: (the length of c equals 0 or
\*   b's slot is greater than Last of c's slot), and GoCounterOk of Counter of c
\*   and b's issuer, and b's ino."
ValidNext(c, b) ==
    /\ Len(c) = 0 \/ b.slot > Last(c).slot
    /\ GoCounterOk(Counter(c, b.issuer), b.ino)

\* In English: the blocks that may follow chain c.
\* Literally: "NextBlocks of c is defined as the set of every b in Blocks such
\*   that ValidNext of c and b."
NextBlocks(c) == {b \in Blocks : ValidNext(c, b)}

\* In English: every one- or two-block suffix that may follow chain c,
\* as long as the result is no longer than MaxLen.
\* Literally: "Suffixes of c is defined as the set of every s in the union of
\*   (the set of the tuple of b, for every b that is a member of NextBlocks of
\*   c) and (the union of the set of (the set of the tuple of b1 and b2, for
\*   every b2 that is a member of NextBlocks of c with b1 appended), for every
\*   b1 that is a member of NextBlocks of c) such that the length of c plus the
\*   length of s is less than or equal to MaxLen."
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
\* Literally: "RefPrefer of ours, cand and restricted is defined as: if the
\*   length of cand does not equal the length of ours then the length of cand is
\*   greater than the length of ours, else, letting o be Last of ours and c be
\*   Last of cand: if o's slot equals c's slot and o's issuer equals c's issuer
\*   and o's ino does not equal c's ino then c's ino is greater than o's ino,
\*   else (restricted is not true or Dist of o's slot and c's slot is less than
\*   or equal to MaxDist) and VrfOf of c is less than VrfOf of o."
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
\* Literally: "RefSwitch of ours, cand and i is defined as: the length of ours
\*   minus i is less than or equal to K, and RefPrefer of ours, cand and
\*   Restricted."
RefSwitch(ours, cand, i) ==
    Len(ours) - i <= K /\ RefPrefer(ours, cand, Restricted)

(***************************************************************************)
(* The gOuroboros rule, as written in selection.go and                     *)
(* selection_preference.go. Each Mutation changes one line of it.          *)
(***************************************************************************)

\* In English: Compare's issue-number guard: same slot and same issuer.
\* Literally: "IssueArmed of x and y is defined as: (Mutation equals "AnySlot"
\*   or x's slot equals y's slot) and (Mutation equals "AnyIssuer" or x's issuer
\*   equals y's issuer)."
IssueArmed(x, y) ==
    /\ Mutation = "AnySlot"   \/ x.slot = y.slot
    /\ Mutation = "AnyIssuer" \/ x.issuer = y.issuer

\* In English: Compare prefers the higher issue number.
\* Literally: "IssueBetter of p and q is defined as: if Mutation equals
\*   "LowerIssueNo" then p is less than q, else p is greater than q."
IssueBetter(p, q) == IF Mutation = "LowerIssueNo" THEN p < q ELSE p > q

\* In English: Compare(a, b): 1 if a ranks above b, -1 if below, 0 if tied.
\* Height first, then the issue number when armed, then the lower VRF.
\* Literally: "GoCompare of a and b is defined as: if the length of a does not
\*   equal the length of b then (if the length of a is greater than the length
\*   of b then 1, else -1), else, letting x be Last of a and y be Last of b: if
\*   IssueArmed of x and y and x's ino does not equal y's ino then (if
\*   IssueBetter of x's ino and y's ino then 1, else -1), else if VrfOf of x is
\*   less than VrfOf of y then 1, else if VrfOf of x is greater than VrfOf of y
\*   then -1, else 0."
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
\* Literally: "TooFar of s and t is defined as: if Mutation equals "DistanceGE"
\*   then Dist of s and t is greater than or equal to MaxDist, else Dist of s
\*   and t is greater than MaxDist."
TooFar(s, t) ==
    IF Mutation = "DistanceGE" THEN Dist(s, t) >= MaxDist ELSE Dist(s, t) > MaxDist

\* In English: PreferCandidate(current, candidate).
\* Literally: "GoPreferCandidate of ours and cand is defined as: if the length
\*   of ours is greater than 0 and Restricted and the length of ours equals the
\*   length of cand and TooFar of Last of ours's slot and Last of cand's slot,
\*   then FALSE, else GoCompare of cand and ours is greater than 0."
GoPreferCandidate(ours, cand) ==
    IF /\ Len(ours) > 0
       /\ Restricted
       /\ Len(ours) = Len(cand)
       /\ TooFar(Last(ours).slot, Last(cand).slot)
    THEN FALSE
    ELSE GoCompare(cand, ours) > 0

\* In English: the slot of the fork point (0 for the start of the chain).
\* Literally: "ForkSlot of c and i is defined as: if i equals 0 then 0, else c
\*   of i's slot."
ForkSlot(c, i) == IF i = 0 THEN 0 ELSE c[i].slot

\* In English: BlocksInWindow: the blocks of c whose slot is after the fork
\* slot f and at most Window slots after it.
\* Literally: "InWindow of c and f is defined as the number of members of the
\*   set of every j in 1 through the length of c such that c of j's slot is
\*   greater than f and c of j's slot minus f is less than or equal to Window."
InWindow(c, f) ==
    Cardinality({j \in 1..Len(c) : c[j].slot > f /\ c[j].slot - f <= Window})

\* In English: PreferCandidateWithDensity: a fork more than k blocks deep
\* (IsDeepFork) is decided by the window count when the counts differ;
\* everything else by PreferCandidate.
\* Literally: "GoDensitySwitch of ours, cand and i is defined as: letting f be
\*   ForkSlot of ours and i: if the length of ours minus i is greater than K and
\*   InWindow of cand and f does not equal InWindow of ours and f, then InWindow
\*   of cand and f is greater than InWindow of ours and f, else
\*   GoPreferCandidate of ours and cand."
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
\* Literally: "GoSwitch of ours, cand and i is defined as: if Routing equals
\*   "GoDensity" then GoDensitySwitch of ours, cand and i, else the length of
\*   ours minus i is less than or equal to K and GoPreferCandidate of ours and
\*   cand."
GoSwitch(ours, cand, i) ==
    IF Routing = "GoDensity" THEN GoDensitySwitch(ours, cand, i)
    ELSE Len(ours) - i <= K /\ GoPreferCandidate(ours, cand)

\* In English: the node follows the reference ("Ref") or gOuroboros.
\* Literally: "Adopt of ours, cand and i is defined as: if Routing equals "Ref"
\*   then RefSwitch of ours, cand and i, else GoSwitch of ours, cand and i."
Adopt(ours, cand, i) ==
    IF Routing = "Ref" THEN RefSwitch(ours, cand, i) ELSE GoSwitch(ours, cand, i)

\* In English: why a switch happened, for the probes.
\* Literally: "Reason of ours and cand is defined as: if the length of cand does
\*   not equal the length of ours then "longer", else if Last of cand's slot
\*   equals Last of ours's slot and Last of cand's issuer equals Last of ours's
\*   issuer then "ocert", else "vrf"."
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

\* Literally: "vars is defined as the tuple of chain, agree, lastRollback,
\*   lastReason and blockedByDist."
vars == <<chain, agree, lastRollback, lastReason, blockedByDist>>

\* In English: every variable holds a value of the expected kind.
\* Literally: "TypeOK is defined as: chain is a member of the set of sequences
\*   of members of Blocks and the length of chain is less than or equal to
\*   MaxLen, and agree is a member of BOOLEAN, and lastRollback is a member of 0
\*   through MaxLen, and lastReason is a member of the set containing "none",
\*   "longer", "ocert" and "vrf", and blockedByDist is a member of BOOLEAN."
TypeOK ==
    /\ chain \in Seq(Blocks) /\ Len(chain) <= MaxLen
    /\ agree \in BOOLEAN
    /\ lastRollback \in 0..MaxLen
    /\ lastReason \in {"none", "longer", "ocert", "vrf"}
    /\ blockedByDist \in BOOLEAN

\* In English: the node starts at the genesis point with no blocks.
\* Literally: "Init is defined as: chain equals the empty sequence, and agree
\*   equals TRUE, and lastRollback equals 0, and lastReason equals "none", and
\*   blockedByDist equals FALSE."
Init ==
    /\ chain = <<>>
    /\ agree = TRUE
    /\ lastRollback = 0
    /\ lastReason = "none"
    /\ blockedByDist = FALSE

\* In English: a peer offers the fork that keeps the first i blocks of the
\* selection and adds suffix s. Both rules decide it; the node acts on Adopt.
\* Literally: "Offer of i and s is defined as: letting cand be the subsequence
\*   of chain from 1 through i followed by s, and sw be Adopt of chain, cand and
\*   i: agree in the next state equals (RefSwitch of chain, cand and i equals
\*   GoSwitch of chain, cand and i), and chain in the next state equals: if sw
\*   then cand, else chain; and lastRollback in the next state equals: if sw
\*   then the length of chain minus i, else 0; and lastReason in the next state
\*   equals: if sw then Reason of chain and cand, else "none"; and blockedByDist
\*   in the next state equals (sw is not true and the length of chain minus i is
\*   less than or equal to K and RefPrefer of chain, cand and FALSE)."
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
\* Literally: "Next is defined as: there exists an i in 0 through the length of
\*   chain such that there exists an s in Suffixes of the subsequence of chain
\*   from 1 through i such that Offer of i and s."
Next ==
    \E i \in 0..Len(chain) :
        \E s \in Suffixes(SubSeq(chain, 1, i)) : Offer(i, s)

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* What must always be true.                                               *)
(***************************************************************************)

\* In English: gOuroboros and the reference decide every offer the same way.
\* Literally: "DecisionsAgree is defined as agree."
DecisionsAgree == agree

\* In English: no switch rolls back more than k blocks [R5].
\* Literally: "NoRollbackBeyondK is defined as: lastRollback is less than or
\*   equal to K."
NoRollbackBeyondK == lastRollback <= K

\* In English: every block of the selection passes the reference counter
\* rule against the blocks before it [R6][R7].
\* Literally: "OpCertCountersOnChain is defined as: for all j in 1 through the
\*   length of chain, SpecCounterOk of (Counter of the subsequence of chain from
\*   1 through j minus 1, and chain of j's issuer), and chain of j's ino."
OpCertCountersOnChain ==
    \A j \in 1..Len(chain) :
        SpecCounterOk(Counter(SubSeq(chain, 1, j - 1), chain[j].issuer),
                      chain[j].ino)

\* In English: slots strictly increase along the selection [R8].
\* Literally: "SlotsIncrease is defined as: for all j in 2 through the length of
\*   chain, chain of j's slot is greater than chain of j minus 1's slot."
SlotsIncrease == \A j \in 2..Len(chain) : chain[j].slot > chain[j - 1].slot

(***************************************************************************)
(* Reachability probes: each claims something never happens. TLC must     *)
(* show that it does, or the invariants above could pass vacuously.        *)
(***************************************************************************)

\* Probe: a replacement hot key never wins on its issue number.
\* Literally: "NeverSwitchedByOCert is defined as: lastReason does not equal
\*   "ocert"."
NeverSwitchedByOCert == lastReason # "ocert"

\* Probe: the VRF never decides a switch.
\* Literally: "NeverSwitchedByVRF is defined as: lastReason does not equal
\*   "vrf"."
NeverSwitchedByVRF == lastReason # "vrf"

\* Probe: the Conway distance rule never refuses a switch.
\* Literally: "NeverBlockedByDistance is defined as: blockedByDist is not true."
NeverBlockedByDistance == ~blockedByDist
=============================================================================
