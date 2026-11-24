--------------------------- MODULE GenesisDensity ---------------------------
(***************************************************************************)
(* Ouroboros Genesis density during sync. A syncing node talks to a few   *)
(* peers; each peer sends headers of its chain one at a time and may say  *)
(* "I have nothing more for now" (idle). On every state the model asks two *)
(* questions side by side:                                                  *)
(*                                                                         *)
(*   - the reference: which peers would the Genesis Density Disconnection *)
(*     governor (GDD) drop, and how far may the Limit on Eagerness (LoE)  *)
(*     let the selection go?                                               *)
(*   - gOuroboros: which candidate does genesis.GenesisSelector.Preferred *)
(*     pick, and does the caller adopting it respect what the reference   *)
(*     would allow?                                                         *)
(*                                                                         *)
(* Sources (README.md has links). ouroboros-consensus commit ec239d57.     *)
(*   [G1] ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/ *)
(*        Genesis/Governor.hs 294-319: sharedCandidatePrefix. The LoE      *)
(*        fragment is the prefix every candidate shares, anchored at the   *)
(*        immutable tip.                                                    *)
(*   [G2] Governor.hs 387-447: densityDisconnect, the bounds. Each         *)
(*        candidate's suffix after the LoE tip is clipped to the slots     *)
(*        before succ(LoE tip) + sgen; lowerBound is its length;           *)
(*        upperBound adds the trailing window slots not yet seen, unless   *)
(*        the peer has shown a header at or after the window's end.        *)
(*        offersMoreThanK: more than k blocks after the LoE tip in total.   *)
(*   [G3] Governor.hs 448-501: densityDisconnect, the losing peers.        *)
(*   [G4] Storage/ChainDB/Impl/ChainSel.hs 907-950: trimToLoE. A          *)
(*        candidate containing the LoE tip may be selected at most k       *)
(*        blocks past it.                                                   *)
(*   [G5] MiniProtocol/ChainSync/Client/State.hs 72-76: csLatestSlot is   *)
(*        unset until a header arrives; GDD skips such peers (G2 394-397). *)
(*                                                                         *)
(* gOuroboros: consensus/genesis/genesis.go (GenesisSelector.Compare,     *)
(* Preferred, SimpleChainFragment.BlockCountInWindow). It has no GDD, no  *)
(* LoE and no ChainSync jumping; the caller adopts what Preferred returns. *)
(*                                                                         *)
(* Abstractions:                                                            *)
(*   - A chain is the list of its block slots after the immutable tip,     *)
(*     which sits at slot 0. Two chains with the same list of slots up to *)
(*     some point share those blocks (the model gives a slot and its       *)
(*     history one block).                                                  *)
(*   - A peer's latest seen slot is its candidate's tip: headers beyond   *)
(*     the forecast horizon (G2 400-403) are not modelled.                 *)
(*   - Peers are never disconnected in the model: every state is a moment *)
(*     at which the governor and the selector are both asked.              *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla.         *)
(* New here:                                                               *)
(*   SubSeq(s, a, b)  items a..b of list s (empty when b < a)             *)
(*   x \div y         whole-number division, rounding down                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    NPeers,     \* how many peers; they are 1..NPeers, handed to Preferred in that order
    MaxSlot,    \* block slots run 1..MaxSlot; the immutable tip is slot 0
    MaxLen,     \* the longest candidate the model builds
    K,          \* the security parameter k, in blocks
    SGen,       \* the Genesis window sgen, in slots: ceiling(3k/f), so at least
                \* 3k; the configs use f = 1, sgen = 3k
    CurLen,     \* our selection may be any chain this long or shorter
                \* (it matters only to Anchoring "Own")
    Anchoring,  \* "Common": every fragment starts at the LoE tip;
                \* "Own": at its own intersection with our selection
    Counter,    \* "Exact": count blocks in the window;
                \* "Simple": SimpleChainFragment's proportional estimate
    Adopt,      \* "Ref": selection trimmed by the LoE [G4];
                \* "Go": the caller adopts Preferred's candidate whole
    KGuard      \* TRUE as in the reference; FALSE drops the offersMoreThanK
                \* guard of [G3] (a mutation, to show the invariant bites)

\* In English: the peers, in the order the caller hands them to Preferred.
\* Literally: "Peers is defined as 1 through NPeers."
Peers == 1..NPeers
\* In English: the slots a block may have.
\* Literally: "Slots is defined as 1 through MaxSlot."
Slots == 1..MaxSlot

VARIABLES
    cur,   \* our node's selection: slots after the immutable tip
    cand,  \* cand[p]: the chain peer p has sent so far
    idle   \* idle[p]: p has said it has nothing more (MsgAwaitReply)

\* Literally: "vars is defined as the tuple of cur, cand and idle."
vars == <<cur, cand, idle>>

\* In English: the last slot of chain c.
\* Literally: "Last of c is defined as c of the length of c."
Last(c) == c[Len(c)]
\* In English: the smaller of a and b.
\* Literally: "Min of a and b is defined as: if a is less than or equal to b
\*   then a, else b."
Min(a, b) == IF a <= b THEN a ELSE b
\* In English: the largest number in S.
\* Literally: "Max of S is defined as the x, chosen from S, such that for all y
\*   in S, y is less than or equal to x."
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* In English: a chain is a strictly increasing list of slots, at most
\* MaxLen long.
\* Literally: "IsChain of c is defined as: the length of c is less than or equal
\*   to MaxLen, and for all i in 1 through the length of c, c of i is a member
\*   of Slots, and for all i in 1 through (the length of c minus 1), c of i is
\*   less than c of i plus 1."
IsChain(c) ==
    /\ Len(c) <= MaxLen
    /\ \A i \in 1..Len(c) : c[i] \in Slots
    /\ \A i \in 1..(Len(c) - 1) : c[i] < c[i + 1]

\* In English: every variable holds the kind of value it should.
\* Literally: "TypeOK is defined as: IsChain of cur, and for all p in Peers,
\*   IsChain of cand of p, and idle is a member of the set of functions from
\*   Peers to BOOLEAN."
TypeOK ==
    /\ IsChain(cur)
    /\ \A p \in Peers : IsChain(cand[p])
    /\ idle \in [Peers -> BOOLEAN]

(***************************************************************************)
(* The reference: LoE fragment and density bounds.                         *)
(***************************************************************************)

\* In English: how many leading blocks chains s and t share.
\* Literally: "Shared of s and t is defined as Max of the set of every n in 0
\*   through Min of the length of s and the length of t such that the
\*   subsequence of s from 1 through n equals the subsequence of t from 1
\*   through n."
Shared(s, t) ==
    Max({n \in 0..Min(Len(s), Len(t)) : SubSeq(s, 1, n) = SubSeq(t, 1, n)})

\* In English: the LoE fragment is the prefix every candidate shares [G1];
\* this is its length.
\* Literally: "LoELen is defined as Max of the set of every n in 0 through
\*   MaxLen such that for all p and q in Peers, n is less than or equal to
\*   Shared of cand of p and cand of q."
LoELen == Max({n \in 0..MaxLen :
                \A p, q \in Peers : n <= Shared(cand[p], cand[q])})

\* In English: the slot of the LoE tip; the immutable tip (slot 0) when the
\* candidates share nothing after it.
\* Literally: "LoESlot is defined as: if LoELen equals 0 then 0, else cand of
\*   (the p, chosen from Peers, such that TRUE) of LoELen."
LoESlot == IF LoELen = 0 THEN 0
           ELSE cand[CHOOSE p \in Peers : TRUE][LoELen]

\* In English: the first slot after the Genesis window: succ(LoE tip) +
\* sgen [G3 500-501]. The window is slots LoESlot+1 .. LoESlot+SGen.
\* Literally: "FirstAfter is defined as LoESlot plus 1 plus SGen."
FirstAfter == LoESlot + 1 + SGen

\* In English: what peer p proposes after the LoE tip [G1].
\* Literally: "Suffix of p is defined as the subsequence of cand of p from
\*   LoELen plus 1 through the length of cand of p."
Suffix(p) == SubSeq(cand[p], LoELen + 1, Len(cand[p]))

\* In English: how many of those blocks lie in the window. Slots increase,
\* so they are a prefix: the clipped fragment [G2 392-393].
\* Literally: "ClipLen of p is defined as the number of members of the set of
\*   every i in 1 through the length of Suffix of p such that Suffix of p of i
\*   is less than FirstAfter."
ClipLen(p) == Cardinality({i \in 1..Len(Suffix(p)) : Suffix(p)[i] < FirstAfter})

\* In English: the slot of the clipped fragment's head, or the LoE tip's
\* when it is empty (an empty fragment's head is its anchor).
\* Literally: "ClipHead of p is defined as: if ClipLen of p equals 0 then
\*   LoESlot, else Suffix of p of ClipLen of p."
ClipHead(p) == IF ClipLen(p) = 0 THEN LoESlot ELSE Suffix(p)[ClipLen(p)]

\* In English: the clipped fragment's AF.lastPoint [G3 470]: its OLDEST
\* block, the first after the LoE tip, or the LoE tip itself when the
\* fragment is empty (an empty fragment's last point is its anchor). A
\* block is named by the list of slots leading to it. GDD compares only
\* these: two peers whose clipped fragments start with the same block are
\* never compared, however they continue (Note [Chain disagreement]).
\* Literally: "ClipPoint of p is defined as the subsequence of cand of p from 1
\*   through LoELen plus Min of ClipLen of p and 1."
ClipPoint(p) == SubSeq(cand[p], 1, LoELen + Min(ClipLen(p), 1))

\* In English: GDD skips a peer that has sent no header yet [G5].
\* Literally: "Considered is defined as the set of every p in Peers such that
\*   the length of cand of p is greater than 0."
Considered == {p \in Peers : Len(cand[p]) > 0}

\* In English: the peer has shown a header at or after the window's end, so
\* no more headers can fall inside it [G2 400-403].
\* Literally: "HasAfter of p is defined as: the length of cand of p is greater
\*   than 0, and Last of cand of p is greater than or equal to FirstAfter."
HasAfter(p) == Len(cand[p]) > 0 /\ Last(cand[p]) >= FirstAfter

\* In English: the blocks in the window known for certain [G2 423] ...
\* Literally: "Lb of p is defined as ClipLen of p."
Lb(p) == ClipLen(p)

\* ... and the most there could be: add the window slots after the clipped
\* head, unless a header at or after the window's end rules them out
\* [G2 410-425].
\* Literally: "Ub of p is defined as: if HasAfter of p then Lb of p, else Lb of
\*   p plus (FirstAfter minus (ClipHead of p plus 1))."
Ub(p) == IF HasAfter(p) THEN Lb(p)
         ELSE Lb(p) + (FirstAfter - (ClipHead(p) + 1))

\* In English: p offers more than k blocks after the LoE tip [G2 429-433].
\* Literally: "MoreThanK of p is defined as: the length of Suffix of p is
\*   greater than K."
MoreThanK(p) == Len(Suffix(p)) > K

\* In English: GDD drops p0 when some p1 [G3 451-496]:
\*   - p0 is idle, or has a block after the LoE tip, or has shown one past
\*     the window (otherwise the two may yet agree);
\*   - the clipped fragments end at different blocks;
\*   - p1 offers more than k blocks, or p0 has shown all its window;
\*   - p1 has at least as many blocks in the window as p0 could have
\*     (as p0 has, when p0 is idle). A tie is enough.
\* Literally: "Loses of p0 is defined as: p0 is a member of Considered, and
\*   there exists a p1 in Considered such that (idle of p0, or ClipLen of p0 is
\*   greater than 0, or HasAfter of p0), and ClipPoint of p0 does not equal
\*   ClipPoint of p1, and if KGuard, then (MoreThanK of p1 or Lb of p0 equals Ub
\*   of p0), and Lb of p1 is greater than or equal to (if idle of p0 then Lb of
\*   p0, else Ub of p0)."
Loses(p0) ==
    /\ p0 \in Considered
    /\ \E p1 \in Considered :
        /\ idle[p0] \/ ClipLen(p0) > 0 \/ HasAfter(p0)
        /\ ClipPoint(p0) # ClipPoint(p1)
        /\ KGuard => (MoreThanK(p1) \/ Lb(p0) = Ub(p0))
        /\ Lb(p1) >= IF idle[p0] THEN Lb(p0) ELSE Ub(p0)

\* In English: the peers GDD drops.
\* Literally: "RefLosing is defined as the set of every p in Peers such that
\*   Loses of p."
RefLosing == {p \in Peers : Loses(p)}

\* In English: the reference selection: the longest candidate (the lowest
\* numbered on a tie; the Praos tiebreakers are 13-consensus' business),
\* trimmed to at most k blocks past the LoE tip [G4]. Every candidate holds
\* the LoE tip, so the trim is a prefix.
\* Literally: "RefBest is defined as: letting top be Max of the set of the
\*   length of cand of p, for every p that is a member of Peers: cand of (the p,
\*   chosen from Peers, such that the length of cand of p equals top, and for
\*   all q in 1 through (p minus 1), the length of cand of q is less than top)."
RefBest == LET top == Max({Len(cand[p]) : p \in Peers})
           IN  cand[CHOOSE p \in Peers :
                      /\ Len(cand[p]) = top
                      /\ \A q \in 1..(p - 1) : Len(cand[q]) < top]
\* Literally: "RefAdopted is defined as the subsequence of RefBest from 1
\*   through Min of the length of RefBest and LoELen plus K."
RefAdopted == SubSeq(RefBest, 1, Min(Len(RefBest), LoELen + K))

(***************************************************************************)
(* gOuroboros: GenesisSelector over one ChainFragment per peer.            *)
(***************************************************************************)

\* In English: where p's fragment starts. ChainFragment.IntersectionSlot is
\* "the slot where this fragment intersects with our chain", so "Own" is
\* the documented contract; "Common" is the caller anchoring every fragment
\* at the LoE tip instead.
\* Literally: "GoAnchorLen of p is defined as: if Anchoring equals "Common" then
\*   LoELen, else Shared of cur and cand of p."
GoAnchorLen(p) == IF Anchoring = "Common" THEN LoELen ELSE Shared(cur, cand[p])
\* Literally: "GoAnchorSlot of p is defined as: if GoAnchorLen of p equals 0
\*   then 0, else cand of p of GoAnchorLen of p."
GoAnchorSlot(p) == IF GoAnchorLen(p) = 0 THEN 0 ELSE cand[p][GoAnchorLen(p)]
\* Literally: "GoFrag of p is defined as the subsequence of cand of p from
\*   GoAnchorLen of p plus 1 through the length of cand of p."
GoFrag(p) == SubSeq(cand[p], GoAnchorLen(p) + 1, Len(cand[p]))

\* In English: BlockCount: the blocks in the fragment.
\* Literally: "GoBlocks of p is defined as the length of GoFrag of p."
GoBlocks(p) == Len(GoFrag(p))

\* In English: TipSlot: the fragment's tip, its anchor when it is empty.
\* Literally: "FragTip of f and a is defined as: if the length of f equals 0
\*   then a, else Last of f."
FragTip(f, a) == IF Len(f) = 0 THEN a ELSE Last(f)

\* In English: BlockCountInWindow(sgen) of fragment f anchored at slot a.
\* "Exact" counts blocks at slots s with s - a <= sgen, the window of
\* [G3]. "Simple" is SimpleChainFragment: none when the tip is not after
\* the anchor, all when the window covers the whole fragment, otherwise
\* blocks * sgen / span rounded down.
\* Literally: "FragCount of f and a is defined as: if Counter equals "Exact"
\*   then the number of members of the set of every i in 1 through the length of
\*   f such that f of i minus a is less than or equal to SGen; else if FragTip
\*   of f and a is less than or equal to a then 0; else if SGen is greater than
\*   or equal to FragTip of f and a minus a then the length of f; else (the
\*   length of f times SGen) integer-divided by (FragTip of f and a minus a)."
FragCount(f, a) ==
    IF Counter = "Exact"
    THEN Cardinality({i \in 1..Len(f) : f[i] - a <= SGen})
    ELSE IF FragTip(f, a) <= a THEN 0
         ELSE IF SGen >= FragTip(f, a) - a THEN Len(f)
         ELSE (Len(f) * SGen) \div (FragTip(f, a) - a)

\* In English: the window count of p's fragment, as gOuroboros computes it.
\* Literally: "GoCount of p is defined as FragCount of GoFrag of p and
\*   GoAnchorSlot of p."
GoCount(p) == FragCount(GoFrag(p), GoAnchorSlot(p))

\* In English: Compare(a, b) > 0: more blocks in the window; on equal
\* counts, more blocks in total.
\* Literally: "GoBetter of a and b is defined as: GoCount of a is greater than
\*   GoCount of b, or GoCount of a equals GoCount of b and GoBlocks of a is
\*   greater than GoBlocks of b."
GoBetter(a, b) ==
    \/ GoCount(a) > GoCount(b)
    \/ GoCount(a) = GoCount(b) /\ GoBlocks(a) > GoBlocks(b)

\* In English: Preferred: start with the first candidate and replace it
\* only with a strictly better one, scanning in peer order.
RECURSIVE Scan(_, _)
\* Literally: "Scan of best and i is defined as: if i is greater than NPeers
\*   then best, else Scan of (if GoBetter of i and best then i, else best) and i
\*   plus 1."
Scan(best, i) ==
    IF i > NPeers THEN best
    ELSE Scan(IF GoBetter(i, best) THEN i ELSE best, i + 1)
\* Literally: "GoChoice is defined as Scan of 1 and 2."
GoChoice == Scan(1, 2)

\* In English: the same Preferred over the candidates as the reference's
\* chain selection sees them: each trimmed to at most k blocks past the
\* LoE tip [G4] (every candidate holds the LoE tip), then cut at the same
\* anchor as GoFrag. GDD's bounds above still use the whole candidates.
\* Literally: "GoTrimFrag of p is defined as the subsequence of cand of p from
\*   GoAnchorLen of p plus 1 through Min of the length of cand of p and LoELen
\*   plus K."
GoTrimFrag(p) == SubSeq(cand[p], GoAnchorLen(p) + 1,
                        Min(Len(cand[p]), LoELen + K))
\* Literally: "GoTrimBetter of a and b is defined as: letting ca be FragCount of
\*   GoTrimFrag of a and GoAnchorSlot of a, and cb be FragCount of GoTrimFrag of
\*   b and GoAnchorSlot of b: ca is greater than cb, or ca equals cb and the
\*   length of GoTrimFrag of a is greater than the length of GoTrimFrag of b."
GoTrimBetter(a, b) ==
    LET ca == FragCount(GoTrimFrag(a), GoAnchorSlot(a))
        cb == FragCount(GoTrimFrag(b), GoAnchorSlot(b))
    IN  \/ ca > cb
        \/ ca = cb /\ Len(GoTrimFrag(a)) > Len(GoTrimFrag(b))
RECURSIVE TrimScan(_, _)
\* Literally: "TrimScan of best and i is defined as: if i is greater than NPeers
\*   then best, else TrimScan of (if GoTrimBetter of i and best then i, else
\*   best) and i plus 1."
TrimScan(best, i) ==
    IF i > NPeers THEN best
    ELSE TrimScan(IF GoTrimBetter(i, best) THEN i ELSE best, i + 1)
\* Literally: "GoTrimChoice is defined as TrimScan of 1 and 2."
GoTrimChoice == TrimScan(1, 2)

\* In English: the reference count of the trimmed candidate: its first k
\* blocks after the LoE tip that lie in the window.
\* Literally: "TrimLb of p is defined as the number of members of the set of
\*   every i in 1 through Min of K and the length of Suffix of p such that
\*   Suffix of p of i is less than FirstAfter."
TrimLb(p) == Cardinality({i \in 1..Min(K, Len(Suffix(p))) : Suffix(p)[i] < FirstAfter})

\* In English: the chain the node ends up on.
\* Literally: "Adopted is defined as: if Adopt equals "Go" then cand of
\*   GoChoice, else RefAdopted."
Adopted == IF Adopt = "Go" THEN cand[GoChoice] ELSE RefAdopted

(***************************************************************************)
(* Behaviour.                                                               *)
(***************************************************************************)

\* In English: "Our selection is any chain up to CurLen long; no peer has sent
\* anything, and none is idle."
\* Literally: "Init is defined as: cur is a member of the set of every c in the
\*   union of all sets in (the set of the set of functions from 1 through n to
\*   Slots, for every n that is a member of 0 through CurLen) such that IsChain
\*   of c; and cand equals the function that maps every p in Peers to the empty
\*   sequence, and idle equals the function that maps every p in Peers to
\*   FALSE."
Init ==
    /\ cur \in {c \in UNION {[1..n -> Slots] : n \in 0..CurLen} : IsChain(c)}
    /\ cand = [p \in Peers |-> <<>>]
    /\ idle = [p \in Peers |-> FALSE]

\* In English: peer p sends its next header, at slot s after its tip.
\* Sending a header ends idling.
\* Literally: "Extend of p and s is defined as: the length of cand of p is less
\*   than MaxLen, and if the length of cand of p equals 0 then TRUE, else s is
\*   greater than Last of cand of p; and cand in the next state equals cand
\*   except that its p entry is the old entry with s appended, and idle in the
\*   next state equals idle except that its p entry is FALSE, and cur is
\*   unchanged."
Extend(p, s) ==
    /\ Len(cand[p]) < MaxLen
    /\ IF Len(cand[p]) = 0 THEN TRUE ELSE s > Last(cand[p])
    /\ cand' = [cand EXCEPT ![p] = Append(@, s)]
    /\ idle' = [idle EXCEPT ![p] = FALSE]
    /\ UNCHANGED cur

\* In English: peer p says it has nothing more for now.
\* Literally: "Idle of p is defined as: idle of p is not true, and idle in the
\*   next state equals idle except that its p entry is TRUE, and cur and cand
\*   are unchanged."
Idle(p) ==
    /\ ~idle[p]
    /\ idle' = [idle EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cur, cand>>

\* In English: once every peer is idle the node simply waits.
\* Literally: "Settled is defined as: for all p in Peers, idle of p, and vars is
\*   unchanged."
Settled ==
    /\ \A p \in Peers : idle[p]
    /\ UNCHANGED vars

\* In English: "Each step is a peer sending a header, a peer going idle, or the
\* settled wait."
\* Literally: "Next is defined as: there exists a p in Peers and an s in Slots
\*   such that Extend of p and s; or there exists a p in Peers such that Idle of
\*   p; or Settled."
Next ==
    \/ \E p \in Peers, s \in Slots : Extend(p, s)
    \/ \E p \in Peers : Idle(p)
    \/ Settled

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                              *)
(***************************************************************************)

\* In English: the density rule picks a chain with the most blocks in the
\* Genesis window after the intersection (the reference count, at the LoE
\* tip). Fails when fragments are anchored at their own intersections or
\* counted by SimpleChainFragment's estimate.
\* Literally: "GoPicksDensest is defined as: for all p in Peers, Lb of p is less
\*   than or equal to Lb of GoChoice."
GoPicksDensest == \A p \in Peers : Lb(p) <= Lb(GoChoice)

\* In English: GDD may drop the chain gOuroboros picked only on an exact
\* tie with a different chain. (A tie drops both in the reference; the
\* honest chain is expected to be strictly denser [G3 478-482].)
\* Literally: "GoChoiceLosesOnlyOnTie is defined as: if GoChoice is a member of
\*   RefLosing, then there exists a q in Peers without the members of the set
\*   containing GoChoice such that Lb of q equals Lb of GoChoice and ClipPoint
\*   of q does not equal ClipPoint of GoChoice."
GoChoiceLosesOnlyOnTie ==
    GoChoice \in RefLosing =>
        \E q \in Peers \ {GoChoice} :
            /\ Lb(q) = Lb(GoChoice)
            /\ ClipPoint(q) # ClipPoint(GoChoice)

\* In English: on candidates trimmed to the LoE, Preferred picks one with
\* the most blocks in the window among the trimmed candidates.
\* Literally: "GoTrimmedPicksDensest is defined as: for all p in Peers, TrimLb
\*   of p is less than or equal to TrimLb of GoTrimChoice."
GoTrimmedPicksDensest == \A p \in Peers : TrimLb(p) <= TrimLb(GoTrimChoice)

\* In English: the node never selects more than k blocks past the prefix
\* every candidate shares [G4].
\* Literally: "LoEBound is defined as: the length of Adopted is less than or
\*   equal to LoELen plus K."
LoEBound == Len(Adopted) <= LoELen + K

\* In English: a peer still sending its window (not idle, upper bound not
\* reached) is dropped only because some peer offers more than k blocks
\* [G3 471-476]; this keeps competing honest peers near the tip.
\* Literally: "KGuardHolds is defined as: for all p in RefLosing, if idle of p
\*   is not true and Lb of p is less than Ub of p, then there exists a q in
\*   Considered such that MoreThanK of q."
KGuardHolds ==
    \A p \in RefLosing :
        (~idle[p] /\ Lb(p) < Ub(p)) => \E q \in Considered : MoreThanK(q)

(***************************************************************************)
(* Reachability probes: each must be VIOLATED (the state is reachable).    *)
(***************************************************************************)

\* GDD drops two peers with equal window counts at once (Go keeps one).
\* Literally: "ProbeTieBothLose is defined as: it is not true that there exist p
\*   and q in Peers such that p does not equal q, and p is a member of RefLosing
\*   and q is a member of RefLosing, and Lb of p equals Lb of q."
ProbeTieBothLose ==
    ~\E p, q \in Peers :
        /\ p # q
        /\ p \in RefLosing /\ q \in RefLosing
        /\ Lb(p) = Lb(q)

\* Density beats length: Go picks a chain shorter than another candidate.
\* Literally: "ProbeDenserShorter is defined as: it is not true that there
\*   exists a q in Peers such that the length of cand of q is greater than the
\*   length of cand of GoChoice."
ProbeDenserShorter ==
    ~\E q \in Peers : Len(cand[q]) > Len(cand[GoChoice])

\* GDD drops a peer that is not idle and has not shown its whole window.
\* Literally: "ProbeDropWhileSending is defined as: it is not true that there
\*   exists a p in RefLosing such that idle of p is not true and Lb of p is less
\*   than Ub of p."
ProbeDropWhileSending ==
    ~\E p \in RefLosing : ~idle[p] /\ Lb(p) < Ub(p)

\* Two peers' clipped fragments start with the same block but end at
\* different ones, so GDD does not compare them (needs three peers: two
\* share a block past the prefix all three share).
\* Literally: "ProbeSameFirstBlock is defined as: it is not true that there
\*   exist p and q in Considered such that ClipPoint of p equals ClipPoint of q,
\*   and the subsequence of cand of p from 1 through LoELen plus ClipLen of p
\*   does not equal the subsequence of cand of q from 1 through LoELen plus
\*   ClipLen of q."
ProbeSameFirstBlock ==
    ~\E p, q \in Considered :
        /\ ClipPoint(p) = ClipPoint(q)
        /\ SubSeq(cand[p], 1, LoELen + ClipLen(p))
              # SubSeq(cand[q], 1, LoELen + ClipLen(q))

\* Trimming to the LoE changes Preferred's pick.
\* Literally: "ProbeTrimChangesChoice is defined as: GoTrimChoice equals
\*   GoChoice."
ProbeTrimChangesChoice == GoTrimChoice = GoChoice
=============================================================================
