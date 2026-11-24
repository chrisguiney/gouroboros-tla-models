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
Peers == 1..NPeers
Slots == 1..MaxSlot

VARIABLES
    cur,   \* our node's selection: slots after the immutable tip
    cand,  \* cand[p]: the chain peer p has sent so far
    idle   \* idle[p]: p has said it has nothing more (MsgAwaitReply)

vars == <<cur, cand, idle>>

Last(c) == c[Len(c)]
Min(a, b) == IF a <= b THEN a ELSE b
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* In English: a chain is a strictly increasing list of slots, at most
\* MaxLen long.
IsChain(c) ==
    /\ Len(c) <= MaxLen
    /\ \A i \in 1..Len(c) : c[i] \in Slots
    /\ \A i \in 1..(Len(c) - 1) : c[i] < c[i + 1]

TypeOK ==
    /\ IsChain(cur)
    /\ \A p \in Peers : IsChain(cand[p])
    /\ idle \in [Peers -> BOOLEAN]

(***************************************************************************)
(* The reference: LoE fragment and density bounds.                         *)
(***************************************************************************)

\* In English: how many leading blocks chains s and t share.
Shared(s, t) ==
    Max({n \in 0..Min(Len(s), Len(t)) : SubSeq(s, 1, n) = SubSeq(t, 1, n)})

\* In English: the LoE fragment is the prefix every candidate shares [G1];
\* this is its length.
LoELen == Max({n \in 0..MaxLen :
                \A p, q \in Peers : n <= Shared(cand[p], cand[q])})

\* In English: the slot of the LoE tip; the immutable tip (slot 0) when the
\* candidates share nothing after it.
LoESlot == IF LoELen = 0 THEN 0
           ELSE cand[CHOOSE p \in Peers : TRUE][LoELen]

\* In English: the first slot after the Genesis window: succ(LoE tip) +
\* sgen [G3 500-501]. The window is slots LoESlot+1 .. LoESlot+SGen.
FirstAfter == LoESlot + 1 + SGen

\* In English: what peer p proposes after the LoE tip [G1].
Suffix(p) == SubSeq(cand[p], LoELen + 1, Len(cand[p]))

\* In English: how many of those blocks lie in the window. Slots increase,
\* so they are a prefix: the clipped fragment [G2 392-393].
ClipLen(p) == Cardinality({i \in 1..Len(Suffix(p)) : Suffix(p)[i] < FirstAfter})

\* In English: the slot of the clipped fragment's head, or the LoE tip's
\* when it is empty (an empty fragment's head is its anchor).
ClipHead(p) == IF ClipLen(p) = 0 THEN LoESlot ELSE Suffix(p)[ClipLen(p)]

\* In English: the clipped fragment's AF.lastPoint [G3 470]: its OLDEST
\* block, the first after the LoE tip, or the LoE tip itself when the
\* fragment is empty (an empty fragment's last point is its anchor). A
\* block is named by the list of slots leading to it. GDD compares only
\* these: two peers whose clipped fragments start with the same block are
\* never compared, however they continue (Note [Chain disagreement]).
ClipPoint(p) == SubSeq(cand[p], 1, LoELen + Min(ClipLen(p), 1))

\* In English: GDD skips a peer that has sent no header yet [G5].
Considered == {p \in Peers : Len(cand[p]) > 0}

\* In English: the peer has shown a header at or after the window's end, so
\* no more headers can fall inside it [G2 400-403].
HasAfter(p) == Len(cand[p]) > 0 /\ Last(cand[p]) >= FirstAfter

\* In English: the blocks in the window known for certain [G2 423] ...
Lb(p) == ClipLen(p)

\* ... and the most there could be: add the window slots after the clipped
\* head, unless a header at or after the window's end rules them out
\* [G2 410-425].
Ub(p) == IF HasAfter(p) THEN Lb(p)
         ELSE Lb(p) + (FirstAfter - (ClipHead(p) + 1))

\* In English: p offers more than k blocks after the LoE tip [G2 429-433].
MoreThanK(p) == Len(Suffix(p)) > K

\* In English: GDD drops p0 when some p1 [G3 451-496]:
\*   - p0 is idle, or has a block after the LoE tip, or has shown one past
\*     the window (otherwise the two may yet agree);
\*   - the clipped fragments end at different blocks;
\*   - p1 offers more than k blocks, or p0 has shown all its window;
\*   - p1 has at least as many blocks in the window as p0 could have
\*     (as p0 has, when p0 is idle). A tie is enough.
Loses(p0) ==
    /\ p0 \in Considered
    /\ \E p1 \in Considered :
        /\ idle[p0] \/ ClipLen(p0) > 0 \/ HasAfter(p0)
        /\ ClipPoint(p0) # ClipPoint(p1)
        /\ KGuard => (MoreThanK(p1) \/ Lb(p0) = Ub(p0))
        /\ Lb(p1) >= IF idle[p0] THEN Lb(p0) ELSE Ub(p0)

RefLosing == {p \in Peers : Loses(p)}

\* In English: the reference selection: the longest candidate (the lowest
\* numbered on a tie; the Praos tiebreakers are 13-consensus' business),
\* trimmed to at most k blocks past the LoE tip [G4]. Every candidate holds
\* the LoE tip, so the trim is a prefix.
RefBest == LET top == Max({Len(cand[p]) : p \in Peers})
           IN  cand[CHOOSE p \in Peers :
                      /\ Len(cand[p]) = top
                      /\ \A q \in 1..(p - 1) : Len(cand[q]) < top]
RefAdopted == SubSeq(RefBest, 1, Min(Len(RefBest), LoELen + K))

(***************************************************************************)
(* gOuroboros: GenesisSelector over one ChainFragment per peer.            *)
(***************************************************************************)

\* In English: where p's fragment starts. ChainFragment.IntersectionSlot is
\* "the slot where this fragment intersects with our chain", so "Own" is
\* the documented contract; "Common" is the caller anchoring every fragment
\* at the LoE tip instead.
GoAnchorLen(p) == IF Anchoring = "Common" THEN LoELen ELSE Shared(cur, cand[p])
GoAnchorSlot(p) == IF GoAnchorLen(p) = 0 THEN 0 ELSE cand[p][GoAnchorLen(p)]
GoFrag(p) == SubSeq(cand[p], GoAnchorLen(p) + 1, Len(cand[p]))

\* In English: BlockCount: the blocks in the fragment.
GoBlocks(p) == Len(GoFrag(p))

\* In English: TipSlot: the fragment's tip, its anchor when it is empty.
FragTip(f, a) == IF Len(f) = 0 THEN a ELSE Last(f)

\* In English: BlockCountInWindow(sgen) of fragment f anchored at slot a.
\* "Exact" counts blocks at slots s with s - a <= sgen, the window of
\* [G3]. "Simple" is SimpleChainFragment: none when the tip is not after
\* the anchor, all when the window covers the whole fragment, otherwise
\* blocks * sgen / span rounded down.
FragCount(f, a) ==
    IF Counter = "Exact"
    THEN Cardinality({i \in 1..Len(f) : f[i] - a <= SGen})
    ELSE IF FragTip(f, a) <= a THEN 0
         ELSE IF SGen >= FragTip(f, a) - a THEN Len(f)
         ELSE (Len(f) * SGen) \div (FragTip(f, a) - a)

GoCount(p) == FragCount(GoFrag(p), GoAnchorSlot(p))

\* In English: Compare(a, b) > 0: more blocks in the window; on equal
\* counts, more blocks in total.
GoBetter(a, b) ==
    \/ GoCount(a) > GoCount(b)
    \/ GoCount(a) = GoCount(b) /\ GoBlocks(a) > GoBlocks(b)

\* In English: Preferred: start with the first candidate and replace it
\* only with a strictly better one, scanning in peer order.
RECURSIVE Scan(_, _)
Scan(best, i) ==
    IF i > NPeers THEN best
    ELSE Scan(IF GoBetter(i, best) THEN i ELSE best, i + 1)
GoChoice == Scan(1, 2)

\* In English: the same Preferred over the candidates as the reference's
\* chain selection sees them: each trimmed to at most k blocks past the
\* LoE tip [G4] (every candidate holds the LoE tip), then cut at the same
\* anchor as GoFrag. GDD's bounds above still use the whole candidates.
GoTrimFrag(p) == SubSeq(cand[p], GoAnchorLen(p) + 1,
                        Min(Len(cand[p]), LoELen + K))
GoTrimBetter(a, b) ==
    LET ca == FragCount(GoTrimFrag(a), GoAnchorSlot(a))
        cb == FragCount(GoTrimFrag(b), GoAnchorSlot(b))
    IN  \/ ca > cb
        \/ ca = cb /\ Len(GoTrimFrag(a)) > Len(GoTrimFrag(b))
RECURSIVE TrimScan(_, _)
TrimScan(best, i) ==
    IF i > NPeers THEN best
    ELSE TrimScan(IF GoTrimBetter(i, best) THEN i ELSE best, i + 1)
GoTrimChoice == TrimScan(1, 2)

\* In English: the reference count of the trimmed candidate: its first k
\* blocks after the LoE tip that lie in the window.
TrimLb(p) == Cardinality({i \in 1..Min(K, Len(Suffix(p))) : Suffix(p)[i] < FirstAfter})

\* In English: the chain the node ends up on.
Adopted == IF Adopt = "Go" THEN cand[GoChoice] ELSE RefAdopted

(***************************************************************************)
(* Behaviour.                                                               *)
(***************************************************************************)

Init ==
    /\ cur \in {c \in UNION {[1..n -> Slots] : n \in 0..CurLen} : IsChain(c)}
    /\ cand = [p \in Peers |-> <<>>]
    /\ idle = [p \in Peers |-> FALSE]

\* In English: peer p sends its next header, at slot s after its tip.
\* Sending a header ends idling.
Extend(p, s) ==
    /\ Len(cand[p]) < MaxLen
    /\ IF Len(cand[p]) = 0 THEN TRUE ELSE s > Last(cand[p])
    /\ cand' = [cand EXCEPT ![p] = Append(@, s)]
    /\ idle' = [idle EXCEPT ![p] = FALSE]
    /\ UNCHANGED cur

\* In English: peer p says it has nothing more for now.
Idle(p) ==
    /\ ~idle[p]
    /\ idle' = [idle EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cur, cand>>

\* In English: once every peer is idle the node simply waits.
Settled ==
    /\ \A p \in Peers : idle[p]
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Peers, s \in Slots : Extend(p, s)
    \/ \E p \in Peers : Idle(p)
    \/ Settled

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                              *)
(***************************************************************************)

\* In English: the density rule picks a chain with the most blocks in the
\* Genesis window after the intersection (the reference count, at the LoE
\* tip). Fails when fragments are anchored at their own intersections or
\* counted by SimpleChainFragment's estimate.
GoPicksDensest == \A p \in Peers : Lb(p) <= Lb(GoChoice)

\* In English: GDD may drop the chain gOuroboros picked only on an exact
\* tie with a different chain. (A tie drops both in the reference; the
\* honest chain is expected to be strictly denser [G3 478-482].)
GoChoiceLosesOnlyOnTie ==
    GoChoice \in RefLosing =>
        \E q \in Peers \ {GoChoice} :
            /\ Lb(q) = Lb(GoChoice)
            /\ ClipPoint(q) # ClipPoint(GoChoice)

\* In English: on candidates trimmed to the LoE, Preferred picks one with
\* the most blocks in the window among the trimmed candidates.
GoTrimmedPicksDensest == \A p \in Peers : TrimLb(p) <= TrimLb(GoTrimChoice)

\* In English: the node never selects more than k blocks past the prefix
\* every candidate shares [G4].
LoEBound == Len(Adopted) <= LoELen + K

\* In English: a peer still sending its window (not idle, upper bound not
\* reached) is dropped only because some peer offers more than k blocks
\* [G3 471-476]; this keeps competing honest peers near the tip.
KGuardHolds ==
    \A p \in RefLosing :
        (~idle[p] /\ Lb(p) < Ub(p)) => \E q \in Considered : MoreThanK(q)

(***************************************************************************)
(* Reachability probes: each must be VIOLATED (the state is reachable).    *)
(***************************************************************************)

\* GDD drops two peers with equal window counts at once (Go keeps one).
ProbeTieBothLose ==
    ~\E p, q \in Peers :
        /\ p # q
        /\ p \in RefLosing /\ q \in RefLosing
        /\ Lb(p) = Lb(q)

\* Density beats length: Go picks a chain shorter than another candidate.
ProbeDenserShorter ==
    ~\E q \in Peers : Len(cand[q]) > Len(cand[GoChoice])

\* GDD drops a peer that is not idle and has not shown its whole window.
ProbeDropWhileSending ==
    ~\E p \in RefLosing : ~idle[p] /\ Lb(p) < Ub(p)

\* Two peers' clipped fragments start with the same block but end at
\* different ones, so GDD does not compare them (needs three peers: two
\* share a block past the prefix all three share).
ProbeSameFirstBlock ==
    ~\E p, q \in Considered :
        /\ ClipPoint(p) = ClipPoint(q)
        /\ SubSeq(cand[p], 1, LoELen + ClipLen(p))
              # SubSeq(cand[q], 1, LoELen + ClipLen(q))

\* Trimming to the LoE changes Preferred's pick.
ProbeTrimChangesChoice == GoTrimChoice = GoChoice
=============================================================================
