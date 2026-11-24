---------------------------- MODULE EraHistory ----------------------------
(***************************************************************************)
(* Era transitions and the hard-fork combinator's era history: when a      *)
(* protocol-version update moves the chain into the next era, and how     *)
(* slots convert to epochs and times when eras have different epoch sizes *)
(* and slot lengths.                                                       *)
(*                                                                         *)
(* The model has three parts.                                              *)
(*   1. The chain, walked one slot at a time. Each slot carries a block.  *)
(*      A block may vote to raise the protocol major version by one; the  *)
(*      new version is adopted at the next epoch boundary, and if it is   *)
(*      the next era's trigger version the next era starts there. The    *)
(*      walk keeps the true epoch and time of the next slot: the ground   *)
(*      truth every conversion is compared with.                          *)
(*   2. The reference's era history (a Summary): the known era starts,    *)
(*      each era's bounds, and the horizon of the last era set by the    *)
(*      safe zone. Conversions are computed from the Summary in closed   *)
(*      form, as Qry.hs does.                                              *)
(*   3. gOuroboros. It computes no era history. Its one slot-to-epoch     *)
(*      formula, ByronConfig.SlotToEpoch (slot / SlotsPerEpoch), is      *)
(*      compared with the walk, in the first era and after it. On main   *)
(*      it answers every slot; the fix (GoByron = "Fixed") refuses a slot *)
(*      at or past Byron's end once the caller has set that end from the *)
(*      era history.                                                       *)
(*                                                                         *)
(* Sources (links and quotes in specs/consensus-eras/README.md).        *)
(*   Specification: ouroboros-consensus ec239d57f618,                      *)
(*   docs/tech-reports/report/chapters/hfc/time.tex:                       *)
(*   [S1] 142-177: time conversion is defined for every past point, and   *)
(*        it is monotone: once defined, applying more blocks never        *)
(*        changes it.                                                      *)
(*   [S2] 179-217: the forecast range and the safe zone, a stretch ahead  *)
(*        of the tip in which no unknown transition can happen.           *)
(*   [S3] 222-260: era transitions must be stable.                        *)
(*   Reference implementation (ouroboros-consensus ec239d57f618,           *)
(*   ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/      *)
(*   HardFork/History/):                                                   *)
(*   [R1] Summary.hs 90-161: Bound (time, slot, epoch) and mkUpperBound:  *)
(*        an era's end is its start plus whole epochs of its own size.    *)
(*   [R2] Summary.hs 164-173: slotToEpochBound rounds a slot up to the    *)
(*        next epoch boundary.                                             *)
(*   [R3] Summary.hs 175-224: INV-1b and INV-2b, the slot and time        *)
(*        invariants of a bounded era.                                     *)
(*   [R4] Summary.hs 400-470: summarize; the last era ends at the epoch   *)
(*        boundary at or after max(tip + 1, era start) + safeFromTip.     *)
(*   [R5] Summary.hs 487-560: invariantSummary (bounds line up, no empty  *)
(*        era, INV-1b, INV-2b).                                            *)
(*   [R6] Summary.hs 630-679: a decoded Summary has at least one era.     *)
(*   [R7] Qry.hs 296-345, 366-378: lower bounds are inclusive, upper      *)
(*        bounds inclusive at an epoch-aligned boundary; in-era slot to   *)
(*        epoch is division by the era's epoch size, slot to time is      *)
(*        multiplication by its slot length.                               *)
(*   [R8] Qry.hs 496-523: eras are tried in order; the first that can     *)
(*        evaluate the query answers it.                                   *)
(*   [R9] ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/     *)
(*        Shelley/ShelleyHFC.hs 198-255: TriggerHardForkAtVersion. The   *)
(*        next era starts at the epoch the updated parameters take effect *)
(*        when their major version EQUALS the trigger, once the update is *)
(*        stable.                                                          *)
(*   [R10] ouroboros-consensus-cardano/.../Cardano/Node.hs 363-382: the   *)
(*        default trigger is the next era's lowest protocol version;      *)
(*        cardano-ledger 1210d37fe6bd, libs/cardano-ledger-core/internal/ *)
(*        Cardano/Ledger/Internal/Definition/Era.hs 87-141: each era's    *)
(*        ProtVerLow and ProtVerHigh.                                      *)
(*                                                                         *)
(* gOuroboros: consensus/byron/byron.go (SlotToEpoch), ledger/byron/       *)
(* byron.go (SlotNumberFromEpochAndSlot), protocol/localstatequery/        *)
(* queries.go (EraHistoryResult, decode only), the per-era                 *)
(* Min/MaxProtocolVersion constants.                                       *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS
    Shape,       \* "Two" or "Three": which era table below to use
    SafeFromTip, \* the safe zone: slots ahead of the tip that are always convertible [R4]
    MaxSlot,     \* the last slot the chain walks to (keeps the model finite)
    Mutation,    \* "none", or one deliberate change that some invariant must catch
    GoByron      \* "Main": ByronConfig.SlotToEpoch on main; "Fixed": fix/consensus-byron-slot-epoch

\* The era tables. Era 1 is Byron-like (long slots, short epochs); later
\* eras have shorter slots and longer epochs, as on mainnet (Byron 20 s
\* slots and 21600-slot epochs, Shelley 1 s slots and 432000-slot epochs),
\* scaled down. Trigger holds each era's lowest protocol major; a major
\* between two triggers is an intra-era version (Alonzo 6, Babbage 8).
\* In English: "the slots per epoch of each era, in era order."
\* Literally: "EpochSize is defined as: if Shape equals "Two" then the tuple
\*   of 3 and 4, else the tuple of 2, 3 and 4."
EpochSize == IF Shape = "Two" THEN <<3, 4>> ELSE <<2, 3, 4>>
\* Literally: "SlotLen is defined as: if Shape equals "Two" then the tuple
\*   of 3 and 1, else the tuple of 4, 2 and 1."
SlotLen   == IF Shape = "Two" THEN <<3, 1>> ELSE <<4, 2, 1>>
\* Literally: "Trigger is defined as: if Shape equals "Two" then the tuple
\*   of 1 and 3, else the tuple of 1, 2 and 4."
Trigger   == IF Shape = "Two" THEN <<1, 3>> ELSE <<1, 2, 4>>
\* In English: "the highest major a vote may reach: one intra-era bump
\* past the last era's trigger."
\* Literally: "MaxPV is defined as element (the length of Trigger) of
\*   Trigger, plus 1."
MaxPV     == Trigger[Len(Trigger)] + 1

\* In English: "how many eras the table has."
\* Literally: "NumEras is defined as the length of EpochSize."
NumEras == Len(EpochSize)

\* In English: "the era numbers."
\* Literally: "Eras is defined as 1 through NumEras."
Eras == 1..NumEras

\* In English: "the largest epoch size of any era."
\* Literally: "MaxEpochSize is defined as the m, chosen from the set of
\*   EpochSize of i for every i that is a member of Eras, such that for all
\*   j in Eras, EpochSize of j is at most m."
MaxEpochSize == CHOOSE m \in {EpochSize[i] : i \in Eras} : \A j \in Eras : EpochSize[j] <= m

\* Slots whose conversions the model remembers, to check they never change.
\* A horizon is at most one epoch past the tip plus the safe zone, so this
\* range covers every convertible slot.
\* In English: "every slot whose conversion could ever be asked for."
\* Literally: "QuerySlots is defined as 0 through MaxSlot plus SafeFromTip
\*   plus 2 times MaxEpochSize."
QuerySlots == 0..(MaxSlot + SafeFromTip + 2 * MaxEpochSize)

ASSUME Len(SlotLen) = NumEras /\ Len(Trigger) = NumEras
ASSUME \A i \in 1..(NumEras - 1) : Trigger[i] < Trigger[i + 1]
ASSUME Mutation \in {"none", "NextEraSize", "LateVote", "HorizonPlusOne", "AnyBump"}
ASSUME GoByron \in {"Main", "Fixed"}

VARIABLES
    nslot,     \* the next slot to fill; the ledger tip is nslot - 1 (-1 is Origin)
    wEra,      \* walk: the era of slot nslot
    wEpoch,    \* walk: the epoch of slot nslot
    wInEpoch,  \* walk: slot nslot's position inside its epoch
    wTime,     \* walk: the start time of slot nslot
    pv,        \* the adopted protocol major version
    pending,   \* a voted version waiting for the epoch boundary (0 = none)
    starts,    \* the start epoch of every era the Summary knows, in era order
    answered   \* every conversion ever given: slot -> <<epoch, time>>

vars == <<nslot, wEra, wEpoch, wInEpoch, wTime, pv, pending, starts, answered>>

(***************************************************************************)
(* The reference's Summary, as a function of the known era starts and the *)
(* ledger tip.                                                             *)
(***************************************************************************)

\* In English: "the larger of a and b."
\* Literally: "Max of a and b is defined as: if a is at least b then a,
\*   else b."
Max(a, b) == IF a >= b THEN a ELSE b

\* The epoch size used when an era's end is computed. The NextEraSize
\* mutation uses the following era's size, a slip that mixes two eras'
\* parameters [R1].
\* In English: "the epoch size era i's bounds are computed with."
\* Literally: "BoundSize of i is defined as: if Mutation equals
\*   "NextEraSize" and i is less than NumEras, then EpochSize of (i plus
\*   1), else EpochSize of i."
BoundSize(i) == IF Mutation = "NextEraSize" /\ i < NumEras
                THEN EpochSize[i + 1]
                ELSE EpochSize[i]

\* mkUpperBound [R1]: the bound hiEpoch epochs after lo, in era i.
\* In English: "the bound of era i at epoch hiEpoch, counting whole epochs
\* of era i's size from lo."
\* Literally: "MkUpper of i, lo and hiEpoch is defined as the record whose
\*   field epoch is hiEpoch, whose field slot is lo's slot plus (hiEpoch
\*   minus lo's epoch) times BoundSize of i, and whose field time is lo's
\*   time plus (hiEpoch minus lo's epoch) times BoundSize of i times
\*   SlotLen of i."
MkUpper(i, lo, hiEpoch) ==
    [epoch |-> hiEpoch,
     slot  |-> lo.slot + (hiEpoch - lo.epoch) * BoundSize(i),
     time  |-> lo.time + (hiEpoch - lo.epoch) * BoundSize(i) * SlotLen[i]]

\* slotToEpochBound [R2]: the first epoch boundary at or after hiSlot.
\* In English: "round slot hiSlot up to an epoch boundary of era i, and
\* name that epoch."
\* Literally: "SlotToEpochBound of i, lo and hiSlot is defined as: letting
\*   n be hiSlot minus lo's slot: lo's epoch plus n integer-divided by
\*   EpochSize of i, plus 1 if n modulo EpochSize of i does not equal 0,
\*   else plus 0."
SlotToEpochBound(i, lo, hiSlot) ==
    LET n == hiSlot - lo.slot
    IN  lo.epoch + n \div EpochSize[i] + (IF n % EpochSize[i] /= 0 THEN 1 ELSE 0)

\* The start bound of each known era: the first starts at zero; each next
\* one is the previous era's upper bound at its start epoch [R4].
\* In English: "where known era i starts: slot, epoch and time."
\* Literally: "StartBound of st and i is defined recursively as: if i
\*   equals 1 then the record whose slot, epoch and time are 0, else
\*   MkUpper of i minus 1, StartBound of st and i minus 1, and element i of
\*   st."
RECURSIVE StartBound(_, _)
StartBound(st, i) ==
    IF i = 1 THEN [slot |-> 0, epoch |-> 0, time |-> 0]
    ELSE MkUpper(i - 1, StartBound(st, i - 1), st[i])

\* The end bound of each known era: the next era's start, or for the last
\* known era, the safe zone from the tip rounded up to an epoch [R4].
\* In English: "where known era i ends, given ledger tip tp."
\* Literally: "EndBound of st, tp and i is defined as: letting lo be
\*   StartBound of st and i: if i is less than the length of st, then
\*   StartBound of st and i plus 1, else MkUpper of i, lo and
\*   SlotToEpochBound of i, lo and (Max of tp plus 1 and lo's slot) plus
\*   SafeFromTip."
EndBound(st, tp, i) ==
    LET lo == StartBound(st, i)
    IN  IF i < Len(st) THEN StartBound(st, i + 1)
        ELSE MkUpper(i, lo, SlotToEpochBound(i, lo, Max(tp + 1, lo.slot) + SafeFromTip))

\* The horizon: the last slot any conversion may name. It is inclusive
\* because the end is epoch-aligned: its epoch and time do not depend on
\* the era after it [R7]. The HorizonPlusOne mutation lets one more slot
\* through.
\* In English: "the last slot this Summary can convert."
\* Literally: "Horizon of st and tp is defined as the slot of EndBound of
\*   st, tp and the length of st, plus (1 if Mutation equals
\*   "HorizonPlusOne", else 0)."
Horizon(st, tp) == EndBound(st, tp, Len(st)).slot + (IF Mutation = "HorizonPlusOne" THEN 1 ELSE 0)

\* In English: "slot s can be converted with this Summary."
\* Literally: "Convertible of st, tp and s is defined as: s is at most
\*   Horizon of st and tp."
Convertible(st, tp, s) == s <= Horizon(st, tp)

\* The era that answers a query about slot s: the first known era whose
\* end is at or after s [R8]. Past the last era's end, the last era (only
\* reachable under the HorizonPlusOne mutation).
\* In English: "the era that answers a query about slot s."
\* Literally: "AnsweringEra of st, tp and s is defined as: if there exists
\*   an i in 1 through the length of st such that s is at most EndBound of
\*   st, tp and i's slot, then the i, chosen from 1 through the length of
\*   st, such that s is at most EndBound of st, tp and i's slot and for all
\*   j in 1 through i minus 1, s is more than EndBound of st, tp and j's
\*   slot; else the length of st."
AnsweringEra(st, tp, s) ==
    IF \E i \in 1..Len(st) : s <= EndBound(st, tp, i).slot
    THEN CHOOSE i \in 1..Len(st) :
            /\ s <= EndBound(st, tp, i).slot
            /\ \A j \in 1..(i - 1) : s > EndBound(st, tp, j).slot
    ELSE Len(st)

\* The conversion [R7]: within its era, a slot's epoch is the era's start
\* epoch plus whole epochs of the era's size, and its time is the era's
\* start time plus slots times the era's slot length.
\* In English: "slot s as <<epoch, time>>."
\* Literally: "Conv of st, tp and s is defined as: letting i be
\*   AnsweringEra of st, tp and s, and lo be StartBound of st and i: the
\*   tuple of lo's epoch plus (s minus lo's slot) integer-divided by
\*   EpochSize of i, and lo's time plus (s minus lo's slot) times SlotLen
\*   of i."
Conv(st, tp, s) ==
    LET i  == AnsweringEra(st, tp, s)
        lo == StartBound(st, i)
    IN  <<lo.epoch + (s - lo.slot) \div EpochSize[i],
          lo.time + (s - lo.slot) * SlotLen[i]>>

(***************************************************************************)
(* The chain.                                                              *)
(***************************************************************************)

\* In English: "the ledger tip: the slot of the last block."
\* Literally: "Tip is defined as nslot minus 1."
Tip == nslot - 1

\* The era a protocol major belongs to: the last era whose trigger is at
\* or below it [R10].
\* In English: "the era protocol version v belongs to."
\* Literally: "EraForPV of v is defined as the i, chosen from Eras, such
\*   that Trigger of i is at most v and for all j in Eras, if Trigger of j
\*   is at most v then j is at most i."
EraForPV(v) == CHOOSE i \in Eras : Trigger[i] <= v /\ \A j \in Eras : Trigger[j] <= v => j <= i

\* Whether adopting version v in era e starts the next era [R9]: v must
\* equal the next era's trigger. AnyBump starts the next era on any bump.
\* In English: "adopting version v in era e moves the chain to the next era."
\* Literally: "StartsNextEra of v and e is defined as: e is less than
\*   NumEras, and (Mutation equals "AnyBump" or v equals Trigger of (e
\*   plus 1))."
StartsNextEra(v, e) == e < NumEras /\ (Mutation = "AnyBump" \/ v = Trigger[e + 1])

\* In English: "the first slot of the epoch after slot nslot's."
\* Literally: "NextBoundary is defined as nslot minus wInEpoch plus
\*   EpochSize of wEra."
NextBoundary == nslot - wInEpoch + EpochSize[wEra]

\* A vote is stable in time only if the Summary before it never let a
\* conversion reach past the coming boundary: the block's own slot plus
\* the safe zone must not pass it [S3][R9]. LateVote drops the deadline.
\* In English: "the block at nslot may still vote this epoch."
\* Literally: "VoteOpen is defined as: Mutation equals "LateVote", or nslot
\*   plus SafeFromTip is at most NextBoundary."
VoteOpen == Mutation = "LateVote" \/ nslot + SafeFromTip <= NextBoundary

\* Every slot the Summary converts now, remembered with its answer. Slots
\* answered before keep their old answer, so a later change shows up as a
\* mismatch in ConversionsStable.
\* In English: "add the answers for every slot that has just become convertible."
\* Literally: "Remember of ans, st and tp is defined as the function that
\*   maps every s in (the domain of ans) union (the set of every q in
\*   QuerySlots such that Convertible of st, tp and q) to: if s is a member
\*   of the domain of ans then ans of s, else Conv of st, tp and s."
Remember(ans, st, tp) ==
    [s \in DOMAIN ans \cup {q \in QuerySlots : Convertible(st, tp, q)} |->
        IF s \in DOMAIN ans THEN ans[s] ELSE Conv(st, tp, s)]

\* In English: "start at slot 0 of the first era, version Trigger[1], with
\* every conversion of the empty chain remembered."
\* Literally: "Init is defined as: nslot equals 0, and wEra equals 1, and
\*   wEpoch, wInEpoch and wTime equal 0, and pv equals Trigger of 1, and
\*   pending equals 0, and starts equals the tuple of 0, and answered equals
\*   Remember of the empty function, the tuple of 0, and minus 1."
Init ==
    /\ nslot = 0
    /\ wEra = 1
    /\ wEpoch = 0
    /\ wInEpoch = 0
    /\ wTime = 0
    /\ pv = Trigger[1]
    /\ pending = 0
    /\ starts = <<0>>
    /\ answered = Remember([s \in {} |-> 0], <<0>>, -1)

\* The block at slot nslot is applied, voting or not. A vote raises the
\* major by one (the ledger lets a version follow only by one major [R9]);
\* if that is the next era's trigger, the Summary learns the next era's
\* start epoch at once. Leaving the epoch's last slot adopts the pending
\* version and, on a trigger, enters the next era.
\* In English: "apply the block at the next slot, with or without a vote."
\* Literally: "Advance of vote is defined as: nslot is at most MaxSlot, and
\*   letting v be pv plus 1, doVote be (vote and pending equals 0 and v is
\*   at most MaxPV and VoteOpen), pend be (if doVote then v else pending),
\*   st be (if doVote and StartsNextEra of v and wEra then starts with
\*   wEpoch plus 1 appended, else starts), last be (wInEpoch plus 1 equals
\*   EpochSize of wEra), and nextEra be (if last and pend does not equal 0
\*   and StartsNextEra of pend and wEra then wEra plus 1 else wEra): nslot
\*   in the next state equals nslot plus 1, and wTime in the next state
\*   equals wTime plus SlotLen of wEra, and wInEpoch in the next state is
\*   (if last then 0 else wInEpoch plus 1), and wEpoch in the next state is
\*   (if last then wEpoch plus 1 else wEpoch), and wEra in the next state
\*   equals nextEra, and pv in the next state is (if last and pend does not
\*   equal 0 then pend else pv), and pending in the next state is (if last
\*   then 0 else pend), and starts in the next state equals st, and
\*   answered in the next state equals Remember of answered, st and nslot."
Advance(vote) ==
    /\ nslot <= MaxSlot
    /\ LET v       == pv + 1
           doVote  == vote /\ pending = 0 /\ v <= MaxPV /\ VoteOpen
           pend    == IF doVote THEN v ELSE pending
           st      == IF doVote /\ StartsNextEra(v, wEra)
                      THEN Append(starts, wEpoch + 1) ELSE starts
           last    == wInEpoch + 1 = EpochSize[wEra]
           nextEra == IF last /\ pend /= 0 /\ StartsNextEra(pend, wEra) THEN wEra + 1 ELSE wEra
       IN  /\ nslot' = nslot + 1
           /\ wTime' = wTime + SlotLen[wEra]
           /\ wInEpoch' = IF last THEN 0 ELSE wInEpoch + 1
           /\ wEpoch' = IF last THEN wEpoch + 1 ELSE wEpoch
           /\ wEra' = nextEra
           /\ pv' = IF last /\ pend /= 0 THEN pend ELSE pv
           /\ pending' = IF last THEN 0 ELSE pend
           /\ starts' = st
           /\ answered' = Remember(answered, st, nslot)

\* In English: "the walk has reached MaxSlot; nothing more happens."
\* Literally: "Done is defined as: nslot is more than MaxSlot, and vars is
\*   unchanged."
Done == nslot > MaxSlot /\ UNCHANGED vars

\* In English: "apply the next block, or stop at the end."
\* Literally: "Next is defined as: there exists a vote in BOOLEAN such that
\*   Advance of vote, or Done."
Next == (\E vote \in BOOLEAN : Advance(vote)) \/ Done

\* In English: "start in Init and take Next steps."
\* Literally: "Spec is defined as: Init and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

\* In English: "every variable holds a value of the expected kind."
\* Literally: "TypeOK is defined as: nslot is a member of 0 through MaxSlot
\*   plus 1, and wEra is a member of Eras, and pv is a member of Trigger of
\*   1 through MaxPV, and pending is a member of {0} union (pv plus 1
\*   through MaxPV), and the length of starts is a member of Eras."
TypeOK ==
    /\ nslot \in 0..(MaxSlot + 1)
    /\ wEra \in Eras
    /\ pv \in Trigger[1]..MaxPV
    /\ pending \in {0} \cup ((pv + 1)..MaxPV)
    /\ Len(starts) \in Eras

\* The Summary converts the next slot exactly as the walk reached it.
\* In English: "the closed-form conversion agrees with walking the chain."
\* Literally: "SummaryMatchesWalk is defined as: Convertible of starts, Tip
\*   and nslot, and Conv of starts, Tip and nslot equals the tuple of wEpoch
\*   and wTime."
SummaryMatchesWalk ==
    /\ Convertible(starts, Tip, nslot)
    /\ Conv(starts, Tip, nslot) = <<wEpoch, wTime>>

\* [S1][S3]: once a slot is converted, it stays convertible and its answer
\* never changes as blocks are applied.
\* In English: "an answer once given is never withdrawn or changed."
\* Literally: "ConversionsStable is defined as: for all s in the domain of
\*   answered, Convertible of starts, Tip and s, and Conv of starts, Tip and
\*   s equals answered of s."
ConversionsStable ==
    \A s \in DOMAIN answered :
        /\ Convertible(starts, Tip, s)
        /\ Conv(starts, Tip, s) = answered[s]

\* [R3][R5]: each bounded era is whole epochs of its own size long, its
\* time is its slots times its slot length, it is not empty, and each era
\* starts where the one before ended.
\* In English: "every era's bounds obey the reference's Summary invariants."
\* Literally: "SummaryInvariants is defined as: for all i in 1 through the
\*   length of starts, letting lo be StartBound of starts and i, and hi be
\*   EndBound of starts, Tip and i: hi's epoch is more than lo's epoch, and
\*   hi's slot equals lo's slot plus (hi's epoch minus lo's epoch) times
\*   EpochSize of i, and hi's time equals lo's time plus (hi's slot minus
\*   lo's slot) times SlotLen of i, and if i is less than the length of
\*   starts then hi equals StartBound of starts and i plus 1."
SummaryInvariants ==
    \A i \in 1..Len(starts) :
        LET lo == StartBound(starts, i)
            hi == EndBound(starts, Tip, i)
        IN  /\ hi.epoch > lo.epoch
            /\ hi.slot = lo.slot + (hi.epoch - lo.epoch) * EpochSize[i]
            /\ hi.time = lo.time + (hi.slot - lo.slot) * SlotLen[i]
            /\ i < Len(starts) => hi = StartBound(starts, i + 1)

\* [R6]: a Summary always names at least one era.
\* In English: "the Summary knows at least one era."
\* Literally: "SummaryNonEmpty is defined as: the length of starts is at
\*   least 1."
SummaryNonEmpty == Len(starts) >= 1

\* [R9][R10]: the chain is in the era its protocol version belongs to.
\* In English: "the chain is in the era its protocol version belongs to."
\* Literally: "EraMatchesVersion is defined as: wEra equals EraForPV of pv."
EraMatchesVersion == wEra = EraForPV(pv)

\* gOuroboros' ByronConfig.SlotToEpoch: slot / SlotsPerEpoch, with the
\* first era's epoch size. It is right while the chain is in the first era.
\* In English: "in the first era, the Byron formula gives the walk's epoch."
\* Literally: "GoByronFormulaInFirstEra is defined as: if wEra equals 1,
\*   then nslot integer-divided by EpochSize of 1 equals wEpoch."
GoByronFormulaInFirstEra == wEra = 1 => nslot \div EpochSize[1] = wEpoch

\* The same formula applied past the first era (expected to fail).
\* In English: "the Byron formula gives the walk's epoch in every era."
\* Literally: "GoByronFormulaEverywhere is defined as: nslot integer-divided
\*   by EpochSize of 1 equals wEpoch."
GoByronFormulaEverywhere == nslot \div EpochSize[1] = wEpoch

\* gOuroboros' ByronConfig.SlotToEpochChecked, with -1 for its error. On
\* main (and through SlotToEpoch) it is slot / SlotsPerEpoch for every
\* slot. On the fix, once the Summary knows a second era the caller sets
\* Byron's end slot (the second era's start), and a slot at or past it is
\* an error: converting it needs the era history [R7][R8].
\* In English: "gOuroboros' Byron epoch for slot s, or -1 for an error,
\* given the known era starts st."
\* Literally: "GoByronEpoch of st and s is defined as: if GoByron equals
\*   "Fixed" and the length of st is more than 1 and s is at least the slot
\*   of StartBound of st and 2, then minus 1, else s integer-divided by
\*   EpochSize of 1."
GoByronEpoch(st, s) ==
    IF GoByron = "Fixed" /\ Len(st) > 1 /\ s >= StartBound(st, 2).slot
    THEN -1
    ELSE s \div EpochSize[1]

\* Every answer gOuroboros gives for a slot the Summary can convert is the
\* Summary's epoch: it never answers a later era's slot with Byron's
\* formula.
\* In English: "every epoch gOuroboros' Byron conversion gives is right."
\* Literally: "GoByronSound is defined as: for all s in QuerySlots, if
\*   Convertible of starts, Tip and s and GoByronEpoch of starts and s does
\*   not equal minus 1, then GoByronEpoch of starts and s equals element 1
\*   of Conv of starts, Tip and s."
GoByronSound ==
    \A s \in QuerySlots :
        Convertible(starts, Tip, s) /\ GoByronEpoch(starts, s) /= -1
            => GoByronEpoch(starts, s) = Conv(starts, Tip, s)[1]

\* The fix still answers while the chain is in the first era.
\* In English: "in the first era gOuroboros answers the next slot, with
\* the walk's epoch."
\* Literally: "GoByronAnswersInFirstEra is defined as: if wEra equals 1,
\*   then GoByronEpoch of starts and nslot equals wEpoch."
GoByronAnswersInFirstEra == wEra = 1 => GoByronEpoch(starts, nslot) = wEpoch

\* [R9]: an era changes only at an epoch boundary.
\* In English: "eras change only where an epoch starts."
\* Literally: "EraChangesAtBoundary is defined as: always, every step is a
\*   step in which (if wEra in the next state does not equal wEra, then
\*   wInEpoch in the next state equals 0), or a step that leaves vars
\*   unchanged."
EraChangesAtBoundary == [][wEra' /= wEra => wInEpoch' = 0]_vars

(***************************************************************************)
(* Reachability probes: each must be violated in its *Bug.cfg.            *)
(***************************************************************************)

\* In English: "the chain never leaves the first era (expected to fail)."
\* Literally: "ProbeTransition is defined as: wEra equals 1."
ProbeTransition == wEra = 1

\* An intra-era version bump (Alonzo 5 to 6, Babbage 7 to 8).
\* In English: "the version is always its era's first (expected to fail)."
\* Literally: "ProbeIntraEraBump is defined as: pv equals Trigger of wEra."
ProbeIntraEraBump == pv = Trigger[wEra]

\* A Summary with two eras whose horizon lies in the second era before the
\* chain has reached it (case iii of the safe zone [R4]).
\* In English: "the Summary never knows an era the chain has not reached (expected to fail)."
\* Literally: "ProbeKnownFutureEra is defined as: it is not true that (the
\*   length of starts is more than 1 and wEra equals 1)."
ProbeKnownFutureEra == ~(Len(starts) > 1 /\ wEra = 1)

=============================================================================
