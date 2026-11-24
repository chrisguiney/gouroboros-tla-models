---------------------------- MODULE ByronEnvelope ----------------------------
(***************************************************************************)
(* The Byron header envelope's slot and block-number rules, checked for   *)
(* every predecessor kind (Origin, main block, EBB), every way the caller *)
(* can pass the predecessor (as a header or as a whole block), every      *)
(* header kind, and a header at an earlier, the same or a later slot and  *)
(* at the same, the next or a skipped block number.                       *)
(*                                                                         *)
(* Sources.                                                               *)
(*   [R8] ouroboros-consensus ec239d57, Ouroboros/Consensus/              *)
(*        HeaderValidation.hs 378-423, validateEnvelope: after Origin the  *)
(*        block number is 0 and any slot is allowed; after a block the    *)
(*        number is expectedNextBlockNo and the slot at least              *)
(*        minimumNextSlotNo.                                               *)
(*   [B1] ouroboros-consensus ec239d57, ouroboros-consensus-cardano/src/  *)
(*        byron/Ouroboros/Consensus/Byron/Ledger/HeaderValidation.hs      *)
(*        30-52: the predecessor's kind is byronHeaderIsEBB of the block   *)
(*        (getTipInfo); an EBB after a main block shares its number; a    *)
(*        main block after an EBB may share its slot.                     *)
(*   [G1] gOuroboros PR #3111 at 094aeac6, consensus/byron/validate.go    *)
(*        ValidateByronBlockHeader: PrevIsEBB only when the predecessor   *)
(*        is a *ByronEpochBoundaryBlockHeader, so an EBB passed as a      *)
(*        *ByronEpochBoundaryBlock counts as a main block.                *)
(*   [G2] The fix: an EBB predecessor counts as an EBB whether it is      *)
(*        passed as a header or as a block.                               *)
(* Hash and protocol-magic checks are out of scope here; the Shelley      *)
(* envelope model covers the predecessor hash after Origin.               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Mutation    \* "none" ([G2]) or "GoEBBHeaderOnly" ([G1])

ASSUME Mutation \in {"none", "GoEBBHeaderOnly"}

\* In English: the slot and block number of the predecessor, when there is
\* one.
\* Literally: "PrevSlot is defined as 20, and PrevNo is defined as 5."
PrevSlot == 20
PrevNo   == 5

\* In English: every case the table checks: the predecessor's kind and how
\* it is passed, the header's kind, its slot and its block number.
\* Literally: "Cases is defined as the set of records whose field prev is
\*   "Origin", "Main" or "EBB", whose field repr is "Header" or "Block",
\*   whose field cur is "Main" or "EBB", whose field slot is 19, 20 or 21, and
\*   whose field no is 0, 4, 5 or 6."
Cases == [prev : {"Origin", "Main", "EBB"}, repr : {"Header", "Block"},
          cur : {"Main", "EBB"}, slot : {19, 20, 21}, no : {0, 4, 5, 6}]

\* In English: the reference's verdict, given whether the predecessor is an
\* EBB [R8][B1]. After Origin, block 0 at any slot.
\* Literally: "EnvOK of c and prevEBB is defined as: if c's prev equals
\*   "Origin" then c's no equals 0; else c's no equals (if prevEBB is not
\*   true and c's cur equals "EBB" then PrevNo else PrevNo plus 1), and c's
\*   slot is at least (if prevEBB and c's cur equals "Main" then PrevSlot
\*   else PrevSlot plus 1)."
EnvOK(c, prevEBB) ==
    IF c.prev = "Origin" THEN c.no = 0
    ELSE /\ c.no = (IF ~prevEBB /\ c.cur = "EBB" THEN PrevNo ELSE PrevNo + 1)
         /\ c.slot >= (IF prevEBB /\ c.cur = "Main" THEN PrevSlot ELSE PrevSlot + 1)

\* In English: the reference takes the predecessor's kind from the block
\* itself, however it is held [B1].
\* Literally: "RefOK of c is defined as EnvOK of c and (c's prev equals
\*   "EBB")."
RefOK(c) == EnvOK(c, c.prev = "EBB")

\* In English: gOuroboros' classification of the predecessor. [G1] sees an
\* EBB only when it is passed as a header; [G2] sees it either way.
\* Literally: "GoPrevIsEBB of c is defined as: c's prev equals "EBB", and
\*   (c's repr equals "Header" or Mutation equals "none")."
GoPrevIsEBB(c) ==
    c.prev = "EBB" /\ (c.repr = "Header" \/ Mutation = "none")

\* In English: gOuroboros' verdict: the reference rules applied to its own
\* classification of the predecessor.
\* Literally: "GoOK of c is defined as EnvOK of c and GoPrevIsEBB of c."
GoOK(c) == EnvOK(c, GoPrevIsEBB(c))

\* The state is one case.
VARIABLE cs
\* In English: TLC starts from every case in the table.
\* Literally: "Init is defined as: cs is a member of Cases."
Init == cs \in Cases
\* In English: nothing moves; each case is checked where it starts.
\* Literally: "Next is defined as: cs is unchanged."
Next == UNCHANGED cs
\* In English: start from any case and never change it.
\* Literally: "Spec is defined as Init and always [Next]_cs."
Spec == Init /\ [][Next]_cs

\* In English: gOuroboros accepts the envelope exactly when the reference
\* does.
\* Literally: "EnvelopeAgrees is defined as: GoOK of cs equals RefOK of cs."
EnvelopeAgrees == GoOK(cs) = RefOK(cs)

\* In English: how the predecessor is passed never changes the verdict.
\* Literally: "ReprIrrelevant is defined as: GoOK of cs equals GoOK of the
\*   record cs with its repr field replaced by "Header"."
ReprIrrelevant == GoOK(cs) = GoOK([cs EXCEPT !.repr = "Header"])

\* In English: PROBE (must fail): no main block ever shares an EBB
\* predecessor's slot.
\* Literally: "NoMainSharesEBBSlot is defined as: if cs's prev equals "EBB"
\*   and cs's cur equals "Main" and cs's slot equals PrevSlot, then GoOK of
\*   cs is not true."
NoMainSharesEBBSlot ==
    (cs.prev = "EBB" /\ cs.cur = "Main" /\ cs.slot = PrevSlot) => ~GoOK(cs)
==============================================================================
