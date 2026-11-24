--------------------------- MODULE ShelleyEnvelope ---------------------------
(***************************************************************************)
(* The Shelley-family header envelope: the sequence checks a header must  *)
(* pass against the block before it, or against Origin when it is the     *)
(* first on the chain. The reference's verdict and gOuroboros' three      *)
(* envelope predicates are compared on every combination of predecessor,  *)
(* slot, block number and named predecessor hash.                         *)
(*                                                                         *)
(* Sources.                                                               *)
(*   [R8] ouroboros-consensus ec239d57, Ouroboros/Consensus/              *)
(*        HeaderValidation.hs 378-423, validateEnvelope: after Origin the  *)
(*        block number is expectedFirstBlockNo (0), the slot is at least  *)
(*        minimumPossibleSlotNo (0), and the predecessor is GenesisHash;   *)
(*        after a block the number is one more, the slot is later, and    *)
(*        the predecessor is BlockHash of that block.                      *)
(*   [G1] gOuroboros d0b95845 consensus/validate.go: no way to say        *)
(*        Origin, so a first header is checked against a zero previous    *)
(*        block and block 0 always fails.                                 *)
(*   [G2] PR #3111 at 1bc529c6: PrevIsOrigin; block 0, any slot, and the   *)
(*        predecessor hash is not checked.                                 *)
(*   [G3] PR #3111 at 64573df5: as [G2], and the predecessor must be      *)
(*        absent or the zero hash, which a null Shelley predecessor        *)
(*        decodes to.                                                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Mutation    \* "none" ([G3]), "GoOriginAnyPrev" ([G2]), "GoNoOrigin" ([G1])

ASSUME Mutation \in {"none", "GoOriginAnyPrev", "GoNoOrigin"}

\* In English: the slot and block number of the block before the header,
\* when there is one.
\* Literally: "PrevSlot is defined as 4, and PrevNo is defined as 3."
PrevSlot == 4
PrevNo   == 3

\* In English: the predecessor hash a header can name. "Absent" and "Zero"
\* are how gOuroboros holds GenesisHash (a null predecessor decodes to the
\* zero hash); "Previous" is the hash of the block before; "Other" is any
\* other block's hash.
\* Literally: "Named is defined as the set containing "Absent", "Zero",
\*   "Previous" and "Other"."
Named == {"Absent", "Zero", "Previous", "Other"}

\* In English: every header the table checks: whether it is the first on
\* the chain, its slot, its block number and the predecessor it names.
\* Literally: "Headers is defined as the set of records whose field origin
\*   is TRUE or FALSE, whose field slot is 0, 4 or 5, whose field no is 0, 1,
\*   4 or 5, and whose field prev is a member of Named."
Headers == [origin : BOOLEAN, slot : {0, 4, 5}, no : {0, 1, 4, 5}, prev : Named]

\* In English: the header names GenesisHash.
\* Literally: "IsGenesis of h is defined as: h's prev is a member of the set
\*   containing "Absent" and "Zero"."
IsGenesis(h) == h.prev \in {"Absent", "Zero"}

\* In English: the reference accepts the header's envelope [R8].
\* Literally: "RefOK of h is defined as: if h's origin then h's no equals 0
\*   and IsGenesis of h, else h's no equals PrevNo plus 1 and h's slot is
\*   greater than PrevSlot and h's prev equals "Previous"."
RefOK(h) ==
    IF h.origin
    THEN h.no = 0 /\ IsGenesis(h)
    ELSE h.no = PrevNo + 1 /\ h.slot > PrevSlot /\ h.prev = "Previous"

\* In English: validateSlotOrdering. After Origin any slot; [G1] compares
\* with a zero previous slot, so slot 0 fails.
\* Literally: "GoSlotOK of h is defined as: if h's origin and Mutation does
\*   not equal "GoNoOrigin" then TRUE, else h's slot is greater than (if h's
\*   origin then 0 else PrevSlot)."
GoSlotOK(h) ==
    IF h.origin /\ Mutation # "GoNoOrigin" THEN TRUE
    ELSE h.slot > (IF h.origin THEN 0 ELSE PrevSlot)

\* In English: validateBlockNumber. After Origin block 0; [G1] expects one
\* more than a zero previous block.
\* Literally: "GoNoOK of h is defined as: if h's origin then h's no equals
\*   (if Mutation equals "GoNoOrigin" then 1 else 0), else h's no equals
\*   PrevNo plus 1."
GoNoOK(h) ==
    IF h.origin THEN h.no = (IF Mutation = "GoNoOrigin" THEN 1 ELSE 0)
    ELSE h.no = PrevNo + 1

\* In English: validatePrevHash. After Origin: [G3] requires the genesis
\* representation, [G2] accepts anything, and [G1] has no previous hash to
\* compare with, so it accepts block 0's predecessor and requires one for a
\* later block (it is never compared). After a block the named hash must be
\* the previous block's; "Absent" and "Zero" differ from it.
\* Literally: "GoPrevOK of h is defined as: if h's origin then (in the case
\*   Mutation equals "GoOriginAnyPrev", TRUE; in the case Mutation equals
\*   "GoNoOrigin", h's no equals 0 or h's prev does not equal "Absent"; in
\*   every other case, IsGenesis of h), else h's prev equals "Previous"."
GoPrevOK(h) ==
    IF h.origin
    THEN CASE Mutation = "GoOriginAnyPrev" -> TRUE
           [] Mutation = "GoNoOrigin"      -> h.no = 0 \/ h.prev # "Absent"
           [] OTHER                        -> IsGenesis(h)
    ELSE h.prev = "Previous"

\* In English: gOuroboros accepts the header's envelope.
\* Literally: "GoOK of h is defined as: GoSlotOK of h and GoNoOK of h and
\*   GoPrevOK of h."
GoOK(h) == GoSlotOK(h) /\ GoNoOK(h) /\ GoPrevOK(h)

\* The state is one header.
VARIABLE hdr
\* In English: TLC starts from every header in the table.
\* Literally: "Init is defined as: hdr is a member of Headers."
Init == hdr \in Headers
\* In English: nothing moves; each header is checked where it starts.
\* Literally: "Next is defined as: hdr is unchanged."
Next == UNCHANGED hdr
\* In English: start from any header and never change it.
\* Literally: "Spec is defined as Init and always [Next]_hdr."
Spec == Init /\ [][Next]_hdr

\* In English: gOuroboros accepts the header's envelope exactly when the
\* reference does.
\* Literally: "EnvelopeAgrees is defined as: GoOK of hdr equals RefOK of
\*   hdr."
EnvelopeAgrees == GoOK(hdr) = RefOK(hdr)

\* In English: a first header naming a block, not the genesis, is refused.
\* This is the defect [G2] had; EnvelopeAgrees implies it.
\* Literally: "OriginNeedsGenesis is defined as: if hdr's origin and
\*   IsGenesis of hdr is not true, then GoOK of hdr is not true."
OriginNeedsGenesis == (hdr.origin /\ ~IsGenesis(hdr)) => ~GoOK(hdr)

\* In English: PROBE (must fail): no first header is ever accepted.
\* Literally: "NoOriginAccepted is defined as: if hdr's origin, then GoOK of
\*   hdr is not true."
NoOriginAccepted == hdr.origin => ~GoOK(hdr)
==============================================================================
