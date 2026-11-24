-------------------------- MODULE HeaderValidation --------------------------
(***************************************************************************)
(* The order of the checks that validate a Praos or TPraos block header,  *)
(* and the error each validator reports for a header with some defects.   *)
(*                                                                         *)
(* A header is described only by its set of defects D: which checks it    *)
(* would fail. The reference runs its checks in its own order and reports *)
(* the first failure (Praos), or the first failure of each group and      *)
(* every OCERT failure (TPraos, whose ledger rules collect failures).     *)
(* gOuroboros' HeaderValidator.ValidateHeader runs every check in its own *)
(* order and returns every error. The model runs the reference, then      *)
(* gOuroboros, one check per step, and compares what they report.         *)
(*                                                                         *)
(* The existing model specs/13-consensus covers the counter rule and the  *)
(* KES window as values; this model covers only the order and the         *)
(* reachability of each rejection.                                         *)
(*                                                                         *)
(* Sources (links and quotes in specs/25-consensus-eras/README.md).        *)
(*   Reference implementation, ouroboros-consensus ec239d57f618:           *)
(*   [H1] ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/ *)
(*        HeaderValidation.hs 369-391: the envelope: block number, then   *)
(*        slot, then previous hash, then the era's extra checks; the     *)
(*        first failure ends validation.                                   *)
(*   [H2] HeaderValidation.hs 515-534: validateHeader runs the envelope,  *)
(*        then the protocol's updateChainDepState.                        *)
(*   [H3] ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/     *)
(*        Shelley/Protocol/EnvelopeChecks.hs 60-91: the extra checks,    *)
(*        ObsoleteNode, HeaderSizeTooLarge, BlockSizeTooLarge.            *)
(*   [P1] ouroboros-consensus-protocol/src/ouroboros-consensus-protocol/   *)
(*        Ouroboros/Consensus/Protocol/PolyPraos.hs 650-694: Praos checks *)
(*        the KES side first, then the VRF side; Except stops at the      *)
(*        first failure.                                                   *)
(*   [P2] PolyPraos.hs 1046-1087: KESBeforeStart, KESAfterEnd, the        *)
(*        operational certificate signature, the KES signature, then the  *)
(*        counter (NoCounter, CounterTooSmall, CounterOverIncremented).   *)
(*   [P3] PolyPraos.hs 953-996: VRFKeyUnknown, VRFKeyWrongVRFKey,         *)
(*        VRFKeyBadProof, VRFLeaderValueTooBig.                           *)
(*   cardano-ledger 1210d37fe6bd, libs/cardano-protocol-tpraos/src/       *)
(*   Cardano/Protocol/TPraos/Rules/:                                       *)
(*   [T1] Overlay.hs 236-282: TPraos checks the VRF side (or the overlay  *)
(*        schedule's slot kind) first, then the OCERT rule.               *)
(*   [T2] Overlay.hs 164-232: VRFKeyUnknown, VRFKeyWrongVRFKey, the nonce *)
(*        VRF, the leader VRF, VRFLeaderValueTooBig, in one Either: the   *)
(*        first failure of the group.                                      *)
(*   [T3] OCert.hs 74-107: KESBeforeStart, KESAfterEnd, the certificate   *)
(*        signature, the KES signature (at evolution 0 when before start),*)
(*        the counter; each a predicate, all collected.                   *)
(*   [T4] API.hs 543-575: TPraos runs PRTCL with applySTS, which          *)
(*        validates all predicates and returns every failure.             *)
(*                                                                         *)
(*   [T5] Overlay.hs 238-282: overlayTransition. lookupInOverlaySchedule  *)
(*        on the slot: Nothing runs praosVrfChecks; NonActiveSlot fails   *)
(*        with NotActiveSlotOVERLAY; ActiveSlot gkey checks the issuer's *)
(*        cold key against gkey's delegate (WrongGenesisColdKeyOVERLAY,   *)
(*        a predicate, so the rule goes on), then pbftVrfChecks. The      *)
(*        OCERT rule runs in every case.                                   *)
(*   [T6] Overlay.hs 219-236: pbftVrfChecks: WrongGenesisVRFKeyOVERLAY,   *)
(*        then the nonce and leader VRF proofs; no stake, no leader value.*)
(*   [T7] Overlay.hs 314-344: classifyOverlaySlot: position =             *)
(*        ceiling((slot - firstSlot) * d), ascInv = floor(1 / f); the     *)
(*        slot is active when position mod ascInv = 0, and belongs to the *)
(*        genesis key at index (position div ascInv) mod |gkeys| in key  *)
(*        order. lookupInOverlaySchedule classifies only overlay slots.   *)
(*   [T8] libs/cardano-ledger-core/src/Cardano/Ledger/Slot.hs 117-130:    *)
(*        isOverlaySlot: ceiling(s * d) < ceiling((s + 1) * d), s the     *)
(*        slot's offset in its epoch. With d = 0 no slot is an overlay    *)
(*        slot, so every slot runs the plain Praos checks.                *)
(*   [H4] ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/     *)
(*        Shelley/Protocol/TPraos.hs 69-80: TPraos compares the header's *)
(*        own protocol major with the node's maximum; Protocol/Praos.hs  *)
(*        82-106: Praos compares the ledger view's protocol major. Both  *)
(*        take the size limits from the protocol parameters.             *)
(*   Specification: cardano-ledger 1210d37fe6bd, eras/shelley/formal-spec/ *)
(*   chain.tex:                                                            *)
(*   [F1] 1170-1192: isOverlaySlot and classifyOverlaySlot; 1198-1274:    *)
(*        the Active-OBFT and Decentralized rules of OVERLAY; 1280-1305:  *)
(*        its nine predicate failures.                                     *)
(*   [F2] 1682-1687: chainChecks: protocol major at most MaxMajorPV,      *)
(*        header size at most maxBHSize, body size at most maxBBSize.     *)
(*                                                                         *)
(* gOuroboros: consensus/validate.go, ValidateHeader and its checks.       *)
(* GoInputs = "Main" is main, whose ValidateHeaderInput cannot carry the   *)
(* overlay schedule or the envelope inputs. "Fixed" is the branch          *)
(* fix/consensus-tpraos-overlay, which requires them, reports a missing    *)
(* one as an error before any other check, and checks them.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Mode,       \* "Praos" (Babbage on) or "TPraos" (Shelley to Alonzo)
    GoOrder,    \* "Today": gOuroboros as it is; "Fixed": the order of the fix branch
    MaxDefects, \* the most defects one header carries (keeps the model finite)
    Extras,     \* TRUE: headers may also fail the reference's extra envelope checks
    Overlay,    \* TRUE: TPraos slots may be overlay slots (decentralisation d > 0)
    Mutation,   \* "none", or one deliberate change to the gOuroboros side
    GoInputs,   \* "Main": no overlay or envelope inputs; "Fixed": required and checked
    Inputs      \* "Full": the caller supplies every input; "Missing": it leaves one out

ASSUME Mode \in {"Praos", "TPraos"}
ASSUME GoOrder \in {"Today", "Fixed"}
ASSUME Overlay => Mode = "TPraos"
ASSUME Mutation \in {"none", "SkipCounter", "SpuriousKES", "SkipGenCold", "FloorPosition"}
ASSUME GoInputs \in {"Main", "Fixed"}
ASSUME Inputs \in {"Full", "Missing"}

(***************************************************************************)
(* Defects. Each is named after the reference error it causes.            *)
(***************************************************************************)

\* In English: "the reference's extra envelope defects."
\* Literally: "EnvelopeExtras is defined as the set containing "Obsolete",
\*   "HdrSize" and "BodySize"."
EnvelopeExtras == {"Obsolete", "HdrSize", "BodySize"}

\* [T5][T6]: in an active overlay slot the issuer must be the scheduled
\* genesis key's delegate (WrongGenesisColdKeyOVERLAY), and its VRF key
\* the one in that genesis delegation (WrongGenesisVRFKeyOVERLAY).
\* In English: "the defects only a header in an active overlay slot can have."
\* Literally: "GenesisDefects is defined as the set containing "GenColdKey"
\*   and "GenVRFKey"."
GenesisDefects == {"GenColdKey", "GenVRFKey"}

\* In English: "every defect a header of this mode can carry."
\* Literally: "Defects is defined as the union of the set containing
\*   "BlockNo", "Slot", "PrevHash", "KESBefore", "KESAfter", "OCertSig",
\*   "KESSig", "NoCounter", "CounterTooSmall", "VRFUnknown", "VRFWrongKey",
\*   "VRFBadProof" and "LeaderTooBig"; the set containing
\*   "CounterOverInc" if Mode equals "Praos", else the set containing
\*   "VRFBadNonce"; EnvelopeExtras if Extras, else the empty set; and
\*   GenesisDefects if Overlay, else the empty set."
Defects ==
    {"BlockNo", "Slot", "PrevHash",
     "KESBefore", "KESAfter", "OCertSig", "KESSig",
     "NoCounter", "CounterTooSmall",
     "VRFUnknown", "VRFWrongKey", "VRFBadProof", "LeaderTooBig"}
    \cup (IF Mode = "Praos" THEN {"CounterOverInc"} ELSE {"VRFBadNonce"})
    \cup (IF Extras THEN EnvelopeExtras ELSE {})
    \cup (IF Overlay THEN GenesisDefects ELSE {})

\* Defects that cannot occur together: a certificate is not both before
\* its start and after its end; a counter fails one way; a pool unknown to
\* the stake distribution has no registered VRF key and no stake. The
\* genesis-delegation defects exist only in an active overlay slot, and
\* the pool defects only outside one (a genesis delegate is not a pool).
\* In English: "D describes a header that could exist in a slot of kind k."
\* Literally: "Consistent of D and k is defined as: the set containing
\*   "KESBefore" and "KESAfter" is not a subset of D, and the number of
\*   members of the intersection of D and the set containing "NoCounter",
\*   "CounterTooSmall" and "CounterOverInc" is at most 1, and if "VRFUnknown"
\*   is a member of D then the intersection of D and the set containing
\*   "VRFWrongKey" and "LeaderTooBig" is empty, and if k does not equal
\*   "OBFT" then the intersection of D and GenesisDefects is empty, and if
\*   k equals "OBFT" then the intersection of D and the set containing
\*   "VRFUnknown", "VRFWrongKey" and "LeaderTooBig" is empty."
Consistent(D, k) ==
    /\ ~({"KESBefore", "KESAfter"} \subseteq D)
    /\ Cardinality(D \cap {"NoCounter", "CounterTooSmall", "CounterOverInc"}) <= 1
    /\ "VRFUnknown" \in D => D \cap {"VRFWrongKey", "LeaderTooBig"} = {}
    /\ k /= "OBFT" => D \cap GenesisDefects = {}
    /\ k = "OBFT" => D \cap {"VRFUnknown", "VRFWrongKey", "LeaderTooBig"} = {}

(***************************************************************************)
(* The overlay schedule [T7][T8][F1], scaled down: a 6-slot epoch, active *)
(* slot coefficient 1/2 (ascInv = 2), two genesis keys. Mainnet's first   *)
(* Shelley epoch had d = 1, f = 1/20 (ascInv = 20) and seven genesis keys.*)
(***************************************************************************)

\* In English: "slots per epoch in the model."
\* Literally: "EpochLen is defined as 6."
EpochLen == 6

\* In English: "floor(1 / f), the gap between active overlay slots."
\* Literally: "AscInv is defined as 2."
AscInv == 2

\* In English: "how many genesis keys delegate."
\* Literally: "NumGenesis is defined as 2."
NumGenesis == 2

\* d as numerator and denominator. Without the overlay only d = 0, which
\* is every epoch from mid-Mary on.
\* In English: "the decentralisation values the model tries."
\* Literally: "DValues is defined as: if Overlay then the set containing
\*   the tuple of 0 and 1, the tuple of 1 and 3, the tuple of 1 and 2, and
\*   the tuple of 1 and 1; else the set containing the tuple of 0 and 1."
DValues == IF Overlay THEN {<<0, 1>>, <<1, 3>>, <<1, 2>>, <<1, 1>>} ELSE {<<0, 1>>}

\* In English: "the slot offsets in the epoch the model tries (only 0
\* without the overlay)."
\* Literally: "SlotOffsets is defined as: if Overlay then 0 through
\*   EpochLen minus 1, else the set containing 0."
SlotOffsets == IF Overlay THEN 0..(EpochLen - 1) ELSE {0}

\* In English: "the ceiling of n / m, for n at least 0 and m at least 1."
\* Literally: "Ceil of n and m is defined as (n plus m minus 1)
\*   integer-divided by m."
Ceil(n, m) == (n + m - 1) \div m

\* [T8]: ceiling(s * d), with d = p / q. The FloorPosition mutation's
\* gOuroboros rounds down instead.
\* In English: "the overlay position of slot offset s under d, rounding
\* up, or down when floor is TRUE."
\* Literally: "Position of s, d and floor is defined as: if floor then
\*   (s times element 1 of d) integer-divided by element 2 of d, else Ceil
\*   of s times element 1 of d, and element 2 of d."
Position(s, d, floor) ==
    IF floor THEN (s * d[1]) \div d[2] ELSE Ceil(s * d[1], d[2])

\* In English: "slot offset s is in the overlay schedule under d."
\* Literally: "IsOverlaySlot of s, d and floor is defined as: Position of
\*   s, d and floor is less than Position of s plus 1, d and floor."
IsOverlaySlot(s, d, floor) == Position(s, d, floor) < Position(s + 1, d, floor)

\* [T7]: the kind of slot s: plain Praos outside the overlay, else active
\* when its position is a multiple of ascInv.
\* In English: "the kind of slot offset s under d."
\* Literally: "ClassifyBy of s, d and floor is defined as: if
\*   IsOverlaySlot of s, d and floor is not true then "Praos", else if
\*   Position of s, d and floor modulo AscInv equals 0 then "OBFT", else
\*   "NonActive"."
ClassifyBy(s, d, floor) ==
    IF ~IsOverlaySlot(s, d, floor) THEN "Praos"
    ELSE IF Position(s, d, floor) % AscInv = 0 THEN "OBFT" ELSE "NonActive"

\* In English: "the reference's kind for slot offset s under d."
\* Literally: "Classify of s and d is defined as ClassifyBy of s, d and
\*   FALSE."
Classify(s, d) == ClassifyBy(s, d, FALSE)

\* [T7]: which genesis key an active overlay slot belongs to, by index in
\* key order.
\* In English: "the index of the genesis key scheduled for slot offset s."
\* Literally: "GenesisIndex of s and d is defined as (Position of s, d and
\*   FALSE integer-divided by AscInv) modulo NumGenesis."
GenesisIndex(s, d) == (Position(s, d, FALSE) \div AscInv) % NumGenesis

\* The kind of slot gOuroboros works with: main has no schedule, so every
\* slot is a plain one; the fix computes the reference's, unless the
\* FloorPosition mutation rounds the position down.
\* In English: "the kind gOuroboros gives slot offset s under d."
\* Literally: "GoClassify of s and d is defined as: if GoInputs equals
\*   "Main" then "Praos", else ClassifyBy of s, d and (Mutation equals
\*   "FloorPosition")."
GoClassify(s, d) ==
    IF GoInputs = "Main" THEN "Praos"
    ELSE ClassifyBy(s, d, Mutation = "FloorPosition")

(***************************************************************************)
(* The reference's program: one record per check, in order. onFail says   *)
(* what a failure does: Halt ends validation, SkipGroup skips the rest of *)
(* its group, Continue goes on.                                            *)
(***************************************************************************)

\* In English: "one step of the reference's program."
\* Literally: "Chk of c, g and f is defined as the record whose field chk
\*   is c, whose field grp is g, and whose field onFail is f."
Chk(c, g, f) == [chk |-> c, grp |-> g, onFail |-> f]

\* [H1][H3][H4]: block number, slot, previous hash, then the extra checks.
\* In English: "the reference's envelope checks, in order."
\* Literally: "EnvelopeProg is defined as the tuple of Chk of "BlockNo",
\*   "env" and "Halt", Chk of "Slot", "env" and "Halt", and Chk of
\*   "PrevHash", "env" and "Halt", followed by (if Extras then the tuple of
\*   Chk of "Obsolete", "env" and "Halt", Chk of "HdrSize", "env" and
\*   "Halt", and Chk of "BodySize", "env" and "Halt", else the empty
\*   tuple)."
EnvelopeProg ==
    <<Chk("BlockNo", "env", "Halt"), Chk("Slot", "env", "Halt"), Chk("PrevHash", "env", "Halt")>>
    \o (IF Extras
        THEN <<Chk("Obsolete", "env", "Halt"), Chk("HdrSize", "env", "Halt"), Chk("BodySize", "env", "Halt")>>
        ELSE <<>>)

\* [P1][P2][P3]: Praos, KES side then VRF side, each stopping everything.
\* In English: "the Praos protocol checks, in order."
\* Literally: "PraosProg is defined as the tuple of Chk of c, "prot" and
\*   "Halt" for c being, in order, "KESBefore", "KESAfter", "OCertSig",
\*   "KESSig", "NoCounter", "CounterTooSmall", "CounterOverInc",
\*   "VRFUnknown", "VRFWrongKey", "VRFBadProof" and "LeaderTooBig"."
PraosProg ==
    <<Chk("KESBefore", "prot", "Halt"), Chk("KESAfter", "prot", "Halt"),
      Chk("OCertSig", "prot", "Halt"), Chk("KESSig", "prot", "Halt"),
      Chk("NoCounter", "prot", "Halt"), Chk("CounterTooSmall", "prot", "Halt"),
      Chk("CounterOverInc", "prot", "Halt"),
      Chk("VRFUnknown", "prot", "Halt"), Chk("VRFWrongKey", "prot", "Halt"),
      Chk("VRFBadProof", "prot", "Halt"), Chk("LeaderTooBig", "prot", "Halt")>>

\* [T1][T2][T5][T6][F1]: the VRF group of TPraos, by slot kind. A
\* non-active overlay slot fails outright; an active overlay slot checks
\* the genesis delegate's cold key (collected, the rule goes on), then its
\* VRF key and both VRF proofs, but no stake and no leader value.
\* In English: "the TPraos VRF checks for a slot of this kind."
\* Literally: "TPraosVrfProg of kind is defined as: in the case kind equals
\*   "NonActive", the tuple of Chk of "NotActiveSlot", "vrf" and
\*   "SkipGroup"; in the case kind equals "OBFT", the tuple of Chk of
\*   "GenColdKey", "obft" and "Continue", Chk of "GenVRFKey", "vrf" and
\*   "SkipGroup", Chk of "VRFBadNonce", "vrf" and "SkipGroup", and Chk of
\*   "VRFBadProof", "vrf" and "SkipGroup"; in every other case, the tuple
\*   of Chk of c, "vrf" and "SkipGroup" for c being "VRFUnknown",
\*   "VRFWrongKey", "VRFBadNonce", "VRFBadProof" and "LeaderTooBig"."
TPraosVrfProg(kind) ==
    CASE kind = "NonActive" -> <<Chk("NotActiveSlot", "vrf", "SkipGroup")>>
      [] kind = "OBFT" ->
            <<Chk("GenColdKey", "obft", "Continue"),
              Chk("GenVRFKey", "vrf", "SkipGroup"), Chk("VRFBadNonce", "vrf", "SkipGroup"),
              Chk("VRFBadProof", "vrf", "SkipGroup")>>
      [] OTHER ->
            <<Chk("VRFUnknown", "vrf", "SkipGroup"), Chk("VRFWrongKey", "vrf", "SkipGroup"),
              Chk("VRFBadNonce", "vrf", "SkipGroup"), Chk("VRFBadProof", "vrf", "SkipGroup"),
              Chk("LeaderTooBig", "vrf", "SkipGroup")>>

\* [T3]: the OCERT rule; every failure is collected.
\* In English: "the TPraos OCERT checks, in order."
\* Literally: "OCertProg is defined as the tuple of Chk of c, "ocert" and
\*   "Continue" for c being, in order, "KESBefore", "KESAfter", "OCertSig",
\*   "KESSig", "NoCounter" and "CounterTooSmall"."
OCertProg ==
    <<Chk("KESBefore", "ocert", "Continue"), Chk("KESAfter", "ocert", "Continue"),
      Chk("OCertSig", "ocert", "Continue"), Chk("KESSig", "ocert", "Continue"),
      Chk("NoCounter", "ocert", "Continue"), Chk("CounterTooSmall", "ocert", "Continue")>>

\* [H2]: the envelope, then the protocol.
\* In English: "every reference check for a slot of this kind, in order."
\* Literally: "RefProg of kind is defined as EnvelopeProg followed by: if
\*   Mode equals "Praos" then PraosProg, else TPraosVrfProg of kind followed
\*   by OCertProg."
RefProg(kind) ==
    EnvelopeProg \o (IF Mode = "Praos" THEN PraosProg ELSE TPraosVrfProg(kind) \o OCertProg)

\* A reference check fails when the header has its defect; the overlay's
\* non-active slot check fails whenever the slot is non-active.
\* In English: "reference check c fails for this header."
\* Literally: "RefFails of c, D and kind is defined as: if c equals
\*   "NotActiveSlot" then kind equals "NonActive", else c is a member of D."
RefFails(c, D, kind) == IF c = "NotActiveSlot" THEN kind = "NonActive" ELSE c \in D

(***************************************************************************)
(* gOuroboros' program: its check functions, in ValidateHeader's order.   *)
(* "inputs", the extra envelope checks, "overlay" and "gencold" exist     *)
(* only on the fix branch (GoInputs = "Fixed"); on main they report       *)
(* nothing.                                                                *)
(***************************************************************************)

\* ValidateHeader today: the inputs, slot, block number, previous hash,
\* the extra envelope checks, the overlay slot kind, the genesis cold key,
\* VRF proof, leadership, nonce VRF (TPraos), KES period, KES signature,
\* certificate signature, counter, VRF key registration.
\* In English: "ValidateHeader's checks on main, in order."
\* Literally: "GoTodayProg is defined as the tuple of "inputs", "slot",
\*   "blockno", "prevhash", "obsolete", "hdrsize", "bodysize", "overlay",
\*   "gencold", "vrfproof", "leadership", "noncevrf", "kesperiod", "kessig",
\*   "opcertsig", "counter" and "vrfreg"."
GoTodayProg ==
    <<"inputs", "slot", "blockno", "prevhash", "obsolete", "hdrsize", "bodysize",
      "overlay", "gencold", "vrfproof", "leadership", "noncevrf",
      "kesperiod", "kessig", "opcertsig", "counter", "vrfreg">>

\* The order fix branch: the reference's order, by mode.
\* In English: "ValidateHeader's checks on the order fix branch, in order."
\* Literally: "GoFixedProg is defined as the tuple of "inputs", "blockno",
\*   "slot", "prevhash", "obsolete", "hdrsize" and "bodysize", followed by:
\*   if Mode equals "Praos" then the tuple of "kesperiod", "opcertsig",
\*   "kessig", "counter", "vrfreg", "vrfproof" and "leadership"; else the
\*   tuple of "overlay", "gencold", "vrfreg", "noncevrf", "vrfproof",
\*   "leadership", "kesperiod", "opcertsig", "kessig" and "counter"."
GoFixedProg ==
    <<"inputs", "blockno", "slot", "prevhash", "obsolete", "hdrsize", "bodysize">>
    \o (IF Mode = "Praos"
        THEN <<"kesperiod", "opcertsig", "kessig", "counter", "vrfreg", "vrfproof",
               "leadership">>
        ELSE <<"overlay", "gencold", "vrfreg", "noncevrf", "vrfproof", "leadership",
               "kesperiod", "opcertsig", "kessig", "counter">>)

\* In English: "the gOuroboros program being checked."
\* Literally: "GoProg is defined as: if GoOrder equals "Today" then
\*   GoTodayProg, else GoFixedProg."
GoProg == IF GoOrder = "Today" THEN GoTodayProg ELSE GoFixedProg

\* What each gOuroboros check reports, as reference error names.
\* On main there is no overlay schedule: a genesis delegate's header in an
\* active overlay slot has no stake and no registered pool VRF key, so the
\* caller can only pass zero stake and no key, which reads as an unknown
\* pool; a non-active overlay slot is checked as a plain one.
\* On the fix (GoInputs = "Fixed"): a missing input is the only error; the
\* extra envelope checks run; a non-active slot reports NotActiveSlot and
\* skips the VRF checks; an active overlay slot checks the genesis
\* delegate's cold key and VRF key and both proofs, with no leadership.
\* Today, the KES signature check repeats the "in the future" error of the
\* KES period check; the fix verifies at evolution 0 instead, as [T3] does.
\* Leadership is skipped after a failed VRF proof, and on the order fix
\* branch also after a failed VRF key check [P3][T2].
\* In English: "the errors gOuroboros check c reports for defects D in a
\* slot the reference calls kind and gOuroboros calls gk, given the checks
\* that already failed."
\* Literally: "GoEmits of c, D, kind, gk and failed is defined as: letting
\*   fixedIn be (GoInputs equals "Fixed"), unknown be ("VRFUnknown" is a
\*   member of D, or kind equals "OBFT" and fixedIn is not true), skipVrf be
\*   (gk equals "NonActive"), obft be (gk equals "OBFT"), and one of e be
\*   the tuple of e if e is a member of D, else the empty tuple: in the case
\*   c equals "inputs", the tuple of "MissingInput" if fixedIn and Inputs
\*   equals "Missing", else the empty tuple; in the case c is "slot",
\*   "blockno" or "prevhash", one of the matching defect; in the case c is
\*   "obsolete", "hdrsize" or "bodysize", one of the matching defect if
\*   fixedIn, else the empty tuple; in the case c equals "overlay", the
\*   tuple of "NotActiveSlot" if skipVrf, else the empty tuple; in the case
\*   c equals "gencold", one of "GenColdKey" if obft and Mutation does not
\*   equal "SkipGenCold", else the empty tuple; in the case c equals
\*   "vrfproof", the empty tuple if skipVrf, else one of "VRFBadProof"; in
\*   the case c equals "leadership", the empty tuple if skipVrf or obft or
\*   "vrfproof" is a member of failed or (GoOrder equals "Fixed" and
\*   "vrfreg" is a member of failed), else the tuple of "VRFUnknown" if
\*   unknown, else one of "LeaderTooBig"; in the case c equals "noncevrf",
\*   one of "VRFBadNonce" if Mode equals "TPraos" and skipVrf is not true,
\*   else the empty tuple; in the case c equals "kesperiod", one of
\*   "KESBefore" followed by one of "KESAfter"; in the case c equals
\*   "kessig", the tuple of "KESBefore" if GoOrder equals "Today" and it is
\*   a member of D, else the tuple of "KESSig" if it is a member of D or
\*   (Mutation equals "SpuriousKES" and "KESAfter" is a member of D), else
\*   the empty tuple; in the case c equals "opcertsig", one of "OCertSig";
\*   in the case c equals "counter", the empty tuple if Mutation equals
\*   "SkipCounter", else one of "NoCounter" followed by one of
\*   "CounterTooSmall" followed by (one of "CounterOverInc" if Mode equals
\*   "Praos"); in the case c equals "vrfreg", the empty tuple if skipVrf,
\*   else one of "GenVRFKey" if obft, else the tuple of "VRFUnknown" if
\*   unknown, else one of "VRFWrongKey"; in every other case, the empty
\*   tuple."
GoEmits(c, D, kind, gk, failed) ==
    LET fixedIn == GoInputs = "Fixed"
        unknown == "VRFUnknown" \in D \/ (kind = "OBFT" /\ ~fixedIn)
        skipVrf == gk = "NonActive"
        obft    == gk = "OBFT"
        one(e)  == IF e \in D THEN <<e>> ELSE <<>>
    IN
    CASE c = "inputs"   -> IF fixedIn /\ Inputs = "Missing" THEN <<"MissingInput">> ELSE <<>>
      [] c = "slot"     -> one("Slot")
      [] c = "blockno"  -> one("BlockNo")
      [] c = "prevhash" -> one("PrevHash")
      [] c = "obsolete" -> IF fixedIn THEN one("Obsolete") ELSE <<>>
      [] c = "hdrsize"  -> IF fixedIn THEN one("HdrSize") ELSE <<>>
      [] c = "bodysize" -> IF fixedIn THEN one("BodySize") ELSE <<>>
      [] c = "overlay"  -> IF skipVrf THEN <<"NotActiveSlot">> ELSE <<>>
      [] c = "gencold"  ->
            IF obft /\ Mutation /= "SkipGenCold" THEN one("GenColdKey") ELSE <<>>
      [] c = "vrfproof" -> IF skipVrf THEN <<>> ELSE one("VRFBadProof")
      [] c = "leadership" ->
            IF skipVrf \/ obft \/ "vrfproof" \in failed
               \/ (GoOrder = "Fixed" /\ "vrfreg" \in failed)
            THEN <<>>
            ELSE IF unknown THEN <<"VRFUnknown">> ELSE one("LeaderTooBig")
      [] c = "noncevrf" ->
            IF Mode = "TPraos" /\ ~skipVrf THEN one("VRFBadNonce") ELSE <<>>
      [] c = "kesperiod" -> one("KESBefore") \o one("KESAfter")
      [] c = "kessig" ->
            IF GoOrder = "Today" /\ "KESBefore" \in D THEN <<"KESBefore">>
            ELSE IF "KESSig" \in D \/ (Mutation = "SpuriousKES" /\ "KESAfter" \in D)
                 THEN <<"KESSig">> ELSE <<>>
      [] c = "opcertsig" -> one("OCertSig")
      [] c = "counter" ->
            IF Mutation = "SkipCounter" THEN <<>>
            ELSE one("NoCounter") \o one("CounterTooSmall")
                 \o (IF Mode = "Praos" THEN one("CounterOverInc") ELSE <<>>)
      [] c = "vrfreg" ->
            IF skipVrf THEN <<>>
            ELSE IF obft THEN one("GenVRFKey")
            ELSE IF unknown THEN <<"VRFUnknown">> ELSE one("VRFWrongKey")
      [] OTHER -> <<>>

(***************************************************************************)
(* The run.                                                                *)
(***************************************************************************)

VARIABLES
    off,      \* the header's slot offset in its epoch
    dval,     \* the epoch's decentralisation parameter d, as <<numerator, denominator>>
    D,        \* the header's defects
    kind,     \* the slot's kind in the reference's overlay schedule
    phase,    \* "ref", then "go", then "done"
    pc,       \* the index of the next check in the running program
    skip,     \* the reference group being skipped, or "none"
    refErrs,  \* the errors the reference reported, in order
    goErrs,   \* the errors gOuroboros reported, in order
    goFailed  \* the gOuroboros checks that reported an error

\* In English: "every variable, for stuttering steps."
\* Literally: "vars is defined as the tuple of off, dval, D, kind, phase,
\*   pc, skip, refErrs, goErrs and goFailed."
vars == <<off, dval, D, kind, phase, pc, skip, refErrs, goErrs, goFailed>>

\* In English: "the parts of the header that never change."
\* Literally: "hdr is defined as the tuple of off, dval, D and kind."
hdr == <<off, dval, D, kind>>

\* In English: "the errors in sequence s, as a set."
\* Literally: "Range of s is defined as the set of s of i, for every i that
\*   is a member of the domain of s."
Range(s) == {s[i] : i \in DOMAIN s}

\* In English: "any possible header: any slot of the epoch, any d, and up
\* to MaxDefects defects consistent with the slot's kind; nothing has run
\* yet."
\* Literally: "Init is defined as: off is a member of SlotOffsets, and dval
\*   is a member of DValues, and kind equals Classify of off and dval, and
\*   D is a member of the set of every S in the set of subsets of Defects
\*   such that the number of members of S is at most MaxDefects and
\*   Consistent of S and kind, and phase equals "ref", and pc equals 1,
\*   and skip equals "none", and refErrs and goErrs equal the empty tuple,
\*   and goFailed equals the empty set."
Init ==
    /\ off \in SlotOffsets
    /\ dval \in DValues
    /\ kind = Classify(off, dval)
    /\ D \in {S \in SUBSET Defects : Cardinality(S) <= MaxDefects /\ Consistent(S, kind)}
    /\ phase = "ref"
    /\ pc = 1
    /\ skip = "none"
    /\ refErrs = <<>>
    /\ goErrs = <<>>
    /\ goFailed = {}

\* One reference check. A check in a skipped group is passed over; a
\* failure is reported, then halts, skips the rest of its group, or goes
\* on.
\* In English: "run the next reference check."
\* Literally: "RefStep is defined as: phase equals "ref", and pc is at most
\*   the length of RefProg of kind, and letting st be element pc of RefProg
\*   of kind: if skip equals st's grp or RefFails of st's chk, D and kind is
\*   not true, then pc in the next state equals pc plus 1 and everything
\*   else is unchanged; else refErrs in the next state equals refErrs with
\*   st's chk appended, and in the case st's onFail equals "Halt", phase in
\*   the next state equals "go" and pc in the next state equals 1; in the
\*   case "SkipGroup", skip in the next state equals st's grp and pc in the
\*   next state equals pc plus 1; in every other case pc in the next state
\*   equals pc plus 1; and hdr, goErrs and goFailed are unchanged."
RefStep ==
    /\ phase = "ref"
    /\ pc <= Len(RefProg(kind))
    /\ LET st == RefProg(kind)[pc]
       IN  IF skip = st.grp \/ ~RefFails(st.chk, D, kind)
           THEN /\ pc' = pc + 1
                /\ UNCHANGED <<hdr, phase, skip, refErrs, goErrs, goFailed>>
           ELSE /\ refErrs' = Append(refErrs, st.chk)
                /\ CASE st.onFail = "Halt" ->
                          phase' = "go" /\ pc' = 1 /\ UNCHANGED skip
                     [] st.onFail = "SkipGroup" ->
                          skip' = st.grp /\ pc' = pc + 1 /\ UNCHANGED phase
                     [] OTHER ->
                          pc' = pc + 1 /\ UNCHANGED <<phase, skip>>
                /\ UNCHANGED <<hdr, goErrs, goFailed>>

\* In English: "the reference has run out of checks; start gOuroboros."
\* Literally: "RefEnd is defined as: phase equals "ref", and pc is more
\*   than the length of RefProg of kind, and phase in the next state equals
\*   "go", and pc in the next state equals 1, and the rest is unchanged."
RefEnd ==
    /\ phase = "ref"
    /\ pc > Len(RefProg(kind))
    /\ phase' = "go"
    /\ pc' = 1
    /\ UNCHANGED <<hdr, skip, refErrs, goErrs, goFailed>>

\* One gOuroboros check: it always runs, and appends what it reports. A
\* missing input ends the run at once: ValidateHeader returns only that
\* error.
\* In English: "run the next gOuroboros check."
\* Literally: "GoStep is defined as: phase equals "go", and pc is at most
\*   the length of GoProg, and letting c be element pc of GoProg and out be
\*   GoEmits of c, D, kind, GoClassify of off and dval, and goFailed:
\*   goErrs in the next state equals goErrs followed by out, and goFailed in
\*   the next state equals (if out does not equal the empty tuple then the
\*   union of goFailed and the set containing c, else goFailed), and pc in
\*   the next state equals (if c equals "inputs" and out does not equal the
\*   empty tuple then the length of GoProg plus 1, else pc plus 1), and the
\*   rest is unchanged."
GoStep ==
    /\ phase = "go"
    /\ pc <= Len(GoProg)
    /\ LET c   == GoProg[pc]
           out == GoEmits(c, D, kind, GoClassify(off, dval), goFailed)
       IN  /\ goErrs' = goErrs \o out
           /\ goFailed' = IF out /= <<>> THEN goFailed \cup {c} ELSE goFailed
           /\ pc' = IF c = "inputs" /\ out /= <<>> THEN Len(GoProg) + 1 ELSE pc + 1
           /\ UNCHANGED <<hdr, phase, skip, refErrs>>

\* In English: "gOuroboros has run out of checks."
\* Literally: "GoEnd is defined as: phase equals "go", and pc is more than
\*   the length of GoProg, and phase in the next state equals "done", and
\*   the rest is unchanged."
GoEnd ==
    /\ phase = "go"
    /\ pc > Len(GoProg)
    /\ phase' = "done"
    /\ UNCHANGED <<hdr, pc, skip, refErrs, goErrs, goFailed>>

\* In English: "both have finished; nothing more happens."
\* Literally: "Finished is defined as: phase equals "done", and vars is
\*   unchanged."
Finished == phase = "done" /\ UNCHANGED vars

\* In English: "take the next step of whichever validator is running."
\* Literally: "Next is defined as: RefStep or RefEnd or GoStep or GoEnd or
\*   Finished."
Next == RefStep \/ RefEnd \/ GoStep \/ GoEnd \/ Finished

\* In English: "start in Init and take Next steps."
\* Literally: "Spec is defined as: Init and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants, read when both validators have finished. The verdict       *)
(* invariants compare a header against the reference only when the caller *)
(* supplied every input; MissingInputReported covers the other case.      *)
(***************************************************************************)

\* In English: "both validators have finished."
\* Literally: "IsDone is defined as: phase equals "done"."
IsDone == phase = "done"

\* In English: "both have finished, and the caller gave every input."
\* Literally: "Judged is defined as: IsDone and Inputs equals "Full"."
Judged == IsDone /\ Inputs = "Full"

\* In English: "gOuroboros accepts a header exactly when the reference
\* does."
\* Literally: "VerdictsAgree is defined as: if Judged, then (goErrs equals
\*   the empty tuple if and only if refErrs equals the empty tuple)."
VerdictsAgree == Judged => (goErrs = <<>> <=> refErrs = <<>>)

\* In English: "every error the reference reports, gOuroboros reports too."
\* Literally: "GoReportsEveryRefError is defined as: if Judged, then Range
\*   of refErrs is a subset of Range of goErrs."
GoReportsEveryRefError == Judged => Range(refErrs) \subseteq Range(goErrs)

\* In English: "on a slot gOuroboros can classify (an ordinary slot, or
\* any slot on the fix), gOuroboros reports only defects the header has,
\* or a non-active slot."
\* Literally: "GoSound is defined as: if Judged and (kind equals "Praos"
\*   or GoInputs equals "Fixed"), then Range of goErrs is a subset of the
\*   union of D and the set containing "NotActiveSlot"."
GoSound ==
    Judged /\ (kind = "Praos" \/ GoInputs = "Fixed")
        => Range(goErrs) \subseteq D \cup {"NotActiveSlot"}

\* In English: "gOuroboros' first error is the error the reference reports
\* first."
\* Literally: "FirstErrorAgrees is defined as: if Judged and refErrs does
\*   not equal the empty tuple, then goErrs does not equal the empty tuple
\*   and element 1 of goErrs equals element 1 of refErrs."
FirstErrorAgrees ==
    Judged /\ refErrs /= <<>> => goErrs /= <<>> /\ goErrs[1] = refErrs[1]

\* In English: "gOuroboros reports each error once."
\* Literally: "NoDuplicateErrors is defined as: if IsDone, then for all i
\*   and j in the domain of goErrs, if i does not equal j then element i of
\*   goErrs does not equal element j of goErrs."
NoDuplicateErrors ==
    IsDone => \A i, j \in DOMAIN goErrs : i /= j => goErrs[i] /= goErrs[j]

\* In English: "the reference reports only defects the header has (or the
\* non-active overlay slot)."
\* Literally: "RefSound is defined as: if IsDone, then Range of refErrs is
\*   a subset of the union of D and the set containing "NotActiveSlot"."
RefSound == IsDone => Range(refErrs) \subseteq D \cup {"NotActiveSlot"}

\* [T5][T6][F1]: one direction of the overlay. A genesis delegate's header
\* that the reference accepts in its active overlay slot, gOuroboros
\* accepts too.
\* In English: "a valid genesis-delegate header is accepted."
\* Literally: "GenesisDelegateAccepted is defined as: if Judged and kind
\*   equals "OBFT" and refErrs equals the empty tuple, then goErrs equals
\*   the empty tuple."
GenesisDelegateAccepted ==
    Judged /\ kind = "OBFT" /\ refErrs = <<>> => goErrs = <<>>

\* [T5][F1]: the other direction. No header is valid in a non-active
\* overlay slot, so gOuroboros rejects every one, and says why.
\* In English: "a header in a non-active overlay slot is rejected as one."
\* Literally: "NonActiveRejected is defined as: if Judged and kind equals
\*   "NonActive", then "NotActiveSlot" is a member of Range of goErrs."
NonActiveRejected ==
    Judged /\ kind = "NonActive" => "NotActiveSlot" \in Range(goErrs)

\* The user's decision: a missing required input is a caller error, not a
\* verdict on the header; it is the one error returned.
\* In English: "when the caller leaves an input out, gOuroboros reports
\* that and nothing else."
\* Literally: "MissingInputReported is defined as: if IsDone and Inputs
\*   equals "Missing", then goErrs equals the tuple of "MissingInput"."
MissingInputReported ==
    IsDone /\ Inputs = "Missing" => goErrs = <<"MissingInput">>

\* [T8]: with d = 0 the overlay is empty: plain Praos.
\* In English: "with d = 0 every slot is an ordinary slot."
\* Literally: "DZeroIsPraos is defined as: if element 1 of dval equals 0,
\*   then kind equals "Praos"."
DZeroIsPraos == dval[1] = 0 => kind = "Praos"

\* In English: "with d = 1 every slot is an overlay slot."
\* Literally: "FullDAllOverlay is defined as: if element 1 of dval equals
\*   element 2 of dval, then kind does not equal "Praos"."
FullDAllOverlay == dval[1] = dval[2] => kind /= "Praos"

\* [T8]: the overlay steps telescope, so an epoch of E slots has exactly
\* ceiling(E * d) overlay slots.
\* In English: "the epoch has ceiling(EpochLen * d) overlay slots."
\* Literally: "OverlayCount is defined as: the number of members of the
\*   set of every s in 0 through EpochLen minus 1 such that IsOverlaySlot
\*   of s, dval and FALSE equals Ceil of EpochLen times element 1 of dval,
\*   and element 2 of dval."
OverlayCount ==
    Cardinality({s \in 0..(EpochLen - 1) : IsOverlaySlot(s, dval, FALSE)})
        = Ceil(EpochLen * dval[1], dval[2])

\* [T7]: with d = 1 the round robin gives every genesis key a slot.
\* In English: "with d = 1 every genesis key has an active slot."
\* Literally: "EveryGenesisKeyScheduled is defined as: if element 1 of
\*   dval equals element 2 of dval, then for all g in 0 through NumGenesis
\*   minus 1, there exists an s in 0 through EpochLen minus 1 such that
\*   Classify of s and dval equals "OBFT" and GenesisIndex of s and dval
\*   equals g."
EveryGenesisKeyScheduled ==
    dval[1] = dval[2] =>
        \A g \in 0..(NumGenesis - 1) :
            \E s \in 0..(EpochLen - 1) :
                Classify(s, dval) = "OBFT" /\ GenesisIndex(s, dval) = g

(***************************************************************************)
(* Reachability probes: each must be violated in its *Bug.cfg.            *)
(***************************************************************************)

\* Praos reports the KES error although the VRF proof is also bad.
\* In English: "Praos never reports a KES error while the VRF proof is also bad (expected to fail)."
\* Literally: "ProbeKESBeforeVRF is defined as: it is not true that
\*   (IsDone and refErrs equals the tuple of "KESBefore" and "VRFBadProof"
\*   is a member of D)."
ProbeKESBeforeVRF == ~(IsDone /\ refErrs = <<"KESBefore">> /\ "VRFBadProof" \in D)

\* The TPraos reference reports more than one error.
\* In English: "the reference never reports two errors (expected to fail)."
\* Literally: "ProbeAccumulates is defined as: it is not true that (IsDone
\*   and the length of refErrs is at least 2)."
ProbeAccumulates == ~(IsDone /\ Len(refErrs) >= 2)

\* A failed envelope hides a protocol defect from the reference.
\* In English: "a failed block number never hides another defect (expected to fail)."
\* Literally: "ProbeEnvelopeHalts is defined as: it is not true that
\*   (IsDone and refErrs equals the tuple of "BlockNo" and the number of
\*   members of D is at least 2)."
ProbeEnvelopeHalts == ~(IsDone /\ refErrs = <<"BlockNo">> /\ Cardinality(D) >= 2)

\* The reference accepts a genesis delegate's header.
\* In English: "the reference never accepts a header in an active overlay
\* slot (expected to fail)."
\* Literally: "ProbeOBFTAccepted is defined as: it is not true that
\*   (IsDone and kind equals "OBFT" and refErrs equals the empty tuple)."
ProbeOBFTAccepted == ~(IsDone /\ kind = "OBFT" /\ refErrs = <<>>)

\* A slot is non-active.
\* In English: "no slot is a non-active overlay slot (expected to fail)."
\* Literally: "ProbeNonActive is defined as: kind does not equal
\*   "NonActive"."
ProbeNonActive == kind /= "NonActive"

=============================================================================
