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
(* gOuroboros: consensus/validate.go, ValidateHeader and its checks.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Mode,       \* "Praos" (Babbage on) or "TPraos" (Shelley to Alonzo)
    GoOrder,    \* "Today": gOuroboros as it is; "Fixed": the order of the fix branch
    MaxDefects, \* the most defects one header carries (keeps the model finite)
    Extras,     \* TRUE: headers may also fail the reference's extra envelope checks
    Overlay,    \* TRUE: TPraos slots may be overlay slots (decentralisation d > 0)
    Mutation    \* "none", or one deliberate change to the gOuroboros side

ASSUME Mode \in {"Praos", "TPraos"}
ASSUME GoOrder \in {"Today", "Fixed"}
ASSUME Overlay => Mode = "TPraos"
ASSUME Mutation \in {"none", "SkipCounter", "SpuriousKES"}

(***************************************************************************)
(* Defects. Each is named after the reference error it causes.            *)
(***************************************************************************)

\* In English: "the reference's extra envelope defects."
\* Literally: "EnvelopeExtras is defined as the set containing "Obsolete",
\*   "HdrSize" and "BodySize"."
EnvelopeExtras == {"Obsolete", "HdrSize", "BodySize"}

\* In English: "every defect a header of this mode can carry."
\* Literally: "Defects is defined as the union of the set containing
\*   "BlockNo", "Slot", "PrevHash", "KESBefore", "KESAfter", "OCertSig",
\*   "KESSig", "NoCounter", "CounterTooSmall", "VRFUnknown", "VRFWrongKey",
\*   "VRFBadProof" and "LeaderTooBig"; the set containing
\*   "CounterOverInc" if Mode equals "Praos", else the set containing
\*   "VRFBadNonce"; and EnvelopeExtras if Extras, else the empty set."
Defects ==
    {"BlockNo", "Slot", "PrevHash",
     "KESBefore", "KESAfter", "OCertSig", "KESSig",
     "NoCounter", "CounterTooSmall",
     "VRFUnknown", "VRFWrongKey", "VRFBadProof", "LeaderTooBig"}
    \cup (IF Mode = "Praos" THEN {"CounterOverInc"} ELSE {"VRFBadNonce"})
    \cup (IF Extras THEN EnvelopeExtras ELSE {})

\* Defects that cannot occur together: a certificate is not both before
\* its start and after its end; a counter fails one way; a pool unknown to
\* the stake distribution has no registered VRF key and no stake.
\* In English: "D describes a header that could exist."
\* Literally: "Consistent of D is defined as: the set containing
\*   "KESBefore" and "KESAfter" is not a subset of D, and the number of
\*   members of the intersection of D and the set containing "NoCounter",
\*   "CounterTooSmall" and "CounterOverInc" is at most 1, and if "VRFUnknown"
\*   is a member of D then the intersection of D and the set containing
\*   "VRFWrongKey" and "LeaderTooBig" is empty."
Consistent(D) ==
    /\ ~({"KESBefore", "KESAfter"} \subseteq D)
    /\ Cardinality(D \cap {"NoCounter", "CounterTooSmall", "CounterOverInc"}) <= 1
    /\ "VRFUnknown" \in D => D \cap {"VRFWrongKey", "LeaderTooBig"} = {}

\* Overlay slot kinds [T1]: an ordinary Praos slot, an active overlay slot
\* (a genesis delegate's, no stake check), a non-active overlay slot (no
\* block may be made in it).
\* In English: "the kinds of slot a header can be in."
\* Literally: "SlotKinds is defined as: if Overlay then the set containing
\*   "Praos", "OBFT" and "NonActive", else the set containing "Praos"."
SlotKinds == IF Overlay THEN {"Praos", "OBFT", "NonActive"} ELSE {"Praos"}

(***************************************************************************)
(* The reference's program: one record per check, in order. onFail says   *)
(* what a failure does: Halt ends validation, SkipGroup skips the rest of *)
(* its group, Continue goes on.                                            *)
(***************************************************************************)

\* In English: "one step of the reference's program."
\* Literally: "Chk of c, g and f is defined as the record whose field chk
\*   is c, whose field grp is g, and whose field onFail is f."
Chk(c, g, f) == [chk |-> c, grp |-> g, onFail |-> f]

\* [H1][H3]: block number, slot, previous hash, then the extra checks.
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

\* [T1][T2]: the VRF group of TPraos, by slot kind. A non-active overlay
\* slot fails outright; an active overlay slot checks the genesis
\* delegate's VRF key and both VRF proofs, but no stake.
\* In English: "the TPraos VRF checks for a slot of this kind."
\* Literally: "TPraosVrfProg of kind is defined as: in the case kind equals
\*   "NonActive", the tuple of Chk of "NotActiveSlot", "vrf" and
\*   "SkipGroup"; in the case kind equals "OBFT", the tuple of Chk of c,
\*   "vrf" and "SkipGroup" for c being "VRFWrongKey", "VRFBadNonce" and
\*   "VRFBadProof"; in every other case, the same for c being "VRFUnknown",
\*   "VRFWrongKey", "VRFBadNonce", "VRFBadProof" and "LeaderTooBig"."
TPraosVrfProg(kind) ==
    CASE kind = "NonActive" -> <<Chk("NotActiveSlot", "vrf", "SkipGroup")>>
      [] kind = "OBFT" ->
            <<Chk("VRFWrongKey", "vrf", "SkipGroup"), Chk("VRFBadNonce", "vrf", "SkipGroup"),
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
(***************************************************************************)

\* ValidateHeader today: slot, block number, previous hash, VRF proof,
\* leadership, nonce VRF (TPraos), KES period, KES signature, certificate
\* signature, counter, VRF key registration.
\* In English: "ValidateHeader's checks on main, in order."
\* Literally: "GoTodayProg is defined as the tuple of "slot", "blockno",
\*   "prevhash", "vrfproof", "leadership", "noncevrf", "kesperiod",
\*   "kessig", "opcertsig", "counter" and "vrfreg"."
GoTodayProg ==
    <<"slot", "blockno", "prevhash", "vrfproof", "leadership", "noncevrf",
      "kesperiod", "kessig", "opcertsig", "counter", "vrfreg">>

\* The fix branch: the reference's order, by mode.
\* In English: "ValidateHeader's checks on the fix branch, in order."
\* Literally: "GoFixedProg is defined as: if Mode equals "Praos" then the
\*   tuple of "blockno", "slot", "prevhash", "kesperiod", "opcertsig",
\*   "kessig", "counter", "vrfreg", "vrfproof" and "leadership"; else the
\*   tuple of "blockno", "slot", "prevhash", "vrfreg", "noncevrf",
\*   "vrfproof", "leadership", "kesperiod", "opcertsig", "kessig" and
\*   "counter"."
GoFixedProg ==
    IF Mode = "Praos"
    THEN <<"blockno", "slot", "prevhash", "kesperiod", "opcertsig", "kessig",
           "counter", "vrfreg", "vrfproof", "leadership">>
    ELSE <<"blockno", "slot", "prevhash", "vrfreg", "noncevrf", "vrfproof",
           "leadership", "kesperiod", "opcertsig", "kessig", "counter">>

\* In English: "the gOuroboros program being checked."
\* Literally: "GoProg is defined as: if GoOrder equals "Today" then
\*   GoTodayProg, else GoFixedProg."
GoProg == IF GoOrder = "Today" THEN GoTodayProg ELSE GoFixedProg

\* What each gOuroboros check reports, as reference error names. gOuroboros
\* has no overlay schedule: a genesis delegate's header in an active
\* overlay slot has no stake and no registered pool VRF key, so the caller
\* can only pass zero stake and no key, which reads as an unknown pool.
\* Today, the KES signature check repeats the "in the future" error of the
\* KES period check; the fix verifies at evolution 0 instead, as [T3] does.
\* Leadership is skipped after a failed VRF proof, and on the fix branch
\* also after a failed VRF key check [P3][T2].
\* In English: "the errors gOuroboros check c reports for defects D in a
\* slot of this kind, given the checks that already failed."
\* Literally: "GoEmits of c, D, kind and failed is defined as: letting
\*   unknown be ("VRFUnknown" is a member of D or kind equals "OBFT"): in
\*   the case c is "slot", "blockno" or "prevhash", the tuple of the
\*   matching defect if it is a member of D, else the empty tuple; in the
\*   case c equals "vrfproof", the tuple of "VRFBadProof" if it is a member
\*   of D; in the case c equals "leadership", the empty tuple if "vrfproof"
\*   is a member of failed or (GoOrder equals "Fixed" and "vrfreg" is a
\*   member of failed), else the tuple of "VRFUnknown" if unknown, else the
\*   tuple of "LeaderTooBig" if it is a member of D; in the case c equals
\*   "noncevrf", the tuple of "VRFBadNonce" if Mode equals "TPraos" and it
\*   is a member of D; in the case c equals "kesperiod", the tuple of
\*   "KESBefore" or "KESAfter", whichever is a member of D; in the case c
\*   equals "kessig", the tuple of "KESBefore" if GoOrder equals "Today"
\*   and it is a member of D, else the tuple of "KESSig" if it is a member
\*   of D or (Mutation equals "SpuriousKES" and "KESAfter" is a member of
\*   D); in the case c equals "opcertsig", the tuple of "OCertSig" if it is
\*   a member of D; in the case c equals "counter", the empty tuple if
\*   Mutation equals "SkipCounter", else the tuple of the counter defect in
\*   D ("CounterOverInc" only in Praos); in the case c equals "vrfreg", the
\*   tuple of "VRFUnknown" if unknown, else of "VRFWrongKey" if it is a
\*   member of D; in every other case, the empty tuple."
GoEmits(c, D, kind, failed) ==
    LET unknown == "VRFUnknown" \in D \/ kind = "OBFT"
        one(e)  == IF e \in D THEN <<e>> ELSE <<>>
    IN
    CASE c = "slot"     -> one("Slot")
      [] c = "blockno"  -> one("BlockNo")
      [] c = "prevhash" -> one("PrevHash")
      [] c = "vrfproof" -> one("VRFBadProof")
      [] c = "leadership" ->
            IF "vrfproof" \in failed \/ (GoOrder = "Fixed" /\ "vrfreg" \in failed)
            THEN <<>>
            ELSE IF unknown THEN <<"VRFUnknown">> ELSE one("LeaderTooBig")
      [] c = "noncevrf" -> IF Mode = "TPraos" THEN one("VRFBadNonce") ELSE <<>>
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
      [] c = "vrfreg" -> IF unknown THEN <<"VRFUnknown">> ELSE one("VRFWrongKey")
      [] OTHER -> <<>>

(***************************************************************************)
(* The run.                                                                *)
(***************************************************************************)

VARIABLES
    D,        \* the header's defects
    kind,     \* the slot's kind
    phase,    \* "ref", then "go", then "done"
    pc,       \* the index of the next check in the running program
    skip,     \* the reference group being skipped, or "none"
    refErrs,  \* the errors the reference reported, in order
    goErrs,   \* the errors gOuroboros reported, in order
    goFailed  \* the gOuroboros checks that reported an error

vars == <<D, kind, phase, pc, skip, refErrs, goErrs, goFailed>>

\* In English: "the errors in sequence s, as a set."
\* Literally: "Range of s is defined as the set of s of i, for every i that
\*   is a member of the domain of s."
Range(s) == {s[i] : i \in DOMAIN s}

\* In English: "any possible header: up to MaxDefects consistent defects,
\* in any slot kind; nothing has run yet."
\* Literally: "Init is defined as: D is a member of the set of every S in
\*   the set of subsets of Defects such that the number of members of S is
\*   at most MaxDefects and Consistent of S, and kind is a member of
\*   SlotKinds, and phase equals "ref", and pc equals 1, and skip equals
\*   "none", and refErrs, goErrs equal the empty tuple, and goFailed equals
\*   the empty set."
Init ==
    /\ D \in {S \in SUBSET Defects : Cardinality(S) <= MaxDefects /\ Consistent(S)}
    /\ kind \in SlotKinds
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
\*   equals pc plus 1."
RefStep ==
    /\ phase = "ref"
    /\ pc <= Len(RefProg(kind))
    /\ LET st == RefProg(kind)[pc]
       IN  IF skip = st.grp \/ ~RefFails(st.chk, D, kind)
           THEN /\ pc' = pc + 1
                /\ UNCHANGED <<D, kind, phase, skip, refErrs, goErrs, goFailed>>
           ELSE /\ refErrs' = Append(refErrs, st.chk)
                /\ CASE st.onFail = "Halt" ->
                          phase' = "go" /\ pc' = 1 /\ UNCHANGED skip
                     [] st.onFail = "SkipGroup" ->
                          skip' = st.grp /\ pc' = pc + 1 /\ UNCHANGED phase
                     [] OTHER ->
                          pc' = pc + 1 /\ UNCHANGED <<phase, skip>>
                /\ UNCHANGED <<D, kind, goErrs, goFailed>>

\* In English: "the reference has run out of checks; start gOuroboros."
\* Literally: "RefEnd is defined as: phase equals "ref", and pc is more
\*   than the length of RefProg of kind, and phase in the next state equals
\*   "go", and pc in the next state equals 1, and the rest is unchanged."
RefEnd ==
    /\ phase = "ref"
    /\ pc > Len(RefProg(kind))
    /\ phase' = "go"
    /\ pc' = 1
    /\ UNCHANGED <<D, kind, skip, refErrs, goErrs, goFailed>>

\* One gOuroboros check: it always runs, and appends what it reports.
\* In English: "run the next gOuroboros check."
\* Literally: "GoStep is defined as: phase equals "go", and pc is at most
\*   the length of GoProg, and letting c be element pc of GoProg and out be
\*   GoEmits of c, D, kind and goFailed: goErrs in the next state equals
\*   goErrs followed by out, and goFailed in the next state equals (if out
\*   does not equal the empty tuple then the union of goFailed and the set
\*   containing c, else goFailed), and pc in the next state equals pc plus
\*   1, and the rest is unchanged."
GoStep ==
    /\ phase = "go"
    /\ pc <= Len(GoProg)
    /\ LET c   == GoProg[pc]
           out == GoEmits(c, D, kind, goFailed)
       IN  /\ goErrs' = goErrs \o out
           /\ goFailed' = IF out /= <<>> THEN goFailed \cup {c} ELSE goFailed
           /\ pc' = pc + 1
           /\ UNCHANGED <<D, kind, phase, skip, refErrs>>

\* In English: "gOuroboros has run out of checks."
\* Literally: "GoEnd is defined as: phase equals "go", and pc is more than
\*   the length of GoProg, and phase in the next state equals "done", and
\*   the rest is unchanged."
GoEnd ==
    /\ phase = "go"
    /\ pc > Len(GoProg)
    /\ phase' = "done"
    /\ UNCHANGED <<D, kind, pc, skip, refErrs, goErrs, goFailed>>

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
(* Invariants, read when both validators have finished.                    *)
(***************************************************************************)

\* In English: "both validators have finished."
\* Literally: "IsDone is defined as: phase equals "done"."
IsDone == phase = "done"

\* In English: "gOuroboros accepts a header exactly when the reference
\* does."
\* Literally: "VerdictsAgree is defined as: if IsDone, then (goErrs equals
\*   the empty tuple if and only if refErrs equals the empty tuple)."
VerdictsAgree == IsDone => (goErrs = <<>> <=> refErrs = <<>>)

\* In English: "every error the reference reports, gOuroboros reports too."
\* Literally: "GoReportsEveryRefError is defined as: if IsDone, then Range
\*   of refErrs is a subset of Range of goErrs."
GoReportsEveryRefError == IsDone => Range(refErrs) \subseteq Range(goErrs)

\* In English: "on an ordinary slot gOuroboros reports only defects the
\* header has."
\* Literally: "GoSound is defined as: if IsDone and kind equals "Praos",
\*   then Range of goErrs is a subset of D."
GoSound == IsDone /\ kind = "Praos" => Range(goErrs) \subseteq D

\* In English: "gOuroboros' first error is the error the reference reports
\* first."
\* Literally: "FirstErrorAgrees is defined as: if IsDone and refErrs does
\*   not equal the empty tuple, then goErrs does not equal the empty tuple
\*   and element 1 of goErrs equals element 1 of refErrs."
FirstErrorAgrees ==
    IsDone /\ refErrs /= <<>> => goErrs /= <<>> /\ goErrs[1] = refErrs[1]

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

=============================================================================
