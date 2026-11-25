-------------------------- MODULE VerifyBlockIssuer --------------------------
(***************************************************************************)
(* Which blocks ledger.VerifyBlock accepts, compared with the reference's  *)
(* block application, and which checks it leaves to its caller.           *)
(*                                                                         *)
(* The reference applies a block in two parts: the header through the     *)
(* protocol (for TPraos the PRTCL rule: OVERLAY, then OCERT), then the     *)
(* body through BBODY. VerifyBlock runs the header cryptography it can     *)
(* check without chain state, the body checks, the transactions, and last *)
(* the issuer against the caller's leader distribution. The envelope       *)
(* (block number, slot, previous hash, protocol version), the stake        *)
(* threshold and the operational certificate counter are the caller's.     *)
(*                                                                         *)
(* A block here is abstract: the kind of its slot in the TPraos overlay    *)
(* schedule, who issued it, whether its VRF key is the one its issuer's   *)
(* role requires, and the set of other checks it fails. The exact order   *)
(* of the header checks is model consensus-eras' (HeaderValidation.tla);   *)
(* the body checks are model ledger-bbody's.                              *)
(*                                                                         *)
(* Sources.                                                                *)
(*   [O1] cardano-ledger 1210d37f libs/cardano-protocol-tpraos/src/        *)
(*        Cardano/Protocol/TPraos/Rules/Overlay.hs 219-282, 314-344: a     *)
(*        non-active overlay slot fails; an active one checks the genesis *)
(*        delegate's cold key and VRF key and the VRF proofs, with no     *)
(*        stake; any other slot checks the pool's VRF key, the proofs and *)
(*        the leader threshold.                                            *)
(*   [O2] .../Cardano/Ledger/Slot.hs 117-130 (isOverlaySlot).              *)
(*   [O3] ouroboros-consensus ec239d57f618 Ouroboros/Consensus/Ledger/     *)
(*        Extended.hs: applying a block validates its header (protocol    *)
(*        state) and then applies the ledger block; Shelley/Ledger/       *)
(*        Ledger.hs applyBlock runs BBODY.                                 *)
(*   [O4] cardano-ledger 1210d37f eras/conway/impl/src/Cardano/Ledger/     *)
(*        Conway/Rules/Bbody.hs: body size, hash, transactions.            *)
(* gOuroboros: ledger/verify_block.go verifyBlock (VRF proofs, opcert     *)
(* signature, KES window, KES signature, body size, body hash) and        *)
(* VerifyBlockState (limits, transactions, then the issuer).              *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Mode,      \* "TPraos" (Shelley to Alonzo, d may be positive) or "Praos"
    GoOverlay  \* TRUE: VerifyBlock checks the overlay schedule (the fix).
               \* FALSE: gOuroboros main

\* In English: "Where a slot falls: a pool slot, or (TPraos only) an
\* active or non-active overlay slot."
\* Literally: "SlotKinds is defined as: if Mode equals "TPraos" then the
\*   set containing "pool", "active" and "nonactive", else the set
\*   containing "pool"."
SlotKinds == IF Mode = "TPraos" THEN {"pool", "active", "nonactive"}
             ELSE {"pool"}

\* Who signed: a pool in the leader distribution, the genesis delegate the
\* schedule names for the slot (not a pool), or someone else.
\* Literally: "Issuers is defined as the set containing "pool", "delegate"
\*   and "stranger"."
Issuers == {"pool", "delegate", "stranger"}

\* Every other check a block can fail. "envelope" stands for block number,
\* slot, previous hash and protocol version.
\* Literally: "Checks is defined as the set containing "envelope",
\*   "vrfProof", "leaderThreshold", "kesWindow", "opcertCounter",
\*   "opcertSig", "kesSig", "bodySize", "bodyHash" and "txs"."
Checks == {"envelope", "vrfProof", "leaderThreshold", "kesWindow",
           "opcertCounter", "opcertSig", "kesSig", "bodySize", "bodyHash",
           "txs"}

\* The checks VerifyBlock leaves to its caller (its doc comment).
\* Literally: "CallerChecks is defined as the set containing "envelope",
\*   "leaderThreshold" and "opcertCounter"."
CallerChecks == {"envelope", "leaderThreshold", "opcertCounter"}

\* The order the reference reports failures in: header (envelope, OVERLAY
\* with the issuer first, then OCERT) before body [O1][O3][O4].
\* Literally: "RefOrder is defined as the sequence "envelope", "issuer",
\*   "vrfProof", "leaderThreshold", "kesWindow", "opcertCounter",
\*   "opcertSig", "kesSig", "bodySize", "bodyHash", "txs"."
RefOrder == <<"envelope", "issuer", "vrfProof", "leaderThreshold",
              "kesWindow", "opcertCounter", "opcertSig", "kesSig",
              "bodySize", "bodyHash", "txs">>

\* The order gOuroboros reports them in: the caller's header checks first
\* (consensus.ValidateHeader or the caller's own), then verifyBlock, then
\* VerifyBlockState with the issuer last.
\* Literally: "GoOrder is defined as the sequence "envelope",
\*   "leaderThreshold", "opcertCounter", "vrfProof", "opcertSig",
\*   "kesWindow", "kesSig", "bodySize", "bodyHash", "txs", "issuer"."
GoOrder == <<"envelope", "leaderThreshold", "opcertCounter", "vrfProof",
             "opcertSig", "kesWindow", "kesSig", "bodySize", "bodyHash",
             "txs", "issuer">>

VARIABLES slot, issuer, vrfOk, fails

vars == <<slot, issuer, vrfOk, fails>>

\* In English: "Every block shape is a starting state; nothing then
\* changes."
\* Literally: "Init is defined as: slot is a member of SlotKinds and issuer
\*   is a member of Issuers and vrfOk is a member of BOOLEAN and fails is a
\*   member of the set of subsets of Checks."
Init == slot \in SlotKinds /\ issuer \in Issuers /\ vrfOk \in BOOLEAN
        /\ fails \in SUBSET Checks

\* Literally: "Next is defined as: vars are unchanged."
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always [Next] on vars."
Spec == Init /\ [][Next]_vars

\* The reference's issuer verdict [O1].
\* In English: "A non-active overlay slot fails; an active one needs the
\* scheduled delegate with its VRF key; a pool slot needs a pool with its
\* VRF key."
\* Literally: "RefIssuerFails is defined as: in the case slot equals
\*   "nonactive", TRUE; in the case "active", issuer is not "delegate" or
\*   not vrfOk; otherwise issuer is not "pool" or not vrfOk."
RefIssuerFails ==
    CASE slot = "nonactive" -> TRUE
      [] slot = "active"    -> issuer # "delegate" \/ ~vrfOk
      [] OTHER              -> issuer # "pool" \/ ~vrfOk

\* An active overlay slot has no stake check, so a failed threshold there
\* is no failure [O1].
\* In English: "The failures that count: all of them, less the threshold
\* in an active overlay slot."
\* Literally: "Counted is defined as fails minus (the set containing
\*   "leaderThreshold" if slot equals "active", else the empty set)."
Counted == fails \ (IF slot = "active" THEN {"leaderThreshold"} ELSE {})

\* gOuroboros' issuer verdict. With the fix a TPraos block goes through the
\* overlay schedule first; otherwise every issuer is looked up in the pool
\* distribution, where a genesis delegate is absent.
\* In English: "With the overlay (or in Praos, where it is the same rule),
\* the reference's verdict; without it, a pool with its VRF key passes in
\* any slot and nobody else does."
\* Literally: "GoIssuerFails is defined as: if GoOverlay or Mode equals
\*   "Praos" then RefIssuerFails else (issuer is not "pool" or not
\*   vrfOk)."
GoIssuerFails == IF GoOverlay \/ Mode = "Praos" THEN RefIssuerFails
                 ELSE issuer # "pool" \/ ~vrfOk

\* In English: "The reference accepts a block with no counted failure and
\* a good issuer."
\* Literally: "RefAccepts is defined as: Counted equals the empty set and
\*   not RefIssuerFails."
RefAccepts == Counted = {} /\ ~RefIssuerFails

\* In English: "VerifyBlock and its caller together accept the same way,
\* with gOuroboros' issuer rule; the caller skips the threshold in an
\* active overlay slot, as the reference does."
\* Literally: "GoAccepts is defined as: Counted equals the empty set and
\*   not GoIssuerFails."
GoAccepts == Counted = {} /\ ~GoIssuerFails

\* In English: "VerifyBlock alone, without its caller's checks."
\* Literally: "VerifyBlockAloneAccepts is defined as: Counted minus
\*   CallerChecks equals the empty set and not GoIssuerFails."
VerifyBlockAloneAccepts == (Counted \ CallerChecks) = {} /\ ~GoIssuerFails

\* In English: "The set of check names that fail, the issuer included."
\* Literally: "Failing is defined as Counted united with (the set
\*   containing "issuer" if RefIssuerFails, else the empty set)."
Failing == Counted \cup (IF RefIssuerFails THEN {"issuer"} ELSE {})

\* In English: "The first failing name in order o; "none" when none fails."
\* Literally: "First of o is defined as: if there exists an i in 1 to the
\*   length of o such that o[i] is a member of Failing, then o[the smallest
\*   such i], else "none"."
First(o) ==
    IF \E i \in 1..Len(o) : o[i] \in Failing
    THEN o[CHOOSE i \in 1..Len(o) : o[i] \in Failing
                    /\ \A j \in 1..(i - 1) : o[j] \notin Failing]
    ELSE "none"

-----------------------------------------------------------------------------
\* In English: "gOuroboros with its caller accepts exactly the blocks the
\* reference accepts."
\* Literally: "AcceptAgrees is defined as GoAccepts equals RefAccepts."
AcceptAgrees == GoAccepts = RefAccepts

\* In English: "Every block the reference accepts, gOuroboros with its
\* caller accepts too": the half of AcceptAgrees that a false rejection
\* breaks, so its Bug config shows main rejects valid blocks.
\* Literally: "NoFalseRejects is defined as: RefAccepts implies GoAccepts."
NoFalseRejects == RefAccepts => GoAccepts

\* In English: "The first failure gOuroboros reports is the reference's."
\* Known to differ: gOuroboros checks the issuer last.
\* Literally: "FirstErrorAgrees is defined as First of GoOrder equals First
\*   of RefOrder."
FirstErrorAgrees == First(GoOrder) = First(RefOrder)

\* Probe, expected violated: VerifyBlock alone accepts a block the
\* reference rejects, so the caller's checks are required.
\* Literally: "ProbeAloneSuffices is defined as: VerifyBlockAloneAccepts
\*   implies RefAccepts."
ProbeAloneSuffices == VerifyBlockAloneAccepts => RefAccepts

\* Probe, expected violated: a block in an active overlay slot is accepted.
\* Literally: "ProbeActiveAccepted is defined as: not (slot equals
\*   "active" and RefAccepts)."
ProbeActiveAccepted == ~(slot = "active" /\ RefAccepts)
=============================================================================
