---------------------------- MODULE LeiosLedger ----------------------------
(***************************************************************************)
(* Linear Leios on the ledger side: a ranking block (RB) may announce an   *)
(* endorser block (EB); the next RB may certify that EB; the EB's          *)
(* transactions are applied to the ledger just before the certifying RB    *)
(* (a "CertRB"), at the announcing RB's slot. A CertRB carries no          *)
(* transactions of its own. Rolling back a CertRB must take the EB's       *)
(* transactions back out of the ledger.                                    *)
(*                                                                         *)
(* The model has two halves.                                               *)
(*   1. The reference: the Dijkstra BBODY and EB rules of cardano-ledger   *)
(*      1210d37f, composed the way the prototype node composes them        *)
(*      (ouroboros-consensus 5cc95f4c applies the EB closure and the       *)
(*      CertRB as one step), with per-block ledger snapshots for rollback. *)
(*   2. What gOuroboros decides for the same blocks. gOuroboros holds no   *)
(*      ledger state and has no EB rule: VerifyBlockState checks a block   *)
(*      against its predecessor header and a caller-supplied state. So     *)
(*      the model says what the caller (Dingo) must do on top: apply the   *)
(*      certified EB before the CertRB (constant GoCallerAppliesEb).       *)
(*                                                                         *)
(* Sources (quotes and links in README.md).                                *)
(*   CIP-0164 at cardano-foundation/CIPs a2cac180:                         *)
(*   [C1] README.md 393-438 "Step 5: Chain Inclusion": RB' holds either a  *)
(*        certificate for the EB announced in RB or transactions; the      *)
(*        certificate only when RB' is >= ceil((3Lhdr+Lvote+Ldiff)/slot)   *)
(*        slots after RB; otherwise the EB is discarded.                   *)
(*   [C2] README.md 1117-1132 "Ledger Management": EB transactions are     *)
(*        added only when certified, validated against the state left by   *)
(*        the announcing RB.                                               *)
(*   [C3] README.md 763-775 and 3378-3392: an EB is an ordered map from    *)
(*        transaction hash to size, without duplicate keys.               *)
(*   Reference, cardano-ledger 1210d37f (eras/dijkstra/impl/src/Cardano/   *)
(*   Ledger/Dijkstra/):                                                    *)
(*   [R1] Rules/Bbody.hs 464-488: a certificate needs an empty body        *)
(*        (LeiosCertBlockBodyHasTxs), an announcement in the state         *)
(*        (LeiosCertWithoutEbAnnouncement), the EB applied                 *)
(*        (LeiosCertEbNotApplied), then LEIOSCERT; no certificate needs    *)
(*        the header flag clear (LeiosCertMissing).                        *)
(*   [R2] Rules/Bbody.hs 490-502: every block replaces the remembered      *)
(*        announcement with its own, or with nothing.                      *)
(*   [R3] Rules/LeiosCert.hs 106-140: the delay rule (LeiosCertTooEarly),  *)
(*        the same-epoch rule (LeiosCertAnnouncedInPreviousEpoch), then    *)
(*        verifyLeiosCert.                                                 *)
(*   [R4] Rules/Eb.hs 192-293: the EB rule: an announcement must exist,    *)
(*        the EB's hash and size must match it, it must not be applied     *)
(*        yet (EbAlreadyApplied), the ledger must not have ticked past the *)
(*        announcing slot; then EBLEDGERS applies its transactions in      *)
(*        order and marks the announcement applied.                        *)
(*   [R5] ouroboros-consensus 5cc95f4c, Storage/LedgerDB/Forker.hs         *)
(*        630-686: the prototype's CertRB path: announcement from the      *)
(*        predecessor, certificate, EB closure applied, then the block.    *)
(*        It has no same-epoch rule.                                       *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit d0b95845):              *)
(*   [G1] ledger/dijkstra/leios_header.go ValidateLeiosCertificateTiming   *)
(*        117-158: a certified header needs an announcing predecessor and  *)
(*        the delay; no epoch rule.                                        *)
(*   [G2] ledger/dijkstra/leios_header.go validateLeiosBlockBody 221-247:  *)
(*        flag iff certificate; certificate excludes transactions.         *)
(*   [G3] ledger/verify_block.go validateDijkstraBlockCertificatesWith     *)
(*        333-454: the certificate itself (LeiosCommittee.tla).            *)
(*   [G4] ledger/common/leios_endorser_block.go 121-138: no duplicate      *)
(*        references in one EB.                                            *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla. New here:*)
(*   s \o t           the sequence s followed by the sequence t            *)
(*   SubSeq(s, i, j)  the elements i..j of the sequence s                  *)
(*   RECURSIVE F(_)   announces that F's definition uses F itself          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,               \* transaction ids; each spends its own input once
    EbChoices,         \* the EB contents a block may announce
    MaxSlot,           \* the last slot a block may occupy
    CertDelay,         \* ceil((3Lhdr+Lvote+Ldiff)/slotLength), in slots [C1]
    EpochLength,       \* slots per epoch
    MaxChain,          \* the longest chain the model builds
    RefSameEpoch,      \* TRUE: ledger 1210d37f's same-epoch rule [R3];
                       \* FALSE: the prototype, which has none [R5]
    Impl,              \* "ref": the reference decides; "go": gOuroboros does
    GoCallerAppliesEb, \* the caller refuses a CertRB whose EB it has not applied
    Mutation           \* "none", or one deliberate break (see below)

VARIABLES
    chain,      \* the blocks of the current chain, oldest first
    snaps,      \* snaps[1] is genesis; snaps[i+1] the state after chain[i]
    pending,    \* <<the state after the tip's EB was applied>>, or <<>>
    rolledCert, \* history: a CertRB was rolled back
    discarded   \* history: an applied EB was dropped by a non-CertRB

vars == <<chain, snaps, pending, rolledCert, discarded>>

\* No announcement remembered.
NoAnn == [present |-> FALSE, slot |-> 0, eb |-> <<>>, applied |-> FALSE]

\* The ledger: the transactions applied so far in order, the announcing
\* slots of the EBs applied so far, and the remembered announcement [R2].
Genesis == [log |-> <<>>, endorsed |-> <<>>, last |-> NoAnn]

\* The state the next block is applied to when it does not certify.
TipState == snaps[Len(snaps)]

\* The slot of the newest block (0 is genesis).
TipSlot == IF chain = <<>> THEN 0 ELSE chain[Len(chain)].slot

\* The set of elements of a sequence.
Range(s) == {s[i] : i \in DOMAIN s}

\* A sequence without repeats.
Distinct(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

\* Transactions are valid on a state when none repeats and none is spent
\* there: the UTxO rule, reduced to "each input is spent once".
TxsValid(st, txs) == Distinct(txs) /\ Range(txs) \cap Range(st.log) = {}

\* The epoch a slot is in.
Epoch(s) == s \div EpochLength

\* The transaction lists a block may carry: none, or one transaction.
TxChoices == {<<>>} \cup {<<t>> : t \in Txs}

\* Every block that could be offered next: a slot after the tip, an EB
\* announced or not, the header flag, a certificate (valid or not), and
\* transactions. A block without a certificate always has certValid FALSE,
\* so equal blocks are not counted twice.
Candidates ==
    [slot : (TipSlot + 1)..MaxSlot, ann : {<<>>} \cup EbChoices,
     flag : BOOLEAN, cert : {FALSE}, certValid : {FALSE}, txs : TxChoices]
    \cup
    [slot : (TipSlot + 1)..MaxSlot, ann : {<<>>} \cup EbChoices,
     flag : BOOLEAN, cert : {TRUE}, certValid : BOOLEAN, txs : TxChoices]

(***************************************************************************)
(* The reference.                                                          *)
(***************************************************************************)

\* The state BBODY runs on: after the EB when a CertRB follows an applied
\* EB [R5], otherwise the tip. A non-CertRB drops any applied EB.
RefBase(b) == IF b.cert /\ pending # <<>> THEN pending[1] ELSE TipState

\* The header flag matches the body, and a certificate comes alone [R1].
RefHeaderBody(b) ==
    /\ b.flag = b.cert
    /\ (b.cert => (b.txs = <<>> \/ Mutation = "TxsWithCert"))

\* A certificate's rules, read from the state BBODY runs on [R1][R3].
RefCertOK(b) ==
    LET a == RefBase(b).last IN
    b.cert =>
        \* an EB was announced (LeiosCertWithoutEbAnnouncement)
        /\ a.present
        \* and has been applied (LeiosCertEbNotApplied)
        /\ a.applied
        \* late enough after the announcement (LeiosCertTooEarly)
        /\ (b.slot >= a.slot + CertDelay \/ Mutation = "NoTiming")
        \* in the announcement's epoch, for ledger 1210d37f only
        /\ (RefSameEpoch => Epoch(b.slot) = Epoch(a.slot))
        \* and the certificate verifies (LeiosCommittee.tla)
        /\ b.certValid

\* The reference accepts a block.
RefAccept(b) ==
    /\ RefHeaderBody(b)
    /\ RefCertOK(b)
    /\ TxsValid(RefBase(b), b.txs)

(***************************************************************************)
(* gOuroboros, and what its caller adds.                                   *)
(***************************************************************************)

\* gOuroboros's own checks, from the block and its predecessor header
\* [G1][G2][G3].
GoChecks(b) ==
    /\ b.flag = b.cert
    /\ (b.cert => b.txs = <<>>)
    /\ (b.cert =>
          \* a predecessor that announced an EB
          /\ chain # <<>>
          /\ chain[Len(chain)].ann # <<>>
          \* late enough after it
          /\ b.slot >= chain[Len(chain)].slot + CertDelay
          \* and the certificate verifies
          /\ b.certValid)

\* The state the caller hands gOuroboros: after the EB if the caller
\* applied it, otherwise the tip.
GoBase(b) ==
    IF b.cert /\ GoCallerAppliesEb /\ pending # <<>> THEN pending[1] ELSE TipState

\* gOuroboros, with its caller, accepts a block.
GoAccept(b) ==
    /\ GoChecks(b)
    \* a caller that applies EBs refuses a CertRB whose EB it does not have
    /\ (b.cert /\ GoCallerAppliesEb => pending # <<>>)
    /\ TxsValid(GoBase(b), b.txs)

(***************************************************************************)
(* Steps.                                                                  *)
(***************************************************************************)

\* Who decides.
Accept(b) == IF Impl = "ref" THEN RefAccept(b) ELSE GoAccept(b)

\* The state a block is applied to.
BaseFor(b) == IF Impl = "ref" THEN RefBase(b) ELSE GoBase(b)

\* What a block leaves remembered: its own announcement, or nothing [R2].
NewLast(st, b) ==
    IF b.ann # <<>>
    THEN [present |-> TRUE, slot |-> b.slot, eb |-> b.ann, applied |-> FALSE]
    ELSE IF Mutation = "KeepAnnouncement" THEN st.last ELSE NoAnn

\* The state after a block: its transactions spent, its announcement kept.
ApplyBlock(st, b) ==
    [log |-> st.log \o b.txs, endorsed |-> st.endorsed,
     last |-> NewLast(st, b)]

Init ==
    /\ chain = <<>>
    /\ snaps = <<Genesis>>
    /\ pending = <<>>
    /\ rolledCert = FALSE
    /\ discarded = FALSE

\* A new block extends the chain, if accepted. Any applied EB it does not
\* certify is dropped [C1].
AddRB ==
    /\ Len(chain) < MaxChain
    /\ \E b \in Candidates :
        /\ Accept(b)
        /\ chain' = Append(chain, b)
        /\ snaps' = Append(snaps, ApplyBlock(BaseFor(b), b))
        /\ pending' = <<>>
        /\ discarded' = (discarded \/ (pending # <<>> /\ ~b.cert))
        /\ UNCHANGED rolledCert

\* The EB rule [R4]: the tip's announced EB arrives and is applied on top
\* of the tip's state, kept aside until a CertRB uses it.
FetchApplyEB ==
    \E eb \in EbChoices :
        LET base == IF pending = <<>> THEN TipState ELSE pending[1]
            a == base.last
            st == [log |-> base.log \o eb,
                   endorsed |-> Append(base.endorsed, a.slot),
                   last |-> [a EXCEPT !.applied = TRUE]]
        IN
        \* an announcement exists (EbWasNotAnnounced)
        /\ a.present
        \* the EB is the announced one (EbAnnouncementHashMismatch)
        /\ (eb = a.eb \/ Mutation = "NoHashCheck")
        \* and is not applied yet (EbAlreadyApplied)
        /\ (~a.applied \/ Mutation = "ReapplyUnchecked")
        \* and its transactions are valid, in order (EBLEDGERS)
        /\ (TxsValid(base, eb) \/ Mutation = "ReapplyUnchecked")
        /\ IF Mutation = "EagerEb"
           \* broken: the EB lands in the tip's own state at once
           THEN /\ snaps' = [snaps EXCEPT ![Len(snaps)] = st]
                /\ UNCHANGED pending
           ELSE /\ pending' = <<st>>
                /\ UNCHANGED snaps
        /\ UNCHANGED <<chain, rolledCert, discarded>>

\* The tip block is rolled back: the state before it comes back, and any
\* applied EB is dropped.
Rollback ==
    /\ chain # <<>>
    /\ chain' = SubSeq(chain, 1, Len(chain) - 1)
    /\ snaps' =
        IF Mutation = "RollbackKeepsState"
        \* broken: the rolled-back block's state stays in force
        THEN [SubSeq(snaps, 1, Len(snaps) - 1)
                EXCEPT ![Len(snaps) - 1] = snaps[Len(snaps)]]
        ELSE SubSeq(snaps, 1, Len(snaps) - 1)
    \* broken under RollbackKeepsPending: the old tip's EB survives
    /\ pending' = IF Mutation = "RollbackKeepsPending" THEN pending ELSE <<>>
    /\ rolledCert' = (rolledCert \/ chain[Len(chain)].cert)
    /\ UNCHANGED discarded

Next == AddRB \/ FetchApplyEB \/ Rollback

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* What must hold.                                                         *)
(***************************************************************************)

\* The EBs the configurations use: one of two transactions, and one of the
\* second alone, so an EB can conflict with an RB transaction or another EB.
DefaultEbs == {<<"t1", "t2">>, <<"t2">>}

\* Every variable has the expected shape.
TypeOK ==
    /\ Len(snaps) = Len(chain) + 1
    /\ \A i \in DOMAIN chain : chain[i].slot \in 1..MaxSlot
    /\ pending = <<>> \/ pending[1].last.applied
    /\ rolledCert \in BOOLEAN
    /\ discarded \in BOOLEAN

\* What the ledger should hold for a chain: per block, the EB of its
\* predecessor if it certifies one [C2], then its own transactions.
RECURSIVE Replay(_)
Replay(c) ==
    IF c = <<>> THEN <<>>
    ELSE LET n == Len(c) IN
         Replay(SubSeq(c, 1, n - 1))
         \o (IF c[n].cert /\ n > 1 THEN c[n - 1].ann ELSE <<>>)
         \o c[n].txs

\* The announcing slots of the EBs a chain certifies.
RECURSIVE Endorsements(_)
Endorsements(c) ==
    IF c = <<>> THEN <<>>
    ELSE LET n == Len(c) IN
         Endorsements(SubSeq(c, 1, n - 1))
         \o (IF c[n].cert /\ n > 1 THEN <<c[n - 1].slot>> ELSE <<>>)

\* The ledger is exactly the replay of the chain: an EB's transactions are
\* in it only while a CertRB for it is on the chain, so a rollback undoes
\* the endorsement, and every reference resolved to the announced EB.
LedgerMatchesChain ==
    /\ TipState.log = Replay(chain)
    /\ TipState.endorsed = Endorsements(chain)

\* Every CertRB on the chain follows an announcing block, late enough,
\* with a valid certificate, the flag set and no transactions [C1][R1].
CertifiedChainWellFormed ==
    \A i \in DOMAIN chain : chain[i].cert =>
        /\ i > 1
        /\ chain[i - 1].ann # <<>>
        /\ chain[i].slot >= chain[i - 1].slot + CertDelay
        /\ (RefSameEpoch => Epoch(chain[i].slot) = Epoch(chain[i - 1].slot))
        /\ chain[i].certValid
        /\ chain[i].flag
        /\ chain[i].txs = <<>>

\* No transaction is applied twice, across RBs and EBs.
NoTxTwice == Distinct(TipState.log)

\* No EB is applied twice, on the chain or in the EB kept aside.
EbAppliedAtMostOnce ==
    /\ Distinct(TipState.endorsed)
    /\ (pending # <<>> => Distinct(pending[1].endorsed))

\* gOuroboros with its caller accepts exactly the blocks the reference
\* accepts, from every reachable state.
GoAgrees == \A b \in Candidates : RefAccept(b) = GoAccept(b)

\* Probes, EXPECTED to be violated: each shows a behaviour is reachable.
ProbeNoCertAccepted == \A i \in DOMAIN chain : ~chain[i].cert
ProbeNoCertRolledBack == ~rolledCert
ProbeNoEbDiscarded == ~discarded
ProbeNoCrossEpochCert ==
    \A i \in DOMAIN chain : (chain[i].cert /\ i > 1) =>
        Epoch(chain[i].slot) = Epoch(chain[i - 1].slot)
=============================================================================
