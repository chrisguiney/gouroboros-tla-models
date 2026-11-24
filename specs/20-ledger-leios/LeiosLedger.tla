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

\* Literally: "vars is defined as the tuple of chain, snaps, pending, rolledCert
\*   and discarded."
vars == <<chain, snaps, pending, rolledCert, discarded>>

\* No announcement remembered.
\* Literally: "NoAnn is defined as the record whose field present is FALSE,
\*   field slot is 0, field eb is the empty sequence, and field applied is
\*   FALSE."
NoAnn == [present |-> FALSE, slot |-> 0, eb |-> <<>>, applied |-> FALSE]

\* The ledger: the transactions applied so far in order, the announcing
\* slots of the EBs applied so far, and the remembered announcement [R2].
\* Literally: "Genesis is defined as the record whose field log is the empty
\*   sequence, field endorsed is the empty sequence, and field last is NoAnn."
Genesis == [log |-> <<>>, endorsed |-> <<>>, last |-> NoAnn]

\* The state the next block is applied to when it does not certify.
\* Literally: "TipState is defined as snaps of the length of snaps."
TipState == snaps[Len(snaps)]

\* The slot of the newest block (0 is genesis).
\* Literally: "TipSlot is defined as: if chain equals the empty sequence then 0,
\*   else chain of the length of chain's slot."
TipSlot == IF chain = <<>> THEN 0 ELSE chain[Len(chain)].slot

\* The set of elements of a sequence.
\* Literally: "Range of s is defined as the set of s of i, for every i that is a
\*   member of the domain of s."
Range(s) == {s[i] : i \in DOMAIN s}

\* A sequence without repeats.
\* Literally: "Distinct of s is defined as: for all i and j in the domain of s,
\*   if i does not equal j, then s of i does not equal s of j."
Distinct(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

\* Transactions are valid on a state when none repeats and none is spent
\* there: the UTxO rule, reduced to "each input is spent once".
\* Literally: "TxsValid of st and txs is defined as: Distinct of txs, and the
\*   intersection of Range of txs and Range of st's log equals the empty set."
TxsValid(st, txs) == Distinct(txs) /\ Range(txs) \cap Range(st.log) = {}

\* The epoch a slot is in.
\* Literally: "Epoch of s is defined as s integer-divided by EpochLength."
Epoch(s) == s \div EpochLength

\* The transaction lists a block may carry: none, or one transaction.
\* Literally: "TxChoices is defined as the union of the set containing the empty
\*   sequence and the set of the tuple of t, for every t that is a member of
\*   Txs."
TxChoices == {<<>>} \cup {<<t>> : t \in Txs}

\* Every block that could be offered next: a slot after the tip, an EB
\* announced or not, the header flag, a certificate (valid or not), and
\* transactions. A block without a certificate always has certValid FALSE,
\* so equal blocks are not counted twice.
\* Literally: "Candidates is defined as the union of: the set of records whose
\*   field slot is a member of (TipSlot plus 1) through MaxSlot, field ann is a
\*   member of the union of the set containing the empty sequence and EbChoices,
\*   field flag is a member of BOOLEAN, field cert is a member of the set
\*   containing FALSE, field certValid is a member of the set containing FALSE,
\*   and field txs is a member of TxChoices; and the set of records whose field
\*   slot is a member of (TipSlot plus 1) through MaxSlot, field ann is a member
\*   of the union of the set containing the empty sequence and EbChoices, field
\*   flag is a member of BOOLEAN, field cert is a member of the set containing
\*   TRUE, field certValid is a member of BOOLEAN, and field txs is a member of
\*   TxChoices."
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
\* Literally: "RefBase of b is defined as: if b's cert and pending does not
\*   equal the empty sequence then element 1 of pending, else TipState."
RefBase(b) == IF b.cert /\ pending # <<>> THEN pending[1] ELSE TipState

\* The header flag matches the body, and a certificate comes alone [R1].
\* Literally: "RefHeaderBody of b is defined as: b's flag equals b's cert, and
\*   if b's cert, then (b's txs equals the empty sequence or Mutation equals
\*   "TxsWithCert")."
RefHeaderBody(b) ==
    /\ b.flag = b.cert
    /\ (b.cert => (b.txs = <<>> \/ Mutation = "TxsWithCert"))

\* A certificate's rules, read from the state BBODY runs on [R1][R3].
\* Literally: "RefCertOK of b is defined as: letting a be RefBase of b's last:
\*   if b's cert, then a's present, and a's applied, and (b's slot is greater
\*   than or equal to a's slot plus CertDelay, or Mutation equals "NoTiming"),
\*   and (if RefSameEpoch, then Epoch of b's slot equals Epoch of a's slot), and
\*   b's certValid."
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
\* Literally: "RefAccept of b is defined as: RefHeaderBody of b, and RefCertOK
\*   of b, and TxsValid of RefBase of b, and b's txs."
RefAccept(b) ==
    /\ RefHeaderBody(b)
    /\ RefCertOK(b)
    /\ TxsValid(RefBase(b), b.txs)

(***************************************************************************)
(* gOuroboros, and what its caller adds.                                   *)
(***************************************************************************)

\* gOuroboros's own checks, from the block and its predecessor header
\* [G1][G2][G3].
\* Literally: "GoChecks of b is defined as: b's flag equals b's cert, and (if
\*   b's cert, then b's txs equals the empty sequence), and (if b's cert, then
\*   chain does not equal the empty sequence, and chain of the length of chain's
\*   ann does not equal the empty sequence, and b's slot is greater than or
\*   equal to chain of the length of chain's slot plus CertDelay, and b's
\*   certValid)."
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
\* Literally: "GoBase of b is defined as: if b's cert and GoCallerAppliesEb and
\*   pending does not equal the empty sequence then element 1 of pending, else
\*   TipState."
GoBase(b) ==
    IF b.cert /\ GoCallerAppliesEb /\ pending # <<>> THEN pending[1] ELSE TipState

\* gOuroboros, with its caller, accepts a block.
\* Literally: "GoAccept of b is defined as: GoChecks of b, and (if b's cert and
\*   GoCallerAppliesEb, then pending does not equal the empty sequence), and
\*   TxsValid of GoBase of b, and b's txs."
GoAccept(b) ==
    /\ GoChecks(b)
    \* a caller that applies EBs refuses a CertRB whose EB it does not have
    /\ (b.cert /\ GoCallerAppliesEb => pending # <<>>)
    /\ TxsValid(GoBase(b), b.txs)

(***************************************************************************)
(* Steps.                                                                  *)
(***************************************************************************)

\* Who decides.
\* Literally: "Accept of b is defined as: if Impl equals "ref" then RefAccept of
\*   b, else GoAccept of b."
Accept(b) == IF Impl = "ref" THEN RefAccept(b) ELSE GoAccept(b)

\* The state a block is applied to.
\* Literally: "BaseFor of b is defined as: if Impl equals "ref" then RefBase of
\*   b, else GoBase of b."
BaseFor(b) == IF Impl = "ref" THEN RefBase(b) ELSE GoBase(b)

\* What a block leaves remembered: its own announcement, or nothing [R2].
\* Literally: "NewLast of st and b is defined as: if b's ann does not equal the
\*   empty sequence then the record whose field present is TRUE, field slot is
\*   b's slot, field eb is b's ann, and field applied is FALSE; else if Mutation
\*   equals "KeepAnnouncement" then st's last, else NoAnn."
NewLast(st, b) ==
    IF b.ann # <<>>
    THEN [present |-> TRUE, slot |-> b.slot, eb |-> b.ann, applied |-> FALSE]
    ELSE IF Mutation = "KeepAnnouncement" THEN st.last ELSE NoAnn

\* The state after a block: its transactions spent, its announcement kept.
\* Literally: "ApplyBlock of st and b is defined as the record whose field log
\*   is st's log followed by b's txs, whose field endorsed is st's endorsed, and
\*   whose field last is NewLast of st and b."
ApplyBlock(st, b) ==
    [log |-> st.log \o b.txs, endorsed |-> st.endorsed,
     last |-> NewLast(st, b)]

\* In English: "An empty chain on the genesis state, no EB kept aside, and no
\* history yet."
\* Literally: "Init is defined as: chain equals the empty sequence, and snaps
\*   equals the tuple of Genesis, and pending equals the empty sequence, and
\*   rolledCert equals FALSE, and discarded equals FALSE."
Init ==
    /\ chain = <<>>
    /\ snaps = <<Genesis>>
    /\ pending = <<>>
    /\ rolledCert = FALSE
    /\ discarded = FALSE

\* A new block extends the chain, if accepted. Any applied EB it does not
\* certify is dropped [C1].
\* Literally: "AddRB is defined as: the length of chain is less than MaxChain,
\*   and there exists a b in Candidates such that Accept of b, and chain in the
\*   next state equals chain with b appended, and snaps in the next state equals
\*   snaps with ApplyBlock of BaseFor of b, and b appended, and pending in the
\*   next state equals the empty sequence, and discarded in the next state
\*   equals (discarded or (pending does not equal the empty sequence and b's
\*   cert is not true)), and rolledCert is unchanged."
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
\* Literally: "FetchApplyEB is defined as: there exists an eb in EbChoices such
\*   that, letting base be: if pending equals the empty sequence then TipState,
\*   else element 1 of pending; a be base's last; and st be the record whose
\*   field log is base's log followed by eb, whose field endorsed is base's
\*   endorsed with a's slot appended, and whose field last is a except that its
\*   applied is TRUE: a's present, and (eb equals a's eb or Mutation equals
\*   "NoHashCheck"), and (a's applied is not true or Mutation equals
\*   "ReapplyUnchecked"), and (TxsValid of base and eb, or Mutation equals
\*   "ReapplyUnchecked"), and if Mutation equals "EagerEb" then (snaps in the
\*   next state equals snaps except that its length of snaps entry is st, and
\*   pending is unchanged), else (pending in the next state equals the tuple of
\*   st, and snaps is unchanged); and chain, rolledCert and discarded are
\*   unchanged."
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
\* Literally: "Rollback is defined as: chain does not equal the empty sequence,
\*   and chain in the next state equals the subsequence of chain from 1 through
\*   the length of chain minus 1, and snaps in the next state equals: if
\*   Mutation equals "RollbackKeepsState" then the subsequence of snaps from 1
\*   through the length of snaps minus 1, except that its (the length of snaps
\*   minus 1) entry is snaps of the length of snaps; else the subsequence of
\*   snaps from 1 through the length of snaps minus 1; and pending in the next
\*   state equals: if Mutation equals "RollbackKeepsPending" then pending, else
\*   the empty sequence; and rolledCert in the next state equals (rolledCert or
\*   chain of the length of chain's cert), and discarded is unchanged."
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

\* In English: "Each step adds a block, fetches and applies an EB, or rolls the
\* tip back."
\* Literally: "Next is defined as: AddRB or FetchApplyEB or Rollback."
Next == AddRB \/ FetchApplyEB \/ Rollback

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* What must hold.                                                         *)
(***************************************************************************)

\* The EBs the configurations use: one of two transactions, and one of the
\* second alone, so an EB can conflict with an RB transaction or another EB.
\* Literally: "DefaultEbs is defined as the set containing the tuple of "t1" and
\*   "t2", and the tuple of "t2"."
DefaultEbs == {<<"t1", "t2">>, <<"t2">>}

\* Every variable has the expected shape.
\* Literally: "TypeOK is defined as: the length of snaps equals the length of
\*   chain plus 1, and for all i in the domain of chain, chain of i's slot is a
\*   member of 1 through MaxSlot, and (pending equals the empty sequence or
\*   element 1 of pending's last's applied), and rolledCert is a member of
\*   BOOLEAN, and discarded is a member of BOOLEAN."
TypeOK ==
    /\ Len(snaps) = Len(chain) + 1
    /\ \A i \in DOMAIN chain : chain[i].slot \in 1..MaxSlot
    /\ pending = <<>> \/ pending[1].last.applied
    /\ rolledCert \in BOOLEAN
    /\ discarded \in BOOLEAN

\* What the ledger should hold for a chain: per block, the EB of its
\* predecessor if it certifies one [C2], then its own transactions.
RECURSIVE Replay(_)
\* Literally: "Replay of c is defined as: if c equals the empty sequence then
\*   the empty sequence, else, letting n be the length of c: Replay of the
\*   subsequence of c from 1 through n minus 1, followed by (if c of n's cert
\*   and n is greater than 1 then c of n minus 1's ann, else the empty
\*   sequence), followed by c of n's txs."
Replay(c) ==
    IF c = <<>> THEN <<>>
    ELSE LET n == Len(c) IN
         Replay(SubSeq(c, 1, n - 1))
         \o (IF c[n].cert /\ n > 1 THEN c[n - 1].ann ELSE <<>>)
         \o c[n].txs

\* The announcing slots of the EBs a chain certifies.
RECURSIVE Endorsements(_)
\* Literally: "Endorsements of c is defined as: if c equals the empty sequence
\*   then the empty sequence, else, letting n be the length of c: Endorsements
\*   of the subsequence of c from 1 through n minus 1, followed by (if c of n's
\*   cert and n is greater than 1 then the tuple of c of n minus 1's slot, else
\*   the empty sequence)."
Endorsements(c) ==
    IF c = <<>> THEN <<>>
    ELSE LET n == Len(c) IN
         Endorsements(SubSeq(c, 1, n - 1))
         \o (IF c[n].cert /\ n > 1 THEN <<c[n - 1].slot>> ELSE <<>>)

\* The ledger is exactly the replay of the chain: an EB's transactions are
\* in it only while a CertRB for it is on the chain, so a rollback undoes
\* the endorsement, and every reference resolved to the announced EB.
\* Literally: "LedgerMatchesChain is defined as: TipState's log equals Replay of
\*   chain, and TipState's endorsed equals Endorsements of chain."
LedgerMatchesChain ==
    /\ TipState.log = Replay(chain)
    /\ TipState.endorsed = Endorsements(chain)

\* Every CertRB on the chain follows an announcing block, late enough,
\* with a valid certificate, the flag set and no transactions [C1][R1].
\* Literally: "CertifiedChainWellFormed is defined as: for all i in the domain
\*   of chain, if chain of i's cert, then i is greater than 1, and chain of i
\*   minus 1's ann does not equal the empty sequence, and chain of i's slot is
\*   greater than or equal to chain of i minus 1's slot plus CertDelay, and (if
\*   RefSameEpoch, then Epoch of chain of i's slot equals Epoch of chain of i
\*   minus 1's slot), and chain of i's certValid, and chain of i's flag, and
\*   chain of i's txs equals the empty sequence."
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
\* Literally: "NoTxTwice is defined as Distinct of TipState's log."
NoTxTwice == Distinct(TipState.log)

\* No EB is applied twice, on the chain or in the EB kept aside.
\* Literally: "EbAppliedAtMostOnce is defined as: Distinct of TipState's
\*   endorsed, and (if pending does not equal the empty sequence, then Distinct
\*   of element 1 of pending's endorsed)."
EbAppliedAtMostOnce ==
    /\ Distinct(TipState.endorsed)
    /\ (pending # <<>> => Distinct(pending[1].endorsed))

\* gOuroboros with its caller accepts exactly the blocks the reference
\* accepts, from every reachable state.
\* Literally: "GoAgrees is defined as: for all b in Candidates, RefAccept of b
\*   equals GoAccept of b."
GoAgrees == \A b \in Candidates : RefAccept(b) = GoAccept(b)

\* Probes, EXPECTED to be violated: each shows a behaviour is reachable.
\* In English: "No CertRB is ever on the chain."
\* Literally: "ProbeNoCertAccepted is defined as: for all i in the domain of
\*   chain, chain of i's cert is not true."
ProbeNoCertAccepted == \A i \in DOMAIN chain : ~chain[i].cert
\* In English: "No CertRB is ever rolled back."
\* Literally: "ProbeNoCertRolledBack is defined as: rolledCert is not true."
ProbeNoCertRolledBack == ~rolledCert
\* In English: "No applied EB is ever dropped by a non-CertRB."
\* Literally: "ProbeNoEbDiscarded is defined as: discarded is not true."
ProbeNoEbDiscarded == ~discarded
\* In English: "No CertRB ever certifies an EB announced in an earlier epoch."
\* Literally: "ProbeNoCrossEpochCert is defined as: for all i in the domain of
\*   chain, if chain of i's cert and i is greater than 1, then Epoch of chain of
\*   i's slot equals Epoch of chain of i minus 1's slot."
ProbeNoCrossEpochCert ==
    \A i \in DOMAIN chain : (chain[i].cert /\ i > 1) =>
        Epoch(chain[i].slot) = Epoch(chain[i - 1].slot)
=============================================================================
