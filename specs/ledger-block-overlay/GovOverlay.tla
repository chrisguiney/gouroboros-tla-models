----------------------------- MODULE GovOverlay -----------------------------
(***************************************************************************)
(* The Conway governance part of the in-block ledger view: what a later    *)
(* transaction sees of the DRep registrations, vote delegations,           *)
(* proposals and committee keys that earlier transactions of the same      *)
(* block made, and what happens to that view when a block is rejected.    *)
(*                                                                         *)
(* The reference applies a block's transactions one after another, each    *)
(* against the state its predecessors left (LEDGERS). gOuroboros keeps the *)
(* ledger state of the previous block untouched and lays a                 *)
(* common.BlockLedgerState over it: maps of what changed, consulted first, *)
(* with the wrapped state answering everything else. The model states both *)
(* and asks whether the two answer every question alike.                   *)
(*                                                                         *)
(* A transaction's own rules are other models' (ledger-utxo,               *)
(* ledger-governance, ledger-conway-dijkstra). Here both sides run the     *)
(* same precondition, Pre, against their own view of the state, so any    *)
(* difference in a verdict comes from the view alone.                      *)
(*                                                                         *)
(* Sources. cardano-ledger 1210d37f:                                       *)
(*   [L1] eras/conway/impl/src/Cardano/Ledger/Conway/Rules/Ledgers.hs:     *)
(*        transactions are applied in order, each to the state the        *)
(*        previous one left.                                               *)
(*   [L2] .../Conway/Rules/Ledger.hs 390-448: a valid transaction runs     *)
(*        CERTS (with the committee proposals of the current state, line   *)
(*        393), then GOV, then UTXOW; a phase-2-invalid one only UTXOW,    *)
(*        which takes its collateral.                                      *)
(*   [L3] .../Conway/Rules/GovCert.hs 190-205: a hot-key authorization or  *)
(*        resignation needs a current or potential future member that has *)
(*        not resigned; 206-270: DRep registration, unregistration (which *)
(*        clears the delegations to it), update.                          *)
(*   [L4] .../Conway/Rules/Gov.hs: votes need a known proposal and a       *)
(*        known voter.                                                     *)
(*   [L5] .../Conway/Rules/Deleg.hs: from protocol version 10 a vote       *)
(*        delegation needs a registered DRep; .../Rules/Certs.hs and       *)
(*        Ledger.hs: a key-hash withdrawal needs a DRep delegation.        *)
(*   [L6] .../Conway/Rules/Bbody.hs: a block that fails is rejected whole; *)
(*        the ledger stays as it was before it.                            *)
(* gOuroboros: ledger/common/block_state.go (BlockLedgerState,             *)
(* applyCertificate, applyLevel, DRepRegistration, DRepDelegationStateFor, *)
(* CommitteeCredentialStateFor), ledger/verify_block.go                    *)
(* (verifyBlockTransactions: a fresh view per call), and                   *)
(* ledger/conway/rules.go (UtxoValidateCommitteeCertificates).             *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxTxs,           \* most transactions in one block
    Blocks,           \* how many blocks are validated one after another
    GoProposedMember, \* TRUE: gOuroboros counts in-block UpdateCommittee
                      \* proposals as potential members (the fix).
                      \* FALSE: gOuroboros main
    Mutation          \* "none", or a deliberate mistake that an invariant
                      \* must catch: "leakInvalid", "noDeregClear",
                      \* "reuseOverlay"

\* Two cold committee credentials: k1 sits on the committee at the start;
\* k2 does not, and becomes a potential member only when an UpdateCommittee
\* proposal names it.
\* Literally: "Colds is defined as the set containing "k1" and "k2"."
Colds == {"k1", "k2"}

\* What a transaction does. One action per transaction keeps the state
\* space small; the order of transactions is what the model is about.
\* In English: "Kinds is every action a transaction can take: register,
\* unregister or delegate to the DRep; propose an UpdateCommittee adding k2,
\* or an Info action; authorize a hot key for, or resign, a cold credential;
\* vote as a committee member or as the DRep; withdraw rewards."
\* An action is a pair: what it does, and the cold credential it names
\* ("-" when it names none).
\* Literally: "Kinds is defined as the union of the set of pairs
\*   <<op, "-">> for every op that is a member of the set containing
\*   "regDRep", "unregDRep", "delegVote", "proposeUC", "proposeInfo",
\*   "voteCC", "voteDRep" and "withdraw", with the set of the pairs
\*   <<"auth", k>> and <<"resign", k>> for every k that is a member of
\*   Colds."
Kinds == {<<op, "-">> : op \in {"regDRep", "unregDRep", "delegVote",
                                 "proposeUC", "proposeInfo", "voteCC",
                                 "voteDRep", "withdraw"}}
         \cup {<<"auth", k>> : k \in Colds} \cup {<<"resign", k>> : k \in Colds}

\* In English: "A transaction is an action and its phase-2 validity flag."
\* Literally: "Txs is defined as the set of records whose field kind is a
\*   member of Kinds and whose field valid is a member of BOOLEAN."
Txs == [kind : Kinds, valid : BOOLEAN]

\* The reference's governance state: is the DRep registered, where does the
\* one stake credential delegate its vote, which credentials a pending
\* UpdateCommittee proposal names, is there any proposal to vote on, and
\* each cold credential's hot key and resignation.
\* In English: "The ledger before the first block: no DRep, no delegation,
\* no proposals, k1's hot key authorized, nobody resigned."
\* Literally: "Genesis is defined as the record whose field drep is FALSE,
\*   whose field deleg is "none", whose field proposed is the empty set,
\*   whose field props is FALSE, whose field hot is the function from Colds
\*   giving "h" for k1 and "none" for every other k, and whose field
\*   resigned is the function
\*   from Colds giving FALSE for every k."
Genesis == [drep |-> FALSE, deleg |-> "none", proposed |-> {},
            props |-> FALSE,
            hot |-> [k \in Colds |-> IF k = "k1" THEN "h" ELSE "none"],
            resigned |-> [k \in Colds |-> FALSE]]

\* What a rule can ask of a state. member is derived: current committee
\* (k1) or named by a pending UpdateCommittee proposal [L3].
\* In English: "The view of a reference state: its fields, with member
\* answering whether each cold credential is a current or potential
\* member."
\* Literally: "RefView of st is defined as the record whose field drep is
\*   st.drep, deleg is st.deleg, props is st.props, member is the function
\*   from Colds giving (k equals "k1" or k is a member of st.proposed),
\*   hot is st.hot, and resigned is st.resigned."
RefView(st) == [drep |-> st.drep, deleg |-> st.deleg, props |-> st.props,
                member |-> [k \in Colds |-> k = "k1" \/ k \in st.proposed],
                hot |-> st.hot, resigned |-> st.resigned]

\* The rules a valid transaction must pass, against a view [L3][L4][L5].
\* A phase-2-invalid transaction runs none of them [L2].
\* In English: "Register needs an unregistered DRep; unregister, delegate
\* and the DRep's vote need a registered one; authorize and resign need a
\* member that has not resigned; a committee vote needs a proposal and an
\* authorized, unresigned hot key; a DRep vote needs a proposal; a
\* withdrawal needs a DRep delegation; proposals need nothing here."
\* Literally: "Pre of v and kind is defined as: in the case kind[1] equals
\*   "regDRep", not v.drep; in the case "unregDRep" or "delegVote",
\*   v.drep; in the case "proposeUC" or "proposeInfo", TRUE; in the case
\*   "voteCC", v.props and there exists a k in Colds such that v.hot[k]
\*   equals "h" and not v.resigned[k]; in the case "voteDRep", v.props
\*   and v.drep; in the case "withdraw", v.deleg equals "d"; otherwise
\*   (kind is a pair), v.member[kind[2]] and not v.resigned[kind[2]]."
Pre(v, kind) ==
    CASE kind[1] = "regDRep"     -> ~v.drep
      [] kind[1] = "unregDRep"   -> v.drep
      [] kind[1] = "delegVote"   -> v.drep
      [] kind[1] = "proposeUC"   -> TRUE
      [] kind[1] = "proposeInfo" -> TRUE
      [] kind[1] = "voteCC"      -> v.props /\ \E k \in Colds :
                                    v.hot[k] = "h" /\ ~v.resigned[k]
      [] kind[1] = "voteDRep"    -> v.props /\ v.drep
      [] kind[1] = "withdraw"    -> v.deleg = "d"
      [] OTHER                -> v.member[kind[2]] /\ ~v.resigned[kind[2]]

\* In English: "A transaction is accepted when it is phase-2-invalid (it
\* only pays collateral) or its rules hold."
\* Literally: "Accepts of v and tx is defined as: not tx.valid, or Pre of
\*   v and tx.kind."
Accepts(v, tx) == ~tx.valid \/ Pre(v, tx.kind)

\* The reference's state change for an accepted valid transaction [L3].
\* Votes and withdrawals change nothing another transaction in the block
\* can see (balances and DRep expiry are not modelled).
\* In English: "Register and unregister flip the DRep (unregistering also
\* clears the delegation to it); delegate sets the delegation; an
\* UpdateCommittee proposal names k2 and makes a proposal to vote on; an
\* Info proposal only makes one to vote on; authorize sets the hot key;
\* resign clears it and marks the credential resigned."
\* Literally: "RefApply of st and kind is defined as: in the case kind
\*   equals "regDRep", st with drep set to TRUE; in the case "unregDRep",
\*   st with drep set to FALSE and deleg set to "none"; in the case
\*   "delegVote", st with deleg set to "d"; in the case "proposeUC", st
\*   with proposed set to its old value united with {"k2"} and props set
\*   to TRUE; in the case "proposeInfo", st with props set to TRUE; in the
\*   case kind[1] equals "auth", st with hot[kind[2]] set to "h"; in the
\*   case kind[1] equals "resign", st with hot[kind[2]] set to "none" and
\*   resigned[kind[2]] set to TRUE; otherwise st."
RefApply(st, kind) ==
    CASE kind[1] = "regDRep"     -> [st EXCEPT !.drep = TRUE]
      [] kind[1] = "unregDRep"   -> [st EXCEPT !.drep = FALSE, !.deleg = "none"]
      [] kind[1] = "delegVote"   -> [st EXCEPT !.deleg = "d"]
      [] kind[1] = "proposeUC"   -> [st EXCEPT !.proposed = @ \cup {"k2"},
                                            !.props = TRUE]
      [] kind[1] = "proposeInfo" -> [st EXCEPT !.props = TRUE]
      [] kind[1] = "auth" ->
             [st EXCEPT !.hot[kind[2]] = "h"]
      [] kind[1] = "resign" ->
             [st EXCEPT !.hot[kind[2]] = "none", !.resigned[kind[2]] = TRUE]
      [] OTHER                -> st

\* gOuroboros' overlay, field for field as BlockLedgerState keeps it: a
\* certificate counter (seq); the DRep's entry (touched, registration, the
\* counter value of its latest deregistration); the account's entry
\* (touched, delegation, the counter value it was made at); the proposals
\* (any, and the cold credentials UpdateCommittee proposals name); and each
\* cold credential's committee entry ("untouched", "h", "resigned").
\* In English: "The empty overlay a fresh BlockLedgerState starts with."
\* Literally: "EmptyOverlay is defined as the record whose field seq is 0,
\*   drepTouched is FALSE, drep is FALSE, deregSeq is 0, acctTouched is
\*   FALSE, deleg is "none", delegSeq is 0, props is FALSE, proposed is the
\*   empty set, and cc is the function from Colds giving "untouched"."
EmptyOverlay == [seq |-> 0, drepTouched |-> FALSE, drep |-> FALSE,
                 deregSeq |-> 0, acctTouched |-> FALSE, deleg |-> "none",
                 delegSeq |-> 0, props |-> FALSE, proposed |-> {},
                 cc |-> [k \in Colds |-> "untouched"]]

\* In English: "Certificates are the actions that bump the counter
\* (applyCertificate's b.seq++)."
\* Literally: "Certs is defined as the union of the pairs <<op, "-">> for
\*   every op in the set containing "regDRep", "unregDRep" and "delegVote"
\*   with the pairs <<"auth", k>>
\*   and <<"resign", k>> for every k in Colds."
Certs == {<<op, "-">> : op \in {"regDRep", "unregDRep", "delegVote"}}
         \cup {<<"auth", k>> : k \in Colds} \cup {<<"resign", k>> : k \in Colds}

\* gOuroboros' ApplyTransaction for an accepted valid transaction, as
\* applyCertificate and applyLevel write the maps.
\* In English: "Each certificate bumps the counter. Register sets the DRep
\* entry; unregister clears it and stamps the deregistration with the
\* counter; delegate sets the account entry, stamped with the counter;
\* proposals are recorded, an UpdateCommittee one with the credential it
\* names; authorize and resign set the committee entry."
\* Literally: "GoApply of ov and kind is defined as: let o be ov with seq
\*   increased by 1 if kind is a member of Certs, and s be o.seq; then in
\*   the case kind[1] equals "regDRep", o with drepTouched TRUE and drep TRUE;
\*   "unregDRep", o with drepTouched TRUE, drep FALSE and deregSeq s;
\*   "delegVote", o with acctTouched TRUE, deleg "d" and delegSeq s;
\*   "proposeUC", o with props TRUE and proposed united with {"k2"};
\*   "proposeInfo", o with props TRUE; an "auth" pair, o with cc[kind[2]]
\*   set to "h"; a "resign" pair, o with cc[kind[2]] set to "resigned";
\*   otherwise o."
GoApply(ov, kind) ==
    LET o == IF kind \in Certs THEN [ov EXCEPT !.seq = @ + 1] ELSE ov
        s == o.seq
    IN CASE kind[1] = "regDRep"   -> [o EXCEPT !.drepTouched = TRUE, !.drep = TRUE]
         [] kind[1] = "unregDRep" -> [o EXCEPT !.drepTouched = TRUE, !.drep = FALSE,
                                            !.deregSeq = s]
         [] kind[1] = "delegVote" -> [o EXCEPT !.acctTouched = TRUE, !.deleg = "d",
                                            !.delegSeq = s]
         [] kind[1] = "proposeUC" -> [o EXCEPT !.props = TRUE,
                                            !.proposed = @ \cup {"k2"}]
         [] kind[1] = "proposeInfo" -> [o EXCEPT !.props = TRUE]
         [] kind[1] = "auth" ->
                [o EXCEPT !.cc[kind[2]] = "h"]
         [] kind[1] = "resign" ->
                [o EXCEPT !.cc[kind[2]] = "resigned"]
         [] OTHER -> o

\* What gOuroboros answers, given the overlay and the wrapped state. The
\* wrapped state is the caller's ledger after the previous block; the
\* caller contract (README) is that it answers each question as the
\* reference state would, including potential members from stored
\* proposals.
\* In English: "DRepRegistration: the overlay's entry if touched, else the
\* base. DRepDelegation: the overlay's entry if touched, else the base's,
\* cleared when the DRep was deregistered after it was made (unless the
\* noDeregClear mistake). GovActionExists: either side. Committee member:
\* the base's, or (with the fix) one an in-block UpdateCommittee proposal
\* names. Hot key and resignation: the overlay's entry if touched, else
\* the base's."
\* Literally: "GoView of ov and base is defined as: let bv be RefView of
\*   base, d be (if ov.acctTouched then ov.deleg else bv.deleg), made be
\*   (if ov.acctTouched then ov.delegSeq else 0); then the record whose
\*   drep is (if ov.drepTouched then ov.drep else bv.drep); deleg is "none"
\*   if d equals "d" and ov.drepTouched and ov.deregSeq is greater than
\*   made and Mutation is not "noDeregClear", else d; props is bv.props or
\*   ov.props; member is the function from Colds giving bv.member[k] or
\*   (GoProposedMember and k is a member of ov.proposed); hot is the
\*   function giving bv.hot[k] if ov.cc[k] equals "untouched", "h" if it
\*   equals "h", else "none"; resigned is the function giving
\*   bv.resigned[k] if ov.cc[k] equals "untouched", else whether ov.cc[k]
\*   equals "resigned"."
GoView(ov, base) ==
    LET bv   == RefView(base)
        d    == IF ov.acctTouched THEN ov.deleg ELSE bv.deleg
        made == IF ov.acctTouched THEN ov.delegSeq ELSE 0
    IN [drep  |-> IF ov.drepTouched THEN ov.drep ELSE bv.drep,
        deleg |-> IF d = "d" /\ ov.drepTouched /\ ov.deregSeq > made
                     /\ Mutation # "noDeregClear"
                  THEN "none" ELSE d,
        props |-> bv.props \/ ov.props,
        member |-> [k \in Colds |->
                      bv.member[k] \/ (GoProposedMember /\ k \in ov.proposed)],
        hot |-> [k \in Colds |->
                   IF ov.cc[k] = "untouched" THEN bv.hot[k]
                   ELSE IF ov.cc[k] = "h" THEN "h" ELSE "none"],
        resigned |-> [k \in Colds |->
                        IF ov.cc[k] = "untouched" THEN bv.resigned[k]
                        ELSE ov.cc[k] = "resigned"]]

VARIABLES
    blk,        \* the block being validated, 1..Blocks; Blocks+1 when done
    n,          \* how many of its transactions have been applied
    committed,  \* the ledger after the previous accepted block
    ref,        \* the reference state after this block's applied transactions
    ov,         \* gOuroboros' BlockLedgerState overlay for this block
    last,       \* the last transaction looked at, or NoTx
    refOk,      \* the reference's verdict on it
    goOk,       \* gOuroboros' verdict on it
    goBefore,   \* gOuroboros' view before it
    sawInBlockAuth, \* an accepted authorization relied on an in-block proposal
    sawRejected     \* some block was rejected

\* The placeholder for "no transaction looked at yet".
\* Literally: "NoTx is defined as the record whose field kind is
\*   <<"none", "-">> and whose field valid is TRUE."
NoTx == [kind |-> <<"none", "-">>, valid |-> TRUE]

vars == <<blk, n, committed, ref, ov, last, refOk, goOk, goBefore,
          sawInBlockAuth, sawRejected>>

\* In English: "Validation starts at the first block, on the genesis
\* ledger, with an empty overlay and nothing looked at."
\* Literally: "Init is defined as: blk equals 1 and n equals 0 and committed
\*   equals Genesis and ref equals Genesis and ov equals EmptyOverlay and
\*   last equals NoTx and refOk equals TRUE and goOk equals TRUE and
\*   goBefore equals GoView of EmptyOverlay and Genesis and sawInBlockAuth
\*   equals FALSE and sawRejected equals FALSE."
Init ==
    /\ blk = 1
    /\ n = 0
    /\ committed = Genesis
    /\ ref = Genesis
    /\ ov = EmptyOverlay
    /\ last = NoTx
    /\ refOk = TRUE
    /\ goOk = TRUE
    /\ goBefore = GoView(EmptyOverlay, Genesis)
    /\ sawInBlockAuth = FALSE
    /\ sawRejected = FALSE

\* The overlay the next block starts with: a fresh one, as
\* verifyBlockTransactions makes per call, unless the reuseOverlay mistake
\* carries the old one over.
\* Literally: "NextOverlay is defined as: if Mutation equals
\*   "reuseOverlay" then ov else EmptyOverlay."
NextOverlay == IF Mutation = "reuseOverlay" THEN ov ELSE EmptyOverlay

\* Apply the next transaction. Both sides judge it against their own view.
\* If the reference accepts, both apply it (gOuroboros' overlay only when
\* it is valid, unless the leakInvalid mistake); if the reference rejects,
\* the block is rejected whole and the committed ledger stays [L6].
\* In English: "Pick any transaction; record both verdicts; on acceptance,
\* apply it to the reference state and the overlay; on rejection, move to
\* the next block from the unchanged committed ledger."
\* Literally: "Step is defined as: blk is at most Blocks and n is less than
\*   MaxTxs and there exists a tx in Txs such that, letting rv be RefView
\*   of ref and gv be GoView of ov and committed and ok be Accepts of rv
\*   and tx: last' equals tx, refOk' equals ok, goOk' equals Accepts of gv
\*   and tx, goBefore' equals gv, sawInBlockAuth' is its old value or
\*   (ok and tx.valid and tx.kind is <<"auth", "k2">> and "k2" is a
\*   member of ref.proposed but not of committed.proposed); and if ok then
\*   n' is n+1, ref' is (RefApply of ref and tx.kind if tx.valid, else
\*   ref), ov' is (GoApply of ov and tx.kind if tx.valid or Mutation is
\*   "leakInvalid", else ov), and blk, committed and sawRejected are
\*   unchanged; else blk' is blk+1, n' is 0, ref' is committed, ov' is
\*   NextOverlay, sawRejected' is TRUE, and committed is unchanged."
Step ==
    /\ blk <= Blocks
    /\ n < MaxTxs
    /\ \E tx \in Txs :
        LET rv == RefView(ref)
            gv == GoView(ov, committed)
            ok == Accepts(rv, tx)
        IN /\ last' = tx
           /\ refOk' = ok
           /\ goOk' = Accepts(gv, tx)
           /\ goBefore' = gv
           /\ sawInBlockAuth' = (sawInBlockAuth \/
                 (ok /\ tx.valid /\ tx.kind = <<"auth", "k2">>
                     /\ "k2" \in ref.proposed
                     /\ "k2" \notin committed.proposed))
           /\ IF ok
              THEN /\ n' = n + 1
                   /\ ref' = IF tx.valid THEN RefApply(ref, tx.kind) ELSE ref
                   /\ ov' = IF tx.valid \/ Mutation = "leakInvalid"
                            THEN GoApply(ov, tx.kind) ELSE ov
                   /\ UNCHANGED <<blk, committed, sawRejected>>
              ELSE /\ blk' = blk + 1
                   /\ n' = 0
                   /\ ref' = committed
                   /\ ov' = NextOverlay
                   /\ sawRejected' = TRUE
                   /\ UNCHANGED committed

\* The block ends after any number of accepted transactions: the caller
\* applies it, so the next block's wrapped state is the reference state.
\* In English: "Accept the block: commit the reference state, start the
\* next block with a fresh overlay."
\* Literally: "EndBlock is defined as: blk is at most Blocks and blk' equals
\*   blk+1 and n' equals 0 and committed' equals ref and ref' equals ref
\*   and ov' equals NextOverlay and last' equals NoTx and refOk' and
\*   goOk' are TRUE and goBefore' equals GoView of NextOverlay and ref,
\*   and sawInBlockAuth and sawRejected are unchanged."
EndBlock ==
    /\ blk <= Blocks
    /\ blk' = blk + 1
    /\ n' = 0
    /\ committed' = ref
    /\ ref' = ref
    /\ ov' = NextOverlay
    /\ last' = NoTx
    /\ refOk' = TRUE
    /\ goOk' = TRUE
    /\ goBefore' = GoView(NextOverlay, ref)
    /\ UNCHANGED <<sawInBlockAuth, sawRejected>>

\* In English: "After the last block nothing more happens."
\* Literally: "Done is defined as: blk is greater than Blocks and every
\*   variable is unchanged."
Done == blk > Blocks /\ UNCHANGED vars

\* Literally: "Next is defined as Step or EndBlock or Done."
Next == Step \/ EndBlock \/ Done

\* Literally: "Spec is defined as Init and always [Next] on vars."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants.

\* In English: "While a block is being validated, gOuroboros' view of the
\* ledger is the reference's state after the same transactions."
\* Literally: "OverlayMatches is defined as: blk is greater than Blocks, or
\*   GoView of ov and committed equals RefView of ref."
OverlayMatches == blk > Blocks \/ GoView(ov, committed) = RefView(ref)

\* In English: "gOuroboros accepts each transaction exactly when the
\* reference does."
\* Literally: "GoAgrees is defined as goOk equals refOk."
GoAgrees == goOk = refOk

\* In English: "A phase-2-invalid transaction that was accepted left
\* gOuroboros' view as it was."
\* Literally: "NoLeak is defined as: last equals NoTx, or last.valid, or
\*   not refOk, or blk is greater than Blocks, or GoView of ov and
\*   committed equals goBefore."
NoLeak == last = NoTx \/ last.valid \/ ~refOk \/ blk > Blocks
          \/ GoView(ov, committed) = goBefore

\* In English: "A block starts from the committed ledger alone: before its
\* first transaction gOuroboros' view is the committed state's."
\* Literally: "FreshOverlay is defined as: n is not 0, or blk is greater
\*   than Blocks, or GoView of ov and committed equals RefView of
\*   committed."
FreshOverlay == n # 0 \/ blk > Blocks
                \/ GoView(ov, committed) = RefView(committed)

\* Probes: each is expected to be violated, showing the case is reached.

\* In English: "No accepted authorization relies on a proposal made
\* earlier in the same block." Violated: the case the fix is about.
\* Literally: "ProbeInBlockAuth is defined as not sawInBlockAuth."
ProbeInBlockAuth == ~sawInBlockAuth

\* In English: "No block is ever rejected." Violated: rollback happens.
\* Literally: "ProbeRejected is defined as not sawRejected."
ProbeRejected == ~sawRejected

\* In English: "The delegation is never cleared by a deregistration in the
\* same block." Violated: the GOVCERT clearing path is reached.
\* Literally: "ProbeDeregClears is defined as: not (ov.acctTouched and
\*   ov.drepTouched and ov.deregSeq is greater than ov.delegSeq)."
ProbeDeregClears == ~(ov.acctTouched /\ ov.drepTouched
                      /\ ov.deregSeq > ov.delegSeq)
=============================================================================
