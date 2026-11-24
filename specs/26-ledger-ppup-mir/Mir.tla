--------------------------------- MODULE Mir ---------------------------------
(***************************************************************************)
(* Move instantaneous rewards (MIR) from Shelley to Babbage: the DELEG     *)
(* predicates on a MIR certificate, the genesis-delegate quorum that       *)
(* authorizes it, and the epoch-boundary MIR rule that pays it out.        *)
(*                                                                         *)
(* A MIR certificate draws from one pot, the reserves or the treasury, and *)
(* either credits stake credentials with deltas or (from Alonzo) moves     *)
(* coin to the other pot. The ledger accumulates the credits in            *)
(* InstantaneousRewards during the epoch and pays them at the boundary.    *)
(* Before Alonzo a credential's new delta replaces its pending amount and  *)
(* must not be negative; from Alonzo deltas add up, may be negative, and   *)
(* the pending amount must stay non-negative. The credits may not exceed   *)
(* the pot (plus its pending transfers, from Alonzo). A certificate must   *)
(* come before the last StabilityWindow slots of the epoch. Conway removed *)
(* the certificate.                                                        *)
(*                                                                         *)
(* The model has two halves: the ledger as the specification and the      *)
(* reference define it, and what gOuroboros decides for the same           *)
(* transactions. gOuroboros does not hold the pots or the pending rewards: *)
(* the caller (Dingo) reports them, and gOuroboros recomputes the checks   *)
(* from totals and per-credential pending amounts. The model assumes the   *)
(* caller reports them faithfully.                                         *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   Specification (eras/shelley/formal-spec/):                            *)
(*   [S1] delegation.tex 584-670: Deleg-Mir: the slot deadline, the right  *)
(*        override of pending credits, the pot bound, non-negative deltas. *)
(*   [S2] utxo.tex 540-549: UTXOW: a transaction with a MIR certificate    *)
(*        needs |genSig| >= Quorum (the spec adds d > 0; the reference     *)
(*        does not check it).                                              *)
(*   Reference implementation (eras/shelley/impl/src/Cardano/Ledger/):     *)
(*   [R1] Shelley/Rules/Deleg.hs 374-421: the MIR case of                  *)
(*        delegationTransition, both eras' branches.                       *)
(*   [R2] Shelley/Rules/Deleg.hs 426-468: checkSlotNotTooLate (one          *)
(*        stabilityWindow) and updateReservesAndTreasury.                  *)
(*   [R3] Shelley/LedgerState/NewEpochState.hs 38-42: availableAfterMIR.   *)
(*   [R4] Shelley/Era.hs 241-244: hardforkAlonzoAllowMIRTransfer, major>4. *)
(*   [R5] Shelley/Rules/Utxow.hs 460-482: validateMIRInsufficientGenesisSigs*)
(*        called from Shelley, Alonzo (Utxow.hs 366-371) and Babbage       *)
(*        (Utxow.hs 311-316) UTXOW, for every transaction.                 *)
(*   [R6] Shelley/Rules/Mir.hs 97-157: the boundary pays registered        *)
(*        credentials if both pots cover them, else pays nothing; either   *)
(*        way the pending rewards are cleared.                             *)
(*   [R7] Alonzo LEDGER runs DELEGS only for an IsValid true transaction.  *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 756a9a89):              *)
(*   [G1] ledger/shelley/rules.go validateMirCertificates 995-1192,        *)
(*        validateMirNotTooLate 1196-1218.                                 *)
(*   [G2] ledger/common/rules.go ValidateMIRGenesisQuorum 1040-1089.        *)
(*   [G3] ledger/alonzo/rules.go 239-242, ledger/babbage/rules.go 246-249: *)
(*        the quorum rule is in the phase-2-valid-only group.              *)
(*   [G4] ledger/conway/conway.go validateConwayCertificateTypes 153-168.  *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla and the   *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets   \* Integers: deltas may be negative

CONSTANTS
    Creds,          \* the stake credentials, e.g. {"c1", "c2"}
    Registered,     \* the credentials with a registered reward account
    StartReserves,  \* the reserves at the start
    StartTreasury,  \* the treasury at the start
    MaxDelta,       \* the largest reward delta a certificate may carry
    Amounts,        \* the coin a pot-to-pot transfer may move
    Quorum,         \* updateQuorum from Shelley genesis
    Sigs,           \* how many genesis delegates may sign a transaction
    EpochLength,    \* slots per epoch
    Window,         \* StabilityWindow, in slots
    MaxEpoch,       \* the last epoch the model runs to
    Era,            \* "Mary" (before the Alonzo hard fork), "Alonzo", "Conway"
    GoQuorumFixed,  \* TRUE: gOuroboros checks the quorum for IsValid false
    Mutation        \* "none", or a deliberate break that proves an invariant
                    \* can fail: "NoNegCheck", "NoPotCheck",
                    \* "TransferIgnoresIR", "LateMir", "NoQuorum"

\* A config file cannot write a negative number, so the deltas are built
\* here: one negative delta and every positive one up to MaxDelta.
\* In English: "Deltas is -1 and 1 through MaxDelta."
\* Literally: "Deltas is defined as -1 through MaxDelta without the members
\*   of the set containing 0."
Deltas == (-1)..MaxDelta \ {0}

\* The two pots a certificate draws from (the wire's 0 and 1).
\* In English: "Pots is the reserves and the treasury."
\* Literally: "Pots is defined as the set containing "reserves" and
\*   "treasury"."
Pots == {"reserves", "treasury"}

\* In English: "The pot that is not p."
\* Literally: "Other of p is defined as: if p equals "reserves" then
\*   "treasury", else "reserves"."
Other(p) == IF p = "reserves" THEN "treasury" ELSE "reserves"

\* [R4]: from the Alonzo hard fork deltas add, may be negative, and a
\* pot-to-pot transfer is allowed.
\* In English: "The era is at or after the Alonzo hard fork."
\* Literally: "Alonzo is defined as Era equals "Alonzo"."
Alonzo == Era = "Alonzo"

\* In English: "The sum of f over the members of S."
\* Literally: "SumOver of f and S is defined recursively as: if S equals the
\*   empty set then 0, else letting x be the x, chosen from S, such that
\*   TRUE: f of x plus SumOver of f and S without the members of the set
\*   containing x."
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE      \* any member; the order is irrelevant
         IN  f[x] + SumOver(f, S \ {x})

\* The slot at which the model stops.
\* In English: "The last slot of the last epoch."
\* Literally: "LastSlot is defined as MaxEpoch plus 1, times EpochLength,
\*   minus 1."
LastSlot == (MaxEpoch + 1) * EpochLength - 1

\* In English: "All the ada, which no step may change."
\* Literally: "Total is defined as StartReserves plus StartTreasury."
Total == StartReserves + StartTreasury

VARIABLES
    slot,           \* the current slot
    pot,            \* pot[p]: the reserves and the treasury
    ir,             \* ir[p][c]: pending credit for c from pot p (iRReserves, iRTreasury)
    dpot,           \* dpot[p]: pending transfer into pot p (deltaReserves, deltaTreasury)
    rewards,        \* rewards[c]: the reward account balances
    submitted,      \* a transaction was already made in this slot
    goMismatch,     \* gOuroboros once decided a transaction differently
    unauthorized,   \* the ledger once accepted a MIR without a quorum
    lateMir,        \* the ledger once applied a MIR at or after the deadline
    paidUnregistered \* probe: a credit to an unregistered credential was dropped

\* In English: "All the variables, so a step can say none of them changed."
\* Literally: "vars is defined as the tuple of every variable above."
vars == <<slot, pot, ir, dpot, rewards, submitted, goMismatch,
          unauthorized, lateMir, paidUnregistered>>

\* In English: "The epoch the current slot is in."
\* Literally: "Epoch is defined as slot integer-divided by EpochLength."
Epoch == slot \div EpochLength

\* [R2] checkSlotNotTooLate: firstSlot(next epoch) - stabilityWindow.
\* In English: "The first slot at which a MIR certificate is too late."
\* Literally: "Cutoff is defined as: letting next be Epoch plus 1, times
\*   EpochLength: if next is greater than Window then next minus Window,
\*   else 0."
Cutoff ==
    LET next == (Epoch + 1) * EpochLength    \* first slot of the next epoch
    IN  IF next > Window THEN next - Window ELSE 0

\* In English: "Every variable holds a value of the kind it should."
\* Literally: "TypeOK is defined as: slot is a member of 0 through LastSlot,
\*   and each other variable is a member of the set written beside it."
TypeOK ==
    /\ slot \in 0..LastSlot
    /\ pot \in [Pots -> Int]
    /\ ir \in [Pots -> [Creds -> Int]]
    /\ dpot \in [Pots -> Int]
    /\ rewards \in [Creds -> Nat]
    /\ submitted \in BOOLEAN
    /\ goMismatch \in BOOLEAN
    /\ unauthorized \in BOOLEAN
    /\ lateMir \in BOOLEAN
    /\ paidUnregistered \in BOOLEAN

\* In English: "At the start nothing is proposed or pending, and no
\* disagreement or violation has been seen."
\* Literally: "Init is defined as: slot equals 0, and each other variable
\*   equals the value written beside it."
Init ==
    /\ slot = 0
    /\ pot = [p \in Pots |-> IF p = "reserves" THEN StartReserves ELSE StartTreasury]
    /\ ir = [p \in Pots |-> [c \in Creds |-> 0]]
    /\ dpot = [p \in Pots |-> 0]
    /\ rewards = [c \in Creds |-> 0]
    /\ submitted = FALSE
    /\ goMismatch = FALSE
    /\ unauthorized = FALSE
    /\ lateMir = FALSE
    /\ paidUnregistered = FALSE

(***************************************************************************)
(* Half 1: the ledger [S1][S2][R1]-[R7].                                   *)
(***************************************************************************)

\* A transaction carries one MIR certificate:
\*   kind "stake": credit c from pot p with delta d;
\*   kind "transfer": move coin a from pot p to the other pot.
\* sigs is how many distinct genesis delegates signed it; valid is IsValid.

\* [R6] availableAfterMIR, [R1]: the pot plus its pending transfers.
\* In English: "What pot p can pay: its balance plus pending transfers in."
\* Literally: "Avail of p is defined as pot of p plus dpot of p."
Avail(p) == pot[p] + dpot[p]

\* [R1] the pending credits after a stake certificate: before Alonzo the new
\* delta replaces the old one (Map.union, left-biased on the certificate);
\* from Alonzo it is added (Map.unionWith (<>)).
\* In English: "Pot p's pending credits after crediting c with d."
\* Literally: "Combined of p, c and d is defined as ir of p except that its c
\*   entry is: if Alonzo then the old entry plus d, else d."
Combined(p, c, d) == [ir[p] EXCEPT ![c] = IF Alonzo THEN @ + d ELSE d]

\* [R1] the stake branch: MIRNegativesNotCurrentlyAllowed before Alonzo,
\* MIRProducesNegativeUpdate from Alonzo, then InsufficientForInstantaneous-
\* RewardsDELEG against the pot (from Alonzo, the pot plus its transfers).
\* In English: "The ledger's DELEG rule accepts crediting c with d from p."
\* Literally: "RefStakeOk of p, c and d is defined as: (Alonzo, or d is at
\*   least 0) and (Mutation equals "NoNegCheck", or Alonzo is not true, or
\*   for all x in Creds, Combined of p, c and d of x is at least 0) and
\*   (Mutation equals "NoPotCheck", or SumOver of Combined of p, c and d and
\*   Creds is at most: if Alonzo then Avail of p, else pot of p)."
RefStakeOk(p, c, d) ==
    /\ Alonzo \/ d >= 0                                   \* pre-Alonzo sign
    /\ Mutation = "NoNegCheck" \/ ~Alonzo \/              \* Alonzo: pending >= 0
         \A x \in Creds : Combined(p, c, d)[x] >= 0
    /\ Mutation = "NoPotCheck" \/                          \* the pot bound
         SumOver(Combined(p, c, d), Creds) <= (IF Alonzo THEN Avail(p) ELSE pot[p])

\* [R1][R3] the transfer branch: not allowed before Alonzo
\* (MIRTransferNotCurrentlyAllowed); from Alonzo bounded by the pot, its
\* transfers and its pending credits (InsufficientForTransferDELEG).
\* In English: "The ledger accepts moving a from pot p."
\* Literally: "RefTransferOk of p and a is defined as: Alonzo, and a is at
\*   most Avail of p minus (if Mutation equals "TransferIgnoresIR" then 0,
\*   else SumOver of ir of p and Creds)."
RefTransferOk(p, a) ==
    /\ Alonzo
    /\ a <= Avail(p) - (IF Mutation = "TransferIgnoresIR" THEN 0
                        ELSE SumOver(ir[p], Creds))

\* In English: "The ledger accepts the transaction: the era has MIR, the
\* quorum signed it (UTXOW, every transaction), and, unless it is IsValid
\* false, the deadline and the branch's predicates hold."
\* Literally: "RefOk of kind, p, c, d, a, sigs and valid is defined as: Era
\*   does not equal "Conway", and (Mutation equals "NoQuorum" or sigs is at
\*   least Quorum), and (valid is not true, or (Mutation equals "LateMir"
\*   or slot is less than Cutoff) and (if kind equals "stake" then
\*   RefStakeOk of p, c and d, else RefTransferOk of p and a))."
RefOk(kind, p, c, d, a, sigs, valid) ==
    /\ Era /= "Conway"                                    \* [G4]: no MIR in Conway
    /\ Mutation = "NoQuorum" \/ sigs >= Quorum            \* [S2][R5]
    /\ \/ ~valid                                          \* [R7]: DELEGS skipped
       \/ /\ Mutation = "LateMir" \/ slot < Cutoff        \* [R2] deadline
          /\ IF kind = "stake" THEN RefStakeOk(p, c, d)
                               ELSE RefTransferOk(p, a)

(***************************************************************************)
(* Half 2: what gOuroboros decides [G1]-[G4].                              *)
(***************************************************************************)

\* [G1] works from totals: accumulated is the pot's pending credits, pending
\* the credential's own; before Alonzo the credential's pending amount is
\* replaced, so it is subtracted (replaced) before adding the new delta.
\* In English: "gOuroboros's stake-branch check."
\* Literally: "GoStakeOk of p, c and d is defined as: letting acc be SumOver
\*   of ir of p and Creds, and pend be ir of p of c: if Alonzo then (pend
\*   plus d is at least 0 and acc plus d is at most Avail of p), else (d is
\*   at least 0 and acc minus pend plus d is at most pot of p)."
GoStakeOk(p, c, d) ==
    LET acc  == SumOver(ir[p], Creds)     \* InstantaneousRewardsTotal
        pend == ir[p][c]                  \* PendingInstantaneousRewards
    IN  IF Alonzo
        THEN pend + d >= 0 /\ acc + d <= Avail(p)
        ELSE d >= 0 /\ acc - pend + d <= pot[p]

\* In English: "gOuroboros's transfer-branch check."
\* Literally: "GoTransferOk of p and a is defined as: Alonzo, and a is at
\*   most Avail of p minus SumOver of ir of p and Creds."
GoTransferOk(p, a) == Alonzo /\ a <= Avail(p) - SumOver(ir[p], Creds)

\* [G3]: today the quorum rule sits with DELEG in the phase-2-valid-only
\* group, so it is skipped for an IsValid false transaction.
\* In English: "gOuroboros checks the quorum on this transaction."
\* Literally: "GoChecksQuorum of valid is defined as: valid, or
\*   GoQuorumFixed."
GoChecksQuorum(valid) == valid \/ GoQuorumFixed

\* In English: "gOuroboros accepts the transaction."
\* Literally: "GoOk of kind, p, c, d, a, sigs and valid is defined as: Era
\*   does not equal "Conway", and (GoChecksQuorum of valid is not true or
\*   sigs is at least Quorum), and (valid is not true, or slot is less than
\*   Cutoff and (if kind equals "stake" then GoStakeOk of p, c and d, else
\*   GoTransferOk of p and a))."
GoOk(kind, p, c, d, a, sigs, valid) ==
    /\ Era /= "Conway"
    /\ ~GoChecksQuorum(valid) \/ sigs >= Quorum
    /\ \/ ~valid
       \/ /\ slot < Cutoff
          /\ IF kind = "stake" THEN GoStakeOk(p, c, d)
                               ELSE GoTransferOk(p, a)

(***************************************************************************)
(* Steps.                                                                  *)
(***************************************************************************)

\* In English: "A transaction with one MIR certificate is submitted; the
\* ledger and gOuroboros each decide, and the ledger's decision takes
\* effect. An IsValid false transaction changes no MIR state."
\* Literally: "Submit of kind, p, c, d, a, sigs and valid is defined as:
\*   submitted is not true, submitted in the next state is TRUE, goMismatch
\*   in the next state is goMismatch or GoOk does not equal RefOk, and:
\*   letting ok be RefOk and valid: if ok then (if kind equals "stake" then
\*   ir in the next state is ir except that its p entry is Combined of p, c
\*   and d, and dpot is unchanged, else dpot in the next state is dpot
\*   except that its p entry is the old entry minus a and its Other of p
\*   entry is the old entry plus a, and ir is unchanged), and unauthorized
\*   in the next state is unauthorized or sigs is less than Quorum, and
\*   lateMir in the next state is lateMir or slot is at least Cutoff; else
\*   ir, dpot, unauthorized and lateMir are unchanged; and slot, pot,
\*   rewards and paidUnregistered are unchanged."
Submit(kind, p, c, d, a, sigs, valid) ==
    /\ ~submitted                                         \* one tx per slot
    /\ submitted' = TRUE
    /\ goMismatch' = (goMismatch \/
            GoOk(kind, p, c, d, a, sigs, valid) /= RefOk(kind, p, c, d, a, sigs, valid))
    /\ LET ok == RefOk(kind, p, c, d, a, sigs, valid) /\ valid
       IN  IF ok
           THEN /\ IF kind = "stake"
                   THEN /\ ir' = [ir EXCEPT ![p] = Combined(p, c, d)]
                        /\ UNCHANGED dpot
                   ELSE /\ dpot' = [dpot EXCEPT ![p] = @ - a, ![Other(p)] = @ + a]
                        /\ UNCHANGED ir
                /\ unauthorized' = (unauthorized \/ sigs < Quorum)
                /\ lateMir' = (lateMir \/ slot >= Cutoff)
           ELSE UNCHANGED <<ir, dpot, unauthorized, lateMir>>
    /\ UNCHANGED <<slot, pot, rewards, paidUnregistered>>

\* [R6] the boundary credits only registered credentials.
\* In English: "Pot p's pending credits to registered credentials."
\* Literally: "Owed of p is defined as SumOver of ir of p and Registered."
Owed(p) == SumOver(ir[p], Registered)

\* In English: "Time moves on one slot; at an epoch boundary the pending
\* credits are paid to registered credentials if both pots cover them, and
\* the pending state is cleared either way."
\* Literally: "Tick is defined as: slot is less than LastSlot, slot in the
\*   next state equals slot plus 1, submitted in the next state is FALSE,
\*   and: if slot plus 1 modulo EpochLength equals 0 then (letting fits be:
\*   for all p in Pots, Owed of p is at most Avail of p: pot in the next
\*   state is (if fits then the function that maps every p in Pots to Avail
\*   of p minus Owed of p, else pot), rewards in the next state is (if fits
\*   then the function that maps every x in Creds to rewards of x plus (if x
\*   is a member of Registered then the sum over Pots of ir of q of x, else
\*   0), else rewards), ir and dpot in the next state are all zero, and
\*   paidUnregistered in the next state is paidUnregistered or there exists
\*   an x in Creds without the members of Registered and a q in Pots such
\*   that ir of q of x does not equal 0), else pot, rewards, ir, dpot and
\*   paidUnregistered are unchanged; and goMismatch, unauthorized and
\*   lateMir are unchanged."
Tick ==
    /\ slot < LastSlot
    /\ slot' = slot + 1
    /\ submitted' = FALSE
    /\ IF (slot + 1) % EpochLength = 0
       THEN LET fits == \A p \in Pots : Owed(p) <= Avail(p)     \* [R6]
            IN  /\ pot' = IF fits THEN [p \in Pots |-> Avail(p) - Owed(p)]
                          ELSE pot
                /\ rewards' = IF fits
                              THEN [x \in Creds |-> rewards[x] +
                                      IF x \in Registered
                                      THEN ir["reserves"][x] + ir["treasury"][x]
                                      ELSE 0]
                              ELSE rewards
                /\ ir' = [p \in Pots |-> [x \in Creds |-> 0]]   \* cleared
                /\ dpot' = [p \in Pots |-> 0]
                /\ paidUnregistered' = (paidUnregistered \/
                        \E x \in Creds \ Registered, q \in Pots : ir[q][x] /= 0)
       ELSE UNCHANGED <<pot, rewards, ir, dpot, paidUnregistered>>
    /\ UNCHANGED <<goMismatch, unauthorized, lateMir>>

\* In English: "At the last slot the model stops; this stutter step keeps
\* TLC from reporting the stop as a deadlock."
\* Literally: "Done is defined as slot equals LastSlot and vars is unchanged."
Done == slot = LastSlot /\ UNCHANGED vars

\* In English: "Some transaction is submitted, or time moves on, or the
\* model has stopped."
\* Literally: "Next is defined as: there exists a kind in the set containing
\*   "stake" and "transfer", a p in Pots, a c in Creds, a d in Deltas, an a
\*   in Amounts, a sigs in Sigs and a valid in (if Alonzo then BOOLEAN else
\*   the set containing TRUE) such that Submit of kind, p, c, d, a, sigs and
\*   valid; or Tick; or Done."
Next ==
    \/ \E kind \in {"stake", "transfer"}, p \in Pots, c \in Creds,
          d \in Deltas, a \in Amounts, sigs \in Sigs,
          valid \in (IF Alonzo THEN BOOLEAN ELSE {TRUE}) :
            Submit(kind, p, c, d, a, sigs, valid)
    \/ Tick
    \/ Done

\* In English: "Start in Init; every step is a Next step or changes nothing."
\* Literally: "Spec is defined as Init and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Questions.                                                              *)
(***************************************************************************)

\* In English: "No ada is created or destroyed."
\* Literally: "ValuePreserved is defined as: pot of "reserves" plus pot of
\*   "treasury" plus SumOver of rewards and Creds equals Total, and dpot of
\*   "reserves" plus dpot of "treasury" equals 0."
ValuePreserved ==
    /\ pot["reserves"] + pot["treasury"] + SumOver(rewards, Creds) = Total
    /\ dpot["reserves"] + dpot["treasury"] = 0

\* In English: "No pending credit is ever negative, so the boundary never
\* has to take ada out of a reward account."
\* Literally: "PendingNonNegative is defined as: for all p in Pots and x in
\*   Creds, ir of p of x is at least 0."
PendingNonNegative == \A p \in Pots, x \in Creds : ir[p][x] >= 0

\* In English: "Each pot can always cover its pending credits, so the
\* boundary's pay-nothing branch is never taken."
\* Literally: "WithinBudget is defined as: for all p in Pots, SumOver of ir
\*   of p and Creds is at most Avail of p."
WithinBudget == \A p \in Pots : SumOver(ir[p], Creds) <= Avail(p)

\* In English: "Every MIR the ledger applied had the quorum."
\* Literally: "QuorumHeld is defined as: unauthorized is not true."
QuorumHeld == ~unauthorized

\* In English: "No MIR was applied in the last StabilityWindow slots."
\* Literally: "BeforeCutoff is defined as: lateMir is not true."
BeforeCutoff == ~lateMir

\* In English: "In Conway nothing ever moves."
\* Literally: "NoMirInConway is defined as: if Era equals "Conway" then for
\*   all p in Pots, dpot of p equals 0 and for all x in Creds, ir of p of x
\*   equals 0."
NoMirInConway ==
    Era = "Conway" => \A p \in Pots : dpot[p] = 0 /\ \A x \in Creds : ir[p][x] = 0

\* In English: "gOuroboros accepts exactly the transactions the ledger
\* accepts."
\* Literally: "GoAgrees is defined as: goMismatch is not true."
GoAgrees == ~goMismatch

\* Reachability probes, violated when the situation is reachable.
\* In English: "No reward is ever paid."
\* Literally: "ProbeNoReward is defined as: for all x in Creds, rewards of x
\*   equals 0."
ProbeNoReward == \A x \in Creds : rewards[x] = 0

\* In English: "No pot-to-pot transfer is ever pending."
\* Literally: "ProbeNoTransfer is defined as: for all p in Pots, dpot of p
\*   equals 0."
ProbeNoTransfer == \A p \in Pots : dpot[p] = 0

\* In English: "A credit to an unregistered credential is never dropped."
\* Literally: "ProbeNoUnregisteredCredit is defined as: paidUnregistered is
\*   not true."
ProbeNoUnregisteredCredit == ~paidUnregistered

\* In English: "The reserves never fall below their start, so the boundary
\* never pays out of them."
\* Literally: "ProbeReservesUntouched is defined as pot of "reserves" is at
\*   least StartReserves."
ProbeReservesUntouched == pot["reserves"] >= StartReserves
=============================================================================
