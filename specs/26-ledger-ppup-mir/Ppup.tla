-------------------------------- MODULE Ppup --------------------------------
(***************************************************************************)
(* Shelley-to-Babbage protocol parameter update proposals (PPUP) and their *)
(* adoption at the epoch boundary (NEWPP inside UPEC).                     *)
(*                                                                         *)
(* A transaction may carry an update: a map from genesis keys to proposed  *)
(* parameter changes, and the epoch the proposal is for. Before the slot   *)
(* of no return (2 * StabilityWindow slots before the epoch ends) a        *)
(* proposal is for this epoch and joins the current proposals; after it,   *)
(* it is for the next epoch and joins the future proposals. At the epoch   *)
(* boundary, an update that at least Quorum genesis keys proposed with the *)
(* same value is adopted, and the future proposals become the current ones *)
(* if every protocol version they propose can follow the new parameters.   *)
(*                                                                         *)
(* The model has three halves:                                             *)
(*   1. The ledger as the specification and the reference define it.      *)
(*   2. What gOuroboros decides for the same transactions. gOuroboros      *)
(*      validates the transaction; it does not hold the proposals.         *)
(*   3. What Dingo adopts at the boundary. Dingo holds the proposals as    *)
(*      stored rows keyed by target epoch and picks the winner when the    *)
(*      epoch it was proposed for has ended.                               *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   Specification (eras/shelley/formal-spec/):                            *)
(*   [S1] update.tex 55-270: PP-Update-Empty, PP-Update-Current and        *)
(*        PP-Update-Future; pvCanFollow; the 2*StabilityWindow window.     *)
(*   [S2] epoch.tex 644-864: NEWPP, updatePpup and votedValue.             *)
(*   Reference implementation (eras/shelley/impl/src/Cardano/Ledger/):     *)
(*   [R1] Shelley/Rules/Ppup.hs 146-200: ppupTransitionNonEmpty. An update *)
(*        whose map is empty still has its target epoch checked.           *)
(*   [R2] Shelley/Rules/Ppup.hs 205-239: votedFuturePParams: exactly one   *)
(*        value with at least quorum votes.                                *)
(*   [R3] Shelley/Rules/Newpp.hs 88-110: updatePpup: future proposals      *)
(*        become current only if all of their versions can follow.        *)
(*   [R4] Shelley/PParams.hs 332-349: pvCanFollow, hasLegalProtVerUpdate.  *)
(*   [R5] libs/cardano-ledger-core/src/Cardano/Ledger/Slot.hs 106-114:     *)
(*        getTheSlotOfNoReturn = firstSlot(next epoch) - 2*stabilityWindow.*)
(*   [R6] eras/alonzo/impl/.../Alonzo/Rules/Utxos.hs 202-221 and           *)
(*        eras/babbage/impl/.../Babbage/Rules/Utxos.hs 165-191: PPUP runs  *)
(*        only for a phase-2-valid transaction (IsValid true).             *)
(*   [R7] Shelley/UTxO.hs 191-204: the delegate of each proposing genesis  *)
(*        key must witness the transaction (UTXOW, every transaction;      *)
(*        model 22 covers witnesses, so this model assumes they are there).*)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 756a9a89):              *)
(*   [G1] ledger/common/rules.go ValidateClassicProtocolParameterUpdates   *)
(*        1093-1197; protocolVersionCanFollow 1199-1208.                   *)
(*   [G2] ledger/alonzo/rules.go 198-243, ledger/babbage/rules.go 216-250: *)
(*        the PPUP rule is in the always-run group.                        *)
(* The Dingo code (commit 2fc7975d3): database/pparams_classic.go          *)
(*   selectClassicPParamUpdate 91-178, classicCarriedOverProposalsFollow   *)
(*   183-228; database/transaction.go 435: rows only for valid txs.        *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla and the   *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets   \* FiniteSets: Cardinality, for counting votes

CONSTANTS
    GenKeys,        \* the genesis keys, e.g. {"g1", "g2", "g3"}
    Outsider,       \* a key that is not a genesis key, e.g. "x"
    Quorum,         \* updateQuorum from Shelley genesis
    EpochLength,    \* slots per epoch
    NoReturn,       \* 2 * StabilityWindow, in slots
    MaxEpoch,       \* the last epoch the model runs to (keeps it finite)
    PhaseTwo,       \* TRUE: Alonzo or Babbage, where a tx may be IsValid false
    GoEmptyFixed,   \* TRUE: gOuroboros checks the epoch of an empty update
    GoPhase2Fixed,  \* TRUE: gOuroboros skips PPUP for an IsValid false tx
    Mutation        \* "none", or a deliberate break that proves an invariant
                    \* can fail: "QuorumOne", "NoCarryCheck", "LateIntoCurrent",
                    \* "AnyVersion", "NoGenesisCheck", "DingoNoCarryCheck"

\* Every key a transaction may name: the genesis keys and one outsider.
\* In English: "AllKeys is the genesis keys plus the outsider."
\* Literally: "AllKeys is defined as the union of GenKeys and the set
\*   containing Outsider."
AllKeys == GenKeys \cup {Outsider}

\* The updates a key can propose. All four set the same ordinary parameter
\* to "a"; "a21" also proposes protocol version 2.1, "a3" version 3.0 and
\* "a4" version 4.0.
\* In English: "Updates is the four proposals the model uses."
\* Literally: "Updates is defined as the set containing "a", "a21", "a3"
\*   and "a4"."
Updates == {"a", "a21", "a3", "a4"}

\* The marker for "this key has no proposal".
\* In English: "None stands for no proposal."
\* Literally: "None is defined as "none"."
None == "none"

\* A protocol version is a <<major, minor>> pair; NoPV marks an update that
\* proposes no version.
\* In English: "NoPV stands for no version proposed."
\* Literally: "NoPV is defined as the tuple of 0 and 0."
NoPV == <<0, 0>>

\* In English: "The version an update proposes: 2.1 for a21, 3.0 for a3,
\* 4.0 for a4, none for a."
\* Literally: "UpdPV of u is defined as: in the case u equals "a21", the
\*   tuple of 2 and 1; in the case u equals "a3", the tuple of 3 and 0; in
\*   the case u equals "a4", the tuple of 4 and 0; in every other case, NoPV."
UpdPV(u) == CASE u = "a21" -> <<2, 1>>
            []   u = "a3"  -> <<3, 0>>
            []   u = "a4"  -> <<4, 0>>
            []   OTHER    -> NoPV

\* [S1] pvCanFollow, [R4]: a major bump that resets the minor, or a minor bump.
\* In English: "Version n can follow version c if it is the next major with
\* minor 0, or the same major with the next minor."
\* Literally: "CanFollow of c and n is defined as: element 1 of n equals
\*   element 1 of c plus 1 and element 2 of n equals 0, or element 1 of n
\*   equals element 1 of c and element 2 of n equals element 2 of c plus 1."
CanFollow(c, n) ==
    \/ n[1] = c[1] + 1 /\ n[2] = 0      \* next major, minor reset
    \/ n[1] = c[1] /\ n[2] = c[2] + 1   \* same major, next minor

\* [R4] hasLegalProtVerUpdate: an update without a version is always legal.
\* In English: "Update u is legal against parameters p if it proposes no
\* version, or its version can follow p's."
\* Literally: "LegalPV of p and u is defined as: UpdPV of u equals NoPV, or
\*   CanFollow of p's pv and UpdPV of u."
LegalPV(p, u) ==
    \/ UpdPV(u) = NoPV                  \* no version: legal
    \/ CanFollow(p.pv, UpdPV(u))        \* a version that can follow

\* The parameters after an update: the ordinary parameter becomes "a", and
\* the version changes only if the update proposes one.
\* In English: "Apply(p, u) is p updated by u."
\* Literally: "Apply of p and u is defined as the record whose field v is
\*   "a" and whose field pv is: if UpdPV of u equals NoPV then p's pv, else
\*   UpdPV of u."
Apply(p, u) == [v  |-> "a",
                pv |-> IF UpdPV(u) = NoPV THEN p.pv ELSE UpdPV(u)]

\* The starting parameters: version 2.0, the ordinary parameter unset.
\* In English: "InitPP is version 2.0 with the parameter at its start value."
\* Literally: "InitPP is defined as the record whose field v is "init" and
\*   whose field pv is the tuple of 2 and 0."
InitPP == [v |-> "init", pv |-> <<2, 0>>]

\* A map with no proposals.
\* In English: "Empty maps every key to no proposal."
\* Literally: "Empty is defined as the function that maps every k in
\*   AllKeys to None."
Empty == [k \in AllKeys |-> None]

\* In English: "How many keys propose u in map m."
\* Literally: "Votes of m and u is defined as the number of members of the
\*   set of every k in AllKeys such that m of k equals u."
Votes(m, u) == Cardinality({k \in AllKeys : m[k] = u})

\* The quorum a value needs; the QuorumOne mutation lowers it to one.
\* In English: "The votes an update needs to be adopted."
\* Literally: "Need is defined as: if Mutation equals "QuorumOne" then 1,
\*   else Quorum."
Need == IF Mutation = "QuorumOne" THEN 1 ELSE Quorum

\* [S2] votedValue, [R2] votedFuturePParams: exactly one value must reach the
\* quorum; none, or two, adopt nothing.
\* In English: "The update to adopt from map m, or None."
\* Literally: "Winner of m is defined as: letting W be the set of every u in
\*   Updates such that Votes of m and u is at least Need: if the number of
\*   members of W equals 1 then the u, chosen from W, such that TRUE, else
\*   None."
Winner(m) ==
    LET W == {u \in Updates : Votes(m, u) >= Need}   \* values with quorum
    IN  IF Cardinality(W) = 1 THEN CHOOSE u \in W : TRUE ELSE None

\* The slot at which the model stops.
\* In English: "The last slot of the last epoch."
\* Literally: "LastSlot is defined as MaxEpoch plus 1, times EpochLength,
\*   minus 1."
LastSlot == (MaxEpoch + 1) * EpochLength - 1

VARIABLES
    slot,           \* the current slot
    pp,             \* the protocol parameters in force
    cur,            \* current proposals: key -> update (sgsCurProposals)
    fut,            \* future proposals (sgsFutureProposals)
    carriedKeys,    \* keys whose current proposal was carried over
    submitted,      \* a transaction was already made in this slot
    goMismatch,     \* gOuroboros once decided a transaction differently
    dCarried,       \* Dingo rows: late proposals for this epoch
    dInWin,         \* Dingo rows: in-window proposals for this epoch
    dLate,          \* Dingo rows: late proposals for the next epoch
    dingoMismatch,  \* Dingo once adopted something the ledger did not
    adoptVotes,     \* votes behind the last adoption (0: none adopted)
    pvOk,           \* every version change so far could follow
    lateCurWrite,   \* a current proposal was written after no return
    carriedDropped, \* probe: carried proposals were once discarded
    carriedAdopted  \* probe: a carried proposal was once adopted

\* In English: "All the variables, so a step can say none of them changed."
\* Literally: "vars is defined as the tuple of every variable above."
vars == <<slot, pp, cur, fut, carriedKeys, submitted, goMismatch,
          dCarried, dInWin, dLate, dingoMismatch, adoptVotes, pvOk,
          lateCurWrite, carriedDropped, carriedAdopted>>

\* In English: "The epoch the current slot is in."
\* Literally: "Epoch is defined as slot integer-divided by EpochLength."
Epoch == slot \div EpochLength

\* [R5] firstSlot(next epoch) - 2*stabilityWindow, saturating at zero.
\* In English: "The first slot whose proposals are for the next epoch."
\* Literally: "NoReturnSlot is defined as: letting next be Epoch plus 1,
\*   times EpochLength: if next is greater than NoReturn then next minus
\*   NoReturn, else 0."
NoReturnSlot ==
    LET next == (Epoch + 1) * EpochLength   \* first slot of the next epoch
    IN  IF next > NoReturn THEN next - NoReturn ELSE 0

\* In English: "The current slot is at or after the slot of no return."
\* Literally: "Late is defined as slot is at least NoReturnSlot."
Late == slot >= NoReturnSlot

\* In English: "Every variable holds a value of the kind it should."
\* Literally: "TypeOK is defined as: slot is a member of 0 through LastSlot,
\*   and each other variable is a member of the set written beside it."
TypeOK ==
    /\ slot \in 0..LastSlot
    /\ pp \in [v : {"init", "a"}, pv : {<<2, 0>>, <<2, 1>>, <<3, 0>>, <<4, 0>>}]
    /\ cur \in [AllKeys -> Updates \cup {None}]
    /\ fut \in [AllKeys -> Updates \cup {None}]
    /\ carriedKeys \subseteq AllKeys
    /\ submitted \in BOOLEAN
    /\ goMismatch \in BOOLEAN
    /\ dCarried \in [AllKeys -> Updates \cup {None}]
    /\ dInWin \in [AllKeys -> Updates \cup {None}]
    /\ dLate \in [AllKeys -> Updates \cup {None}]
    /\ dingoMismatch \in BOOLEAN
    /\ adoptVotes \in 0..Cardinality(AllKeys)
    /\ pvOk \in BOOLEAN
    /\ lateCurWrite \in BOOLEAN
    /\ carriedDropped \in BOOLEAN
    /\ carriedAdopted \in BOOLEAN

\* In English: "At the start nothing is proposed or pending, and no
\* disagreement or violation has been seen."
\* Literally: "Init is defined as: slot equals 0, and each other variable
\*   equals the value written beside it."
Init ==
    /\ slot = 0
    /\ pp = InitPP
    /\ cur = Empty
    /\ fut = Empty
    /\ carriedKeys = {}
    /\ submitted = FALSE
    /\ goMismatch = FALSE
    /\ dCarried = Empty
    /\ dInWin = Empty
    /\ dLate = Empty
    /\ dingoMismatch = FALSE
    /\ adoptVotes = 0
    /\ pvOk = TRUE
    /\ lateCurWrite = FALSE
    /\ carriedDropped = FALSE
    /\ carriedAdopted = FALSE

(***************************************************************************)
(* Half 1: the ledger's PPUP rule [S1][R1].                                *)
(***************************************************************************)

\* [R6]: from Alonzo, PPUP runs only for a phase-2-valid transaction; before
\* it every transaction is valid.
\* In English: "The ledger runs PPUP on this transaction."
\* Literally: "RefRunsPpup of valid is defined as: PhaseTwo is not true, or
\*   valid."
RefRunsPpup(valid) == ~PhaseTwo \/ valid

\* The three PPUP predicates. An empty map passes the first two vacuously,
\* but not the third [S1][R1].
\* In English: "The proposal names only genesis keys, proposes a version
\* that can follow, and targets the epoch the slot allows."
\* Literally: "PpupOk of keys, u and target is defined as: (Mutation equals
\*   "NoGenesisCheck", or keys is a subset of GenKeys) and (Mutation equals
\*   "AnyVersion", or keys equals the empty set, or LegalPV of pp and u) and
\*   target equals: if Late and Mutation does not equal "LateIntoCurrent"
\*   then Epoch plus 1, else Epoch."
PpupOk(keys, u, target) ==
    /\ Mutation = "NoGenesisCheck" \/ keys \subseteq GenKeys  \* NonGenesisUpdatePPUP
    /\ Mutation = "AnyVersion" \/ keys = {} \/ LegalPV(pp, u) \* PVCannotFollowPPUP
    /\ target = IF Late /\ Mutation /= "LateIntoCurrent"      \* PPUpdateWrongEpoch
                THEN Epoch + 1 ELSE Epoch

\* In English: "The ledger accepts the transaction."
\* Literally: "RefOk of keys, u, target and valid is defined as:
\*   RefRunsPpup of valid is not true, or PpupOk of keys, u and target."
RefOk(keys, u, target, valid) ==
    ~RefRunsPpup(valid) \/ PpupOk(keys, u, target)

\* Right override [S1]: each proposing key's entry is replaced.
\* In English: "Map m with every key in keys now proposing u."
\* Literally: "Override of m, keys and u is defined as the function that
\*   maps every k in AllKeys to: if k is a member of keys then u, else m of k."
Override(m, keys, u) == [k \in AllKeys |-> IF k \in keys THEN u ELSE m[k]]

(***************************************************************************)
(* Half 2: what gOuroboros decides [G1][G2].                               *)
(***************************************************************************)

\* [G2]: the PPUP rule is in the always-run group, so today it also runs for
\* an IsValid false transaction.
\* In English: "gOuroboros runs its PPUP checks on this transaction."
\* Literally: "GoRunsPpup of valid is defined as: RefRunsPpup of valid, or
\*   GoPhase2Fixed is not true."
GoRunsPpup(valid) == RefRunsPpup(valid) \/ ~GoPhase2Fixed

\* [G1] 1100: "if len(updates) == 0 { return nil }" skips every check,
\* including the target epoch.
\* In English: "gOuroboros's PPUP checks pass."
\* Literally: "GoPpupOk of keys, u and target is defined as: (keys equals
\*   the empty set and GoEmptyFixed is not true), or PpupOk of keys, u and
\*   target."
GoPpupOk(keys, u, target) ==
    \/ keys = {} /\ ~GoEmptyFixed        \* the early return today
    \/ PpupOk(keys, u, target)           \* otherwise the same predicates

\* In English: "gOuroboros accepts the transaction."
\* Literally: "GoOk of keys, u, target and valid is defined as: GoRunsPpup of
\*   valid is not true, or GoPpupOk of keys, u and target."
GoOk(keys, u, target, valid) ==
    ~GoRunsPpup(valid) \/ GoPpupOk(keys, u, target)

(***************************************************************************)
(* The transaction step.                                                   *)
(***************************************************************************)

\* One transaction per slot carrying an update in which every named key
\* proposes u for epoch target. Only an accepted, phase-2-valid transaction
\* changes the proposals; Dingo stores rows only for those (database/
\* transaction.go 435).
\* In English: "A transaction with this update is submitted; the ledger and
\* gOuroboros each decide on it, and the ledger's decision takes effect."
\* Literally: "Submit of keys, u, target and valid is defined as: submitted
\*   is not true, and submitted in the next state is TRUE, and goMismatch in
\*   the next state equals goMismatch or (GoOk of keys, u, target and valid
\*   does not equal RefOk of keys, u, target and valid), and: if RefOk and
\*   RefRunsPpup of valid then (if Late and target equals Epoch plus 1 then
\*   fut and dLate in the next state are their overrides and cur, dInWin,
\*   carriedKeys and lateCurWrite are unchanged, else cur and dInWin in the
\*   next state are their overrides, carriedKeys in the next state is
\*   carriedKeys without the members of keys, lateCurWrite in the next state
\*   equals lateCurWrite or Late, and fut and dLate are unchanged), else
\*   cur, fut, carriedKeys, dInWin, dLate and lateCurWrite are unchanged;
\*   and the rest are unchanged."
Submit(keys, u, target, valid) ==
    /\ ~submitted                                         \* one tx per slot
    /\ submitted' = TRUE
    /\ goMismatch' = (goMismatch \/                       \* disagreement
            GoOk(keys, u, target, valid) /= RefOk(keys, u, target, valid))
    /\ IF RefOk(keys, u, target, valid) /\ RefRunsPpup(valid)
       THEN IF Late /\ target = Epoch + 1
            THEN /\ fut' = Override(fut, keys, u)         \* PP-Update-Future
                 /\ dLate' = Override(dLate, keys, u)     \* Dingo row
                 /\ UNCHANGED <<cur, dInWin, carriedKeys, lateCurWrite>>
            ELSE /\ cur' = Override(cur, keys, u)         \* PP-Update-Current
                 /\ dInWin' = Override(dInWin, keys, u)   \* Dingo row
                 /\ carriedKeys' = carriedKeys \ keys     \* replaced by a new one
                 /\ lateCurWrite' = (lateCurWrite \/ Late)
                 /\ UNCHANGED <<fut, dLate>>
       ELSE UNCHANGED <<cur, fut, carriedKeys, dInWin, dLate, lateCurWrite>>
    /\ UNCHANGED <<slot, pp, dCarried, dingoMismatch, adoptVotes, pvOk,
                   carriedDropped, carriedAdopted>>

(***************************************************************************)
(* The epoch boundary: NEWPP [S2][R3] and Dingo's selection.               *)
(***************************************************************************)

\* Dingo's carried-over check [Dingo classicCarriedOverProposalsFollow]: at
\* the boundary that ends the epoch, against that epoch's parameters.
\* In English: "Dingo keeps the carried-over proposals."
\* Literally: "DingoKeep is defined as: Mutation equals "DingoNoCarryCheck",
\*   or for all k in AllKeys, dCarried of k equals None or LegalPV of pp and
\*   dCarried of k."
DingoKeep ==
    \/ Mutation = "DingoNoCarryCheck"
    \/ \A k \in AllKeys : dCarried[k] = None \/ LegalPV(pp, dCarried[k])

\* Dingo's vote for each key: its in-window row, else its carried row if the
\* carried rows are kept [Dingo selectClassicPParamUpdate].
\* In English: "The proposal Dingo counts for each key."
\* Literally: "DingoVotes is defined as the function that maps every k in
\*   AllKeys to: if dInWin of k does not equal None then dInWin of k, else
\*   if DingoKeep then dCarried of k, else None."
DingoVotes == [k \in AllKeys |->
                IF dInWin[k] /= None THEN dInWin[k]
                ELSE IF DingoKeep THEN dCarried[k] ELSE None]

\* In English: "Time moves on one slot; at an epoch boundary the winning
\* update is adopted, the future proposals become current if they can all
\* follow the new parameters, and Dingo's own choice is compared."
\* Literally: "Tick is defined as: slot is less than LastSlot, and slot in
\*   the next state equals slot plus 1, and submitted in the next state is
\*   FALSE, and: if slot plus 1 modulo EpochLength equals 0 then (letting w
\*   be Winner of cur, ppNew be (if w equals None then pp else Apply of pp
\*   and w), and keep be Mutation equals "NoCarryCheck" or for all k in
\*   AllKeys, fut of k equals None or LegalPV of ppNew and fut of k: pp in
\*   the next state equals ppNew, adoptVotes in the next state is (if w
\*   equals None then 0 else Votes of cur and w), pvOk in the next state is
\*   pvOk and (ppNew's pv equals pp's pv or CanFollow of pp's pv and ppNew's
\*   pv), cur in the next state is (if keep then fut else Empty), fut in the
\*   next state is Empty, carriedKeys in the next state is (if keep then the
\*   set of every k in AllKeys such that fut of k does not equal None, else
\*   the empty set), carriedDropped in the next state is carriedDropped or
\*   keep is not true, carriedAdopted in the next state is carriedAdopted or
\*   (w does not equal None and there exists a k in carriedKeys such that
\*   cur of k equals w), dingoMismatch in the next state is dingoMismatch or
\*   Winner of DingoVotes does not equal w, dCarried in the next state is
\*   dLate, and dInWin and dLate in the next state are Empty), else all of
\*   those are unchanged; and goMismatch and lateCurWrite are unchanged."
Tick ==
    /\ slot < LastSlot
    /\ slot' = slot + 1
    /\ submitted' = FALSE
    /\ IF (slot + 1) % EpochLength = 0
       THEN LET w     == Winner(cur)                          \* votedValue
                ppNew == IF w = None THEN pp ELSE Apply(pp, w)
                keep  == \/ Mutation = "NoCarryCheck"
                         \/ \A k \in AllKeys :                \* updatePpup
                               fut[k] = None \/ LegalPV(ppNew, fut[k])
            IN  /\ pp' = ppNew
                /\ adoptVotes' = IF w = None THEN 0 ELSE Votes(cur, w)
                /\ pvOk' = (pvOk /\ (ppNew.pv = pp.pv \/ CanFollow(pp.pv, ppNew.pv)))
                /\ cur' = IF keep THEN fut ELSE Empty
                /\ fut' = Empty
                /\ carriedKeys' = IF keep THEN {k \in AllKeys : fut[k] /= None}
                                  ELSE {}
                /\ carriedDropped' = (carriedDropped \/ ~keep)
                /\ carriedAdopted' = (carriedAdopted \/
                        (w /= None /\ \E k \in carriedKeys : cur[k] = w))
                /\ dingoMismatch' = (dingoMismatch \/ Winner(DingoVotes) /= w)
                /\ dCarried' = dLate
                /\ dInWin' = Empty
                /\ dLate' = Empty
       ELSE UNCHANGED <<pp, adoptVotes, pvOk, cur, fut, carriedKeys,
                        carriedDropped, carriedAdopted, dingoMismatch,
                        dCarried, dInWin, dLate>>
    /\ UNCHANGED <<goMismatch, lateCurWrite>>

\* In English: "At the last slot the model stops; this stutter step keeps
\* TLC from reporting the stop as a deadlock."
\* Literally: "Done is defined as slot equals LastSlot and vars is unchanged."
Done == slot = LastSlot /\ UNCHANGED vars

\* The transactions the model tries: at most two keys named, any update,
\* this epoch or the next, valid or (from Alonzo) not.
\* In English: "Some transaction is submitted, or time moves on, or the
\* model has stopped."
\* Literally: "Next is defined as: there exists a keys in the set of every K
\*   in the set of subsets of AllKeys such that the number of members of K
\*   is at most 2, a u in Updates, a target in the set containing Epoch and
\*   Epoch plus 1, and a valid in (if PhaseTwo then BOOLEAN else the set
\*   containing TRUE) such that Submit of keys, u, target and valid; or
\*   Tick; or Done."
Next ==
    \/ \E keys \in {K \in SUBSET AllKeys : Cardinality(K) <= 2},
          u \in Updates,
          target \in {Epoch, Epoch + 1},
          valid \in (IF PhaseTwo THEN BOOLEAN ELSE {TRUE}) :
            Submit(keys, u, target, valid)
    \/ Tick
    \/ Done

\* In English: "Start in Init; every step is a Next step or changes nothing."
\* Literally: "Spec is defined as Init and always, every step is a Next
\*   step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Questions.                                                              *)
(***************************************************************************)

\* In English: "Only genesis keys ever have a proposal recorded."
\* Literally: "ProposersAreGenesis is defined as: for all k in AllKeys
\*   without the members of GenKeys, cur of k equals None and fut of k equals
\*   None."
ProposersAreGenesis ==
    \A k \in AllKeys \ GenKeys : cur[k] = None /\ fut[k] = None

\* In English: "Every adoption had at least Quorum votes."
\* Literally: "AdoptedHadQuorum is defined as: adoptVotes equals 0, or
\*   adoptVotes is at least Quorum."
AdoptedHadQuorum == adoptVotes = 0 \/ adoptVotes >= Quorum

\* In English: "The protocol version only ever moves to a version that can
\* follow it."
\* Literally: "VersionFollows is defined as pvOk."
VersionFollows == pvOk

\* In English: "No current proposal is written at or after the slot of no
\* return, so what the boundary adopts is fixed 2*StabilityWindow early."
\* Literally: "CurFrozenAfterNoReturn is defined as: lateCurWrite is not
\*   true."
CurFrozenAfterNoReturn == ~lateCurWrite

\* In English: "gOuroboros accepts exactly the transactions the ledger
\* accepts."
\* Literally: "GoAgrees is defined as: goMismatch is not true."
GoAgrees == ~goMismatch

\* In English: "Dingo adopts exactly what the ledger adopts."
\* Literally: "DingoAgrees is defined as: dingoMismatch is not true."
DingoAgrees == ~dingoMismatch

\* Reachability probes: each is violated when the situation it names is
\* reachable, which a *Bug.cfg proves.
\* In English: "No update is ever adopted."
\* Literally: "ProbeNeverAdopted is defined as pp equals InitPP."
ProbeNeverAdopted == pp = InitPP

\* In English: "Carried-over proposals are never discarded."
\* Literally: "ProbeCarriedNeverDropped is defined as: carriedDropped is
\*   not true."
ProbeCarriedNeverDropped == ~carriedDropped

\* In English: "A carried-over proposal is never adopted."
\* Literally: "ProbeCarriedNeverAdopted is defined as: carriedAdopted is not
\*   true."
ProbeCarriedNeverAdopted == ~carriedAdopted

\* In English: "The version never reaches 4.0, which needs two adoptions."
\* Literally: "ProbeNeverVersion4 is defined as: pp's pv does not equal the
\*   tuple of 4 and 0."
ProbeNeverVersion4 == pp.pv /= <<4, 0>>
=============================================================================
