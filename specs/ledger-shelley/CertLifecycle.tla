--------------------------- MODULE CertLifecycle ---------------------------
(***************************************************************************)
(* Shelley certificate lifecycles and the ada they move: stake credential  *)
(* registration, delegation and deregistration (DELEG), pool registration, *)
(* re-registration and retirement (POOL), the epoch boundary that reaps    *)
(* retired pools (POOLREAP), and preservation of value across all of them. *)
(*                                                                         *)
(* The model has two halves.                                               *)
(*   1. The ledger as the specification and the reference implementation *)
(*      define it: what each certificate is allowed to do, and what it    *)
(*      does to the deposits, the reward accounts and the pots.           *)
(*   2. What gOuroboros decides for the same transactions. gOuroboros      *)
(*      does not hold ledger state: a caller (Dingo) supplies a           *)
(*      LedgerState, and gOuroboros validates each transaction against it, *)
(*      folding earlier transactions of the same block in with            *)
(*      BlockLedgerState. So the model also says what that caller-supplied *)
(*      view shows (the constant View), and checks that gOuroboros accepts *)
(*      exactly what the ledger accepts and charges exactly its deposits. *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd; links and     *)
(* quotes are in specs/ledger-shelley/README.md.                        *)
(*   Specification (eras/shelley/formal-spec/):                            *)
(*   [S1] delegation.tex 403-510: Deleg-Reg, Deleg-Dereg (balance must be *)
(*        zero), Deleg-Deleg (credential must be registered).             *)
(*   [S2] delegation.tex 1137: DELEGS rejects a delegation to a pool not  *)
(*        in poolParams.                                                   *)
(*   [S3] delegation.tex 737-830: Pool-Reg (new pool), Pool-reReg (future *)
(*        parameters, cancels retirement), Pool-Retire                    *)
(*        (cepoch < e <= cepoch + emax).                                   *)
(*   [S4] epoch.tex 559-640: POOLREAP refunds a retired pool's deposit to *)
(*        its reward account if registered, else to the treasury, and     *)
(*        removes the pool, its retirement and the delegations to it.     *)
(*   [S5] utxo.tex 100-111, 267-305: consumed = inputs + withdrawals +    *)
(*        key refunds; produced = outputs + fee + deposits; equal.        *)
(*   Reference implementation (eras/shelley/impl/src/Cardano/Ledger/):     *)
(*   [R1] Shelley/Rules/Deleg.hs 305-342: the same three DELEG cases; the *)
(*        pool check of [S2] is made here (DelegateeNotRegisteredDELEG).  *)
(*   [R2] Shelley/Rules/Pool.hs 251-315: new vs re-registration decided   *)
(*        by membership of psStakePools; retirement bounds.               *)
(*   [R3] Shelley/Rules/PoolReap.hs 120-217: the reaping of [S4].         *)
(*   [R4] Shelley/TxCert.hs 670-719: a pool deposit is due only for a pool*)
(*        not registered and not registered earlier in the transaction.   *)
(*   [R5] Shelley/AdaPots.hs 51-93: total ada = treasury + reserves +     *)
(*        rewards + utxo + fees + deposits (obligations).                 *)
(*   [R6] Shelley/Rules/Epoch.hs 157-164: SNAP, then POOLREAP.            *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit 61046085):              *)
(*   [G1] ledger/shelley/rules.go UtxoValidateDelegation 757-864           *)
(*   [G2] ledger/shelley/rules.go validatePoolRetirement 1644-1692         *)
(*   [G3] ledger/shelley/rules.go UtxoValidateValueNotConservedUtxo        *)
(*        341-450, and ledger/common/pool_deposit.go                       *)
(*        PoolRegistrationDepositDue 40-66                                 *)
(*   [G4] ledger/common/block_state.go applyPoolRegistration 566-592,      *)
(*        applyPoolCertificate 520-535, PoolCurrentState 702-723,          *)
(*        IsPoolRegistered 747-753                                          *)
(*   [G5] ledger/common/state.go PoolState 103-125 (the provider contract) *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla. New here:*)
(*   Cardinality(S)   "how many things are in the set S" (FiniteSets)      *)
(*   RECURSIVE F(_)   announces that F's definition uses F itself          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets   \* Integers: a refund is a negative deposit

CONSTANTS
    Creds,          \* the stake credentials, e.g. {"c1", "c2"}
    RewardCred,     \* the credential the pool's reward account belongs to
    KeyDeposit,     \* ppKeyDeposit, held while a credential is registered
    PoolDeposit,    \* ppPoolDeposit, held while the pool is registered
    EMax,           \* ppEMax: how many epochs ahead a retirement may be set
    Fee,            \* the fee every transaction in the model pays
    StartUtxo,      \* ada in the UTxO at the start
    StartReserves,  \* ada in the reserves at the start
    MaxEpoch,       \* the last epoch the model runs to (keeps it finite)
    View,           \* what the caller's LedgerState shows for a reaped pool:
                    \*  "Reaped": nothing, the pool is gone (a faithful view)
                    \*  "StaleHonest": PoolCurrentState still returns the old
                    \*    registration and its retirement epoch, and
                    \*    IsPoolRegistered says FALSE. [G3]'s comment says a
                    \*    provider may do this.
                    \*  "StaleMock": the same, but IsPoolRegistered is
                    \*    "PoolCurrentState returned a registration", as in
                    \*    ouroboros-mock and Dingo's LedgerView.
    GoFixed,        \* TRUE: applyPoolRegistration decides "new pool" with
                    \*  IsPoolRegistered, as on fix/ledger-shelley-reregister-
                    \*  reaped-pool. FALSE: with PoolCurrentState, as today.
    Mutation        \* "none", or one deliberate mistake (see Mutations below)

\* The one pool in the model, and "no pool" for an undelegated credential.
\* Literally: "Pool is defined as "p"."
Pool == "p"
\* Literally: "NoPool is defined as "none"."
NoPool == "none"

\* A certificate is a record. Kind says which; cred and epoch are used only by
\* the kinds that carry them.
\* Literally: "Certs is defined as the union of: the set of records whose field
\*   kind is a member of the set containing "RegKey", "DeregKey" and "Deleg" and
\*   whose field cred is a member of Creds; the set of records whose field kind
\*   is a member of the set containing "RegPool"; and the set of records whose
\*   field kind is a member of the set containing "RetirePool" and whose field
\*   epoch is a member of 0 through (MaxEpoch plus EMax plus 1)."
Certs ==
    [kind : {"RegKey", "DeregKey", "Deleg"}, cred : Creds]
    \cup [kind : {"RegPool"}]
    \cup [kind : {"RetirePool"}, epoch : 0..(MaxEpoch + EMax + 1)]

\* The total ada in the model. Nothing creates or destroys ada, so every pot
\* added together must stay at this [R5].
\* Literally: "Total is defined as StartUtxo plus StartReserves."
Total == StartUtxo + StartReserves

VARIABLES
    \* ---- the ledger, as the specification and reference define it ----
    epoch,      \* the current epoch
    registered, \* the set of registered stake credentials (dom rewards)
    balance,    \* balance[c]: the reward balance of credential c
    deleg,      \* deleg[c]: the pool c delegates to, or NoPool
    poolReg,    \* TRUE when the pool is in poolParams / psStakePools
    retiring,   \* the epoch the pool is set to retire in, or 0 for none
    utxo,       \* ada held in transaction outputs
    deposited,  \* the deposit pot (utxosDeposited)
    fees,       \* fees collected this epoch
    treasury,   \* the treasury
    reserves,   \* the reserves
    \* ---- what gOuroboros sees ----
    reapedAt,   \* the epoch the pool's last retirement took effect, or 0.
                \* A stale View keeps showing that retirement after POOLREAP.
    baseReg,    \* the caller's view at the start of the block: does
                \* PoolCurrentState return a registration for the pool?
    baseRet,    \* ... and which retirement epoch (0 for none)
    baseIsReg,  \* ... and what IsPoolRegistered answers
    ovReg,      \* BlockLedgerState's own record for the pool [G4]: TRUE
                \* once a registration in this block recorded it as new
                \* (registrationKnown with a registration)
    ovRetKnown, \* ... TRUE once this block recorded a retirement epoch
    ovRet,      \* ... and that retirement epoch, 0 for none
    \* ---- bookkeeping for the probes ----
    seen        \* set of event names that have happened, for the probes

\* In English: "The ledger's variables."
\* Literally: "ledgerVars is defined as the tuple of epoch, registered, balance,
\*   deleg, poolReg, retiring, utxo, deposited, fees, treasury and reserves."
ledgerVars == <<epoch, registered, balance, deleg, poolReg, retiring,
                utxo, deposited, fees, treasury, reserves>>
\* In English: "What gOuroboros sees."
\* Literally: "goVars is defined as the tuple of reapedAt, baseReg, baseRet,
\*   baseIsReg, ovReg, ovRetKnown and ovRet."
goVars     == <<reapedAt, baseReg, baseRet, baseIsReg, ovReg, ovRetKnown, ovRet>>
\* Literally: "vars is defined as the tuple of ledgerVars, goVars and seen."
vars       == <<ledgerVars, goVars, seen>>

-----------------------------------------------------------------------------
(* The caller's view.                                                      *)

\* In English: what the caller's LedgerState reports for the pool at the
\* start of a block, given the ledger state. A registered pool is reported
\* as it is. A reaped pool is reported as absent by a faithful view, and as
\* its old registration plus the reached retirement by a stale one [G5].
\* Literally: "ViewReg is defined as: poolReg, or (View does not equal "Reaped"
\*   and reapedAt does not equal 0)."
ViewReg   == poolReg \/ (View # "Reaped" /\ reapedAt # 0)     \* PoolCurrentState returns a registration
\* Literally: "ViewRet is defined as: if poolReg then retiring, else if View
\*   does not equal "Reaped" and reapedAt does not equal 0 then reapedAt, else
\*   0."
ViewRet   == IF poolReg THEN retiring                         \* a pending retirement, if any
             ELSE IF View # "Reaped" /\ reapedAt # 0 THEN reapedAt  \* the stale, reached retirement
             ELSE 0
\* Literally: "ViewIsReg is defined as: poolReg, or (View equals "StaleMock" and
\*   reapedAt does not equal 0)."
ViewIsReg == poolReg \/ (View = "StaleMock" /\ reapedAt # 0)   \* IsPoolRegistered

\* In English: start a fresh block: the caller's view is refreshed from the
\* ledger, and BlockLedgerState starts with no records of its own.
\* Literally: "FreshBlock is defined as: baseReg in the next state equals
\*   ViewReg, and baseRet in the next state equals ViewRet, and baseIsReg in the
\*   next state equals ViewIsReg, and ovReg in the next state equals FALSE, and
\*   ovRetKnown in the next state equals FALSE, and ovRet in the next state
\*   equals 0."
FreshBlock ==
    /\ baseReg'   = ViewReg      \* re-read the caller's view of the ledger as it is now
    /\ baseRet'   = ViewRet
    /\ baseIsReg' = ViewIsReg
    /\ ovReg'     = FALSE        \* NewBlockLedgerState: no records yet
    /\ ovRetKnown' = FALSE
    /\ ovRet'     = 0

\* In English: what BlockLedgerState answers inside the block [G4].
\* PoolCurrentState uses its own record when it has one, otherwise the view.
\* Literally: "GoCurReg is defined as: ovReg or baseReg."
GoCurReg == ovReg \/ baseReg
\* Literally: "GoCurRet is defined as: if ovRetKnown then ovRet, else baseRet."
GoCurRet == IF ovRetKnown THEN ovRet ELSE baseRet
\* IsPoolRegistered is TRUE if this block registered the pool as new,
\* otherwise whatever the caller's view says.
\* Literally: "GoIsReg is defined as: ovReg or baseIsReg."
GoIsReg  == ovReg \/ baseIsReg

-----------------------------------------------------------------------------
(* The ledger's rules: which certificates are allowed, and their deposits. *)

\* In English: the ledger accepts certificate c in the current state.
\* Literally: "SpecAccepts of c is defined as: in the case c's kind equals
\*   "RegKey", c's cred is not a member of registered; in the case c's kind
\*   equals "DeregKey", c's cred is a member of registered and balance of c's
\*   cred equals 0; in the case c's kind equals "Deleg", c's cred is a member of
\*   registered and poolReg; in the case c's kind equals "RegPool", TRUE; in the
\*   case c's kind equals "RetirePool", poolReg and epoch is less than c's epoch
\*   and c's epoch is less than or equal to epoch plus EMax plus (if Mutation
\*   equals "RetireLate" then 1, else 0)."
SpecAccepts(c) ==
    CASE c.kind = "RegKey"     -> c.cred \notin registered               \* [S1] Deleg-Reg
      [] c.kind = "DeregKey"   -> c.cred \in registered                  \* [S1] Deleg-Dereg
                                  /\ balance[c.cred] = 0                 \*  ... only an empty account
      [] c.kind = "Deleg"      -> c.cred \in registered /\ poolReg       \* [S1] Deleg-Deleg, [S2]/[R1]
      [] c.kind = "RegPool"    -> TRUE                                   \* [S3] Pool-Reg or Pool-reReg
      [] c.kind = "RetirePool" -> poolReg                                \* [S3] Pool-Retire
                                  /\ epoch < c.epoch
                                  /\ c.epoch <= epoch + EMax
                                     + (IF Mutation = "RetireLate" THEN 1 ELSE 0)

\* In English: the deposit certificate c adds to the pot (negative for a
\* refund) [S5]/[R4]. A pool deposit is due only for a new pool.
\* Literally: "SpecDeposit of c is defined as: in the case c's kind equals
\*   "RegKey", KeyDeposit; in the case c's kind equals "DeregKey", minus
\*   KeyDeposit; in the case c's kind equals "RegPool", if poolReg is not true
\*   or Mutation equals "ReRegDeposit" then PoolDeposit, else 0; in every other
\*   case, 0."
SpecDeposit(c) ==
    CASE c.kind = "RegKey"   -> KeyDeposit
      [] c.kind = "DeregKey" -> -KeyDeposit
      [] c.kind = "RegPool"  -> IF ~poolReg \/ Mutation = "ReRegDeposit"
                                THEN PoolDeposit ELSE 0
      [] OTHER               -> 0

-----------------------------------------------------------------------------
(* gOuroboros' decisions for the same certificate.                          *)

\* In English: gOuroboros accepts certificate c. Credentials are read
\* through the same view and BlockLedgerState keeps them exactly
\* (block_state.go 346-364, 655-697), so the credential checks match the
\* ledger's; the pool checks read the pool through GoIsReg [G1][G2].
\* Literally: "GoAccepts of c is defined as: in the case c's kind equals
\*   "RegKey", c's cred is not a member of registered; in the case c's kind
\*   equals "DeregKey", c's cred is a member of registered and balance of c's
\*   cred equals 0; in the case c's kind equals "Deleg", c's cred is a member of
\*   registered and GoIsReg; in the case c's kind equals "RegPool", TRUE; in the
\*   case c's kind equals "RetirePool", GoIsReg and epoch is less than c's epoch
\*   and c's epoch is less than or equal to epoch plus EMax."
GoAccepts(c) ==
    CASE c.kind = "RegKey"     -> c.cred \notin registered               \* StakeKeyAlreadyRegisteredError
      [] c.kind = "DeregKey"   -> c.cred \in registered                  \* StakeKeyNotRegisteredError
                                  /\ balance[c.cred] = 0                 \* StakeKeyNonZeroAccountBalanceError
      [] c.kind = "Deleg"      -> c.cred \in registered /\ GoIsReg       \* DelegateToUnregisteredPoolError [G1]
      [] c.kind = "RegPool"    -> TRUE                                   \* cost, network, metadata: not modelled
      [] c.kind = "RetirePool" -> GoIsReg                                \* StakePoolNotRegisteredOnKeyError [G2]
                                  /\ epoch < c.epoch
                                  /\ c.epoch <= epoch + EMax

\* In English: the deposit gOuroboros' value-conservation check charges
\* for c [G3]. PoolRegistrationDepositDue: due when PoolCurrentState has no
\* registration, or its retirement epoch has been reached.
\* Literally: "GoDeposit of c is defined as: in the case c's kind equals
\*   "RegKey", KeyDeposit; in the case c's kind equals "DeregKey", minus
\*   KeyDeposit; in the case c's kind equals "RegPool", if GoCurReg is not true
\*   or (GoCurRet does not equal 0 and epoch is greater than or equal to
\*   GoCurRet) then PoolDeposit, else 0; in every other case, 0."
GoDeposit(c) ==
    CASE c.kind = "RegKey"   -> KeyDeposit
      [] c.kind = "DeregKey" -> -KeyDeposit
      [] c.kind = "RegPool"  -> IF ~GoCurReg \/ (GoCurRet # 0 /\ epoch >= GoCurRet)
                                THEN PoolDeposit ELSE 0
      [] OTHER               -> 0

\* In English: how BlockLedgerState records a pool certificate [G4].
\* A registration is "new" when PoolCurrentState returns none (today), or
\* also when IsPoolRegistered is FALSE (GoFixed). New: the pool's record is
\* set and any retirement cleared. Otherwise only the retirement is cleared
\* (the parameters wait for the epoch boundary). A retirement records its
\* epoch.
\* Literally: "GoApply of c is defined as: in the case c's kind equals
\*   "RegPool", letting isNew be (GoCurReg is not true, or GoFixed and GoIsReg
\*   is not true): ovReg in the next state equals (ovReg or isNew), and
\*   ovRetKnown in the next state equals TRUE, and ovRet in the next state
\*   equals 0; in the case c's kind equals "RetirePool", ovReg in the next state
\*   equals ovReg, and ovRetKnown in the next state equals TRUE, and ovRet in
\*   the next state equals c's epoch; in every other case, ovReg, ovRetKnown and
\*   ovRet are unchanged."
GoApply(c) ==
    CASE c.kind = "RegPool" ->
            LET isNew == ~GoCurReg \/ (GoFixed /\ ~GoIsReg)
            IN /\ ovReg' = (ovReg \/ isNew)        \* new: pool.registration = cert
               /\ ovRetKnown' = TRUE                 \* retirementEpoch = nil
               /\ ovRet' = 0
      [] c.kind = "RetirePool" ->
            /\ ovReg' = ovReg
            /\ ovRetKnown' = TRUE
            /\ ovRet' = c.epoch                     \* retirementEpoch = &epoch
      [] OTHER -> UNCHANGED <<ovReg, ovRetKnown, ovRet>>

-----------------------------------------------------------------------------
(* The steps.                                                              *)

\* In English: the starting state: nothing registered, all ada in the UTxO
\* and the reserves, and a fresh block.
\* Literally: "Init is defined as: epoch equals 0, and registered equals the
\*   empty set, and balance equals the function that maps every c in Creds to 0,
\*   and deleg equals the function that maps every c in Creds to NoPool, and
\*   poolReg equals FALSE, and retiring equals 0, and utxo equals StartUtxo, and
\*   deposited equals 0, and fees equals 0, and treasury equals 0, and reserves
\*   equals StartReserves, and reapedAt equals 0, and baseReg equals FALSE, and
\*   baseRet equals 0, and baseIsReg equals FALSE, and ovReg equals FALSE, and
\*   ovRetKnown equals FALSE, and ovRet equals 0, and seen equals the empty
\*   set."
Init ==
    /\ epoch = 0
    /\ registered = {}
    /\ balance = [c \in Creds |-> 0]
    /\ deleg = [c \in Creds |-> NoPool]
    /\ poolReg = FALSE
    /\ retiring = 0
    /\ utxo = StartUtxo
    /\ deposited = 0
    /\ fees = 0
    /\ treasury = 0
    /\ reserves = StartReserves
    /\ reapedAt = 0
    /\ baseReg = FALSE
    /\ baseRet = 0
    /\ baseIsReg = FALSE
    /\ ovReg = FALSE
    /\ ovRetKnown = FALSE
    /\ ovRet = 0
    /\ seen = {}

\* In English: a transaction carrying certificate c goes on chain. Only a
\* transaction the ledger accepts can be in a block. It pays the fee and the
\* deposit from the UTxO (a refund goes back to it), and changes the
\* registrations as the rules say. BlockLedgerState records it too.
\* Literally: "Tx of c is defined as: epoch is less than MaxEpoch, and
\*   SpecAccepts of c, and utxo is greater than or equal to Fee plus (if
\*   SpecDeposit of c is greater than 0 then SpecDeposit of c, else 0), and utxo
\*   in the next state equals utxo minus Fee minus SpecDeposit of c, and fees in
\*   the next state equals fees plus Fee, and deposited in the next state equals
\*   deposited plus SpecDeposit of c minus (if Mutation equals "RefundTwice" and
\*   c's kind equals "DeregKey" then 1, else 0), and registered in the next
\*   state equals: in the case c's kind equals "RegKey", the union of registered
\*   and the set containing c's cred; in the case c's kind equals "DeregKey",
\*   registered without the members of the set containing c's cred; in every
\*   other case, registered; and deleg in the next state equals: in the case c's
\*   kind equals "Deleg", deleg except that its c's cred entry is Pool; in the
\*   case c's kind equals "DeregKey", deleg except that its c's cred entry is
\*   NoPool; in every other case, deleg; and poolReg in the next state equals
\*   (poolReg or c's kind equals "RegPool"), and retiring in the next state
\*   equals: in the case c's kind equals "RegPool", 0; in the case c's kind
\*   equals "RetirePool", c's epoch; in every other case, retiring; and seen in
\*   the next state equals the union of seen, (if c's kind equals "RegPool" and
\*   poolReg and retiring does not equal 0 then the set containing
\*   "reRegCancelsRetirement", else the empty set), and (if c's kind equals
\*   "RegPool" and poolReg is not true and reapedAt does not equal 0 then the
\*   set containing "reaped pool registered again", else the empty set); and
\*   GoApply of c, and epoch, balance, treasury, reserves, reapedAt, baseReg,
\*   baseRet and baseIsReg are unchanged."
Tx(c) ==
    /\ epoch < MaxEpoch
    /\ SpecAccepts(c)
    /\ utxo >= Fee + (IF SpecDeposit(c) > 0 THEN SpecDeposit(c) ELSE 0)  \* the inputs can pay
    /\ utxo' = utxo - Fee - SpecDeposit(c)            \* outputs = inputs + refund - fee - deposit [S5]
    /\ fees' = fees + Fee
    /\ deposited' = deposited + SpecDeposit(c)
       - (IF Mutation = "RefundTwice" /\ c.kind = "DeregKey" THEN 1 ELSE 0)
    /\ registered' = CASE c.kind = "RegKey"   -> registered \cup {c.cred}   \* rewards U {hk -> 0}
                       [] c.kind = "DeregKey" -> registered \ {c.cred}      \* {hk} <| rewards
                       [] OTHER               -> registered
    /\ deleg' = CASE c.kind = "Deleg"    -> [deleg EXCEPT ![c.cred] = Pool]
                  [] c.kind = "DeregKey" -> [deleg EXCEPT ![c.cred] = NoPool]  \* {hk} <| delegations
                  [] OTHER               -> deleg
    /\ poolReg' = (poolReg \/ c.kind = "RegPool")      \* a new pool joins poolParams
    /\ retiring' = CASE c.kind = "RegPool"    -> 0         \* re-registration cancels retirement [S3]
                     [] c.kind = "RetirePool" -> c.epoch   \* retiring U {hk -> e}
                     [] OTHER                 -> retiring
    /\ seen' = seen \cup
               (IF c.kind = "RegPool" /\ poolReg /\ retiring # 0
                THEN {"reRegCancelsRetirement"} ELSE {})
               \cup (IF c.kind = "RegPool" /\ ~poolReg /\ reapedAt # 0
                     THEN {"reaped pool registered again"} ELSE {})
    /\ GoApply(c)
    /\ UNCHANGED <<epoch, balance, treasury, reserves, reapedAt,
                   baseReg, baseRet, baseIsReg>>

\* In English: a registered credential with a balance withdraws all of it to
\* the UTxO, in a transaction that pays the fee.
\* Literally: "Withdraw of c is defined as: epoch is less than MaxEpoch, and c
\*   is a member of registered, and balance of c is greater than 0, and utxo
\*   plus balance of c is greater than or equal to Fee, and utxo in the next
\*   state equals utxo plus balance of c minus Fee, and balance in the next
\*   state equals balance except that its c entry is 0, and fees in the next
\*   state equals fees plus Fee, and epoch, registered, deleg, poolReg,
\*   retiring, deposited, treasury, reserves, goVars and seen are unchanged."
Withdraw(c) ==
    /\ epoch < MaxEpoch
    /\ c \in registered
    /\ balance[c] > 0
    /\ utxo + balance[c] >= Fee
    /\ utxo' = utxo + balance[c] - Fee
    /\ balance' = [balance EXCEPT ![c] = 0]
    /\ fees' = fees + Fee
    /\ UNCHANGED <<epoch, registered, deleg, poolReg, retiring, deposited,
                   treasury, reserves, goVars, seen>>

\* In English: a reward of one lovelace moves from the reserves to a
\* registered credential. This stands in for the reward update, whose amounts
\* are not modelled; what matters here is that balances become non-zero.
\* Literally: "Reward of c is defined as: epoch is less than MaxEpoch, and c is
\*   a member of registered, and reserves is greater than 0, and reserves in the
\*   next state equals reserves minus 1, and balance in the next state equals
\*   balance except that its c entry is the old entry plus 1, and epoch,
\*   registered, deleg, poolReg, retiring, utxo, deposited, fees, treasury,
\*   goVars and seen are unchanged."
Reward(c) ==
    /\ epoch < MaxEpoch
    /\ c \in registered
    /\ reserves > 0
    /\ reserves' = reserves - 1
    /\ balance' = [balance EXCEPT ![c] = @ + 1]
    /\ UNCHANGED <<epoch, registered, deleg, poolReg, retiring, utxo,
                   deposited, fees, treasury, goVars, seen>>

\* In English: a new block starts within the epoch. The caller commits the
\* last block's effects, so its view is refreshed.
\* Literally: "NewBlock is defined as: epoch is less than MaxEpoch, and (ovReg
\*   or ovRetKnown), and FreshBlock, and ledgerVars, reapedAt and seen are
\*   unchanged."
NewBlock ==
    /\ epoch < MaxEpoch
    /\ ovReg \/ ovRetKnown                    \* only if the block changed the pool
    /\ FreshBlock
    /\ UNCHANGED <<ledgerVars, reapedAt, seen>>

\* In English: the epoch boundary. The fees go to the reserves (standing in
\* for the reward update). POOLREAP [S4][R3][R6] retires the pool if its
\* retirement epoch is the new epoch: its deposit goes to its reward account
\* if that is registered, otherwise to the treasury; delegations to it are
\* cleared; it leaves poolParams. A new block starts.
\* Literally: "EpochBoundary is defined as: letting e be epoch plus 1, reap be
\*   poolReg and retiring equals e, and claim be reap and RewardCred is a member
\*   of registered: epoch is less than MaxEpoch, and epoch in the next state
\*   equals e, and reserves in the next state equals reserves plus fees, and
\*   fees in the next state equals 0, and poolReg in the next state equals
\*   (poolReg and reap is not true), and retiring in the next state equals: if
\*   reap then 0, else retiring; and deposited in the next state equals: if reap
\*   then deposited minus PoolDeposit, else deposited; and balance in the next
\*   state equals: if claim then balance except that its RewardCred entry is the
\*   old entry plus PoolDeposit, else balance; and treasury in the next state
\*   equals: if reap and claim is not true and Mutation does not equal
\*   "DropUnclaimed" then treasury plus PoolDeposit, else treasury; and deleg in
\*   the next state equals: if reap and Mutation does not equal
\*   "KeepDelegations" then the function that maps every c in Creds to NoPool,
\*   else deleg; and reapedAt in the next state equals: if reap then e, else
\*   reapedAt; and seen in the next state equals the union of seen, (if reap and
\*   claim is not true then the set containing "unclaimed", else the empty set),
\*   and (if reap and there exists a c in Creds such that deleg of c equals
\*   Pool, then the set containing "delegation cleared", else the empty set);
\*   and baseReg in the next state equals (poolReg in the next state, or (View
\*   does not equal "Reaped" and reapedAt in the next state does not equal 0)),
\*   and baseRet in the next state equals: if poolReg in the next state then
\*   retiring in the next state, else if View does not equal "Reaped" and
\*   reapedAt in the next state does not equal 0 then reapedAt in the next
\*   state, else 0; and baseIsReg in the next state equals (poolReg in the next
\*   state, or (View equals "StaleMock" and reapedAt in the next state does not
\*   equal 0)), and ovReg in the next state equals FALSE, and ovRetKnown in the
\*   next state equals FALSE, and ovRet in the next state equals 0, and
\*   registered and utxo are unchanged."
EpochBoundary ==
    LET e     == epoch + 1
        reap  == poolReg /\ retiring = e
        claim == reap /\ RewardCred \in registered
    IN
    /\ epoch < MaxEpoch
    /\ epoch' = e
    /\ reserves' = reserves + fees
    /\ fees' = 0
    /\ poolReg' = (poolReg /\ ~reap)
    /\ retiring' = IF reap THEN 0 ELSE retiring
    /\ deposited' = IF reap THEN deposited - PoolDeposit ELSE deposited
    /\ balance' = IF claim THEN [balance EXCEPT ![RewardCred] = @ + PoolDeposit]
                  ELSE balance
    /\ treasury' = IF reap /\ ~claim /\ Mutation # "DropUnclaimed"
                   THEN treasury + PoolDeposit ELSE treasury
    /\ deleg' = IF reap /\ Mutation # "KeepDelegations"
                THEN [c \in Creds |-> NoPool]      \* delegations |>/ retired
                ELSE deleg
    /\ reapedAt' = IF reap THEN e ELSE reapedAt
    /\ seen' = seen \cup (IF reap /\ ~claim THEN {"unclaimed"} ELSE {})
                    \cup (IF reap /\ \E c \in Creds : deleg[c] = Pool
                          THEN {"delegation cleared"} ELSE {})
    \* The caller's view after the boundary, computed from the new ledger.
    /\ baseReg'   = (poolReg' \/ (View # "Reaped" /\ reapedAt' # 0))
    /\ baseRet'   = IF poolReg' THEN retiring'
                    ELSE IF View # "Reaped" /\ reapedAt' # 0 THEN reapedAt'
                    ELSE 0
    /\ baseIsReg' = (poolReg' \/ (View = "StaleMock" /\ reapedAt' # 0))
    /\ ovReg' = FALSE
    /\ ovRetKnown' = FALSE
    /\ ovRet' = 0
    /\ UNCHANGED <<registered, utxo>>

\* In English: at the last epoch the model stops; this step changes nothing,
\* so TLC does not report the end as a deadlock.
\* Literally: "Done is defined as: epoch equals MaxEpoch, and vars is
\*   unchanged."
Done ==
    /\ epoch = MaxEpoch
    /\ UNCHANGED vars

\* In English: "Each step is a transaction, a withdrawal, a reward, a new block,
\* an epoch boundary, or the end."
\* Literally: "Next is defined as: there exists a c in Certs such that Tx of c;
\*   or there exists a c in Creds such that Withdraw of c or Reward of c; or
\*   NewBlock; or EpochBoundary; or Done."
Next ==
    \/ \E c \in Certs : Tx(c)
    \/ \E c \in Creds : Withdraw(c) \/ Reward(c)
    \/ NewBlock
    \/ EpochBoundary
    \/ Done

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must always be true.                                               *)

\* In English: every variable holds the kind of value it should.
\* Literally: "TypeOK is defined as: epoch is a member of 0 through MaxEpoch,
\*   and registered is a subset of Creds, and balance is a member of the set of
\*   functions from Creds to 0 through Total, and deleg is a member of the set
\*   of functions from Creds to the set containing Pool and NoPool, and poolReg
\*   is a member of BOOLEAN, and retiring is a member of 0 through (MaxEpoch
\*   plus EMax plus 1), and ovReg is a member of BOOLEAN, and ovRetKnown is a
\*   member of BOOLEAN, and ovRet is a member of 0 through (MaxEpoch plus EMax
\*   plus 1)."
TypeOK ==
    /\ epoch \in 0..MaxEpoch
    /\ registered \subseteq Creds
    /\ balance \in [Creds -> 0..Total]
    /\ deleg \in [Creds -> {Pool, NoPool}]
    /\ poolReg \in BOOLEAN
    /\ retiring \in 0..(MaxEpoch + EMax + 1)
    /\ ovReg \in BOOLEAN
    /\ ovRetKnown \in BOOLEAN
    /\ ovRet \in 0..(MaxEpoch + EMax + 1)

\* In English: the reward balances of the credentials in S, added up.
\* RECURSIVE lets a definition use itself: take any credential out of S, add
\* its balance to the sum of the rest.
RECURSIVE SumBalances(_)
\* Literally: "SumBalances of S is defined as: if S equals the empty set then 0,
\*   else, letting c be the x, chosen from S, such that TRUE: balance of c plus
\*   SumBalances of (S without the members of the set containing c)."
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE LET c == CHOOSE x \in S : TRUE      \* any one credential in S
         IN balance[c] + SumBalances(S \ {c})

\* In English: the sum of every pot is the starting total: no ada is made or
\* lost by any step [R5].
\* Literally: "ValuePreserved is defined as: utxo plus deposited plus fees plus
\*   treasury plus reserves plus SumBalances of Creds equals Total."
ValuePreserved ==
    utxo + deposited + fees + treasury + reserves + SumBalances(Creds) = Total

\* In English: the deposit pot holds exactly one key deposit per registered
\* credential and one pool deposit for a registered pool (obligation, [S4]
\* epoch.tex 244-250; the reference asserts it after POOLREAP [R3]).
\* Literally: "DepositsMatchObligation is defined as: deposited equals
\*   KeyDeposit times the number of members of registered, plus (if poolReg then
\*   PoolDeposit, else 0)."
DepositsMatchObligation ==
    deposited = KeyDeposit * Cardinality(registered)
                + (IF poolReg THEN PoolDeposit ELSE 0)

\* In English: only a registered credential delegates, and only to a
\* registered pool (after POOLREAP clears delegations to a retired pool).
\* Literally: "DelegationsWellFormed is defined as: for all c in Creds, if deleg
\*   of c equals Pool, then c is a member of registered and poolReg."
DelegationsWellFormed ==
    \A c \in Creds : deleg[c] = Pool => c \in registered /\ poolReg

\* In English: a scheduled retirement is for a registered pool and lies in
\* the future (POOLREAP runs at the start of the retirement epoch).
\* Literally: "RetirementPending is defined as: if retiring does not equal 0,
\*   then poolReg and retiring is greater than epoch and retiring is less than
\*   or equal to epoch plus EMax."
RetirementPending ==
    retiring # 0 => poolReg /\ retiring > epoch /\ retiring <= epoch + EMax

\* In English: gOuroboros accepts exactly the certificates the ledger
\* accepts, in every state of every block, and charges the same deposit
\* for each one it accepts.
\* Literally: "GoAgrees is defined as: for all c in Certs, GoAccepts of c equals
\*   SpecAccepts of c, and if SpecAccepts of c, then GoDeposit of c equals
\*   SpecDeposit of c."
GoAgrees ==
    \A c \in Certs :
        /\ GoAccepts(c) = SpecAccepts(c)
        /\ SpecAccepts(c) => GoDeposit(c) = SpecDeposit(c)

-----------------------------------------------------------------------------
(* Reachability probes. Each claims something never happens; a config that *)
(* checks one must FAIL, which shows the passing configs are not vacuous.  *)

\* In English: "A reaped pool's deposit never goes unclaimed."
\* Literally: "ProbeUnclaimedNeverHappens is defined as: "unclaimed" is not a
\*   member of seen."
ProbeUnclaimedNeverHappens        == "unclaimed" \notin seen
\* In English: "Reaping never clears a delegation."
\* Literally: "ProbeDelegationNeverCleared is defined as: "delegation cleared"
\*   is not a member of seen."
ProbeDelegationNeverCleared       == "delegation cleared" \notin seen
\* In English: "A re-registration never cancels a pending retirement."
\* Literally: "ProbeReRegNeverCancels is defined as: "reRegCancelsRetirement" is
\*   not a member of seen."
ProbeReRegNeverCancels            == "reRegCancelsRetirement" \notin seen
\* In English: "A reaped pool is never registered again."
\* Literally: "ProbeReapedPoolNeverRegistered is defined as: "reaped pool
\*   registered again" is not a member of seen."
ProbeReapedPoolNeverRegistered    == "reaped pool registered again" \notin seen
=============================================================================
