--------------------------- MODULE ByronDelegation ---------------------------
(***************************************************************************)
(* Byron heavyweight delegation: genesis keys post certificates naming a   *)
(* delegate that signs blocks for them. A certificate is scheduled when    *)
(* its block is applied and takes effect 2k slots later.                   *)
(*                                                                         *)
(* The model runs two copies of the delegation state side by side over the *)
(* same chain of blocks: the reference implementation's, and gOuroboros'   *)
(* PBFTDelegationState. Every block offers a payload of up to two          *)
(* certificates; both decide whether the payload is valid, and when both   *)
(* accept, both apply it and tick. The PBFT header check that uses the     *)
(* resulting map is in specs/13-consensus, not here.                       *)
(*                                                                         *)
(* gOuroboros keeps the state as a value, but the caller owns the chain:   *)
(* it must call ApplyPayloadCbor once per main block, in slot order, with  *)
(* that block's epoch and slot, and keep the returned state only when the  *)
(* block is adopted. The model's Block step is that contract.              *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   Specification (eras/byron/ledger/formal-spec/delegation.tex):         *)
(*   [S1] 139-175 SDELEG: (e_d, vk_s) not in eks; 0 <= e_d - e <= 1;       *)
(*        d = 2k; (s + d, (vk_s, _)) not in sds. Adds (s + d, (vk_s,vk_d)) *)
(*        to sds and (e_d, vk_s) to eks.                                   *)
(*   [S2] 279-305 ADELEG: vk_d not in range dms and any earlier slot for  *)
(*        vk_s is below s: dms := dms (+) {vk_s -> vk_d}. Otherwise no-op. *)
(*   Reference (eras/byron/ledger/impl/src/Cardano/Chain/Delegation/       *)
(*   Validation/):                                                         *)
(*   [R1] Scheduling.hs 177-234 scheduleCertificate: the delegator is a   *)
(*        genesis key; currentEpoch <= epoch <= currentEpoch + 1; not in  *)
(*        keyEpochDelegations; no scheduled delegation by the delegator   *)
(*        at the same activation slot; activation slot = slot + 2k.       *)
(*   [R2] Activation.hs 65-79 activateDelegation: delegate notMemberR     *)
(*        delegationMap, and previous slot < slot or slot = 0.            *)
(*   [R3] Interface.hs 94-137 initialState: every genesis key maps to    *)
(*        itself at slot 0, then the genesis certificates are scheduled   *)
(*        with k = 0 and ticked.                                           *)
(*   [R4] Interface.hs 148-217 updateDelegation: fold scheduleCertificate *)
(*        over the block's certificates (any error rejects the block),    *)
(*        then tick: activate every scheduled delegation with slot <=     *)
(*        current slot in order, keep schedules with slot >= current + 1, *)
(*        keep key-epochs with epoch >= current epoch.                     *)
(*   gOuroboros (commit d0b95845, consensus/byron/pbft_delegation.go):     *)
(*   [G1] NewPBFTDelegationState 55-137: self map, then genesis           *)
(*        delegations activated at slot 0.                                 *)
(*   [G2] Tick 152-180 and ApplyPayloadCbor 220-240: the fold and tick.   *)
(*   [G3] scheduleCertificate 282-353: the checks of [R1].                 *)
(*   [G4] activate and delegateIsActive (PR 3174 head faad03cd): [R2].   *)
(*        On main (delegateIsActiveForOther) the delegate only had to be  *)
(*        free of OTHER delegators; Mutation "OwnEntryExempt" is main.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Genesis,       \* the genesis keys, e.g. {"g1", "g2"}
    Outsiders,     \* keys that are not genesis keys, e.g. {"d1"}
    GenesisDeleg,  \* the genesis key that starts delegated
    GenesisDel,    \* ... and the outsider it starts delegated to
    K,             \* the security parameter k
    SlotsPerEpoch, \* slots in an epoch
    MaxSlot,       \* the last slot a block may have (keeps it finite)
    Mutation       \* "none", or one deliberate gOuroboros mistake

\* In English: every key, genesis or not.
\* Literally: "Keys is defined as the union of Genesis and Outsiders."
Keys == Genesis \cup Outsiders

\* The epoch a slot is in.
\* Literally: "EpochOf of s is defined as s integer-divided by SlotsPerEpoch."
EpochOf(s) == s \div SlotsPerEpoch

VARIABLES
    slot,       \* the slot of the last applied block (0: genesis only)
    rSds,       \* reference: scheduled delegations, a sequence of
                \*   [at, dlg, del] in the order they were scheduled
    rEks,       \* reference: the set of <<epoch, delegator>> already used
    rDms,       \* reference: rDms[g] is the active delegate of genesis key g
    rDws,       \* reference: rDws[g] is the slot g's delegation activated
    gSds, gEks, gDms, gDws,  \* the same four, in gOuroboros
    lastRef,    \* did the reference accept the last payload offered?
    lastGo,     \* did gOuroboros accept it?
    issued      \* issued[<<e, g>>]: certificates gOuroboros accepted from g
                \*   for epoch e (history, for OncePerEpoch)

\* In English: "The reference's variables."
\* Literally: "refVars is defined as the tuple of rSds, rEks, rDms and rDws."
refVars == <<rSds, rEks, rDms, rDws>>
\* In English: "gOuroboros' variables."
\* Literally: "goVars is defined as the tuple of gSds, gEks, gDms and gDws."
goVars  == <<gSds, gEks, gDms, gDws>>
\* Literally: "vars is defined as the tuple of slot, refVars, goVars, lastRef,
\*   lastGo and issued."
vars    == <<slot, refVars, goVars, lastRef, lastGo, issued>>

\* A certificate: who delegates, to whom, for which epoch. Epochs up to two
\* past the last one a block can be in, so the window check has something
\* to reject.
\* Literally: "Certs is defined as the set of records whose field dlg is a
\*   member of Keys, whose field del is a member of Keys, and whose field ep is
\*   a member of 0 through (EpochOf of MaxSlot plus 2)."
Certs == [dlg : Keys, del : Keys, ep : 0..(EpochOf(MaxSlot) + 2)]

\* Payloads: no certificate, one, or two.
\* Literally: "Payloads is defined as the union of the set containing the empty
\*   sequence, the set of the tuple of c, for every c that is a member of Certs,
\*   and the set of the tuple of c and d, for every c and d that are members of
\*   Certs."
Payloads == {<<>>} \cup {<<c>> : c \in Certs} \cup {<<c, d>> : c, d \in Certs}

\* In English: every value function f takes.
\* Literally: "Range of f is defined as the set of f of x, for every x that is a
\*   member of the domain of f."
Range(f) == {f[x] : x \in DOMAIN f}

-----------------------------------------------------------------------------
(* Scheduling [S1][R1][G3].                                                *)

\* In English: certificate c may be scheduled in a block at slot s in epoch
\* e, given the scheduled list sds and the used key-epochs eks.
\* Literally: "CanSchedule of sds, eks, e, s, c, act and window is defined as:
\*   c's dlg is a member of Genesis, and e is less than or equal to c's ep and
\*   c's ep is less than or equal to e plus window, and the tuple of c's ep and
\*   c's dlg is not a member of eks, and it is not true that there exists an i
\*   in the domain of sds such that sds of i's at equals act and sds of i's dlg
\*   equals c's dlg."
CanSchedule(sds, eks, e, s, c, act, window) ==
    /\ c.dlg \in Genesis                                  \* NonGenesisDelegator
    /\ e <= c.ep /\ c.ep <= e + window                    \* WrongEpoch
    /\ <<c.ep, c.dlg>> \notin eks                         \* MultipleDelegationsForEpoch
    /\ ~\E i \in DOMAIN sds :                             \* MultipleDelegationsForSlot
          sds[i].at = act /\ sds[i].dlg = c.dlg

\* In English: the scheduling state after certificate c.
\* Literally: "Scheduled of sds, act and c is defined as sds with the record
\*   whose field at is act, field dlg is c's dlg, and field del is c's del
\*   appended."
Scheduled(sds, act, c) == Append(sds, [at |-> act, dlg |-> c.dlg, del |-> c.del])

\* In English: fold the payload's certificates through scheduling. Returns
\* [ok, sds, eks]; ok is FALSE when any certificate fails.
RECURSIVE Fold(_, _, _, _, _, _, _)
\* Literally: "Fold of sds, eks, e, s, p, d and window is defined as: if p
\*   equals the empty sequence then the record whose field ok is TRUE, field sds
\*   is sds and field eks is eks; else, letting c be the head of p: if
\*   CanSchedule of sds, eks, e, s, c, s plus d, and window, then Fold of
\*   Scheduled of sds, s plus d and c, the union of eks and the set containing
\*   the tuple of c's ep and c's dlg, e, s, the tail of p, d, and window; else
\*   the record whose field ok is FALSE, field sds is sds and field eks is eks."
Fold(sds, eks, e, s, p, d, window) ==
    IF p = <<>> THEN [ok |-> TRUE, sds |-> sds, eks |-> eks]
    ELSE LET c == Head(p)
         IN IF CanSchedule(sds, eks, e, s, c, s + d, window)
            THEN Fold(Scheduled(sds, s + d, c), eks \cup {<<c.ep, c.dlg>>},
                      e, s, Tail(p), d, window)
            ELSE [ok |-> FALSE, sds |-> sds, eks |-> eks]

-----------------------------------------------------------------------------
(* Activation [S2][R2][G4].                                                *)

\* In English: the reference activation of one scheduled delegation x.
\* Literally: "RefActivate of st and x is defined as: if x's del is not a member
\*   of Range of st's dms, and (st's dws of x's dlg is less than x's at, or x's
\*   at equals 0), then the record whose field dms is st's dms except that its
\*   x's dlg entry is x's del, and whose field dws is st's dws except that its
\*   x's dlg entry is x's at; else st."
RefActivate(st, x) ==
    IF /\ x.del \notin Range(st.dms)                      \* delegate notMemberR map
       /\ (st.dws[x.dlg] < x.at \/ x.at = 0)
    THEN [dms |-> [st.dms EXCEPT ![x.dlg] = x.del],
          dws |-> [st.dws EXCEPT ![x.dlg] = x.at]]
    ELSE st

\* In English: the gOuroboros activation: the delegate must not be active
\* for any delegator, the delegator itself included (delegateIsActive).
\* "OwnEntryExempt" is main before the fix: only other delegators count, so
\* re-delegating to the current delegate rewrites the activation slot.
\* Literally: "GoActivate of st and x is defined as: if (in the case Mutation
\*   equals "NoInjectivity", TRUE; in the case Mutation equals "OwnEntryExempt",
\*   it is not true that there exists a g in Genesis such that g does not equal
\*   x's dlg and st's dms of g equals x's del; in every other case, x's del is
\*   not a member of Range of st's dms), and (st's dws of x's dlg is less than
\*   x's at, or x's at equals 0), then the record whose field dms is st's dms
\*   except that its x's dlg entry is x's del, and whose field dws is st's dws
\*   except that its x's dlg entry is x's at; else st."
GoActivate(st, x) ==
    IF /\ CASE Mutation = "NoInjectivity"  -> TRUE
              [] Mutation = "OwnEntryExempt" ->
                   ~\E g \in Genesis : g # x.dlg /\ st.dms[g] = x.del
              [] OTHER -> x.del \notin Range(st.dms)
       /\ (st.dws[x.dlg] < x.at \/ x.at = 0)
    THEN [dms |-> [st.dms EXCEPT ![x.dlg] = x.del],
          dws |-> [st.dws EXCEPT ![x.dlg] = x.at]]
    ELSE st

\* In English: activate, in order, every scheduled delegation due by slot s.
RECURSIVE ActivateAll(_, _, _, _)
\* Literally: "ActivateAll of st, sds, s and ref is defined as: if sds equals
\*   the empty sequence then st, else, letting x be the head of sds, and st2 be:
\*   if x's at is greater than s then st, else if ref then RefActivate of st and
\*   x, else GoActivate of st and x: ActivateAll of st2, the tail of sds, s, and
\*   ref."
ActivateAll(st, sds, s, ref) ==
    IF sds = <<>> THEN st
    ELSE LET x == Head(sds)
             st2 == IF x.at > s THEN st
                    ELSE IF ref THEN RefActivate(st, x) ELSE GoActivate(st, x)
         IN ActivateAll(st2, Tail(sds), s, ref)

\* In English: drop schedules that have activated and key-epochs from past
\* epochs [R4].
\* Literally: "Keep of sds and s is defined as the subsequence of sds of every x
\*   such that x's at is greater than or equal to s plus 1."
Keep(sds, s) == SelectSeq(sds, LAMBDA x : x.at >= s + 1)
\* Literally: "KeepEks of eks and e is defined as the set of every p in eks such
\*   that element 1 of p is greater than or equal to e."
KeepEks(eks, e) == {p \in eks : p[1] >= e}

-----------------------------------------------------------------------------
(* The steps.                                                              *)

\* In English: genesis [R3][G1]. Every genesis key delegates to itself;
\* GenesisDeleg's certificate (epoch 0) activates at slot 0.
\* Literally: "Init is defined as: letting self be the function that maps every
\*   g in Genesis to g, zero be the function that maps every g in Genesis to 0,
\*   and dms0 be self except that its GenesisDeleg entry is GenesisDel: slot
\*   equals 0, and rSds equals the empty sequence and gSds equals the empty
\*   sequence, and rEks equals the set containing the tuple of 0 and
\*   GenesisDeleg and gEks equals the set containing the tuple of 0 and
\*   GenesisDeleg, and rDms equals dms0 and gDms equals dms0, and rDws equals
\*   zero and gDws equals zero, and lastRef equals TRUE and lastGo equals TRUE,
\*   and issued equals the function that maps every p in the set of pairs of a
\*   member of 0 through (EpochOf of MaxSlot plus 2) and a member of Genesis to:
\*   if p equals the tuple of 0 and GenesisDeleg then 1, else 0."
Init ==
    LET self  == [g \in Genesis |-> g]
        zero  == [g \in Genesis |-> 0]
        dms0  == [self EXCEPT ![GenesisDeleg] = GenesisDel]
    IN /\ slot = 0
       /\ rSds = <<>> /\ gSds = <<>>
       /\ rEks = {<<0, GenesisDeleg>>} /\ gEks = {<<0, GenesisDeleg>>}
       /\ rDms = dms0 /\ gDms = dms0
       /\ rDws = zero /\ gDws = zero
       /\ lastRef = TRUE /\ lastGo = TRUE
       /\ issued = [p \in (0..(EpochOf(MaxSlot) + 2)) \X Genesis |->
                      IF p = <<0, GenesisDeleg>> THEN 1 ELSE 0]

\* In English: a main block at slot s carrying payload p. Both sides decide.
\* A payload both accept is applied and ticked on both sides; one both
\* reject leaves the state alone (the block is not adopted). A
\* disagreement is recorded in lastRef/lastGo and the state is left alone.
\* Literally: "Block of s and p is defined as: letting e be EpochOf of s; ref be
\*   Fold of rSds, rEks, e, s, p, 2 times K, and 1; go be Fold of gSds, gEks, e,
\*   s, p, (in the case Mutation equals "NoDelay", 0; in the case Mutation
\*   equals "LongDelay", 2 times K plus 1; in every other case, 2 times K), and
\*   (if Mutation equals "WideEpoch" then 2, else 1); rAct be ActivateAll of the
\*   record whose field dms is rDms and field dws is rDws, ref's sds, s, and
\*   TRUE; gAct be ActivateAll of the record whose field dms is gDms and field
\*   dws is gDws, go's sds, s, and FALSE; and goEks be: if Mutation equals
\*   "NoKeyEpoch" then gEks, else go's eks: lastRef in the next state equals
\*   ref's ok, and lastGo in the next state equals go's ok, and if ref's ok and
\*   go's ok, then (slot in the next state equals s, and rSds in the next state
\*   equals Keep of ref's sds and s, and rEks in the next state equals KeepEks
\*   of ref's eks and e, and rDms in the next state equals rAct's dms and rDws
\*   in the next state equals rAct's dws, and gSds in the next state equals: if
\*   Mutation equals "NoPrune" then go's sds, else Keep of go's sds and s; and
\*   gEks in the next state equals: if Mutation equals "NoPrune" then goEks,
\*   else KeepEks of goEks and e; and gDms in the next state equals gAct's dms
\*   and gDws in the next state equals gAct's dws), else slot, refVars and
\*   goVars are unchanged; and issued in the next state equals: if go's ok then
\*   the function that maps every q in the domain of issued to issued of q plus
\*   the number of members of the set of every i in the domain of p such that
\*   the tuple of p of i's ep and p of i's dlg equals q, else issued."
Block(s, p) ==
    LET e     == EpochOf(s)
        ref   == Fold(rSds, rEks, e, s, p, 2 * K, 1)
        go    == Fold(gSds, gEks, e, s, p,
                      CASE Mutation = "NoDelay"   -> 0
                        [] Mutation = "LongDelay" -> 2 * K + 1
                        [] OTHER                  -> 2 * K,
                      IF Mutation = "WideEpoch" THEN 2 ELSE 1)
        rAct  == ActivateAll([dms |-> rDms, dws |-> rDws], ref.sds, s, TRUE)
        gAct  == ActivateAll([dms |-> gDms, dws |-> gDws], go.sds, s, FALSE)
        goEks == IF Mutation = "NoKeyEpoch" THEN gEks ELSE go.eks
    IN /\ lastRef' = ref.ok
       /\ lastGo' = go.ok
       /\ IF ref.ok /\ go.ok
          THEN /\ slot' = s
               /\ rSds' = Keep(ref.sds, s)
               /\ rEks' = KeepEks(ref.eks, e)
               /\ rDms' = rAct.dms /\ rDws' = rAct.dws
               /\ gSds' = IF Mutation = "NoPrune" THEN go.sds ELSE Keep(go.sds, s)
               /\ gEks' = IF Mutation = "NoPrune" THEN goEks ELSE KeepEks(goEks, e)
               /\ gDms' = gAct.dms /\ gDws' = gAct.dws
          ELSE UNCHANGED <<slot, refVars, goVars>>
       \* the history counts every payload gOuroboros accepted, adopted or not
       /\ issued' = IF go.ok
                    THEN [q \in DOMAIN issued |->
                            issued[q] + Cardinality({i \in DOMAIN p :
                                <<p[i].ep, p[i].dlg>> = q})]
                    ELSE issued

\* In English: the next block is one or two slots on, with any payload.
\* Literally: "Next is defined as: there exists an s in (slot plus 1) through
\*   (slot plus 2) and a p in Payloads such that s is less than or equal to
\*   MaxSlot and Block of s and p; or (slot is greater than or equal to MaxSlot
\*   minus 1 and vars is unchanged)."
Next ==
    \/ \E s \in (slot + 1)..(slot + 2), p \in Payloads :
          s <= MaxSlot /\ Block(s, p)
    \/ (slot >= MaxSlot - 1 /\ UNCHANGED vars)   \* the run is over

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must hold.                                                         *)

\* In English: every variable holds the kind of value it should.
\* Literally: "TypeOK is defined as: slot is a member of 0 through MaxSlot, and
\*   rDms is a member of the set of functions from Genesis to Keys and gDms is a
\*   member of the set of functions from Genesis to Keys, and lastRef is a
\*   member of BOOLEAN and lastGo is a member of BOOLEAN."
TypeOK ==
    /\ slot \in 0..MaxSlot
    /\ rDms \in [Genesis -> Keys] /\ gDms \in [Genesis -> Keys]
    /\ lastRef \in BOOLEAN /\ lastGo \in BOOLEAN

\* In English: gOuroboros accepts exactly the payloads the reference
\* accepts.
\* Literally: "VerdictsAgree is defined as: lastRef equals lastGo."
VerdictsAgree == lastRef = lastGo

\* In English: gOuroboros' active delegation map is the reference's.
\* Literally: "MapsAgree is defined as: gDms equals rDms."
MapsAgree == gDms = rDms

\* In English: gOuroboros records the same activation slot for every key.
\* Literally: "SlotsAgree is defined as: gDws equals rDws."
SlotsAgree == gDws = rDws

\* In English: no two genesis keys share an active delegate, so a delegate
\* signs for at most one genesis key.
\* Literally: "GoInjective is defined as: for all g and h in Genesis, if g does
\*   not equal h, then gDms of g does not equal gDms of h."
GoInjective == \A g, h \in Genesis : g # h => gDms[g] # gDms[h]

\* In English: after every tick, nothing due is still scheduled, and no
\* key-epoch from a past epoch is kept.
\* Literally: "GoPruned is defined as: for all i in the domain of gSds, gSds of
\*   i's at is greater than slot, and for all q in gEks, element 1 of q is
\*   greater than or equal to EpochOf of slot."
GoPruned ==
    /\ \A i \in DOMAIN gSds : gSds[i].at > slot
    /\ \A q \in gEks : q[1] >= EpochOf(slot)

\* In English: gOuroboros never accepts two certificates from one genesis
\* key for the same epoch, counting payloads it accepted that the
\* reference rejected.
\* Literally: "OncePerEpoch is defined as: for all q in the domain of issued,
\*   issued of q is less than or equal to 1."
OncePerEpoch == \A q \in DOMAIN issued : issued[q] <= 1

\* In English: a scheduled delegation never activates sooner than 2k
\* slots after the block that carried it: every pending one is due within
\* (slot, slot + 2k].
\* Literally: "GoDelayed is defined as: for all i in the domain of gSds, gSds of
\*   i's at is less than or equal to slot plus 2 times K."
GoDelayed == \A i \in DOMAIN gSds : gSds[i].at <= slot + 2 * K

-----------------------------------------------------------------------------
(* Reachability probes: each is expected to be violated (named *Bug.cfg).  *)

\* A genesis key's delegation is revoked back to itself.
\* Literally: "ProbeRevoke is defined as: (rDms of GenesisDeleg equals
\*   GenesisDeleg) is not true."
ProbeRevoke == ~(rDms[GenesisDeleg] = GenesisDeleg)

\* The genesis outsider moves to the other genesis key.
\* Literally: "ProbeMove is defined as: (there exists a g in Genesis such that g
\*   does not equal GenesisDeleg and rDms of g equals GenesisDel) is not true."
ProbeMove == ~(\E g \in Genesis : g # GenesisDeleg /\ rDms[g] = GenesisDel)

\* A payload is rejected by both.
\* Literally: "ProbeRejected is defined as lastRef."
ProbeRejected == lastRef
=============================================================================
