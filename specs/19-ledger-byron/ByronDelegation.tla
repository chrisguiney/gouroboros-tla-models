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
(*   [G4] activate 355-368, delegateIsActiveForOther 370-381: like [R2],  *)
(*        but the delegate only has to be free of OTHER delegators.       *)
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

Keys == Genesis \cup Outsiders

\* The epoch a slot is in.
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

refVars == <<rSds, rEks, rDms, rDws>>
goVars  == <<gSds, gEks, gDms, gDws>>
vars    == <<slot, refVars, goVars, lastRef, lastGo, issued>>

\* A certificate: who delegates, to whom, for which epoch. Epochs up to two
\* past the last one a block can be in, so the window check has something
\* to reject.
Certs == [dlg : Keys, del : Keys, ep : 0..(EpochOf(MaxSlot) + 2)]

\* Payloads: no certificate, one, or two.
Payloads == {<<>>} \cup {<<c>> : c \in Certs} \cup {<<c, d>> : c, d \in Certs}

Range(f) == {f[x] : x \in DOMAIN f}

-----------------------------------------------------------------------------
(* Scheduling [S1][R1][G3].                                                *)

\* In English: certificate c may be scheduled in a block at slot s in epoch
\* e, given the scheduled list sds and the used key-epochs eks.
CanSchedule(sds, eks, e, s, c, act, window) ==
    /\ c.dlg \in Genesis                                  \* NonGenesisDelegator
    /\ e <= c.ep /\ c.ep <= e + window                    \* WrongEpoch
    /\ <<c.ep, c.dlg>> \notin eks                         \* MultipleDelegationsForEpoch
    /\ ~\E i \in DOMAIN sds :                             \* MultipleDelegationsForSlot
          sds[i].at = act /\ sds[i].dlg = c.dlg

\* In English: the scheduling state after certificate c.
Scheduled(sds, act, c) == Append(sds, [at |-> act, dlg |-> c.dlg, del |-> c.del])

\* In English: fold the payload's certificates through scheduling. Returns
\* [ok, sds, eks]; ok is FALSE when any certificate fails.
RECURSIVE Fold(_, _, _, _, _, _, _)
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
RefActivate(st, x) ==
    IF /\ x.del \notin Range(st.dms)                      \* delegate notMemberR map
       /\ (st.dws[x.dlg] < x.at \/ x.at = 0)
    THEN [dms |-> [st.dms EXCEPT ![x.dlg] = x.del],
          dws |-> [st.dws EXCEPT ![x.dlg] = x.at]]
    ELSE st

\* In English: the gOuroboros activation: the delegate must not be active
\* for a different delegator (delegateIsActiveForOther).
GoActivate(st, x) ==
    IF /\ (Mutation = "NoInjectivity"
           \/ ~\E g \in Genesis : g # x.dlg /\ st.dms[g] = x.del)
       /\ (st.dws[x.dlg] < x.at \/ x.at = 0)
    THEN [dms |-> [st.dms EXCEPT ![x.dlg] = x.del],
          dws |-> [st.dws EXCEPT ![x.dlg] = x.at]]
    ELSE st

\* In English: activate, in order, every scheduled delegation due by slot s.
RECURSIVE ActivateAll(_, _, _, _)
ActivateAll(st, sds, s, ref) ==
    IF sds = <<>> THEN st
    ELSE LET x == Head(sds)
             st2 == IF x.at > s THEN st
                    ELSE IF ref THEN RefActivate(st, x) ELSE GoActivate(st, x)
         IN ActivateAll(st2, Tail(sds), s, ref)

\* In English: drop schedules that have activated and key-epochs from past
\* epochs [R4].
Keep(sds, s) == SelectSeq(sds, LAMBDA x : x.at >= s + 1)
KeepEks(eks, e) == {p \in eks : p[1] >= e}

-----------------------------------------------------------------------------
(* The steps.                                                              *)

\* In English: genesis [R3][G1]. Every genesis key delegates to itself;
\* GenesisDeleg's certificate (epoch 0) activates at slot 0.
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
Next ==
    \/ \E s \in (slot + 1)..(slot + 2), p \in Payloads :
          s <= MaxSlot /\ Block(s, p)
    \/ (slot >= MaxSlot - 1 /\ UNCHANGED vars)   \* the run is over

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* What must hold.                                                         *)

TypeOK ==
    /\ slot \in 0..MaxSlot
    /\ rDms \in [Genesis -> Keys] /\ gDms \in [Genesis -> Keys]
    /\ lastRef \in BOOLEAN /\ lastGo \in BOOLEAN

\* In English: gOuroboros accepts exactly the payloads the reference
\* accepts.
VerdictsAgree == lastRef = lastGo

\* In English: gOuroboros' active delegation map is the reference's.
MapsAgree == gDms = rDms

\* In English: no two genesis keys share an active delegate, so a delegate
\* signs for at most one genesis key.
GoInjective == \A g, h \in Genesis : g # h => gDms[g] # gDms[h]

\* In English: after every tick, nothing due is still scheduled, and no
\* key-epoch from a past epoch is kept.
GoPruned ==
    /\ \A i \in DOMAIN gSds : gSds[i].at > slot
    /\ \A q \in gEks : q[1] >= EpochOf(slot)

\* In English: gOuroboros never accepts two certificates from one genesis
\* key for the same epoch, counting payloads it accepted that the
\* reference rejected.
OncePerEpoch == \A q \in DOMAIN issued : issued[q] <= 1

\* In English: a scheduled delegation never activates sooner than 2k
\* slots after the block that carried it: every pending one is due within
\* (slot, slot + 2k].
GoDelayed == \A i \in DOMAIN gSds : gSds[i].at <= slot + 2 * K

-----------------------------------------------------------------------------
(* Reachability probes: each is expected to be violated (named *Bug.cfg).  *)

\* A genesis key's delegation is revoked back to itself.
ProbeRevoke == ~(rDms[GenesisDeleg] = GenesisDeleg)

\* The genesis outsider moves to the other genesis key.
ProbeMove == ~(\E g \in Genesis : g # GenesisDeleg /\ rDms[g] = GenesisDel)

\* The two sides record a different activation slot for some key (a
\* re-delegation to the delegate already active: the reference does
\* nothing, gOuroboros rewrites the slot). The maps still agree.
ProbeSlotsDiffer == gDws = rDws

\* A payload is rejected by both.
ProbeRejected == lastRef
=============================================================================
