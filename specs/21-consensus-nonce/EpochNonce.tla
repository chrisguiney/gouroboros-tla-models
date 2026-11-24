---------------------------- MODULE EpochNonce ----------------------------
(***************************************************************************)
(* The epoch nonce: how each block's VRF output is folded into the        *)
(* evolving nonce, how the candidate nonce freezes a stabilisation window *)
(* before the end of the epoch, and how the next epoch's nonce is made    *)
(* from the candidate, the lab nonce of the previous epoch and the extra  *)
(* entropy parameter.                                                     *)
(*                                                                         *)
(* The model has two halves.                                               *)
(*   1. The reference: the nonce state ouroboros-consensus keeps, computed *)
(*      from scratch from the chain (RefFold). A rollback is free here:   *)
(*      the state is a function of the chain.                              *)
(*   2. A caller of gOuroboros. gOuroboros keeps no chain state; it offers *)
(*      CalculateRollingNonce and CalculateEpochNonce and leaves the rest *)
(*      to the caller (Dingo). The caller keeps the nonces, ticks at each  *)
(*      epoch change, freezes the candidate, keeps one snapshot per block  *)
(*      and restores a snapshot on rollback. The model checks that what    *)
(*      the caller holds is always what the reference holds.              *)
(*                                                                         *)
(* Hashing is symbolic. A nonce is a term; Hash(x) is blake2b_256 of x,   *)
(* and two terms are equal only if they were built the same way, so the   *)
(* model treats the hash as injective (no collisions).                    *)
(*                                                                         *)
(* Sources (links and quotes in specs/21-consensus-nonce/README.md).       *)
(*   Specification: cardano-ledger 1210d37fe6bd, eras/shelley/formal-spec: *)
(*   [S1] chain.tex 600-640: UPDN. The evolving nonce takes every block;  *)
(*        the candidate takes it only while                               *)
(*        s < firstSlot(epoch(s)+1) - StabilityWindow.                    *)
(*   [S2] chain.tex 514-533: TICKN. At a new epoch,                        *)
(*        eta0 := etaC * etaH * extraEntropy and etaH := etaPH.           *)
(*   [S3] chain.tex 1691-1697, 1748, 1809: etaPH is the hash of the last  *)
(*        applied block itself (lab' holds bhash of the new block).       *)
(*   [S4] errata.tex 35-53: the implementation freezes the candidate with *)
(*        the 3k/f StabilityWindow, the spec meant the 4k/f               *)
(*        RandomnessStabilisationWindow; consensus uses 4k/f from Conway. *)
(*   Reference implementation:                                             *)
(*   [R1] cardano-ledger libs/cardano-ledger-core/src/Cardano/Ledger/      *)
(*        BaseTypes.hs 607-612: the operator *. Two nonces hash their     *)
(*        concatenation; NeutralNonce is the identity on both sides.      *)
(*   [R2] BaseTypes.hs 615-619: a TPraos block nonce is                    *)
(*        blake2b_256(VRF output), not the raw 64-byte output;            *)
(*        libs/cardano-protocol/src/Cardano/Protocol/TPraos/               *)
(*        BlockHeader.hs 468-469 (bnonce). Praos: libs/cardano-protocol/  *)
(*        src/Cardano/Protocol/Praos/VRF.hs 97-134 (vrfNonceValue,        *)
(*        blake2b_256(blake2b_256("N" || output))).                       *)
(*   [R3] libs/cardano-protocol-tpraos/src/Cardano/Protocol/TPraos/Rules/ *)
(*        Updn.hs 60-75 (TPraos, StabilityWindow, strict <), and          *)
(*        ouroboros-consensus ec239d57f618 ouroboros-consensus-protocol/  *)
(*        .../Protocol/PolyPraos.hs 700-742 (Praos, the configured        *)
(*        praosRandomnessStabilisationWindow, strict <).                  *)
(*   [R4] Tickn.hs 71-81 (TPraos: etaC * etaH * extraEntropy) and         *)
(*        PolyPraos.hs 606-640 (Praos: no extra entropy).                 *)
(*   [R5] API.hs 543-600 and PolyPraos.hs 713: after a block the lab      *)
(*        nonce is prevHashToNonce of that block's PREVIOUS hash, not its *)
(*        own; BlockHeader.hs 290-298: GenesisHash maps to NeutralNonce.  *)
(*   [R6] ouroboros-consensus .../Protocol/Ledger/Util.hs 22-42: a tick is*)
(*        a new epoch when the block's epoch is after the last block's    *)
(*        (Origin counts as epoch 0), once however many epochs passed.    *)
(*   [R7] ouroboros-consensus-cardano .../Cardano/CanHardFork.hs 393-423: *)
(*        at the Byron-to-Shelley transition evolving, candidate and      *)
(*        epoch nonce are the initial nonce, the last-epoch-block nonce   *)
(*        and the lab nonce NeutralNonce; API.hs 451-468 does the same    *)
(*        for a chain that starts in Shelley.                              *)
(*   [R8] ouroboros-consensus-cardano .../Cardano/Node.hs 590-597, 692-702:*)
(*        Babbage and TPraos eras freeze at 3k/f, Conway on at 4k/f.      *)
(*   [R9] Praos/VRF.hs 64-78 and TPraos/BlockHeader.hs 422-435: the VRF   *)
(*        input omits a NeutralNonce epoch nonce (slot bytes only).       *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit d0b95845):              *)
(*   [G1] ledger/common/nonce.go CalculateRollingNonce 92-150              *)
(*   [G2] ledger/common/nonce.go CalculateEpochNonce 152-187               *)
(*   [G3] vrf/vrf.go MkInputVrf 245-267, MkSeedTPraos 313-345;             *)
(*        consensus/block.go ComputeVRFInput 523-544;                      *)
(*        ledger/verify_block.go verifyNonceVrf 775-793                    *)
(*   The caller is Dingo (ledger/eras/*.go, ledger/extra_entropy.go        *)
(*   assembleEpochNonce, ledger/epoch_lab_nonce.go).                       *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla and       *)
(* specs/13-consensus/ChainSelection.tla (SubSeq). New here:              *)
(*   RECURSIVE F(_)  announces that F's definition uses F itself           *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    SlotsPerEpoch,  \* slots in an epoch
    Window,         \* the randomness stabilisation window, in slots
    MaxSlot,        \* the last slot a block may occupy (keeps the model finite)
    MaxBlocks,      \* how many distinct blocks may ever be made
    MaxRollback,    \* the deepest rollback, in blocks (k)
    Start,          \* "Genesis": the chain starts in Shelley at slot 0;
                    \* "Byron": Shelley starts at epoch 1 after a Byron chain
    InitNonce,      \* "GenesisHash": the initial nonce is the Shelley genesis
                    \*   file hash, as every public network has it;
                    \* "Neutral": NeutralNonce, which the reference allows
    Era,            \* "TPraos" or "Praos": how a VRF output becomes a nonce
    EntropyEpochs,  \* epochs whose extraEntropy parameter is set (TPraos only)
    Caller,         \* how the caller uses gOuroboros:
                    \*  "Contract": calls gOuroboros only where it computes
                    \*    the reference's value, and applies * itself for a
                    \*    NeutralNonce operand (the contract main needs);
                    \*  "Dingo": what Dingo does today;
                    \*  "Direct": passes everything to gOuroboros, with
                    \*    NeutralNonce as 32 zero bytes
    Operand,        \* what the caller passes CalculateRollingNonce:
                    \*  "Nonce": the block's 32-byte nonce [R2]
                    \*  "Raw": the 64-byte VRF output
    GoFix,          \* gOuroboros fixes in force, a subset of
                    \*  {"Neutral", "RawOperand"}; {} is main
    Mutation        \* "none", or one deliberate mistake (see below)

-----------------------------------------------------------------------------
(* Symbolic values.                                                         *)

Neutral   == <<"NeutralNonce">>   \* the reference's identity nonce
Zero      == <<"zero32">>         \* how a []byte caller spells NeutralNonce
Empty     == <<"noBytes">>        \* an empty slice (extraEntropy's NeutralNonce)
GenesisHash == <<"GenesisHash">> \* the predecessor of a chain's first block

\* In English: blake2b_256 of x, and blake2b_256(a || b). Every value is a
\* tuple whose first element names what it is, so TLC can compare any two.
Hash(x)   == <<"blake2b", x>>
Cat(a, b) == Hash(<<"cat", a, b>>)

\* In English: the 64-byte VRF output in block b's header, and block b's
\* header hash.
RawVrf(b)     == <<"vrfOutput", b>>
HeaderHash(b) == <<"headerHash", b>>
ByronTipHash  == <<"lastByronHeaderHash">>

\* In English: the nonce block b contributes [R2]. TPraos hashes the nonce
\* VRF output once; Praos range-extends the single VRF output with "N" and
\* hashes the result again.
BlockNonce(b) == IF Era = "TPraos"
                 THEN Hash(RawVrf(b))
                 ELSE Hash(Hash(<<"N", RawVrf(b)>>))

\* In English: the reference's nonce operator * [R1]. Two nonces hash their
\* concatenation; NeutralNonce on either side gives back the other.
Op(a, b) == CASE a = Neutral -> b
              [] b = Neutral -> a
              [] OTHER       -> Cat(a, b)

\* In English: the initial nonce [R7].
InitialNonce == IF InitNonce = "GenesisHash" THEN <<"shelleyGenesisHash">>
                ELSE Neutral

\* In English: the extra entropy protocol parameter in force in epoch e;
\* NeutralNonce when unset [R4].
ExtraEntropy(e) == IF e \in EntropyEpochs THEN <<"extraEntropy", e>>
                   ELSE Neutral

-----------------------------------------------------------------------------
(* Slots and epochs.                                                        *)

FirstSlot(e) == e * SlotsPerEpoch           \* first slot of epoch e
EpochOf(s)   == s \div SlotsPerEpoch        \* the epoch slot s is in
FirstShelleySlot == IF Start = "Byron" THEN SlotsPerEpoch ELSE 0

\* In English: a block in slot s is still before its epoch's freeze point:
\* s plus the window is strictly before the next epoch's first slot [S1][R3].
BeforeFreeze(s) == s + Window < FirstSlot(EpochOf(s) + 1)

\* In English: the hash a block names as its predecessor. The first block's
\* predecessor is the genesis (a chain that starts in Shelley) or the last
\* Byron block.
PrevOf(seq, i) == IF i = 1
                  THEN (IF Start = "Genesis" THEN GenesisHash ELSE ByronTipHash)
                  ELSE HeaderHash(seq[i - 1].id)

\* In English: prevHashToNonce [R5]: GenesisHash is NeutralNonce, any block
\* hash is a nonce.
PrevHashToNonce(p) == IF p = GenesisHash THEN Neutral ELSE p

-----------------------------------------------------------------------------
(* The reference, computed from the chain.                                  *)

\* In English: the nonce state before any Shelley block [R7]: every nonce is
\* the initial nonce except the two hash nonces, which are NeutralNonce.
\* last is the epoch of the last block (Origin and the Byron era count as 0).
RefInit == [ev   |-> InitialNonce,   \* evolving nonce
            cand |-> InitialNonce,   \* candidate nonce
            eta0 |-> InitialNonce,   \* epoch nonce
            lab  |-> Neutral,        \* lab nonce
            leb  |-> Neutral,        \* last-epoch-block nonce (etaH)
            last |-> 0]

\* In English: the tick before a block in epoch e [R4][R6]: if e is after
\* the last block's epoch, the epoch nonce becomes candidate * etaH * extra
\* entropy, and etaH becomes the current lab nonce.
RefTick(st, e) ==
    IF e > st.last
    THEN [st EXCEPT !.eta0 = Op(Op(st.cand, st.leb), ExtraEntropy(e)),  \* [R4]
                    !.leb  = st.lab]                                     \* etaH := lab
    ELSE st

\* In English: apply block blk, whose predecessor nonce is prevN [R3][R5].
\* The evolving nonce takes the block's nonce; the candidate follows it only
\* before the freeze point; the lab nonce becomes the predecessor's hash.
RefApply(st, blk, prevN) ==
    LET t   == RefTick(st, EpochOf(blk.slot))
        ev2 == Op(t.ev, BlockNonce(blk.id))
    IN [t EXCEPT
          !.ev   = ev2,                                          \* every block
          !.cand = IF BeforeFreeze(blk.slot) \/ Mutation = "RefNoFreeze"
                   THEN ev2 ELSE t.cand,                         \* frozen after
          !.lab  = IF Mutation = "RefLabSelf"
                   THEN HeaderHash(blk.id)                       \* the spec's reading [S3]
                   ELSE prevN,                                   \* the reference [R5]
          !.last = EpochOf(blk.slot)]

\* In English: the reference state after the chain seq, block by block.
RECURSIVE RefFold(_)
RefFold(seq) ==
    IF seq = <<>> THEN RefInit
    ELSE RefApply(RefFold(SubSeq(seq, 1, Len(seq) - 1)),
                  seq[Len(seq)],
                  PrevHashToNonce(PrevOf(seq, Len(seq))))

-----------------------------------------------------------------------------
(* The same values written as closed formulas over the chain, used to       *)
(* check the reference's invariants independently of RefApply.              *)

\* In English: the initial nonce folded with every block's nonce.
RECURSIVE EvFold(_)
EvFold(seq) == IF seq = <<>> THEN InitialNonce
               ELSE Op(EvFold(SubSeq(seq, 1, Len(seq) - 1)),
                       BlockNonce(seq[Len(seq)].id))

\* In English: the position of the last block that was before its epoch's
\* freeze point, or 0 if there is none.
LastPre(seq) == LET pre == {i \in 1..Len(seq) : BeforeFreeze(seq[i].slot)}
                IN IF pre = {} THEN 0
                   ELSE CHOOSE i \in pre : \A j \in pre : j <= i

\* In English: the candidate nonce is the evolving nonce as it stood after
\* the last block before a freeze point. Blocks after it do not count.
CandOf(seq) == EvFold(SubSeq(seq, 1, LastPre(seq)))

\* In English: block i is the first block of a later epoch than block i-1
\* (block 1 against epoch 0) [R6].
IsTick(seq, i) ==
    EpochOf(seq[i].slot) > (IF i = 1 THEN 0 ELSE EpochOf(seq[i - 1].slot))

\* In English: the last tick at or before position j, or 0.
LastTick(seq, j) == LET ts == {i \in 1..j : IsTick(seq, i)}
                    IN IF ts = {} THEN 0
                       ELSE CHOOSE i \in ts : \A k \in ts : k <= i

\* In English: the lab nonce after the first k blocks.
LabAfter(seq, k) == IF k = 0 THEN Neutral ELSE PrevHashToNonce(PrevOf(seq, k))

\* In English: the epoch nonce after seq. Before any tick it is the initial
\* nonce. Otherwise it is the candidate as it stood before the last tick,
\* combined with the lab nonce as it stood before the tick before that, and
\* the extra entropy of the new epoch.
Eta0Of(seq) ==
    LET t == LastTick(seq, Len(seq))
    IN IF t = 0 THEN InitialNonce
       ELSE LET p   == LastTick(seq, t - 1)
                leb == IF p = 0 THEN Neutral ELSE LabAfter(seq, p - 1)
            IN Op(Op(CandOf(SubSeq(seq, 1, t - 1)), leb),
                  ExtraEntropy(EpochOf(seq[t].slot)))

-----------------------------------------------------------------------------
(* gOuroboros' functions, on the caller's byte values.                      *)

\* In English: how a []byte caller stores a nonce: NeutralNonce as 32 zero
\* bytes, any other nonce as its 32 bytes.
Enc(n) == IF n = Neutral THEN Zero ELSE n
Dec(x) == IF x \in {Zero, Empty} THEN Neutral ELSE x

IsRaw(x) == x[1] = "vrfOutput"   \* a 64-byte operand

\* In English: CalculateRollingNonce(prev, x) [G1]. 32 zero bytes is
\* NeutralNonce: main returns blake2b_256(x); the "Neutral" fix returns a
\* 32-byte x unchanged, as * does. Otherwise main hashes prev || x, with a
\* 64-byte x concatenated raw; the "RawOperand" fix hashes a 64-byte x first,
\* as TPraos' bnonce does [R2].
GoRolling(prev, x) ==
    LET operand == IF IsRaw(x) /\ "RawOperand" \in GoFix THEN Hash(x) ELSE x
    IN IF prev = Zero
       THEN (IF IsRaw(x) THEN Hash(x)                          \* blake2b_256(output)
             ELSE IF "Neutral" \in GoFix THEN x                 \* fixed: identity
             ELSE Hash(x))                                      \* main: hashed again
       ELSE Cat(prev, operand)

\* In English: CalculateEpochNonce(c, l, ee) [G2]. Main hashes c || l and
\* then that || ee unless ee is empty; zero bytes are hashed like any value.
\* The "Neutral" fix treats zero or empty c and l as NeutralNonce, giving the
\* reference's c * l * ee.
GoEpoch(c, l, ee) ==
    IF "Neutral" \in GoFix
    THEN Enc(Op(Op(Dec(c), Dec(l)), Dec(ee)))
    ELSE LET t == Cat(c, l)
         IN IF ee = Empty THEN t ELSE Cat(t, ee)

\* In English: the bytes a caller passes as extraEntropy: none when unset.
EEBytes(e) == IF ExtraEntropy(e) = Neutral THEN Empty ELSE ExtraEntropy(e)

\* In English: the VRF input for the current epoch nonce, abstracting the
\* slot [R9][G3]. The reference omits a NeutralNonce; gOuroboros takes 32
\* bytes and always appends them.
RefVrfInput(n) == IF n = Neutral THEN Hash(<<"slotOnly">>) ELSE Hash(<<"slotAnd", n>>)
GoVrfInput(x)  == Hash(<<"slotAnd", x>>)

-----------------------------------------------------------------------------
(* The caller.                                                              *)

\* In English: the epoch nonce the caller computes at a tick into epoch e,
\* from its candidate c and etaH l.
CallerEpochNonce(c, l, e) ==
    CASE Caller = "Direct" ->
            GoEpoch(c, l, EEBytes(e))
      [] Caller = "Dingo" ->                       \* assembleEpochNonce
            IF l = Zero
            THEN (IF EEBytes(e) = Empty THEN c
                  ELSE IF c = Zero THEN EEBytes(e)
                  ELSE Cat(c, EEBytes(e)))
            ELSE GoEpoch(c, l, EEBytes(e))
      [] Caller = "Contract" ->
            IF (c = Zero \/ l = Zero) /\ "Neutral" \notin GoFix
            THEN Enc(Op(Op(Dec(c), Dec(l)), ExtraEntropy(e)))  \* * by hand
            ELSE GoEpoch(c, l, EEBytes(e))

\* In English: the evolving nonce the caller computes from prev and block b.
CallerRolling(prev, b) ==
    LET x == IF Operand = "Raw" THEN RawVrf(b) ELSE BlockNonce(b)
    IN IF Caller = "Contract" /\ prev = Zero /\ "Neutral" \notin GoFix
       THEN Enc(Op(Neutral, BlockNonce(b)))   \* * by hand
       ELSE GoRolling(prev, x)

\* In English: the caller's freeze test. The mutations put it one slot off
\* or remove it.
CallerBeforeFreeze(s) ==
    CASE Mutation = "FreezeLE"    -> s + Window <= FirstSlot(EpochOf(s) + 1)
      [] Mutation = "NoFreeze"    -> TRUE
      [] Mutation = "OtherWindow" -> s + Window + 1 < FirstSlot(EpochOf(s) + 1)
      [] OTHER                    -> BeforeFreeze(s)

\* In English: the caller's state before any block, in bytes.
CallerInit == [ev |-> Enc(InitialNonce), cand |-> Enc(InitialNonce),
               eta0 |-> Enc(InitialNonce), lab |-> Zero, leb |-> Zero,
               last |-> 0]

\* In English: the caller's tick, as the reference's but through
\* CallerEpochNonce.
CallerTick(st, e) ==
    IF e > st.last
    THEN [st EXCEPT !.eta0 = CallerEpochNonce(st.cand, st.leb, e),
                    !.leb  = st.lab]
    ELSE st

\* In English: the caller applies block blk, whose predecessor is prev.
CallerApply(st, blk, prev) ==
    LET t   == CallerTick(st, EpochOf(blk.slot))
        ev2 == CallerRolling(t.ev, blk.id)
    IN [t EXCEPT
          !.ev   = ev2,
          !.cand = IF CallerBeforeFreeze(blk.slot) THEN ev2 ELSE t.cand,
          !.lab  = IF Mutation = "SpecLab"
                   THEN HeaderHash(blk.id)              \* the block's own hash
                   ELSE Enc(PrevHashToNonce(prev)),     \* its predecessor's
          !.last = EpochOf(blk.slot)]

\* In English: the reference state written in the caller's bytes.
EncState(st) == [ev |-> Enc(st.ev), cand |-> Enc(st.cand),
                 eta0 |-> Enc(st.eta0), lab |-> Enc(st.lab),
                 leb |-> Enc(st.leb), last |-> st.last]

-----------------------------------------------------------------------------

VARIABLES
    chain,   \* the caller's chain: a sequence of [id, slot] blocks
    nextId,  \* the id the next new block gets (every block is distinct)
    cs,      \* the caller's nonce state
    snaps,   \* snaps[i]: the caller's state after block i, kept for rollback
    seen     \* events that have happened, for the probes

vars == <<chain, nextId, cs, snaps, seen>>

Init ==
    /\ chain  = <<>>        \* no Shelley block yet
    /\ nextId = 1
    /\ cs     = CallerInit
    /\ snaps  = <<>>
    /\ seen   = {}

\* In English: the slot after the tip (or the first Shelley slot).
NextFreeSlot == IF chain = <<>> THEN FirstShelleySlot
                ELSE chain[Len(chain)].slot + 1

\* In English: a new block arrives in a later slot. The caller applies it
\* and keeps a snapshot. The probes note what happened at its tick.
Extend ==
    \E s \in NextFreeSlot..MaxSlot :
        LET blk  == [id |-> nextId, slot |-> s]
            new  == Append(chain, blk)
            pre  == RefFold(chain)
            e    == EpochOf(s)
            tick == e > pre.last
        IN /\ nextId <= MaxBlocks                                  \* model bound
           /\ chain'  = new                                        \* adopt the block
           /\ nextId' = nextId + 1
           /\ cs'     = CallerApply(cs, blk, PrevOf(new, Len(new)))
           /\ snaps'  = Append(snaps, cs')                         \* snapshot
           /\ seen'   = seen
                \cup (IF tick /\ pre.leb # Neutral THEN {"tickLab"} ELSE {})
                \cup (IF tick /\ e > pre.last + 1 THEN {"skip"} ELSE {})
                \cup (IF tick /\ ExtraEntropy(e) # Neutral THEN {"entropy"} ELSE {})
                \cup (IF ~BeforeFreeze(s) THEN {"postFreeze"} ELSE {})

\* In English: the caller rolls back d blocks and restores the snapshot of
\* the new tip (or its initial state). The "NoRestore" mutation restores the
\* evolving nonce only.
Rollback ==
    \E d \in 1..MaxRollback :
        LET n    == Len(chain) - d
            back == IF n = 0 THEN CallerInit ELSE snaps[n]
        IN /\ d <= Len(chain)
           /\ chain' = SubSeq(chain, 1, n)                         \* drop d blocks
           /\ snaps' = SubSeq(snaps, 1, n)
           /\ cs'    = IF Mutation = "NoRestore"
                       THEN [cs EXCEPT !.ev = back.ev]
                       ELSE back                                   \* restore
           /\ nextId' = nextId
           /\ seen'  = seen
                \cup (IF RefFold(SubSeq(chain, 1, n)).cand # RefFold(chain).cand
                      THEN {"rollbackCand"} ELSE {})

\* In English: every block id has been used; the run may stop here.
Done == nextId > MaxBlocks /\ UNCHANGED vars

Next == Extend \/ Rollback \/ Done

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants.                                                              *)

\* In English: the caller's whole nonce state is the reference's.
StateAgrees == cs = EncState(RefFold(chain))

\* In English: the caller's epoch nonce, the one VRF checks use, is the
\* reference's.
EpochNonceAgrees == cs.eta0 = Enc(RefFold(chain).eta0)

\* In English: the VRF input gOuroboros builds from the caller's epoch nonce
\* is the reference's [R9][G3].
VrfInputAgrees == GoVrfInput(cs.eta0) = RefVrfInput(RefFold(chain).eta0)

\* In English: the reference's candidate depends only on the blocks up to
\* the last one before a freeze point.
CandidateFrozen == RefFold(chain).cand = CandOf(chain)

\* In English: the reference's epoch nonce depends only on blocks before
\* the previous epoch's freeze point, the lab nonce carried from the tick
\* before, and the extra entropy.
EpochNonceDenotation == RefFold(chain).eta0 = Eta0Of(chain)

\* Probes: each is expected to be violated, which proves the case is reached.
ProbeTickLab       == "tickLab" \notin seen        \* an epoch nonce used a real etaH
ProbeSkippedEpoch  == "skip" \notin seen           \* a tick crossed an empty epoch
ProbeEntropy       == "entropy" \notin seen        \* extra entropy was mixed in
ProbePostFreeze    == "postFreeze" \notin seen     \* a block came after the freeze
ProbeRollbackCand  == "rollbackCand" \notin seen   \* a rollback changed the candidate
=============================================================================
