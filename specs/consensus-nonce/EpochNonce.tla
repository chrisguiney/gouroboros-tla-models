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
(*      nonce functions and leaves the rest to the caller (Dingo). The    *)
(*      caller keeps the nonces, ticks at each epoch change, freezes the  *)
(*      candidate, keeps one snapshot per block and restores a snapshot   *)
(*      on rollback. The model checks that what the caller holds is       *)
(*      always what the reference holds.                                   *)
(*   gOuroboros has two sets of nonce functions, chosen by GoApi:          *)
(*     "Bytes": the deprecated []byte functions (CalculateRollingNonce,    *)
(*       CalculateEpochNonce, MkInputVrf, MkSeedTPraos), which have no     *)
(*       spelling for NeutralNonce;                                        *)
(*     "Nonce": the common.Nonce functions (NonceFromTPraosVRF,            *)
(*       NonceFromPraosVRF, CombineNonces, EpochNonceFromNonces,           *)
(*       MkInputVrfFromNonce, MkSeedTPraosFromNonce), where NeutralNonce   *)
(*       is a type of its own.                                             *)
(*                                                                         *)
(* Hashing is symbolic. A nonce is a term; Hash(x) is blake2b_256 of x,   *)
(* and two terms are equal only if they were built the same way, so the   *)
(* model treats the hash as injective (no collisions).                    *)
(*                                                                         *)
(* Sources (links and quotes in specs/consensus-nonce/README.md).       *)
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
(* The gOuroboros code it is compared with. "Bytes" (commit d0b95845):    *)
(*   [G1] ledger/common/nonce.go CalculateRollingNonce 92-150              *)
(*   [G2] ledger/common/nonce.go CalculateEpochNonce 152-187               *)
(*   [G3] vrf/vrf.go MkInputVrf 245-267, MkSeedTPraos 313-345;             *)
(*        consensus/block.go ComputeVRFInput 523-544;                      *)
(*        ledger/verify_block.go verifyNonceVrf 775-793                    *)
(* "Nonce" (main 756a9a89 and branch fix/nonce-neutral-epoch-and-vrf-input):*)
(*   [G4] ledger/common/nonce.go NonceFromTPraosVRF 96, NonceFromPraosVRF *)
(*        110, CombineNonces 128-149 (main 756a9a89)                       *)
(*   [G5] ledger/common/nonce.go EpochNonceFromNonces 188-194;             *)
(*        vrf/vrf.go MkInputVrfFromNonce 278-292, MkSeedTPraosFromNonce    *)
(*        385-403; consensus/block.go ComputeVRFInputFromNonce 557         *)
(*        (branch commit da43d778)                                         *)
(*   The caller is Dingo (ledger/eras/*.go, ledger/extra_entropy.go        *)
(*   assembleEpochNonce, ledger/epoch_lab_nonce.go).                       *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and       *)
(* specs/consensus/ChainSelection.tla (SubSeq). New here:              *)
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
    GoFix,          \* gOuroboros fixes in force on the "Bytes" path, a
                    \*  subset of {"Neutral", "RawOperand"}; {} is d0b95845
    GoApi,          \* which gOuroboros functions the caller uses:
                    \*  "Bytes": the []byte functions [G1][G2][G3];
                    \*  "Nonce": the common.Nonce functions [G4][G5].
                    \*  Caller, Operand and GoFix matter only for "Bytes".
    Mutation        \* "none", or one deliberate mistake (see below); on
                    \*  the "Nonce" path, "NewNoIdentity" (the epoch
                    \*  function hashes a neutral operand in) and
                    \*  "NewVrfAppend" (the VRF input appends a neutral
                    \*  epoch nonce as zero bytes)

-----------------------------------------------------------------------------
(* Symbolic values.                                                         *)

\* Literally: "Neutral is defined as the tuple of "NeutralNonce"."
Neutral   == <<"NeutralNonce">>   \* the reference's identity nonce
\* Literally: "Zero is defined as the tuple of "zero32"."
Zero      == <<"zero32">>         \* how a []byte caller spells NeutralNonce
\* Literally: "Empty is defined as the tuple of "noBytes"."
Empty     == <<"noBytes">>        \* an empty slice (extraEntropy's NeutralNonce)
\* Literally: "GenesisHash is defined as the tuple of "GenesisHash"."
GenesisHash == <<"GenesisHash">> \* the predecessor of a chain's first block

\* In English: blake2b_256 of x, and blake2b_256(a || b). Every value is a
\* tuple whose first element names what it is, so TLC can compare any two.
\* Literally: "Hash of x is defined as the tuple of "blake2b" and x."
Hash(x)   == <<"blake2b", x>>
\* Literally: "Cat of a and b is defined as Hash of the tuple of "cat", a and
\*   b."
Cat(a, b) == Hash(<<"cat", a, b>>)

\* In English: the 64-byte VRF output in block b's header, and block b's
\* header hash.
\* Literally: "RawVrf of b is defined as the tuple of "vrfOutput" and b."
RawVrf(b)     == <<"vrfOutput", b>>
\* Literally: "HeaderHash of b is defined as the tuple of "headerHash" and b."
HeaderHash(b) == <<"headerHash", b>>
\* Literally: "ByronTipHash is defined as the tuple of "lastByronHeaderHash"."
ByronTipHash  == <<"lastByronHeaderHash">>

\* In English: the nonce block b contributes [R2]. TPraos hashes the nonce
\* VRF output once; Praos range-extends the single VRF output with "N" and
\* hashes the result again.
\* Literally: "BlockNonce of b is defined as: if Era equals "TPraos" then Hash
\*   of RawVrf of b, else Hash of Hash of the tuple of "N" and RawVrf of b."
BlockNonce(b) == IF Era = "TPraos"
                 THEN Hash(RawVrf(b))
                 ELSE Hash(Hash(<<"N", RawVrf(b)>>))

\* In English: the reference's nonce operator * [R1]. Two nonces hash their
\* concatenation; NeutralNonce on either side gives back the other.
\* Literally: "Op of a and b is defined as: in the case a equals Neutral, b; in
\*   the case b equals Neutral, a; in every other case, Cat of a and b."
Op(a, b) == CASE a = Neutral -> b
              [] b = Neutral -> a
              [] OTHER       -> Cat(a, b)

\* In English: the initial nonce [R7].
\* Literally: "InitialNonce is defined as: if InitNonce equals "GenesisHash"
\*   then the tuple of "shelleyGenesisHash", else Neutral."
InitialNonce == IF InitNonce = "GenesisHash" THEN <<"shelleyGenesisHash">>
                ELSE Neutral

\* In English: the extra entropy protocol parameter in force in epoch e;
\* NeutralNonce when unset [R4].
\* Literally: "ExtraEntropy of e is defined as: if e is a member of
\*   EntropyEpochs then the tuple of "extraEntropy" and e, else Neutral."
ExtraEntropy(e) == IF e \in EntropyEpochs THEN <<"extraEntropy", e>>
                   ELSE Neutral

-----------------------------------------------------------------------------
(* Slots and epochs.                                                        *)

\* Literally: "FirstSlot of e is defined as e times SlotsPerEpoch."
FirstSlot(e) == e * SlotsPerEpoch           \* first slot of epoch e
\* Literally: "EpochOf of s is defined as s integer-divided by SlotsPerEpoch."
EpochOf(s)   == s \div SlotsPerEpoch        \* the epoch slot s is in
\* In English: the first Shelley slot.
\* Literally: "FirstShelleySlot is defined as: if Start equals "Byron" then
\*   SlotsPerEpoch, else 0."
FirstShelleySlot == IF Start = "Byron" THEN SlotsPerEpoch ELSE 0

\* In English: a block in slot s is still before its epoch's freeze point:
\* s plus the window is strictly before the next epoch's first slot [S1][R3].
\* Literally: "BeforeFreeze of s is defined as: s plus Window is less than
\*   FirstSlot of (EpochOf of s plus 1)."
BeforeFreeze(s) == s + Window < FirstSlot(EpochOf(s) + 1)

\* In English: the hash a block names as its predecessor. The first block's
\* predecessor is the genesis (a chain that starts in Shelley) or the last
\* Byron block.
\* Literally: "PrevOf of seq and i is defined as: if i equals 1 then (if Start
\*   equals "Genesis" then GenesisHash, else ByronTipHash), else HeaderHash of
\*   seq of i minus 1's id."
PrevOf(seq, i) == IF i = 1
                  THEN (IF Start = "Genesis" THEN GenesisHash ELSE ByronTipHash)
                  ELSE HeaderHash(seq[i - 1].id)

\* In English: prevHashToNonce [R5]: GenesisHash is NeutralNonce, any block
\* hash is a nonce.
\* Literally: "PrevHashToNonce of p is defined as: if p equals GenesisHash then
\*   Neutral, else p."
PrevHashToNonce(p) == IF p = GenesisHash THEN Neutral ELSE p

-----------------------------------------------------------------------------
(* The reference, computed from the chain.                                  *)

\* In English: the nonce state before any Shelley block [R7]: every nonce is
\* the initial nonce except the two hash nonces, which are NeutralNonce.
\* last is the epoch of the last block (Origin and the Byron era count as 0).
\* Literally: "RefInit is defined as the record whose field ev is InitialNonce,
\*   field cand is InitialNonce, field eta0 is InitialNonce, field lab is
\*   Neutral, field leb is Neutral, and field last is 0."
RefInit == [ev   |-> InitialNonce,   \* evolving nonce
            cand |-> InitialNonce,   \* candidate nonce
            eta0 |-> InitialNonce,   \* epoch nonce
            lab  |-> Neutral,        \* lab nonce
            leb  |-> Neutral,        \* last-epoch-block nonce (etaH)
            last |-> 0]

\* In English: the tick before a block in epoch e [R4][R6]: if e is after
\* the last block's epoch, the epoch nonce becomes candidate * etaH * extra
\* entropy, and etaH becomes the current lab nonce.
\* Literally: "RefTick of st and e is defined as: if e is greater than st's last
\*   then st except that its eta0 is Op of Op of st's cand and st's leb, and
\*   ExtraEntropy of e, and its leb is st's lab; else st."
RefTick(st, e) ==
    IF e > st.last
    THEN [st EXCEPT !.eta0 = Op(Op(st.cand, st.leb), ExtraEntropy(e)),  \* [R4]
                    !.leb  = st.lab]                                     \* etaH := lab
    ELSE st

\* In English: apply block blk, whose predecessor nonce is prevN [R3][R5].
\* The evolving nonce takes the block's nonce; the candidate follows it only
\* before the freeze point; the lab nonce becomes the predecessor's hash.
\* Literally: "RefApply of st, blk and prevN is defined as: letting t be RefTick
\*   of st and EpochOf of blk's slot, and ev2 be Op of t's ev and BlockNonce of
\*   blk's id: t except that its ev is ev2, its cand is (if BeforeFreeze of
\*   blk's slot or Mutation equals "RefNoFreeze" then ev2, else t's cand), its
\*   lab is (if Mutation equals "RefLabSelf" then HeaderHash of blk's id, else
\*   prevN), and its last is EpochOf of blk's slot."
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
\* Literally: "RefFold of seq is defined as: if seq equals the empty sequence
\*   then RefInit, else RefApply of RefFold of the subsequence of seq from 1
\*   through the length of seq minus 1, seq of the length of seq, and
\*   PrevHashToNonce of PrevOf of seq and the length of seq."
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
\* Literally: "EvFold of seq is defined as: if seq equals the empty sequence
\*   then InitialNonce, else Op of EvFold of the subsequence of seq from 1
\*   through the length of seq minus 1, and BlockNonce of seq of the length of
\*   seq's id."
EvFold(seq) == IF seq = <<>> THEN InitialNonce
               ELSE Op(EvFold(SubSeq(seq, 1, Len(seq) - 1)),
                       BlockNonce(seq[Len(seq)].id))

\* In English: the position of the last block that was before its epoch's
\* freeze point, or 0 if there is none.
\* Literally: "LastPre of seq is defined as: letting pre be the set of every i
\*   in 1 through the length of seq such that BeforeFreeze of seq of i's slot:
\*   if pre equals the empty set then 0, else the i, chosen from pre, such that
\*   for all j in pre, j is less than or equal to i."
LastPre(seq) == LET pre == {i \in 1..Len(seq) : BeforeFreeze(seq[i].slot)}
                IN IF pre = {} THEN 0
                   ELSE CHOOSE i \in pre : \A j \in pre : j <= i

\* In English: the candidate nonce is the evolving nonce as it stood after
\* the last block before a freeze point. Blocks after it do not count.
\* Literally: "CandOf of seq is defined as EvFold of the subsequence of seq from
\*   1 through LastPre of seq."
CandOf(seq) == EvFold(SubSeq(seq, 1, LastPre(seq)))

\* In English: block i is the first block of a later epoch than block i-1
\* (block 1 against epoch 0) [R6].
\* Literally: "IsTick of seq and i is defined as: EpochOf of seq of i's slot is
\*   greater than (if i equals 1 then 0, else EpochOf of seq of i minus 1's
\*   slot)."
IsTick(seq, i) ==
    EpochOf(seq[i].slot) > (IF i = 1 THEN 0 ELSE EpochOf(seq[i - 1].slot))

\* In English: the last tick at or before position j, or 0.
\* Literally: "LastTick of seq and j is defined as: letting ts be the set of
\*   every i in 1 through j such that IsTick of seq and i: if ts equals the
\*   empty set then 0, else the i, chosen from ts, such that for all k in ts, k
\*   is less than or equal to i."
LastTick(seq, j) == LET ts == {i \in 1..j : IsTick(seq, i)}
                    IN IF ts = {} THEN 0
                       ELSE CHOOSE i \in ts : \A k \in ts : k <= i

\* In English: the lab nonce after the first k blocks.
\* Literally: "LabAfter of seq and k is defined as: if k equals 0 then Neutral,
\*   else PrevHashToNonce of PrevOf of seq and k."
LabAfter(seq, k) == IF k = 0 THEN Neutral ELSE PrevHashToNonce(PrevOf(seq, k))

\* In English: the epoch nonce after seq. Before any tick it is the initial
\* nonce. Otherwise it is the candidate as it stood before the last tick,
\* combined with the lab nonce as it stood before the tick before that, and
\* the extra entropy of the new epoch.
\* Literally: "Eta0Of of seq is defined as: letting t be LastTick of seq and the
\*   length of seq: if t equals 0 then InitialNonce, else, letting p be LastTick
\*   of seq and t minus 1, and leb be: if p equals 0 then Neutral, else LabAfter
\*   of seq and p minus 1: Op of Op of CandOf of the subsequence of seq from 1
\*   through t minus 1, and leb, and ExtraEntropy of EpochOf of seq of t's
\*   slot."
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
\* Literally: "Enc of n is defined as: if n equals Neutral then Zero, else n."
Enc(n) == IF n = Neutral THEN Zero ELSE n
\* In English: how a []byte value reads back as a nonce: 32 zero bytes or an
\* empty slice is NeutralNonce.
\* Literally: "Dec of x is defined as: if x is a member of the set containing
\*   Zero and Empty then Neutral, else x."
Dec(x) == IF x \in {Zero, Empty} THEN Neutral ELSE x

\* Literally: "IsRaw of x is defined as: element 1 of x equals "vrfOutput"."
IsRaw(x) == x[1] = "vrfOutput"   \* a 64-byte operand

\* In English: CalculateRollingNonce(prev, x) [G1]. 32 zero bytes is
\* NeutralNonce: main returns blake2b_256(x); the "Neutral" fix returns a
\* 32-byte x unchanged, as * does. Otherwise main hashes prev || x, with a
\* 64-byte x concatenated raw; the "RawOperand" fix hashes a 64-byte x first,
\* as TPraos' bnonce does [R2].
\* Literally: "GoRolling of prev and x is defined as: letting operand be: if
\*   IsRaw of x and "RawOperand" is a member of GoFix then Hash of x, else x: if
\*   prev equals Zero then (if IsRaw of x then Hash of x, else if "Neutral" is a
\*   member of GoFix then x, else Hash of x), else Cat of prev and operand."
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
\* Literally: "GoEpoch of c, l and ee is defined as: if "Neutral" is a member of
\*   GoFix then Enc of Op of Op of Dec of c and Dec of l, and Dec of ee; else,
\*   letting t be Cat of c and l: if ee equals Empty then t, else Cat of t and
\*   ee."
GoEpoch(c, l, ee) ==
    IF "Neutral" \in GoFix
    THEN Enc(Op(Op(Dec(c), Dec(l)), Dec(ee)))
    ELSE LET t == Cat(c, l)
         IN IF ee = Empty THEN t ELSE Cat(t, ee)

\* In English: the bytes a caller passes as extraEntropy: none when unset.
\* Literally: "EEBytes of e is defined as: if ExtraEntropy of e equals Neutral
\*   then Empty, else ExtraEntropy of e."
EEBytes(e) == IF ExtraEntropy(e) = Neutral THEN Empty ELSE ExtraEntropy(e)

\* In English: the VRF input for the current epoch nonce, abstracting the
\* slot [R9][G3]. The reference omits a NeutralNonce; gOuroboros takes 32
\* bytes and always appends them.
\* Literally: "RefVrfInput of n is defined as: if n equals Neutral then Hash of
\*   the tuple of "slotOnly", else Hash of the tuple of "slotAnd" and n."
RefVrfInput(n) == IF n = Neutral THEN Hash(<<"slotOnly">>) ELSE Hash(<<"slotAnd", n>>)
\* Literally: "GoVrfInput of x is defined as Hash of the tuple of "slotAnd" and
\*   x."
GoVrfInput(x)  == Hash(<<"slotAnd", x>>)

-----------------------------------------------------------------------------
(* gOuroboros' common.Nonce functions ("Nonce" path) [G4][G5].             *)

\* In English: how the caller holds a nonce. With the []byte functions it
\* holds bytes, NeutralNonce as 32 zero bytes; with the common.Nonce
\* functions it holds the typed nonce itself, so NeutralNonce stays neutral.
\* Literally: "Hold of n is defined as: if GoApi equals "Nonce" then n, else
\*   Enc of n."
Hold(n) == IF GoApi = "Nonce" THEN n ELSE Enc(n)

\* In English: CombineNonces(a, b) [G4]. A NonceTypeNeutral operand on
\* either side gives back the other; two NonceTypeNonce values hash their
\* concatenation. This is the reference's * [R1].
\* Literally: "GoCombine of a and b is defined as: in the case a equals
\*   Neutral, b; in the case b equals Neutral, a; in every other case, Cat of a
\*   and b."
GoCombine(a, b) == CASE a = Neutral -> b
                     [] b = Neutral -> a
                     [] OTHER       -> Cat(a, b)

\* In English: EpochNonceFromNonces(c, l, ee) [G5]: CombineNonces twice,
\* c * l * ee, as the reference's tick does [R4]. The "NewNoIdentity"
\* mutation hashes every operand in, neutral or not, as the []byte
\* function does.
\* Literally: "GoEpochNonce of c, l and ee is defined as: if Mutation equals
\*   "NewNoIdentity" then Cat of Cat of c and l, and ee; else GoCombine of
\*   GoCombine of c and l, and ee."
GoEpochNonce(c, l, ee) ==
    IF Mutation = "NewNoIdentity"
    THEN Cat(Cat(c, l), ee)                       \* mutation: no identity
    ELSE GoCombine(GoCombine(c, l), ee)           \* c * l * ee

\* In English: MkInputVrfFromNonce and MkSeedTPraosFromNonce [G5],
\* abstracting the slot: a NonceTypeNeutral epoch nonce adds no bytes, as
\* in the reference [R9]. The "NewVrfAppend" mutation appends it as 32
\* zero bytes, as the []byte functions do.
\* Literally: "GoVrfInputNonce of n is defined as: if n equals Neutral and
\*   Mutation does not equal "NewVrfAppend" then Hash of the tuple of
\*   "slotOnly", else Hash of the tuple of "slotAnd" and Enc of n."
GoVrfInputNonce(n) ==
    IF n = Neutral /\ Mutation # "NewVrfAppend"
    THEN Hash(<<"slotOnly">>)                     \* slot bytes only
    ELSE Hash(<<"slotAnd", Enc(n)>>)              \* slot bytes || eta0

\* In English: the VRF input gOuroboros builds from the epoch nonce the
\* caller holds, through whichever functions it uses.
\* Literally: "GoVrfInputOf of x is defined as: if GoApi equals "Nonce" then
\*   GoVrfInputNonce of x, else GoVrfInput of x."
GoVrfInputOf(x) == IF GoApi = "Nonce" THEN GoVrfInputNonce(x) ELSE GoVrfInput(x)

-----------------------------------------------------------------------------
(* The caller.                                                              *)

\* In English: the epoch nonce the caller computes at a tick into epoch e,
\* from its candidate c and etaH l. With the common.Nonce functions every
\* caller passes the typed nonces to EpochNonceFromNonces, extra entropy
\* included (NeutralNonce when unset). With the []byte functions it depends
\* on the caller.
\* Literally: "CallerEpochNonce of c, l and e is defined as: in the case GoApi
\*   equals "Nonce", GoEpochNonce of c, l and ExtraEntropy of e; in the case
\*   Caller equals "Direct", GoEpoch of c, l and EEBytes of e; in the case Caller
\*   equals "Dingo", if l equals Zero then (if EEBytes of e equals Empty then c,
\*   else if c equals Zero then EEBytes of e, else Cat of c and EEBytes of e),
\*   else GoEpoch of c, l and EEBytes of e; in the case Caller equals
\*   "Contract", if (c equals Zero or l equals Zero) and "Neutral" is not a
\*   member of GoFix then Enc of Op of Op of Dec of c and Dec of l, and
\*   ExtraEntropy of e; else GoEpoch of c, l and EEBytes of e."
CallerEpochNonce(c, l, e) ==
    CASE GoApi = "Nonce" ->                        \* EpochNonceFromNonces
            GoEpochNonce(c, l, ExtraEntropy(e))
      [] Caller = "Direct" ->
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
\* With the common.Nonce functions the caller derives the block nonce from
\* the raw VRF output with NonceFromTPraosVRF or NonceFromPraosVRF, which
\* compute BlockNonce [G4], and folds it in with CombineNonces.
\* Literally: "CallerRolling of prev and b is defined as: letting x be: if
\*   Operand equals "Raw" then RawVrf of b, else BlockNonce of b: if GoApi
\*   equals "Nonce" then GoCombine of prev and BlockNonce of b, else if Caller
\*   equals "Contract" and prev equals Zero and "Neutral" is not a member of
\*   GoFix then Enc of Op of Neutral and BlockNonce of b, else GoRolling of prev
\*   and x."
CallerRolling(prev, b) ==
    LET x == IF Operand = "Raw" THEN RawVrf(b) ELSE BlockNonce(b)
    IN IF GoApi = "Nonce"
       THEN GoCombine(prev, BlockNonce(b))    \* NonceFrom*VRF, CombineNonces
       ELSE IF Caller = "Contract" /\ prev = Zero /\ "Neutral" \notin GoFix
       THEN Enc(Op(Neutral, BlockNonce(b)))   \* * by hand
       ELSE GoRolling(prev, x)

\* In English: the caller's freeze test. The mutations put it one slot off
\* or remove it.
\* Literally: "CallerBeforeFreeze of s is defined as: in the case Mutation
\*   equals "FreezeLE", s plus Window is less than or equal to FirstSlot of
\*   (EpochOf of s plus 1); in the case Mutation equals "NoFreeze", TRUE; in the
\*   case Mutation equals "OtherWindow", s plus Window plus 1 is less than
\*   FirstSlot of (EpochOf of s plus 1); in every other case, BeforeFreeze of
\*   s."
CallerBeforeFreeze(s) ==
    CASE Mutation = "FreezeLE"    -> s + Window <= FirstSlot(EpochOf(s) + 1)
      [] Mutation = "NoFreeze"    -> TRUE
      [] Mutation = "OtherWindow" -> s + Window + 1 < FirstSlot(EpochOf(s) + 1)
      [] OTHER                    -> BeforeFreeze(s)

\* In English: the caller's state before any block, as the caller holds it
\* (bytes, or typed nonces).
\* Literally: "CallerInit is defined as the record whose field ev is Hold of
\*   InitialNonce, field cand is Hold of InitialNonce, field eta0 is Hold of
\*   InitialNonce, field lab is Hold of Neutral, field leb is Hold of Neutral,
\*   and field last is 0."
CallerInit == [ev |-> Hold(InitialNonce), cand |-> Hold(InitialNonce),
               eta0 |-> Hold(InitialNonce), lab |-> Hold(Neutral),
               leb |-> Hold(Neutral), last |-> 0]

\* In English: the caller's tick, as the reference's but through
\* CallerEpochNonce.
\* Literally: "CallerTick of st and e is defined as: if e is greater than st's
\*   last then st except that its eta0 is CallerEpochNonce of st's cand, st's
\*   leb and e, and its leb is st's lab; else st."
CallerTick(st, e) ==
    IF e > st.last
    THEN [st EXCEPT !.eta0 = CallerEpochNonce(st.cand, st.leb, e),
                    !.leb  = st.lab]
    ELSE st

\* In English: the caller applies block blk, whose predecessor is prev.
\* Literally: "CallerApply of st, blk and prev is defined as: letting t be
\*   CallerTick of st and EpochOf of blk's slot, and ev2 be CallerRolling of t's
\*   ev and blk's id: t except that its ev is ev2, its cand is (if
\*   CallerBeforeFreeze of blk's slot then ev2, else t's cand), its lab is (if
\*   Mutation equals "SpecLab" then HeaderHash of blk's id, else Hold of
\*   PrevHashToNonce of prev), and its last is EpochOf of blk's slot."
CallerApply(st, blk, prev) ==
    LET t   == CallerTick(st, EpochOf(blk.slot))
        ev2 == CallerRolling(t.ev, blk.id)
    IN [t EXCEPT
          !.ev   = ev2,
          !.cand = IF CallerBeforeFreeze(blk.slot) THEN ev2 ELSE t.cand,
          !.lab  = IF Mutation = "SpecLab"
                   THEN HeaderHash(blk.id)              \* the block's own hash
                   ELSE Hold(PrevHashToNonce(prev)),    \* its predecessor's
          !.last = EpochOf(blk.slot)]

\* In English: the reference state written as the caller holds it.
\* Literally: "EncState of st is defined as the record whose field ev is Hold
\*   of st's ev, field cand is Hold of st's cand, field eta0 is Hold of st's
\*   eta0, field lab is Hold of st's lab, field leb is Hold of st's leb, and
\*   field last is st's last."
EncState(st) == [ev |-> Hold(st.ev), cand |-> Hold(st.cand),
                 eta0 |-> Hold(st.eta0), lab |-> Hold(st.lab),
                 leb |-> Hold(st.leb), last |-> st.last]

-----------------------------------------------------------------------------

VARIABLES
    chain,   \* the caller's chain: a sequence of [id, slot] blocks
    nextId,  \* the id the next new block gets (every block is distinct)
    cs,      \* the caller's nonce state
    snaps,   \* snaps[i]: the caller's state after block i, kept for rollback
    seen     \* events that have happened, for the probes

\* Literally: "vars is defined as the tuple of chain, nextId, cs, snaps and
\*   seen."
vars == <<chain, nextId, cs, snaps, seen>>

\* In English: "No Shelley block yet; the caller starts from its initial state."
\* Literally: "Init is defined as: chain equals the empty sequence, and nextId
\*   equals 1, and cs equals CallerInit, and snaps equals the empty sequence,
\*   and seen equals the empty set."
Init ==
    /\ chain  = <<>>        \* no Shelley block yet
    /\ nextId = 1
    /\ cs     = CallerInit
    /\ snaps  = <<>>
    /\ seen   = {}

\* In English: the slot after the tip (or the first Shelley slot).
\* Literally: "NextFreeSlot is defined as: if chain equals the empty sequence
\*   then FirstShelleySlot, else chain of the length of chain's slot plus 1."
NextFreeSlot == IF chain = <<>> THEN FirstShelleySlot
                ELSE chain[Len(chain)].slot + 1

\* In English: a new block arrives in a later slot. The caller applies it
\* and keeps a snapshot. The probes note what happened at its tick.
\* Literally: "Extend is defined as: there exists an s in NextFreeSlot through
\*   MaxSlot such that, letting blk be the record whose field id is nextId and
\*   field slot is s; new be chain with blk appended; pre be RefFold of chain; e
\*   be EpochOf of s; and tick be e is greater than pre's last: nextId is less
\*   than or equal to MaxBlocks, and chain in the next state equals new, and
\*   nextId in the next state equals nextId plus 1, and cs in the next state
\*   equals CallerApply of cs, blk, and PrevOf of new and the length of new, and
\*   snaps in the next state equals snaps with cs in the next state appended,
\*   and seen in the next state equals the union of seen, (if tick and pre's leb
\*   does not equal Neutral then the set containing "tickLab", else the empty
\*   set), (if tick and e is greater than pre's last plus 1 then the set
\*   containing "skip", else the empty set), (if tick and ExtraEntropy of e does
\*   not equal Neutral then the set containing "entropy", else the empty set),
\*   and (if BeforeFreeze of s is not true then the set containing "postFreeze",
\*   else the empty set)."
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
\* Literally: "Rollback is defined as: there exists a d in 1 through MaxRollback
\*   such that, letting n be the length of chain minus d, and back be: if n
\*   equals 0 then CallerInit, else snaps of n: d is less than or equal to the
\*   length of chain, and chain in the next state equals the subsequence of
\*   chain from 1 through n, and snaps in the next state equals the subsequence
\*   of snaps from 1 through n, and cs in the next state equals: if Mutation
\*   equals "NoRestore" then cs except that its ev is back's ev, else back; and
\*   nextId in the next state equals nextId, and seen in the next state equals
\*   the union of seen and (if RefFold of the subsequence of chain from 1
\*   through n's cand does not equal RefFold of chain's cand then the set
\*   containing "rollbackCand", else the empty set)."
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
\* Literally: "Done is defined as: nextId is greater than MaxBlocks, and vars is
\*   unchanged."
Done == nextId > MaxBlocks /\ UNCHANGED vars

\* In English: "Each step adds a block, rolls back, or stops."
\* Literally: "Next is defined as: Extend or Rollback or Done."
Next == Extend \/ Rollback \/ Done

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants.                                                              *)

\* In English: the caller's whole nonce state is the reference's.
\* Literally: "StateAgrees is defined as: cs equals EncState of RefFold of
\*   chain."
StateAgrees == cs = EncState(RefFold(chain))

\* In English: the caller's epoch nonce, the one VRF checks use, is the
\* reference's.
\* Literally: "EpochNonceAgrees is defined as: cs's eta0 equals Hold of
\*   RefFold of chain's eta0."
EpochNonceAgrees == cs.eta0 = Hold(RefFold(chain).eta0)

\* In English: the VRF input gOuroboros builds from the caller's epoch nonce
\* is the reference's [R9][G3][G5].
\* Literally: "VrfInputAgrees is defined as: GoVrfInputOf of cs's eta0 equals
\*   RefVrfInput of RefFold of chain's eta0."
VrfInputAgrees == GoVrfInputOf(cs.eta0) = RefVrfInput(RefFold(chain).eta0)

\* In English: the reference's candidate depends only on the blocks up to
\* the last one before a freeze point.
\* Literally: "CandidateFrozen is defined as: RefFold of chain's cand equals
\*   CandOf of chain."
CandidateFrozen == RefFold(chain).cand = CandOf(chain)

\* In English: the reference's epoch nonce depends only on blocks before
\* the previous epoch's freeze point, the lab nonce carried from the tick
\* before, and the extra entropy.
\* Literally: "EpochNonceDenotation is defined as: RefFold of chain's eta0
\*   equals Eta0Of of chain."
EpochNonceDenotation == RefFold(chain).eta0 = Eta0Of(chain)

\* Probes: each is expected to be violated, which proves the case is reached.
\* Literally: "ProbeTickLab is defined as: "tickLab" is not a member of seen."
ProbeTickLab       == "tickLab" \notin seen        \* an epoch nonce used a real etaH
\* Literally: "ProbeSkippedEpoch is defined as: "skip" is not a member of seen."
ProbeSkippedEpoch  == "skip" \notin seen           \* a tick crossed an empty epoch
\* Literally: "ProbeEntropy is defined as: "entropy" is not a member of seen."
ProbeEntropy       == "entropy" \notin seen        \* extra entropy was mixed in
\* Literally: "ProbePostFreeze is defined as: "postFreeze" is not a member of
\*   seen."
ProbePostFreeze    == "postFreeze" \notin seen     \* a block came after the freeze
\* Literally: "ProbeRollbackCand is defined as: "rollbackCand" is not a member
\*   of seen."
ProbeRollbackCand  == "rollbackCand" \notin seen   \* a rollback changed the candidate
=============================================================================
