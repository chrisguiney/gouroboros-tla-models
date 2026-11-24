--------------------------- MODULE LeiosCommittee ---------------------------
(***************************************************************************)
(* Verifying a Leios certificate against the epoch's voting committee.     *)
(*                                                                         *)
(* The committee is the top Nc pools by stake, or every pool when fewer    *)
(* are registered. A certificate is a signer bitfield, one bit per seat    *)
(* and ceil(seats / 8) bytes long, plus one aggregate signature. It is     *)
(* valid when no keyless seat signed, the signers' stake reaches the       *)
(* quorum share of the total active stake, and the signature verifies      *)
(* under the aggregate of exactly the signers' keys. Bits past the last    *)
(* seat are padding and are ignored.                                       *)
(*                                                                         *)
(* The model holds one certificate, chosen freely at the start, and asks   *)
(* whether gOuroboros accepts it exactly when the reference does. It has   *)
(* no steps: every certificate is an initial state.                        *)
(*                                                                         *)
(* Sources (quotes and links in README.md).                                *)
(*   CIP-0164 at cardano-foundation/CIPs a2cac180:                         *)
(*   [C1] README.md 851-860 "Committee Structure" and 1146-1158            *)
(*        "Committee Selection": the top Nc pools; all of them if fewer.   *)
(*   [C2] README.md 3397-3423: the signers bitfield is ceil(N/8) bytes,   *)
(*        N the committee size: Nc, or the number of pools if smaller.     *)
(*   [C3] README.md 911-930 "Certificate Validation": signature, voter     *)
(*        eligibility, stake quorum.                                       *)
(*   Reference:                                                            *)
(*   [R1] cardano-ledger 1210d37f, libs/cardano-ledger-core/src/Cardano/   *)
(*        Ledger/State/Leios.hs 93-108 selectLeiosCommittee: size =        *)
(*        min committeeSize (number of candidates). The prototype's        *)
(*        ledger 505fa72 has the same line (State/LeiosCommittee.hs 99).   *)
(*   [R2] cardano-base c1e1ed8d (the prototype's), cardano-crypto-leios/   *)
(*        src/Cardano/Crypto/Leios.hs 289-326 verifyLeiosCert: bitfield    *)
(*        length must be (n+7) div 8 for the committee's own n; keyless    *)
(*        signers, then weight, then the aggregate signature.              *)
(*                                                                         *)
(* The gOuroboros code it is compared with (commit d0b95845):              *)
(*   [G1] ledger/leios/certificate.go VerifyDijkstraCertificateForMessage  *)
(*        102-235: len(Committee) must equal committeeSize (121), the      *)
(*        bitfield must be ceil(committeeSize/8) bytes (143), keyless      *)
(*        signers, at least one signer, quorum, signature.                 *)
(*   [G2] ledger/verify_block.go 400-410: committeeSize is the             *)
(*        LeiosCommitteeSize protocol parameter, Nc, and the bitfield is   *)
(*        checked against it before the committee is even looked up.      *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nc,        \* the committee-size protocol parameter
    Pools,     \* the number of registered pools
    B,         \* bits per bitfield byte (8 in reality; 2 keeps sets small)
    Keyed,     \* the seats whose pool has a valid voting key
    TauNum,    \* the quorum threshold is TauNum / TauDen of active stake
    TauDen,
    GoFixed,   \* TRUE: gOuroboros sizes the bitfield by the real committee
    StatePads, \* TRUE: the caller pads the committee to Nc keyless seats
    Mutation   \* "none", or one deliberate break of gOuroboros (see below)

VARIABLES
    len,      \* the bitfield's length in bytes
    bits,     \* the bit indices set in the bitfield
    signedBy  \* the seats whose signatures were aggregated

vars == <<len, bits, signedBy>>

\* The smaller of two numbers.
Min(a, b) == IF a < b THEN a ELSE b

\* The number of bytes for k bits, rounded up.
Bytes(k) == (k + B - 1) \div B

\* Pool i's stake: pools are numbered by descending stake, so seat i is
\* pool i [C1].
Stake(i) == Pools - i

\* The total stake of a set of pools.
RECURSIVE SumStake(_)
SumStake(S) ==
    IF S = {} THEN 0
    ELSE LET i == CHOOSE x \in S : TRUE IN Stake(i) + SumStake(S \ {i})

\* The total active stake: every pool, seated or not.
Total == SumStake(0..(Pools - 1))

\* The stake reaches the quorum share of the total.
Quorum(S) == SumStake(S) * TauDen >= TauNum * Total

(***************************************************************************)
(* The reference [R1][R2].                                                 *)
(***************************************************************************)

\* The committee's size: Nc, or every pool if fewer.
N == Min(Nc, Pools)

\* The seats.
Seats == 0..(N - 1)

\* The signers: set bits that name a seat; the rest is padding.
RefSigners == bits \cap Seats

\* The reference accepts the certificate.
RefAccept ==
    \* the bitfield is exactly ceil(N/8) bytes (MalformedSigners)
    /\ len = Bytes(N)
    \* no keyless seat signed (SignerWithoutKey)
    /\ RefSigners \cap Keyed = RefSigners
    \* the signers carry the quorum (InsufficientWeight)
    /\ Quorum(RefSigners)
    \* the signature is the aggregate of exactly the signers' (InvalidSignature)
    /\ signedBy = RefSigners

(***************************************************************************)
(* gOuroboros [G1][G2].                                                    *)
(***************************************************************************)

\* How many seats the caller's committee has: the real committee, or Nc
\* seats when the caller pads it with keyless, stakeless seats.
GoSeatCount == IF StatePads THEN Nc ELSE N

\* The seats gOuroboros reads.
GoSeats == 0..(GoSeatCount - 1)

\* The committee size the bitfield is checked against: Nc today, the
\* committee's own size once fixed.
GoBitfieldSeats == IF GoFixed THEN GoSeatCount ELSE Nc

\* The signers gOuroboros counts: set bits that name one of its seats.
GoSigners ==
    IF Mutation = "CountPadding" THEN bits ELSE bits \cap GoSeats

\* gOuroboros accepts the certificate.
GoAccept ==
    \* the committee has Nc seats (today) or at most Nc (fixed)
    /\ IF GoFixed THEN GoSeatCount <= Nc ELSE GoSeatCount = Nc
    \* the bitfield is sized for that committee
    /\ len = Bytes(GoBitfieldSeats)
    \* no keyless seat signed
    /\ (GoSigners \cap Keyed = GoSigners \/ Mutation = "NoKeylessCheck")
    \* someone signed
    /\ GoSigners # {}
    \* the signers carry the quorum
    /\ (Quorum(GoSigners) \/ Mutation = "NoQuorum")
    \* the signature is the aggregate of exactly the signers' (under
    \* NoKeylessCheck a keyless signer contributes no key but its stake)
    /\ IF Mutation = "NoKeylessCheck"
       THEN signedBy = GoSigners \cap Keyed
       ELSE signedBy = GoSigners

(***************************************************************************)
(* The certificates.                                                       *)
(***************************************************************************)

\* Every certificate: any length up to one byte past Nc's, any bits within
\* it, any set of keyed seats having signed.
Init ==
    /\ len \in 0..(Bytes(Nc) + 1)
    /\ bits \in SUBSET (0..(len * B - 1))
    /\ signedBy \in SUBSET (Keyed \cap 0..(Nc - 1))

\* Nothing happens: each certificate is checked once.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Every variable has the expected shape.
TypeOK ==
    /\ len \in Nat
    /\ bits \subseteq 0..(len * B - 1)
    /\ signedBy \subseteq Keyed

\* gOuroboros accepts exactly the certificates the reference accepts.
AcceptAgrees == RefAccept = GoAccept

\* Whatever gOuroboros accepts is sound: seated, keyed signers with quorum.
GoSound ==
    GoAccept =>
        /\ GoSigners \subseteq Seats
        /\ GoSigners \subseteq Keyed
        /\ Quorum(GoSigners)

\* Probe, EXPECTED to be violated: some certificate is accepted.
ProbeNeverAccepted == ~GoAccept
=============================================================================
