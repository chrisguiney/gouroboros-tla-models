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
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.          *)
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

\* Literally: "vars is defined as the tuple of len, bits and signedBy."
vars == <<len, bits, signedBy>>

\* The smaller of two numbers.
\* Literally: "Min of a and b is defined as: if a is less than b then a, else
\*   b."
Min(a, b) == IF a < b THEN a ELSE b

\* The number of bytes for k bits, rounded up.
\* Literally: "Bytes of k is defined as (k plus B minus 1) integer-divided by
\*   B."
Bytes(k) == (k + B - 1) \div B

\* Pool i's stake: pools are numbered by descending stake, so seat i is
\* pool i [C1].
\* Literally: "Stake of i is defined as Pools minus i."
Stake(i) == Pools - i

\* The total stake of a set of pools.
RECURSIVE SumStake(_)
\* Literally: "SumStake of S is defined as: if S equals the empty set then 0,
\*   else, letting i be the x, chosen from S, such that TRUE: Stake of i plus
\*   SumStake of (S without the members of the set containing i)."
SumStake(S) ==
    IF S = {} THEN 0
    ELSE LET i == CHOOSE x \in S : TRUE IN Stake(i) + SumStake(S \ {i})

\* The total active stake: every pool, seated or not.
\* Literally: "Total is defined as SumStake of 0 through (Pools minus 1)."
Total == SumStake(0..(Pools - 1))

\* The stake reaches the quorum share of the total.
\* Literally: "Quorum of S is defined as: SumStake of S times TauDen is greater
\*   than or equal to TauNum times Total."
Quorum(S) == SumStake(S) * TauDen >= TauNum * Total

(***************************************************************************)
(* The reference [R1][R2].                                                 *)
(***************************************************************************)

\* The committee's size: Nc, or every pool if fewer.
\* Literally: "N is defined as Min of Nc and Pools."
N == Min(Nc, Pools)

\* The seats.
\* Literally: "Seats is defined as 0 through (N minus 1)."
Seats == 0..(N - 1)

\* The signers: set bits that name a seat; the rest is padding.
\* Literally: "RefSigners is defined as the intersection of bits and Seats."
RefSigners == bits \cap Seats

\* The reference accepts the certificate.
\* Literally: "RefAccept is defined as: len equals Bytes of N, and the
\*   intersection of RefSigners and Keyed equals RefSigners, and Quorum of
\*   RefSigners, and signedBy equals RefSigners."
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
\* Literally: "GoSeatCount is defined as: if StatePads then Nc, else N."
GoSeatCount == IF StatePads THEN Nc ELSE N

\* The seats gOuroboros reads.
\* Literally: "GoSeats is defined as 0 through (GoSeatCount minus 1)."
GoSeats == 0..(GoSeatCount - 1)

\* The committee size the bitfield is checked against: Nc today, the
\* committee's own size once fixed.
\* Literally: "GoBitfieldSeats is defined as: if GoFixed then GoSeatCount, else
\*   Nc."
GoBitfieldSeats == IF GoFixed THEN GoSeatCount ELSE Nc

\* The signers gOuroboros counts: set bits that name one of its seats.
\* Literally: "GoSigners is defined as: if Mutation equals "CountPadding" then
\*   bits, else the intersection of bits and GoSeats."
GoSigners ==
    IF Mutation = "CountPadding" THEN bits ELSE bits \cap GoSeats

\* gOuroboros accepts the certificate.
\* Literally: "GoAccept is defined as: (if GoFixed then GoSeatCount is less than
\*   or equal to Nc, else GoSeatCount equals Nc), and len equals Bytes of
\*   GoBitfieldSeats, and (the intersection of GoSigners and Keyed equals
\*   GoSigners, or Mutation equals "NoKeylessCheck"), and GoSigners does not
\*   equal the empty set, and (Quorum of GoSigners or Mutation equals
\*   "NoQuorum"), and if Mutation equals "NoKeylessCheck" then signedBy equals
\*   the intersection of GoSigners and Keyed, else signedBy equals GoSigners."
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
\* Literally: "Init is defined as: len is a member of 0 through (Bytes of Nc
\*   plus 1), and bits is a member of the set of subsets of 0 through (len times
\*   B minus 1), and signedBy is a member of the set of subsets of the
\*   intersection of Keyed and 0 through (Nc minus 1)."
Init ==
    /\ len \in 0..(Bytes(Nc) + 1)
    /\ bits \in SUBSET (0..(len * B - 1))
    /\ signedBy \in SUBSET (Keyed \cap 0..(Nc - 1))

\* Nothing happens: each certificate is checked once.
\* Literally: "Next is defined as: vars is unchanged."
Next == UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

\* Every variable has the expected shape.
\* Literally: "TypeOK is defined as: len is a member of Nat, and bits is a
\*   subset of 0 through (len times B minus 1), and signedBy is a subset of
\*   Keyed."
TypeOK ==
    /\ len \in Nat
    /\ bits \subseteq 0..(len * B - 1)
    /\ signedBy \subseteq Keyed

\* gOuroboros accepts exactly the certificates the reference accepts.
\* Literally: "AcceptAgrees is defined as: RefAccept equals GoAccept."
AcceptAgrees == RefAccept = GoAccept

\* Whatever gOuroboros accepts is sound: seated, keyed signers with quorum.
\* Literally: "GoSound is defined as: if GoAccept, then GoSigners is a subset of
\*   Seats, and GoSigners is a subset of Keyed, and Quorum of GoSigners."
GoSound ==
    GoAccept =>
        /\ GoSigners \subseteq Seats
        /\ GoSigners \subseteq Keyed
        /\ Quorum(GoSigners)

\* Probe, EXPECTED to be violated: some certificate is accepted.
\* Literally: "ProbeNeverAccepted is defined as: GoAccept is not true."
ProbeNeverAccepted == ~GoAccept
=============================================================================
