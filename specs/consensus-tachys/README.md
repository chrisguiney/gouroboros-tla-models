# 27: consensus — the Tachys public leader schedule

Ouroboros Tachys (CIP-0177) is Praos with one change: who may make a block
in a slot. Praos runs a private VRF lottery; Tachys publishes a schedule
that names exactly one pool for every slot:

- before the epoch, the stake distribution becomes a **cumulative
  distribution**: pools in order of their 28-byte ID, each owning an
  interval `[lo, hi)` as wide as its stake;
- for each slot, `sample = hash(nonce ‖ slot)`, read as a fraction of
  2^256, picks the interval that holds it;
- a header is authorised when its issuer (the hash of its cold key) is that
  pool. VRF, KES and opcert checks stay exactly as in Praos.

gOuroboros implements this in `consensus/tachys.go`
(`NewTachysLeaderSelector`, `TachysSample`, `Leader`, `LeaderForSample`,
`IsLeader`, `AuthorizeIssuer`, `IsTachysSlotLeader`), in
`consensus/validate.go` (`NewTachysHeaderValidator`, the Tachys branch of
`validateLeadership`), and in `consensus/block.go` (`NewTachysBlockBuilder`).
The only caller is Dingo's `ledger/tachys.go`
(`tachysPoolsFromStakeDistribution`), which drops zero-stake pools before
building.

Model `consensus` covers Praos chain selection, opcerts and KES; model `consensus-nonce` covers the
epoch nonce. This model takes both as given.

## Sources

- **Specification**: CIP-0177 at `cardano-foundation/CIPs`
  `86b89208d3b2aabb5dcc5b778dfbe09096b4e114`, `CIP-0177/README.md` (the
  revision gOuroboros pins in `TachysSpecificationRevision`; identical to
  `master` at the time of writing). It has no test vectors.
  - [S1] lines 96, 112: "the epoch structure and nonce computations are
    exactly the same, and it continues to use both VRF and KES"; "we
    replace the authorisation component … but we keep the authentication
    the same".
  - [S2] 114-116, 390: "a unique SPO identity for every slot"; "the
    probability of each SPO being leader in each slot is the same as the
    fraction of stake".
  - [S3] 151-155: the new leader check compares the computed SPO identifier
    with "a hash of the SPO's cold verification key" from the header.
  - [S4] 163-165: "Take the representation of the epoch nonce, and the
    representation of the slot number; concatenate their representations
    and take their cryptographic hash … interpreted as a fraction … using a
    denominator of 2^256."
  - [S5] 167-171: intervals "inclusive below and exclusive above", width
    "exactly the fraction of total active stake", contiguous over [0, 1);
    "can be implemented faithfully using only (big) integer arithmetic".
  - [S6] 175-183: the running sum, "taking the SPOs in order of the
    representation of their identifiers".
  - [S7] 191-195: block production "reuses that predicate".
- **Reference implementation**: none. Searched IntersectMBO
  `ouroboros-consensus` at `ec239d57f618` and `cardano-ledger` at
  `1210d37f` (trees and code search for "tachys"), their branches, and the
  CIP's links (the CIP PR #1149 and its "Implementation Plan", which only
  plans a Haskell prototype). The model follows the CIP alone, and uses
  cardano-ledger only for the distribution a node would read:
  - [R1] `libs/cardano-ledger-core/src/Cardano/Ledger/State/SnapShots.hs`
    679-696: `calculatePoolDistr'` keeps a pool when
    `spssNumDelegators spss > 0`, so a pool whose delegators hold no stake
    is in `PoolDistr` with stake 0.
  - [R2] same file 317-321: `ssTotalActiveStake` is a `NonZero Coin`
    "defaulted to 1".
- **gOuroboros**: main at `756a9a898573`. `consensus/tachys.go` 56-102
  (build), 109-121 (sample), 142-167 (lookup), 184-197 (issuer),
  202-260 (forging); `consensus/validate.go` 39-53, 185-198, 480-500.

## The model (`TachysSchedule.tla`)

Pool IDs are numbers (numeric order stands for byte order); a sample is a
number in `0..D-1` (D stands for 2^256); the hash is any function from
(nonce, slot) to a sample, so TLC tries every possible hash output. Header
cryptography is a record of booleans (VRF, KES, opcert, registered VRF key,
and whether the VRF output would also have won the Praos lottery).

The state machine: the initial state picks a reference distribution (any
pools, any stake 0..MaxStake, including zero), any order of the caller's
slice, any hash, and the declared total. `Build` calls
`NewTachysLeaderSelector`; `Query` asks for a leader and logs the answer;
`CallerReuses` overwrites the caller's slice afterwards.

Constants: `ZeroStake` (`Filter`: Dingo drops zero-stake pools; `Pass`: the
reference `PoolDistr` as is), `Declared` (`Exact` or `Any` total), `GoZero`
(`Reject`: gOuroboros main; `Accept`: zero-stake pools get empty
intervals), `WordMax` (uint64, scaled down), and `Mutation`.

| Rule | Specification (CIP-0177) | Reference | gOuroboros (main `756a9a89`) |
| --- | --- | --- | --- |
| Order | by "representation of their identifiers" [S6] | none; `KeyHash` `Ord` is byte order | `bytes.Compare` on the 28-byte ID |
| Interval | `[lo, hi)`, width = stake / total [S5] | none | `upperStake` = running sum; lookup is `sample·T < upper·2^256` via `sort.Search` |
| Zero stake | a zero-width interval, never selected [S5] | `PoolDistr` includes pools with delegators but no stake [R1] | **refused**: the whole selector fails ("has zero stake"); Dingo filters first, which gives the same schedule |
| No stake | no interval covers [0, 1) | total defaults to 1 [R2] | refused (empty, zero total) |
| Total | sum of active stake | `pdTotalActiveStake` | caller declares it; must equal the sum, and fit uint64 |
| Sample | `hash(repr(nonce) ‖ repr(slot))` / 2^256 [S4]; representations unspecified | none | `BLAKE2b-256(nonce32 ‖ uint64be(slot))`; nonce must be 32 bytes |
| Authorisation | issuer hash = scheduled SPO [S3] | none | `AuthorizeIssuer`: `Blake2b224(vkey)` constant-time compared |
| Other checks | VRF, KES, opcert unchanged [S1] | Praos `PRTCL` | unchanged; schedule checked only after the VRF proof verifies |
| Forging | reuse the predicate [S7] | none | `IsTachysSlotLeader` ignores the Praos stake inputs |

## Invariants

- `BuildAgrees`: gOuroboros builds a selector exactly when the CIP has a
  schedule (some stake is delegated).
- `ExactlyOneLeader`: every sample is in exactly one CIP interval and in
  exactly one gOuroboros interval.
- `LeaderDefined`: the lookup never runs off the end (Go would panic).
- `LeaderAgrees`: gOuroboros names the CIP's leader for every sample.
- `WidthEqualsStake`: each interval is exactly its pool's stake wide.
- `Proportional`: of the D samples, a pool leads within one of
  `stake·D/T`.
- `ZeroStakeNeverLeads`: a pool without stake is never the leader.
- `SameInputsSameLeader`: the same (nonce, slot) always gives the same
  leader, even after the caller reuses its slice.
- `ValidatorExact`: a header is valid exactly when VRF, KES, opcert and
  VRF-key checks pass and its issuer is scheduled, whatever the Praos
  lottery says.
- `ForgeMatchesValidate`: a producer forges exactly when scheduled.

## Configurations

| Config | Question | Expected |
| --- | --- | --- |
| `TachysSchedule` | main with the Dingo caller; 3 pools, stake 0..2, D = 4, 2 slots | pass (117,376 states) |
| `TachysScheduleDeep` | stake 0..3, D = 6, 1 slot | pass (148,812) |
| `TachysScheduleAccept` | the reference `PoolDistr` as is, zero-stake pools accepted as empty intervals | pass (302,240): filtering and accepting give the same schedule |
| `TachysScheduleAnyTotal` | any declared total; every invariant but `BuildAgrees` | pass (134,144): a wrong total is always refused |
| `TachysZeroStakePassBug` | main fed the reference `PoolDistr` as is | `BuildAgrees` fails: a pool with delegators but no stake refuses the epoch |
| `TachysOverflowBug` | totals past uint64 | `BuildAgrees` fails (the CIP's rationals are unbounded; real totals are below 45·10^15) |
| `TachysInclusiveBug` | `<=` in the lookup | `ExactlyOneLeader` fails |
| `TachysNoTotalCheckBug` | no sum check, any total | `LeaderDefined` fails |
| `TachysUnsortedBug` | intervals in slice order | `LeaderAgrees` fails |
| `TachysUpperIsStakeBug` | upper = own stake | `WidthEqualsStake` fails |
| `TachysProportionalBug` | upper = own stake | `Proportional` fails |
| `TachysZeroStakeInclusiveBug` | zero stake accepted, plus `<=` | `ZeroStakeNeverLeads` fails |
| `TachysAliasBug` | selector reads the caller's slice | `SameInputsSameLeader` fails |
| `TachysPraosThresholdBug` | Praos threshold kept | `ValidatorExact` fails |
| `TachysSkipVrfBug` | VRF proof not verified | `ValidatorExact` fails |
| `TachysAnyPoolBug` | any distribution pool accepted | `ValidatorExact` fails |
| `TachysForgePraosBug` | forging also asks the lottery | `ForgeMatchesValidate` fails |
| `TachysProbe*Bug` | a sample on an upper bound; a zero-stake reference pool with a schedule; a single pool; the largest sample; a reused slice | each probe is violated (reachable) |

Run with `make consensus-tachys`.

## gOuroboros test

`consensus/tachys_model_test.go` (branch `test/tachys-model`) walks the
model's cells: every three-pool distribution with stake 0..3 through the
Dingo caller, every slice ordering, declared totals 0, sum-1 and sum+1,
both edges of every interval and the smallest and largest sample against
an independent exact-rational CIP lookup, the interval widths, sixteen
slots on the hash path with every pool asked `IsLeader`, and 64
header-check combinations plus forging. Each mutation above that has a
one-line Go form (`unsorted`, `inclusive`, `upperIsStake`,
`noTotalCheck`, `praosThreshold`, `skipVrf`, `anyPool`, `forgePraos`, and
"sample 0 picks a zero pool") fails it. `alias` has no Go form: the
selector holds its own interval array, built at construction.

## Findings

1. **Zero-stake pools are refused, not given empty intervals.** The CIP
   allows zero-width intervals, and the reference `PoolDistr` contains
   such pools. gOuroboros refuses the whole distribution; Dingo, the only
   caller, filters them first, and the model shows the schedules are the
   same. A caller contract, documented in `consensus/README.md`, not a
   defect today.
2. **The sample's byte representation is gOuroboros' choice.** CIP-0177
   says "the representation" of nonce and slot without fixing it, and has
   no vectors. gOuroboros uses the 32 raw nonce bytes then the 8-byte
   big-endian slot (the reverse of Praos `mkInputVRF`, which puts the
   slot first), and rejects a non-32-byte nonce, so it has no form for
   `NeutralNonce`. The Haskell implementation, when it exists, may choose
   differently.
3. **Which stake integer to pass is the caller's.** Conway's
   `individualTotalPoolStake` adds proposal deposits [R1, PoolDistr.hs
   65-76], so it does not sum to `pdTotalActiveStake`; the CIP's fraction
   is `individualPoolStake`. Dingo reads its own snapshot sum.

### Follow-up: header validation order

The header validator now runs its checks in the reference order. A failed registered-VRF-key check skips the eligibility check, and the Tachys schedule check is part of eligibility. The Go table test therefore expects the "not the scheduled leader" error only when both the VRF proof and the registered VRF key pass.

This changes only which error is reported. Which headers are accepted is unchanged, so the model is unaffected: `ValidatorExact` constrains acceptance, not error order. The validation order itself is modelled in `consensus-eras` (`HeaderValidation.tla`).
