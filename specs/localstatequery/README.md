# local state query

Local state query is how a node-to-client program (a wallet, `cardano-cli`,
an indexer) reads the node's ledger. The client asks the node to **acquire**
a ledger state: a specific point, the volatile tip, or the immutable tip.
It then sends **queries** against that state, and finally **releases** it or
moves straight to another state with `MsgReAcquire`. A run ends with
`MsgDone`.

```
StIdle --MsgAcquire--> StAcquiring --MsgAcquired--> StAcquired --MsgQuery--> StQuerying
  ^  \                     |                          |  |  ^                    |
  |   MsgDone              MsgFailure                 |  |  +-----MsgResult------+
  |    v                   v                          |  MsgReAcquire --> StAcquiring
  |  StDone              StIdle                       |
  +--------------------MsgRelease---------------------+
```

The gOuroboros client (`protocol/localstatequery/client.go`, about 2,200
lines) is mostly query and result types. This model covers what all of them
lean on: the **state machine** (slice 1) and the **client's concurrency**
(slice 2), the code paths every `Get...` call goes through. It does not
check the encoding of individual queries.

Read [Model `keepalive`](../keepalive/README.md) first. The receive table and
"Waits / Held" vocabulary come from there.

## Slice 1: the state machine (`LocalStateQuery.tla`)

### What the specification and reference say

Five states. The client has agency in `StIdle` and `StAcquired`, the server
in `StAcquiring` and `StQuerying`, and nobody in `StDone` [S2][R1]. There
are eight transitions [S3][R1]. `MsgAcquire` and `MsgReAcquire` carry a
**target**, and the codec gives each target its own wire key, so there are
twelve message kinds on the wire [R3]. Only a `SpecificPoint` can fail:
the volatile and immutable tips "cannot fail to be acquired" [R2]. A failed
re-acquire drops the old state: "failure to re-acquire is equivalent to
`MsgRelease`" [S3].

The model has a client that may send any message the reference client type
allows, and a server that answers as the reference allows. After `MsgDone`
the client may start a second run on the same connection. The reference's
node-to-client server runs under the inbound governor, which **restarts** a
responder that ended cleanly [R4].

### The questions

1. **`NoViolations`**: does either side ever receive a message its state
   does not allow?
2. **`NeverBothHaveAgency`**: do the two sides ever both think they may send?
3. **`ViewsAgreeWhenQuiet`**: with nothing in flight, do they agree on the
   state?
4. **`QueriesOnlyWhenAcquired`**: is a query only ever answered while the
   client is in `StQuerying`, so queries run only on an acquired state?
5. Does anything deadlock (TLC checks this by default)?

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LocalStateQuery.cfg`: the reference, two runs, server restarts | 2,204 | passes all five |
| `LocalStateQueryNoRestartBug.cfg`: the gOuroboros server, which does not restart | | **fails**: deadlock after 5 steps |
| `LocalStateQueryFailureBug.cfg`: mutation, a failed re-acquire keeps the old state | | **fails** `NoViolations` |

The deadlock trace is short: the client sends `MsgDone`, the server reads it
and stays in `StDone`, the client starts a new run and sends `MsgAcquire`,
and nobody ever reads it.

`LocalStateQueryTable.tla` prints the receive table: 120 cells (2 roles x 5
states x 12 kinds). The gOuroboros test holds the same rows.

### Checking the checks

`LocalStateQueryFailureBug.cfg` breaks the "failure equals release" rule
and `NoViolations` fails (the client queries, the server is in `StIdle`).
The reachability probes each claim something never happens, and TLC shows
each does: a failed re-acquire (`ProbeNoFailedReAcquire`), a query
(`ProbeNoQuery`), a second run (`ProbeNoSecondRun`), and acquiring the
immutable tip (`ProbeNoImmutable`).

## Slice 2: the gOuroboros client (`LocalStateQueryClient.tla`)

### What the code does

- Every public call (`Acquire...`, `Release`, every `Get...`) holds
  `busyMutex` from before it sends until its answer arrives, so at most one
  request is outstanding.
- `acquire` sends `MsgReAcquire` if the `acquired` flag is set, otherwise
  `MsgAcquire`, then waits on the unbuffered `acquireResultChan`.
- A query made while `acquired` is false first **acquires the volatile tip
  itself** (`runQueryMaxItems`), then sends `MsgQuery` and waits on the
  unbuffered `queryResultChan`. On `61046085` nothing ever releases that
  state; with the fix, the call releases it as it returns.
- Some calls make two queries: `GetEpochNo` and `GetCurrentProtocolParams`
  ask for the era, then for that era's data. The model's `Query2` is such a
  call.
- `release` sends `MsgRelease` and clears the flag, whatever the flag was.
- The handler sets `acquired` on `MsgAcquired` and clears it on
  `MsgFailure`, then blocks handing the answer over.
- `Stop` closes `stopChan`. Once the receive and send loops exit, `DoneChan`
  closes, and a goroutine started by `Start` closes both result channels, so
  a waiting call returns `ErrProtocolShuttingDown`. `Start` runs once
  (`onceStart`), so a stopped client is never restarted.
- `protocol.Protocol` checks each message against `StateMap` as it is sent
  and as it is read. One that is not legal is a protocol error that tears
  the connection down.

The model has two goroutines making two calls each, a server whose chain
grows, and `Stop` at any moment.

### The questions

1. **`OwnAnswer`**: does every call receive the answer to its own request?
   This is the defect chain-sync had (Model `chainsync`, slice 3).
2. **`NoViolation`**: does either side ever see a message its state does not
   allow?
3. **`FlagMatchesState`**: when nothing is in flight, is `acquired` true
   exactly when the protocol is in `StAcquired`?
4. **`FreshImplicitSnapshot`**: does a query made without an explicit
   acquire answer from a state at least as new as the chain was when the call
   began?
5. **`OneSnapshotPerCall`**: do all the queries of one call answer from the
   same state?
6. Does every call return, including when `Stop` lands while a request is
   outstanding? (This is TLC's deadlock check. `Finished` is the only
   stutter step.)

### The answers

| Config | States | Result |
| --- | --- | --- |
| `LocalStateQueryClient.cfg`: today, every call except `Release` | 636,116 | passes 1, 2, 3, 6 |
| `LocalStateQueryClientReleaseIdleBug.cfg`: today, with `Release` | | **fails** `NoViolation` |
| `LocalStateQueryClientReleaseCheck.cfg`: `Release` refuses when nothing is acquired | 1,105,828 | passes 1, 2, 3, 6 |
| `LocalStateQueryClientImmutableOldBug.cfg`: today, node-to-client v9-v15 | | **fails** `NoViolation` |
| `LocalStateQueryClientImmutableOld.cfg`: v9-v15 with the version gate | 506,062 | passes 1, 2, 3, 6 |
| `LocalStateQueryClientStaleBug.cfg`: today | | **fails** `FreshImplicitSnapshot` |
| `LocalStateQueryClientFresh.cfg`: the implicit-acquire fix and the `Release` check, with two-query calls | 1,791,198 | passes 1-6 |
| `LocalStateQueryClientPerQueryReleaseBug.cfg`: rejected design, release after each query | | **fails** `OneSnapshotPerCall` |

(The counts grew slightly from the first version of this model: each call
now also tracks how many queries it has left and the states they answered
from.)

So the concurrency is sound. `busyMutex` is held across the whole exchange.
The result channels are unbuffered, so no stale answer can sit in a buffer.
No call returns before its answer except by shutdown. So no answer can reach
another call. Unlike chain-sync, `Stop` has no restart hazard: `Start` never
brings a stopped client back. A call that is waiting when `Stop` lands
returns `ErrProtocolShuttingDown`.

Three defects were found:

- **`Release` with nothing acquired.** It sends `MsgRelease` from `StIdle`.
  The send loop refuses it and the connection is torn down, while `Release`
  returns nil.
- **The immutable tip on an old version.** It was added in node-to-client
  v16 [R6], and the reference refuses to encode it before that [R3].
  gOuroboros supports v9 and later and sends it anyway, so an older node
  cannot decode it.
- **The implicit acquire is never released.** The first query on an idle
  client pins the volatile tip. Every later query answers from that
  snapshot, even though `GetChainPoint` is documented as returning "the
  current chain tip". The reference has no implicit acquire [R5]. Fixed on
  a branch: the call releases it as it returns.

### Checking the checks

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `LocalStateQueryClientNoMutexBug.cfg` | calls take `busyMutex` | `OwnAnswer`, and `NoViolation` |
| `LocalStateQueryClientKeepFlagBug.cfg` | `handleFailure` clears `acquired` | `FlagMatchesState`, and `NoViolation` (the next call sends `MsgReAcquire` from `StIdle`) |

The cfg files list both invariants, and TLC stops at the first one that
fails. Each was also run alone and fails alone.

Probes, each violated against `LocalStateQueryClient.cfg`:
`ProbeNoStopWhileWaiting` (`Stop` lands while a call waits),
`ProbeNoImplicit`, `ProbeNoReAcquire`, `ProbeNoFailure`, and
`ProbeOneInside` (a second goroutine queues on the mutex while the first
waits).

### The modelling mistake

The first version modelled a server that does not restart as judging the
next run's message in `StDone`, where nothing is legal, and so reporting a
violation. The Go test showed otherwise: gOuroboros leaves the message
unread and the client waits until its acquire times out. The model now
leaves it unread too, so the failure shows up as a deadlock, which is what
the code does.

## Slice 3: query encodings (`LocalStateQueryCodec.tla`)

### What the code does

A table, not a protocol: each cell is a Shelley-based era, a block query
and the filter a caller passes (nil, empty or non-empty). The model does
no byte arithmetic; a set argument is a plain array, an array behind tag
258, or CBOR null. Three rules of gOuroboros are switchable between `main`
and the fix, one per DRIFT entry:

- `EraSetRule` (N48): main writes the delegations filter of
  `GetFilteredDelegationsAndRewardAccounts` tagged in every era and the two
  UTxO filters as the caller's slice, so nil is null;
  `fix/localstatequery-era-set-encoding` (`eraFilterSet`) tags the three
  from Conway and sends nil as the empty set.
- `AccountStateRule` (N49): main sends `GetAccountState` only from Conway;
  `fix/localstatequery-account-state-all-eras` sends it in every Shelley
  era.
- `FuturePParamsRule` (N50): main's server has no query type 33;
  `fix/localstatequery-decode-future-pparams` decodes it.

The reference [Q1]-[Q5], [L1]-[L3]: the three filters use the era's own
encoding at the era's lowest protocol version, so a set is tagged from
Conway (version 9) and the node refuses the tag before it; null is never a
set. `GetNonMyopicMemberRewards`, `GetStakePoolParams` and
`GetStakeDelegDeposits` use cardano-binary and are tagged in every era.
`GetGovState` and `GetAccountState` are answered in every Shelley era;
`GetConstitution`, `GetRatifyState`, `GetFuturePParams` and the Conway set
queries only from Conway (`requireCG`).

### The questions

| Invariant | Question | Reference rule |
| --- | --- | --- |
| `ClientSetsDecode` | does a node decode every set the client sends? | `decodeSet` [L3] |
| `ClientSetsAsReference` | is every set the shape the reference writes? | `toEraCBOR` [L1], `encodeSet` [L2], goldens |
| `ClientOffersAnswered` | does the client send every query a node answers in that era? | [Q4] |
| `ClientSendsAnswered` | does it send only those? | [Q3] |
| `ServerDecodesAnswered` | does the server decode every query a node decodes? | [Q5] |
| `ServerRefusesAsReference` | probe: does it decode only those, era by era? | [Q3] |

Three `ASSUME`s tie the table to the Go tests: on main, 23 of
`TestEraFilterSetEncoding`'s 35 cells have the wrong shape, five eras of
`TestGetAccountStateEveryShelleyEra` are refused (Shelley to Babbage), and
`TestDecodeGetFuturePParamsQuery`'s two eras (Conway, Dijkstra) fail to
decode.

### The answers

| Config | Rules | Result | Counterexample |
| --- | --- | --- | --- |
| `LocalStateQueryCodec.cfg` | all three fixes | passes (294 cells) | |
| `LocalStateQueryCodecEraSetDecodeBug.cfg` | N48 on main | `ClientSetsDecode` fails | Shelley, `GetUTxOByAddress(nil)`: null, the Go cell `GetUTxOByAddress nil/Shelley` |
| `LocalStateQueryCodecEraSetBytesBug.cfg` | N48 on main | `ClientSetsAsReference` fails | the same cell; the bytes check also catches the untagged UTxO filters from Conway, which a node still decodes |
| `LocalStateQueryCodecAccountStateBug.cfg` | N49 on main | `ClientOffersAnswered` fails | Shelley, `GetAccountState` |
| `LocalStateQueryCodecFuturePParamsBug.cfg` | N50 on main | `ServerDecodesAnswered` fails | Conway, query 33 |
| `LocalStateQueryCodecGovStateBeforeConwayBug.cfg` | known difference | `ClientOffersAnswered` fails | Shelley, `GetGovState`: the client sends it only from Conway because `GovStateResult` decodes the Conway state (recorded, not fixed) |
| `LocalStateQueryCodecProbeServerEraBug.cfg` | probe | `ServerRefusesAsReference` fails | Shelley, `GetConstitution` |

With the fixes, the fixed rule's "era at least Conway" agrees with the
reference's "lowest version at least 9" in every era, and the six sibling
set queries already had the reference's shape. The probe shows the server
decodes a Conway-only query in any era and hands it, with the era, to the
query callback, where the reference refuses it at decode. That holds for
the new query 33 as for `GetConstitution` and `GetRatifyState` before it;
answering it is the callback's job, not a defect of the fix.

## Go tests and fixes

All on gOuroboros `61046085`. Every test was run with `-race`.

### `test/localstatequery-state-model`

`protocol/localstatequery/statemap_model_test.go`:

- `TestStateMapMatchesModel` checks every within-run cell of the 120-row
  table against `StateMap`, including cells no running role can rest in.
- `TestUnreachableStates` checks which transitions enter `Done`,
  `Querying`, `Acquired` and `Idle`. For example, a query can only be sent
  from `Acquired`, and a failed acquire or re-acquire returns to `Idle`.
- `TestReceiveMatchesModel` drives a running client or server into each
  state it can rest in and sends every kind. It records two differences.
  First, gOuroboros refuses a message sent while the receiver holds agency
  (`Waits`) instead of leaving it to wait; the keep-alive test records the
  same. Second, the server does not restart after `MsgDone` (the defect
  below).
- `TestConcurrentCallsGetOwnAnswers`: 8 goroutines x 25 calls of two query
  kinds; each must decode its own answer.
- `TestStopWithQueryOutstanding`: `Stop` while the server computes;
  the call returns `ErrProtocolShuttingDown`, and so does a call after
  `Start`.

| Mutation | Tests that fail |
| --- | --- |
| `MsgFailure` moves to `Acquired` | `TestStateMapMatchesModel`, `TestUnreachableStates` |
| `MsgRelease` removed from `Acquired` | the two above and `TestReceiveMatchesModel` |
| `MsgQuery` allowed in `Idle` | the same three |
| no `busyMutex` in `GetChainBlockNo` and `GetChainPoint` | `TestConcurrentCallsGetOwnAnswers` |
| `Start`'s cleanup does not close `queryResultChan` | `TestStopWithQueryOutstanding` (the call hangs), `TestReceiveMatchesModel` |

Failed acquire, re-acquire after failure, and the wire key for every target
were already covered by `TestAcquisitionWireMatrix` in `server_test.go`.

### Fixes, one branch each

| Branch | Fix | Test, and the evidence it failed before |
| --- | --- | --- |
| `fix/localstatequery-release-when-idle` | `Release` returns `ErrNotAcquired` and sends nothing | `TestReleaseWithNothingAcquired`. Before: `Release()` returned nil, then "message *MsgRelease not allowed in current protocol state Idle", and every later call returned "protocol is shutting down" (5 runs of 5) |
| `fix/localstatequery-immutable-tip-version` | below v16, acquiring or re-acquiring the immutable tip returns `ErrAcquireImmutableTipUnsupportedVersion` and keeps any acquired state | `TestAcquireImmutableTipNeedsVersion16`. Before: the client sent it on v15 |
| `fix/localstatequery-implicit-acquire` | a query on an idle client acquires the volatile tip for the rest of the public call; `endCall`, which every public call defers, releases it before letting the next call in | `TestImplicitQueryAnswersFromCurrentTip` (before: second `GetChainBlockNo` returned 100, want 200), `TestImplicitAcquireSpansTheCall` (before: no release), `TestExplicitAcquireKeepsSnapshot` (before: no release after the implicit call), `TestCurrentEraNotCachedAcrossImplicitCalls` (before: era 5, want 6). With per-query release instead, `TestImplicitAcquireSpansTheCall` fails (epoch 8, want 7) |
| `fix/localstatequery-server-restart` | the server replaces its protocol instance after `MsgDone`, as the chain-sync server does; `Stop` wins over a restart in progress; connection shutdown calls the server's `Stop` | `TestServerAnswersAcquireSentDuringRestart` and `TestServerAnswersBackToBackRestarts` failed with "no reply from restarted server"; a new `localstatequery` case in `TestServerStopDuringRestartStopsServer` fails if `initProtocol` ignores `stopped` |

When the restart fix and the test branch are merged, `gouroborosServer` in
the test must go back to the reference table. Merged, 12 server `Done`
cells fail until it does, and the package passes once it does.

### The implicit acquire

Reproduced on `61046085`. The server's tip is 100 and the client calls
`GetChainBlockNo`. The tip moves to 200 and the client calls it again. The
second call returns 100, and the server saw one acquire (3 runs of 3).

Releasing after each query is not enough: calls such as
`GetCurrentProtocolParams` make two queries (the era, then the parameters),
and a release between them lets the two straddle an era boundary.
`LocalStateQueryClientPerQueryReleaseBug.cfg` shows it. So the implicit
acquire lasts for the public call. Every public call already took
`busyMutex` and deferred its unlock, so the fix replaces that one deferred
line with `endCall`, which releases an implicitly acquired state and then
unlocks. No query method changed otherwise.

The era is cached for as long as a state is held. Calls made without an
explicit acquire no longer share it, so each such call that needs the era
asks for it: one more round trip.

Merging: textually clean with the other three fix branches and the test
branch. Merged with `test/localstatequery-state-model`,
`TestConcurrentCallsGetOwnAnswers` times out, because its server has no
`ReleaseFunc` and the gOuroboros server treats `MsgRelease` without one as
an error. Giving that test's server a `ReleaseFunc` makes the package pass.
With `fix/localstatequery-release-when-idle`, `endCall` only releases when
`acquired` is set, so it never meets `ErrNotAcquired`.

## Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| States, agency, transitions | [S2][S3] | Same [R1] | Same (`StateMap`) | Agree |
| Queries only while acquired | `MsgQuery` only from `StAcquired` [S3] | Typed [R1][R5] | Yes; an idle client acquires first | Agree on the wire |
| Failed (re-)acquire | Back to `StIdle`, old state dropped [S3] | Same [R1] | Same; clears `acquired` | Agree |
| Can a tip acquire fail? | Not said | No [R2] | Client accepts a failure anyway | Lenient, harmless |
| Immutable tip before v16 | Not said | Refused [R3][R6] | Sent | **Defect, fixed on a branch** |
| Release with nothing acquired | Illegal [S3] | Impossible by types [R5] | Sent; tears down the connection | **Defect, fixed on a branch** |
| Server after `MsgDone` | "terminate" [S3] | Restarted by the inbound governor [R4] | Stays in `Done`, holds later messages | **Defect, fixed on a branch** |
| Which call gets an answer | The one that asked | The continuation that sent [R5] | The one holding `busyMutex`; always the asker | Agree |
| Implicit acquire | None | None [R5] | Volatile tip, never released | **Stale answers; fixed on a branch** (released as the call returns) |
| Client ending with `MsgDone` | Client may terminate [S3] | `SendMsgDone` [R5] | No API; `Stop` unregisters without `MsgDone` or `MsgRelease`, so the node holds the state until the connection closes | Recorded |
| Timeouts | "No timeouts" [S3, line 2020] | "There is a timeout" in `StAcquiring` (`Type.hs` line 55) | Acquiring 5 s, Querying 180 s, client side | Recorded |
| A message while the receiver has agency | Not said | Waits | Refused at once | Recorded (as keep-alive) |

## Sources

Pinned to [IntersectMBO/ouroboros-network `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c)
and gOuroboros `origin/main` at `61046085`. `P` below is
`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/LocalStateQuery`.

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | `docs/network-spec/miniprotocols.tex` lines 27-36 | One side has agency; an unexpected message aborts the connection. |
| S2 | same file, lines 1915-1948 | Local-state-query state machine and agency table. |
| S3 | same file, lines 1950-2020 | Messages, targets, "failure to re-acquire is equivalent to MsgRelease" (line 1990), the transition table, "No size limits", "No timeouts". |
| R1 | `P/Type.hs` lines 44-70, 139-200 | States, messages, agency; `StDone` is `NobodyAgency`. |
| R2 | `P/Type.hs` lines 114-130 | `VolatileTip` and `ImmutableTip` cannot fail; `ImmutableTip` "Requires at least NodeToClientV_16". |
| R3 | `P/Codec.hs` lines 80-206 | Wire keys 0-11; lines 89-96 and 130-137 refuse to encode an immutable-tip acquire without v16; decoding is per state. |
| R4 | `ouroboros-network/lib/Ouroboros/Network/Diffusion.hs` lines 402-419; `ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs` lines 440-476 | The local (node-to-client) server runs under the inbound governor, which restarts a responder that terminated cleanly. |
| R5 | `P/Client.hs` lines 36-89, 149-205 | The reference client: one continuation per state; no implicit acquire; `SendMsgDone` from `StIdle`. |
| R6 | `cardano-diffusion/api/lib/Cardano/Network/NodeToClient/Version.hs` lines 48-50 | v16 "added ImmutableTip". At this commit only v23 is supported, and `cardano-diffusion/.../LocalStateQuery/Codec.hs` lines 42-43 always uses `LocalStateQuery_V2`. |
| G1 | gOuroboros `protocol/localstatequery/` | `localstatequery.go` (`StateMap`), `client.go` (`acquire`, `release`, `runQueryMaxItems`, the handlers, `Start`), `server.go` (`handleDone`); `protocol/protocol.go` (`stop`, `enqueueMessage`, the receive checks). |
| Q1-Q5 | ouroboros-consensus `ec239d57f618` `ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/Ledger/Query.hs` lines 739, 742, 750, 760, 765, 773 (encode); 842-848, 855, 859, 864, 871-872, 882, 885-886 (decode, `requireCG`); 498, 503, 507 (supported on every version); goldens `golden/cardano/QueryVersion3/CardanoNodeToClientVersion19/Query_<Era>_<Query>` | Which set encoding each query argument uses, and which queries are refused before Conway. |
| L1 | cardano-ledger `1210d37fe6bd` `libs/cardano-ledger-core/src/Cardano/Ledger/Core/Era.hs` 232-242; `libs/cardano-ledger-core/internal/Cardano/Ledger/Internal/Definition/Era.hs` 95-140 | `toEraCBOR`/`fromEraCBOR` use the era's lowest version: Shelley 2 ... Conway 9, Dijkstra 12. |
| L2 | same, `libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Encoding/Encoder.hs` 479-490 | `encodeSet`: tag 258 from version 9. |
| L3 | same, `libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/Decoder.hs` 933-952 | `decodeSet`: tag refused from 2 to 8, permitted but not enforced from 9. |
| G3 | gOuroboros `62fa36d1` `protocol/localstatequery/client.go` 594, 674, 892; branch `fix/localstatequery-era-set-encoding` (`eraFilterSet`) | The three filters. |
| G4 | same, `client.go` 941-945; branch `fix/localstatequery-account-state-all-eras` | The `GetAccountState` era guard. |
| G5 | same, `queries.go` 81, 244; branch `fix/localstatequery-decode-future-pparams` | No query type 33 on main; `ShelleyFuturePParamsQuery` on the branch. |
| G2 | gOuroboros `35982911` (`fix/localstatequery-implicit-acquire`), `client.go` | `endCall`, `runQueryMaxItems`; `GetEpochNo` makes two queries. |

## Not modelled

The encoding and results of individual queries other than the set
arguments, era guards and query type 33 in `LocalStateQueryCodec.tla`; Byron
(where the fixed `GetAccountState` guard refuses); the cached era
(`currentEra`), the server's callbacks, timeouts (a timeout is a protocol
error, like the violations here), and the message size limit
(`MaxReadBufferSize`).

## Running it

```sh
cd specs/localstatequery
../../bin/tlc -config LocalStateQuery.cfg LocalStateQuery.tla
../../bin/tlc -config LocalStateQueryNoRestartBug.cfg LocalStateQuery.tla || true   # expected to fail
../../bin/tlc -config LocalStateQueryFailureBug.cfg LocalStateQuery.tla || true     # expected to fail
../../bin/tlc -config LocalStateQueryTable.cfg LocalStateQueryTable.tla | grep '^<<'
../../bin/tlc -workers 4 -config LocalStateQueryClient.cfg LocalStateQueryClient.tla
../../bin/tlc -workers 4 -config LocalStateQueryClientReleaseCheck.cfg LocalStateQueryClient.tla
../../bin/tlc -workers 4 -config LocalStateQueryClientImmutableOld.cfg LocalStateQueryClient.tla
../../bin/tlc -workers 4 -config LocalStateQueryClientFresh.cfg LocalStateQueryClient.tla
# expected to fail:
for c in ReleaseIdle ImmutableOld Stale PerQueryRelease NoMutex KeepFlag; do
  ../../bin/tlc -workers 4 -config LocalStateQueryClient${c}Bug.cfg LocalStateQueryClient.tla || true
done
../../bin/tlc -config LocalStateQueryCodec.cfg LocalStateQueryCodec.tla
for c in EraSetDecode EraSetBytes AccountState FuturePParams GovStateBeforeConway ProbeServerEra; do
  ../../bin/tlc -config LocalStateQueryCodec${c}Bug.cfg LocalStateQueryCodec.tla || true   # expected to fail
done
```

To run a probe, copy a passing config and replace its `INVARIANT` lines
with the probe's name.
