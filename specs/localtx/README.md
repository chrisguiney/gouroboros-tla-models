# local transaction submission and monitoring

Two node-to-client mini-protocols that a wallet or `cardano-cli` uses
against its own node:

- **local-tx-submission** (protocol 6): submit one transaction, get
  `MsgAcceptTx` or `MsgRejectTx`, repeat, then `MsgDone`.
- **local-tx-monitor** (protocol 9): acquire a snapshot of the mempool, ask
  about it (`MsgNextTx`, `MsgHasTx`, `MsgGetSizes`, `MsgGetMeasures`),
  re-acquire or release it, then `MsgDone`.

Both are plain request/response protocols with no pipelining. The questions
are about **which answer belongs to which request**, **when a side may wait
without limit**, and **how a run ends**.

Read [Model `keepalive`](../keepalive/README.md) first: the receive table, the
"Waits" and "Held" outcomes and server restarts carry over.

## Slice 1: local-tx-monitor (`LocalTxMonitor.tla`)

### What the code does

- `StateMap` (`protocol/localtxmonitor/localtxmonitor.go`) has one `Busy`
  state. A `stateContext` remembers the query that entered it (`matchQuery`)
  and `matchReply` accepts only that query's reply. This plays the role of
  the reference's `StBusy StBusyKind`.
- The client (`client.go`) serialises every call with `busyMutex`. Each
  query call acquires a snapshot first if it has none, and leaves it
  acquired. `Acquire()` sends `[1]` from Idle or from Acquired; from
  Acquired those bytes are `MsgAwaitAcquire` [R2]. `Stop()` sends `MsgDone`.
  `Stop()` takes the same `busyMutex`; on PR #3154 it first closes a
  channel that ends any call waiting for the server, and then closes the
  protocol without `MsgDone`, because the server holds agency.
  `NewClient` puts `AcquireTimeout` (5 s) on Acquiring and `QueryTimeout`
  (30 s) on Busy.
- The server (`server.go`) answers inside its message handler: an acquire,
  from Idle or Acquired, takes a new snapshot from `GetMempoolFunc` at once.
  It has no `MsgGetMeasures` and does not restart after `MsgDone`.

### The questions

1. **`RepliesMatchQueries`**: does the client ever hand a caller a reply to
   a different query?
2. **`NeverBothHaveAgency`**, **`BusyViewsAgree`**: do the two sides ever
   disagree about who may send, or does the client move on while the server
   is busy?
3. **`AwaitGetsNewSnapshot`**: is `MsgAwaitAcquire` ever answered with the
   snapshot the client already holds?
4. **`NoFailures`**: with honest peers, is the connection ever torn down?
5. **`NewRunServed`**: while the connection is up, can the server always
   read the message waiting for it? After `MsgDone` that is the first
   message of the client's next run, which only a restarted server reads.
   Written as `ENABLED Recv("Server")`, so it says nothing about how the
   server restarts, only that it can read.
6. **`StopNeverWaitsOnPeer`**: can a `Stop()` that has been called always
   take its next step without the server doing anything? The call lock is
   modelled (`lock`): every call holds it from its send until the client
   holds agency again, the protocol fails, or Stop cancels it.
7. Does anything get stuck? (TLC's deadlock check; a client waiting for a
   mempool change that the model has run out of is an allowed end,
   `WaitsForever`.)

Two constants model the version gate on `MsgGetMeasures` [R6]:
`NegotiatedV20` (the handshake agreed `NodeToClientV_20` or later) and
`ClientChecksVersion` (the client sends `MsgGetMeasures` only then).

### The answers

| Config | Setting | States (distinct) | Result |
| --- | --- | --- | --- |
| `LocalTxMonitor.cfg` | reference client and node; 2 runs, 2 queries, 2 mempool changes | 10,647 | all hold |
| `LocalTxMonitorGouroboros.cfg` | gOuroboros client and server, with the Stop fixes; 1 run, 3 queries | 11,602 | all hold |
| `LocalTxMonitorRogue.cfg` | one rogue message | 160,884 | `RepliesMatchQueries` holds |
| `LocalTxMonitorTable.cfg` | prints the receive table (192 rows) | 12 | passes |
| `LocalTxMonitorTimeoutBug.cfg` | **gOuroboros client against the node** | 664 | `NoFailures` violated in 8 steps |
| `LocalTxMonitorStopBug.cfg` | **gOuroboros `Stop()` after a query** | 209 | `NoFailures` violated |
| `LocalTxMonitorStopWaitBug.cfg` | **gOuroboros `Stop()` at PR #3154 `e9996ade`, waiting on the call lock** | 6 | `StopNeverWaitsOnPeer` violated |
| `LocalTxMonitorMeasuresBug.cfg` | reference client against gOuroboros server | 59 | `NoFailures` violated |
| `LocalTxMonitorRestartBug.cfg` | gOuroboros server on main, second run | 21 | `NewRunServed` violated |
| `LocalTxMonitorAwaitBug.cfg` | gOuroboros server answers await at once | 50 | `AwaitGetsNewSnapshot` violated |
| `LocalTxMonitorFixed.cfg` | gOuroboros with the get-measures, await and restart fixes, plus the open Stop and await-timeout client fixes and Stop ending a waiting call; as the reference config | 10,647 | all hold |
| `LocalTxMonitorOldNode.cfg` | fixed client against a node before `NodeToClientV_20` | 452 | all hold |
| `LocalTxMonitorOldNodeBug.cfg` | the same, client does not check the version | 369 | `NoFailures` violated |

So, against the reference: (1) to (3) hold, and (4) holds for the
reference pair. gOuroboros has two defects and three deviations:

- **Await timeout (defect).** The shortest trace: acquire, acquired,
  `Acquire()` again (`MsgAwaitAcquire` on the wire), the node waits for its
  mempool to change [R5], the client's 5-second `AcquireTimeout` fires and
  tears down the whole node-to-client connection. Against a gOuroboros
  server it never shows, because that server answers at once
  (`LocalTxMonitorGouroboros.cfg` passes with the timers on).
- **Stop after a query (defect).** Every query call leaves the snapshot
  acquired; `Stop()` then sends `MsgDone`, which has no transition from
  Acquired, so the client's own send loop refuses it and reports a protocol
  error. Reproduced in Go: "message \*localtxmonitor.MsgDone not allowed in
  current protocol state Acquired".
- **Stop waits for the server (defect, found in review of PR #3154).**
  With the re-acquire untimed, `Acquire()` holds `busyMutex` while
  `MsgAwaitAcquire` waits for a mempool change, and `Stop()` took the same
  mutex before acting, so only the node's answer let it return. The model
  shared the defect: its `ClientStop` started "only while the client holds
  agency", so it never had Stop called during a wait. It now models the
  lock and Stop's request, cancel and run as separate steps, and
  `StopNeverWaitsOnPeer` fails in two steps (acquire, then Stop) when Stop
  cannot cancel (`StopCancelsWait = FALSE`). Any call waiting for the server
  shows it; the await is the case with no bound. PR #3154 head `615e2a84`
  closes a channel before taking the mutex: a waiting call returns
  `ErrProtocolShuttingDown`, and Stop closes the protocol without
  `MsgDone`, as a reference client thread that is cancelled sends nothing
  (`StopCancelsWait = TRUE`, the `Closed` client view). Go:
  `TestStopDoesNotWaitForPeer` (re-acquire and each query; fails before the
  fix with "Stop waited for the node to answer").
- **No `MsgGetMeasures`, no restart, await answered at once
  (deviations).** See the comparison table. Branches fix all three (see
  Go tests); `LocalTxMonitorFixed.cfg` is gOuroboros with them, and checks
  the same state space as the reference config, since with the fixes the
  two behave alike. The await fix is opt-in (`AwaitMempoolFunc`): without
  it the server still answers at once (`LocalTxMonitorAwaitBug.cfg`), and
  with it but without the open client fix for the await timeout, a
  gOuroboros client against that server fails as against the node
  (`LocalTxMonitorTimeoutBug.cfg`). So the default should change only
  after that client fix lands, and only where the application can say when
  its mempool changed.
- **Review of PR #3196 (head `26f0e50a`): the awaited acquire times out
  against gOuroboros's own client.** The reviewer reproduced
  `LocalTxMonitorTimeoutBug.cfg` in Go: with `AwaitMempoolFunc` set, a
  default client's `AcquireTimeout` (5 s) fires while the server waits, and
  the PR's tests pass only because they zero it. The model already had this
  trace, so it needs no change: the fix is the client one, PR #3154
  (`e9996ade`, `matchAwaitAcquire` and a `TimeoutFunc` that returns 0 for an
  await), which the reference matches (no time limit on `StAcquiring` [S4]).
  Checked on a scratch merge of PR #3154 into `26f0e50a` with the tests'
  `AcquireTimeout` set to 50 ms: the await tests pass (the await lasts at
  least 100 ms); on `26f0e50a` alone the same change fails
  `TestServerAwaitAcquireWaitsForChange` with "protocol is shutting down".
  So PR #3154 merges first, and PR #3196 then drops the zeroed timeout from
  its test helper. The scratch merge also showed that PR #3154's state-map
  model test and `TestStopDoesNotWaitForPeer` need `MsgGetMeasures` rows
  once both land, a merge-order conflict for whichever lands second.

### Checking the checks

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `LocalTxMonitorBusyKindsBug.cfg` | Busy remembers its query (`matchReply`) | `RepliesMatchQueries` |
| `LocalTxMonitorAgencyBug.cfg` | the same | `NeverBothHaveAgency` |
| `LocalTxMonitorStopBug.cfg` | Stop releases first | `NoFailures` |
| `LocalTxMonitorStopWaitBug.cfg` | Stop ends a waiting call | `StopNeverWaitsOnPeer` |
| `LocalTxMonitorAwaitBug.cfg` | the server waits for a change | `AwaitGetsNewSnapshot` |
| `LocalTxMonitorRestartBug.cfg` | the server restarts | `NewRunServed` |
| `LocalTxMonitorOldNodeBug.cfg` | the client checks the version | `NoFailures` |

Reachability probes, each violated on the reference config, so the passing
run does reach: the server blocked on an await
(`ProbeServerNeverBlocks`), an answered await (`ProbeAwaitNeverAnswered`),
`StBusy GetMeasures` (`ProbeNoGetMeasures`), a second run
(`ProbeNoSecondRun`), Stop's release-then-done
(`ProbeNoReleaseThenDone`), and Stop cancelling a waiting
`MsgAwaitAcquire` (`ProbeNoCancelledAwait`). One config each,
`LocalTxMonitorProbe*Bug.cfg`.

The rogue configs set `CHECK_DEADLOCK FALSE`: a rogue `MsgAcquire` to a
server whose client is done leaves an answer nobody reads, which is a stuck
connection, not a protocol property.

## Slice 2: local-tx-submission (`LocalTxSubmission.tla`)

### What the code does

The client's `SubmitTx` takes `busyMutex`, sends `MsgSubmitTx`, and waits on
an unbuffered `submitResultChan`, which both answer handlers write to.
`NewConfig` sets a 30-second timeout on Busy on main; PR #3140 sets none by
default, and `WithTimeout` opts in (`ClientTimeouts`). `NewClient` copies
that value onto its own Busy state: `TestClientBusyTimeout` checks on a
running client that a held submission is not timed by default and is timed
with `WithTimeout`. That test changes no behaviour, so the model is
unaffected by it: `ClientTimeouts` already describes both settings.
`Stop()` takes the same `busyMutex`; on PR #3140 it first closes a channel
that ends a waiting `SubmitTx`, then closes the protocol without `MsgDone`.
The server calls `SubmitTxFunc` inside its handler and answers; it does not
restart after `MsgDone`.

### The questions

1. **`AnswersReachTheirCallers`**: answers carry no transaction ID, so only
   order ties them to a request. Does an answer ever reach the wrong caller?
2. **`OneSubmitInFlight`**: is more than one transaction ever on the wire?
3. **`NoFailures`**, **`NeverBothHaveAgency`**, deadlock, as above.
4. **`StopNeverWaitsOnPeer`**, as above; a waiting `SubmitTx` holds
   `busyMutex` (`LockHeld`).

### The answers

| Config | Setting | States (distinct) | Result |
| --- | --- | --- | --- |
| `LocalTxSubmission.cfg` | reference; 2 runs, 2 transactions, mempool fills and drains twice | 453 | all hold |
| `LocalTxSubmissionGouroboros.cfg` | gOuroboros client, server never waits; 1 run | 82 | all hold |
| `LocalTxSubmissionTable.cfg` | prints the receive table (24 rows) | 3 | passes |
| `LocalTxSubmissionTimeoutBug.cfg` | **gOuroboros client against the node, mempool full** | 63 | `NoFailures` violated |
| `LocalTxSubmissionStopWaitBug.cfg` | **gOuroboros `Stop()` at PR #3140 `18f07468`, mempool full** | 16 | `StopNeverWaitsOnPeer` violated |
| `LocalTxSubmissionRestartBug.cfg` | gOuroboros server on main, second run | 23 | `NewRunServed` violated |

The node's `addTx` "will block until the transaction fits into the
mempool" [R4], and the reference sets no timeout [S3]. The gOuroboros
client's 30-second default tears the connection down while a full mempool
drains. PR #3140 changes the default to none.

That made a second defect reachable, found in the class audit of the
review of PR #3140: with no timer, `SubmitTx` holds `busyMutex` for as long
as the mempool stays full, and `Stop()` took the same mutex before acting.
The model shared it: `ClientStop` ran only when no caller waited. Stop is
now called at any time, and `LocalTxSubmissionStopWaitBug.cfg` fails
`StopNeverWaitsOnPeer` when Stop cannot cancel. PR #3140 head `641eff0a`
has Stop end the waiting `SubmitTx` and close without `MsgDone`
(`StopCancelsWait = TRUE`); Go: `TestStopDoesNotWaitForSubmit`, which fails
before the fix with "Stop waited for the node to answer".

### Checking the checks

| Config (expected to fail) | Safeguard removed | Invariant broken |
| --- | --- | --- |
| `LocalTxSubmissionNoMutexBug.cfg` | `busyMutex` in `SubmitTx` | `AnswersReachTheirCallers` |
| `LocalTxSubmissionOneSubmitBug.cfg` | honest client (rogue extra `MsgSubmitTx`) | `OneSubmitInFlight` |
| `LocalTxSubmissionAgencyBug.cfg` | honest server (rogue answer) | `NeverBothHaveAgency` |
| `LocalTxSubmissionTimeoutBug.cfg` | no client timer | `NoFailures` |
| `LocalTxSubmissionRestartBug.cfg` | the server restarts | `NewRunServed` |
| `LocalTxSubmissionStopWaitBug.cfg` | Stop ends a waiting `SubmitTx` | `StopNeverWaitsOnPeer` |

Without `busyMutex` the second transaction still waits in the send queue
(the send loop needs agency), but two callers wait on one channel and the
first answer may wake either (probe `ProbeNoQueuedBehind`, on the mutation).
The Go runtime wakes receivers in arrival order, so this is not
reproducible deterministically in Go; the model is the evidence.

Probes on the reference config: `ProbeServerNeverBlocks`,
`ProbeNoSecondRun`, `ProbeNoCancelledHeldSubmit` (Stop cancels a
submission the node holds for a full mempool).

## The modelling mistakes

- `ClientStop` was enabled only while the client held agency, on the
  assumption that Stop waits for the call in progress. That hid the hang
  in review of PR #3154: with the await untimed, the wait has no bound.
  The call lock is now a variable, Stop is called at any time, and
  `StopNeverWaitsOnPeer` checks it.

- The first `LocalTxMonitorRogue.cfg` run reported a deadlock: a rogue
  `MsgAcquire` restarted a server whose client was done, and the answer was
  never read. That is a stuck connection, not a protocol property; the rogue
  configs now check safety only.
- The first `Stop` fix test read one muxer segment per message and timed
  out: the muxer sent `MsgRelease` and `MsgDone` in one segment. The test
  now splits segments into messages.

## Go tests and mutations

Patches against gOuroboros `origin/main` 61046085 (commits could not be
signed in this session; see the parent's handoff):

| Branch | File | Covers | Mutation that fails it |
| --- | --- | --- | --- |
| `test/localtxmonitor-state-model` | `protocol/localtxmonitor/statemap_model_test.go` | all 192 role x state x message cells: statically against `StateMap` (busy cells per query kind, through `matchReply`), and on a running client and server; Done only from Idle; `StBusy GetMeasures` cannot be entered | drop Acquired's `MsgRelease` row; drop `matchReply` on `MsgReplyHasTx`; add `MsgDone` from Acquired |
| `test/localtxsubmission-state-model` | `protocol/localtxsubmission/statemap_model_test.go` | all 24 cells, statically and running; Done only from Idle | drop Busy's `MsgRejectTx` row; drop Idle's `MsgDone` row; give Busy client agency |
| `fix/localtxmonitor-stop-releases` | `client.go`, `client_stop_test.go` | `Stop()` sends `MsgRelease` then `MsgDone` when acquired | test fails before the fix (no message, protocol error) |
| `fix/localtxmonitor-await-acquire-timeout` | `localtxmonitor.go`, `client.go`, `await_acquire_test.go` | no `AcquireTimeout` on an acquire from Acquired; still timed from Idle | test fails before the fix ("timeout waiting on transition from protocol state Acquiring") |

Fixes against gOuroboros `origin/main` `d8f5bc2a`, each with a test that
fails without it:

| Branch | Commit | Covers | Fails before the fix |
| --- | --- | --- | --- |
| `fix/localtxmonitor-get-measures` | `923a32dc` | `MsgGetMeasures` (11) and `MsgReplyGetMeasures` (12), their transitions, `Client.GetMeasures`, the server's answer over the transactions `NextTx` has not returned, gated on `NodeToClientV_20` both ways | `TestServerAnswersGetMeasures`: "no reply ... ReplyGetMeasures" (decoding failed) |
| `fix/localtxmonitor-await-acquire` | `c0ec388e` | opt-in `AwaitMempoolFunc`: the server answers `MsgAwaitAcquire` only once it returns; stop ends the wait | `TestServerAwaitAcquireWaitsForChange`: "MsgAwaitAcquire answered with an unchanged mempool" |
| `fix/localtxmonitor-server-restart` | `885a5991` | restart in Idle after `MsgDone` | `TestServerAnswersAcquireSentDuringRestart`: "no reply from restarted server: Acquired" |
| `fix/localtxsubmission-server-restart` | `1086fdb1` | restart in Idle after `MsgDone` | `TestServerAnswersSubmitSentDuringRestart`: "no reply from restarted server: AcceptTx" |

Existing tests already covered: every query/reply pair in `matchReply`, a
mismatched reply refused by a running client, shutdown releasing waiting
callers, `MsgDone` from Idle in submission, and accept/reject round trips.

## Spec, reference, and gOuroboros

| Question | Specification | Reference | gOuroboros | Verdict |
| --- | --- | --- | --- | --- |
| Which reply in `StBusy HasTx`? | Table says `MsgReplyNextTx` [S3 l.2157]; figure says `MsgReplyHasTx` | `MsgReplyHasTx` [R1][R2] | `MsgReplyHasTx` (`matchReply`) | Spec typo; follow the reference |
| Busy kind decides the legal reply? | Yes, `StBusy` per query [S2] | Yes [R1][R2] | Yes, via `stateContext` | Agree |
| Queries only while acquired? | Yes [S3] | Yes | Yes | Agree |
| `MsgAwaitAcquire` | waits for a new snapshot [S3] | same bytes as `MsgAcquire` [R2]; node blocks until the snapshot differs [R5] | client: same bytes, but timed (5 s); server: answers at once | **Client defect** (fixed); server deviation, fixed opt-in on `fix/localtxmonitor-await-acquire` (`AwaitMempoolFunc`), since only the application knows when its mempool changed |
| `MsgGetMeasures` | in the protocol [S3] | always decoded and answered [R2][R3] | not implemented; decoding fails and the connection is torn down | Deviation; fixed on `fix/localtxmonitor-get-measures` |
| `MsgGetMeasures` before `NodeToClientV_20` | not stated | the encoder refuses both messages [R6]; the node now negotiates only V_23, so it never arises there | with the fix: the client returns an error without sending; the server fails the protocol | Follows the reference |
| Timeouts | "No timeouts" [S4], [S3 submission] | none defined | monitor: 5 s / 30 s; submission: 30 s; PR #3140 `641eff0a`: submission none by default, `WithTimeout` opts in, checked on a running client | Deviation; harmful where the node may wait (await; full mempool); submission fixed on PR #3140 |
| Stop while a submission is held | no client message from `StBusy` [S2] | the client thread is cancelled; nothing is sent [R4] | PR #3140 `18f07468`: `Stop()` waits under `busyMutex` for as long as the mempool stays full; `641eff0a`: ends the wait and closes without `MsgDone` | **Defect** (fixed on PR #3140) |
| `MsgDone` from Acquired | not allowed [S3] | not expressible [R4] | `Stop()` sends it and fails | **Defect** (fixed) |
| Stop while waiting for the server | no client message from `StAcquiring` or `StBusy` [S2] | the client thread is cancelled; nothing is sent [R4] | PR #3154 `e9996ade`: `Stop()` waits for the answer under `busyMutex`, forever for an await; `615e2a84`: ends the wait and closes without `MsgDone` | **Defect** (fixed on PR #3154) |
| Server after `MsgDone` | restarts [S5] | inbound governor restarts it [R7] | stays done | Deviation; fixed for both servers on `fix/localtxmonitor-server-restart` and `fix/localtxsubmission-server-restart` |
| Receiving while holding agency | not stated | not read until peer has agency | refused at once | Deviation, as in Model `keepalive` |

## Sources

Pinned to [IntersectMBO/ouroboros-network `5f356486ab3e`](https://github.com/IntersectMBO/ouroboros-network/tree/5f356486ab3e6cc16ab15bddb04ed5068b9ed84c),
[IntersectMBO/ouroboros-consensus `ec239d57f618`](https://github.com/IntersectMBO/ouroboros-consensus/tree/ec239d57f618d698b6350b48bf017b02c0c96a5f),
and gOuroboros `origin/main` at `61046085`. `P` below is
`ouroboros-network/protocols/lib/Ouroboros/Network/Protocol`.

| Ref | Where | What it says |
| --- | --- | --- |
| S1 | `docs/network-spec/miniprotocols.tex` 27-36 | One side has agency; an unexpected message closes the connection. |
| S2 | `miniprotocols.tex` 2055-2103 | Local tx-monitor figure and agency table. |
| S3 | `miniprotocols.tex` 2105-2166 (monitor messages and table); 1840-1886 (submission) | Messages and transitions; submission "No size limits", "No timeouts". |
| S4 | `miniprotocols.tex` 2168-2174 | Monitor: "No size limits", "No timeouts". |
| S5 | `docs/network-spec/connection-manager.tex` 489-503, 629-634 | Responders restart after a clean end; node-to-client servers run in ResponderMode. |
| R1 | `P/LocalTxMonitor/Type.hs` 70-95, 130-141, 200-289; `P/LocalTxSubmission/Type.hs` 36-55, 104-132 | States, busy kinds, messages, agency; `MsgAwaitAcquire` blocks; StBusy "there's no timeout". |
| R2 | `P/LocalTxMonitor/Codec.hs` 63-174; `P/LocalTxSubmission/Codec.hs` 107-169 | Tags; `MsgAwaitAcquire` = `[1]`; per-kind reply decoding; `MsgGetMeasures` decoded at every version. |
| R3 | `cardano-diffusion/protocols/lib/Cardano/Network/Protocol/LocalTxMonitor/Codec.hs` 41-42 | The node always uses `LocalTxMonitor_V2`. |
| R4 | `P/LocalTxMonitor/{Client,Server}.hs` 121-166, 117-191; `P/LocalTxSubmission/{Client,Server}.hs` 94-106, 56-80; consensus `Ouroboros/Consensus/Mempool/API.hs` 142-145 and `MiniProtocol/LocalTxSubmission/Server.hs` 26-38 | Typed peers; adding a transaction blocks until it fits. |
| R5 | consensus `Ouroboros/Consensus/MiniProtocol/LocalTxMonitor/Server.hs` 85-104 | `recvMsgAwaitAcquire` retries until the snapshot differs; 75-84 `recvMsgGetMeasures` counts the transactions not yet returned by `MsgNextTx`. |
| R6 | `P/LocalTxMonitor/Codec.hs` 57, 78-86, 102-113; `P/LocalTxMonitor/Type.hs` 316-317; `cardano-diffusion/api/lib/Cardano/Network/NodeToClient/Version.hs` 58-59 | The encoder sends `MsgGetMeasures` and `MsgReplyGetMeasures` only at `LocalTxMonitor_V2`, that is `NodeToClientV_20` and later. |
| R7 | `ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs` 455-470; `ouroboros-network/lib/Ouroboros/Network/Diffusion.hs` 402-418 | A responder that ended cleanly is restarted; the node-to-client server runs under an inbound governor too. |
| G1 | gOuroboros `protocol/localtxmonitor/{localtxmonitor,client,server}.go`, `protocol/localtxsubmission/{localtxsubmission,client,server}.go`, `protocol/protocol.go` | State maps, matchers, timeouts, `Stop`, send and receive checks. |

The receive-before-agency rule cited as Model `keepalive`'s [S8] (typed-protocols
`Driver.hs`) was not re-read for this model.

## Not modelled

Message contents (transaction validity, reject reasons, `MsgReplyNextTx`
order within a snapshot), size limits (none in the spec), CBOR decoding
limits, the server's transaction-ID cache, and API misuse such as
`Release()` from Idle (it sends `MsgRelease` and fails the same way as
`Stop()` did).

## After merging main into #3196

Merge `763c0977` (main at `cc300dc8`) keeps #3196's await on
`MsgAwaitAcquire` and get-measures on top of main's restart after `MsgDone`
(#3197) and maphash ID cache (#3224). The await watches the stop channel of
the run that is waiting, as every other restarted call does. `MsgDone` is
accepted only in `StIdle`, after `MsgRelease` has cleared the held snapshot,
so a restarted run never starts holding one and the merge changes nothing the
model checks.

## Running it

```sh
cd specs/localtx
../../bin/tlc -config LocalTxMonitor.cfg LocalTxMonitor.tla
../../bin/tlc -config LocalTxMonitorGouroboros.cfg LocalTxMonitor.tla
../../bin/tlc -config LocalTxMonitorFixed.cfg LocalTxMonitor.tla
../../bin/tlc -config LocalTxMonitorOldNode.cfg LocalTxMonitor.tla
../../bin/tlc -config LocalTxMonitorRogue.cfg LocalTxMonitor.tla
../../bin/tlc -config LocalTxMonitorTable.cfg LocalTxMonitor.tla | grep '^<<'
../../bin/tlc -config LocalTxSubmission.cfg LocalTxSubmission.tla
../../bin/tlc -config LocalTxSubmissionGouroboros.cfg LocalTxSubmission.tla
../../bin/tlc -config LocalTxSubmissionTable.cfg LocalTxSubmission.tla | grep '^<<'
# expected to fail (bugs, deviations, mutations, probes):
for c in LocalTxMonitor*Bug.cfg; do ../../bin/tlc -config $c LocalTxMonitor.tla || true; done
for c in LocalTxSubmission*Bug.cfg; do ../../bin/tlc -config $c LocalTxSubmission.tla || true; done
```

## Merging main into #3133, #3140 and #3154

Main had #3196 (`MsgGetMeasures`, `AwaitMempoolFunc`) and #3197 (servers
restart after `MsgDone`), the behaviour `LocalTxMonitorFixed.cfg` and the
`ServerRestarts` setting already describe, so no model change. The merges
change only the Go side to match: #3140 (`ffc14012`) drops the server-restart
deviation from its receive table and documents no default submit timeout;
#3154 (`9f549801`) drops the `MsgGetMeasures` and restart deviations, covers
`StBusy GetMeasures` in both receive tests, removes
`TestBusyGetMeasuresCannotBeEntered`, keeps the untimed re-acquire beside
`WithAwaitMempoolFunc`, and makes `GetMeasures` end on `stopRequested` like
the other waiting calls (`StopCancelsWait`;
`TestStopDoesNotWaitForPeer/GetMeasures` failed "Stop waited for the node to
answer" on the merge before it). #3133 (`43090651`) conflicted only in
`protocol/peersharing/README.md`.
