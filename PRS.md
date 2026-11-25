# Pull requests each model produced

This file is local bookkeeping. The models are not published, so the pull
requests and issues below never mention them: they describe each test by what
it checks against the reference. Use this table to find the model behind a PR,
or the PRs behind a model.

States are as of 2026-11-24. "Closes" lists the gOuroboros issues each PR
closes. A PR can draw on more than one model.

| Model | Pull requests | Closes | State |
| --- | --- | --- | --- |
| `keepalive` | gouroboros #3080 (server restarts after MsgDone); #3077 closed in its favour | #3076 | merged |
| `connection` | #3087 (stop servers restarting after MsgDone) | #3085 | merged |
| `engine` | #3090 (admission generation drift tests) | #3089 | merged |
| `engine` | #3159 (time only the receiver; no default node-to-client timeouts) | #3145, #3146 | merged |
| `connection` (`ConnectionTeardown`), `engine` (`EngineLifecycle`) | local branch `fix/connection-teardown-joins` (`c164be91`; supersedes `fix/connection-close-during-dial` and `fix/connection-late-forwarder`), not yet published | | local |
| `engine` (`EngineLifecycle`) | local branch `test/protocol-lifecycle` (`c5ab084c`), not yet published | | local |
| `chainsync` | #3092 (close the connection when Stop cannot send MsgDone) | #3091 | merged |
| `chainsync` | #3094 (GetCurrentTip waits for its own answer) | #3093 | merged |
| `chainsync` | #3112 (MustReply timeout, node-to-node message size, state map tests) | #3096, #3097, #3101 | merged |
| `handshake` | #3127 (negotiate before a query reply, simultaneous open, its proposal written before ending, state map tests) | #3115, #3116, #3117 | open |
| `handshake` | #3194 (negotiated data in the accept, recognised key order) | #3181, #3182 | merged |
| `blockfetch` | #3114 (Stop, refused requests, Busy timeout, state map tests) | #3107, #3108, #3109, #3110 | merged |
| `txsubmission` | #3128 (txid request blocking rules, state map tests) | #3118, #3119, #3120 | merged |
| `txsubmission` | #3195 (clamp over-window requests from V16) | #3183 | merged |
| `peersharing` | #3133 (WithTimeout doc, state map tests) | #3131, #3132 | open |
| `localtx` | #3140 (no default submit timeout; Stop never waits on a submit) | #3134, #3135 | open |
| `localtx` | #3154 (re-acquire untimed; Stop never waits on the peer) | #3143, #3144 | open |
| `localtx` | #3196 (get-measures, opt-in await on await-acquire) | #3184, #3185 | merged |
| `localtx`, `dmq`, `leios-peras` | #3197 (six servers restart after done) | #3186 | merged |
| `localstatequery` | #3113 (acquire, release, restart, implicit acquire, state map tests) | #3098, #3102, #3103, #3104, #3105, #3106 | merged |
| `dmq` | #3130 (interoperate with dmq-node, repeat requests, state map tests) | #3121, #3122, #3123 | open |
| `dmq` | #3142 (empty blocking replies, lost wakeup) | #3137, #3138, #3139 | merged |
| `leios-peras` | #3160 (quit, cancel, pipelined vote requests, state map tests) | #3150, #3151, #3152, #3153 | merged |
| `leios-peras` | #3165 (await, server idle, timeouts) | #3162, #3163, #3164 | merged |
| `consensus` | #3111 (header envelope, first header after Origin) | #3095, #3099, #3100 | open |
| `ledger-shelley` | #3129 (epoch-aware pool registration) | #3124, #3125, #3126 | merged |
| `ledger-governance` | #3155 (nil voter, governance lookup contract) | #3147, #3148, #3149 | merged |
| `ledger-governance` | ouroboros-mock #368 (governance action expiry at the last slot) | ouroboros-mock #367 | approved |
| `pipeline-cbor` | #3161 (drain after the apply runner, lossless Results; reentrant drain follow-up `1cfba318`) | #3156, #3157, #3158 | merged `1559924b` |
| `pipeline-cbor` | #3141 (transaction body id without stored CBOR) | #3136 | merged |
| `ledger-utxo` | #3193 (BadInputs covers collateral and reference inputs) | #3179, #3180 | merged |
| `consensus-genesis` | #3173 (exact window count, density table tests) | #3169, #3170 | merged |
| `ledger-byron` | #3174 (empty transactions, heavyweight delegation activation) | #3171, #3172 | merged |
| `ledger-leios` | #3192 (committee smaller than the parameter) | #3177, #3178 | merged |
| `ledger-leios` (`LeiosVoting`) | local branch `test/leios-voting-model` (`eb73b151`; certificates formed by the reference vote collection over reference-seated committees, mutated aggregation, quorum boundary vectors), not yet published | | local |
| `ledger-leios` (`LeiosVoting`) | local branch `fix/leios-voting-key-age` (`93c3df5d`; certificates refuse aged-out voting keys, required key-age method, breaking), not yet published | | local |
| `ledger-leios` (`LeiosVoteShape`) | local branch `fix/leios-vote-shape` (`eb4c2421`; CIP-0164 vote encoding, rc-2026w41 golden vote, breaking), not yet published | | local |
| `dmq` (`MessageValidity`, `MessageIngress`, `MessagePayloadBytes`) | local branches `fix/dmq-kes-claimed-period`, `fix/dmq-ttl-reference-bounds`, `fix/dmq-message-body-size`, `fix/dmq-commit-recheck-every-counter`, `fix/dmq-payload-preserved-bytes`, `fix/dmq-drop-chain-counter-check`, `fix/dmq-sig-rate-limit`, `fix/messagesubmission-reference-receipt` (DRIFT N52-N58), not yet published | | local |
| `consensus-nonce` | reviewed and approved jtranq's #3053 (rolling nonce derivation; it reproduced the model's 15 mainnet vectors) | #3052 | merged |
| `consensus-eras` | #3201 (header check order, KES before the opcert start, TPraos overlay and envelope inputs) | #3198, #3199, #3200 | merged |
| `consensus-eras` | #3205 (empty era history, Byron slot-to-epoch, era table tests) | #3202, #3203, #3204 | merged |
| `ledger-bbody` | #3208 (Conway header protocol-version check, block body table tests) | #3206, #3207 | merged |
| `ledger-witnesses` | #3211 (bootstrap witnesses in the genesis-delegate quorum, witness table tests) | #3209, #3210 | open |
| `ledger-ppup-mir` | #3216 (empty update, phase-2-invalid update and MIR quorum, table tests) | #3212, #3213, #3214, #3215 | merged |
| `ledger-conway-dijkstra` | #3218 (table tests) | #3217 | merged |
| `ledger-conway-dijkstra` (`SubCerts`) | local branch `test/dijkstra-subtx-certs-model` (`b1d3d9db`, `727e0cd0`, `f8b8a8a9`; certificate, deposit, owner-witness, retirement, multi-certificate, legacy, balance-interval cells), not yet published | | local |
| `ledger-conway-dijkstra` (`SubGov`) | local branch `test/dijkstra-subtx-certs-model` (`727e0cd0`; governance and DRep/committee cells); `fix/dijkstra-committee-proposed-member` published as #3245 | | local |
| `ledger-conway-dijkstra` (`SubGuards`, `SubGov` family 3) | local branch `test/dijkstra-subtx-certs-model` (`824672bf`; guard, guard-context and proposal-check cells); `fix/dijkstra-ppu-well-formed` published as #3246 | | local |
| `ledger-conway-dijkstra` (`SubGov`, `SubGuards`) | #3245 (`0a8bde9f`, DRIFT L23: earlier-level UpdateCommittee proposals count as members), #3246 (`9f7e7d38`, DRIFT L24: eMax 0 and pledge leverage below 1 refused) | #3243, #3244 | open |
| `consensus-tachys` | #3220 (table tests against CIP-0177) | #3219 | merged |
| `consensus-nonce` | #3223 (neutral epoch nonce and VRF input, as new functions) | #3221, #3222 | merged |
| `dmq` (`LocalMessageSubmissionOwnAnswer`) | #3231 (`SubmitMessage` returns its own answer; breaking; merge 1 of 12) | #3225 | open |
| `leios-peras` (`LeiosFetchRangeDelivery`; CONCURRENCY C8) | #3232 (a finished range's delivery stops when its caller leaves; merge 2 of 12) | #3226 | open |
| `pipeline-cbor` (`PipelineLifecycle`) | #3233 (`Stop(ctx)`, ApplyFunc may stop or drain, parent-cancel teardown; folds `fix/pipeline-callback-stop`, `fix/pipeline-cancel-cleanup`, `test/pipeline-lifecycle-model`; breaking; merge 3 of 12; #3161 first; main merged in at `5cb98604`, model `PipelineLifecycleMain*.cfg`) | #3227, #3228 | open |
| `connection` (`ConnectionTeardown`, `ConnectionCloseConcurrent`), `engine` (`EngineLifecycle`) | #3239 (teardown during Dial, late forwarder, Close before setup, protocol-loop join; merge 5 of 12; review at `f60a0213`: concurrent `CloseContext` mutual wait and conn left open with no muxer, fixed at `c321f708`, models `ConnectionCloseConcurrent*.cfg`, `ConnectionTeardownCloseOpenConnBug.cfg`) | #3236, #3237, #3238 | open |
| `connection` (`ConnectionTeardown`, Muxer.Stop join) | ouroboros-mock #370 (Stop and Close with either signature; released before merge 6) | ouroboros-mock #369 | open |
| `ledger-hash-cache` | #3234 (scoped-memo panic retried; folds `test/ledger-hash-cache-model`; merge 4 of 12) | #3229 | open |
| `connection` (`ConnectionTeardown`, `MuxerStop*`), `engine` (`EngineLifecycle`, `Ctx` RunLoop join) | #3253 (`fix/protocol-callback-context` `e49dd6a8`; `Stop(ctx) error` everywhere, `Close(ctx)`, `Muxer.Stop(ctx)` + `CallbackContext`, chainsync stop watcher joined; mock v0.21.4; breaking; merge 6 of 12) | #3187 | open |
| `blockfetch` (`BlockFetchBusyDelivery`) | #3254 (`fix/blockfetch-stop-callbacks-context` `be33b326`; Stop's callbacks unlocked, client goroutines joined; merge 7 of 12) | #3247 | open |
| `blockfetch` (`BlockFetchClientReader`; CONCURRENCY B4) | #3264 (`fix/blockfetch-client-protocol-race` `36aa9c31`; fetches read the instance under `protocolMu`; merge 8 of 12) | #3248 | open |
| `keepalive` (`KeepAliveLifecycle` reader: `KeepAliveLifecycleReader.cfg`, `KeepAliveLifecycleReaderUnlockedBug.cfg`) | #3272 (`fix/server-restart-protocol-race` `242cd282`; twelve restarting servers stop embedding the instance, including messagesubmission, localmessagesubmission, localmessagenotification, localtxsubmission, localtxmonitor and perasvotes; breaking; merge 9 of 12) | #3249 | open |
| `keepalive` (`KeepAliveLifecycle` reader); CONCURRENCY C9, C12, C20 | #3273 (`fix/leios-server-protocol-race` `250fecf8`; three leios servers; breaking; merge 10 of 12) | #3250 | open |
| `engine` (`EngineSendBeforeStart`; CONCURRENCY A9) | #3274 (`fix/protocol-send-before-start` `ffd6c838`; a message sent before `Start` is queued; merge 11 of 12) | #3251 | open |
| `leios-peras` (`PerasClientOpMu`; CONCURRENCY C13, C14, C15) | #3276 (`fix/perasvotes-op-lock-and-await-panic` `39f34f8a`; `Sync` honours callers' contexts, `VoteFunc` re-entry fails, await panics contained; merge 12 of 12) | #3252 | open |
| `ledger-rewards` | local branch `fix/ledger-rewards-reference` (`9675856a`, `bdba9c8b`, `203f3624`; reward pots and pool split as cardano-ledger; pledge owners as a set), not yet published | | local |
| `ledger-governance` | local branch `test/conway-gov-reference` (`7c2f2013`; ledger vectors replayed through gOuroboros rules alone, network-id and return-address tables), not yet published | | local |
| `ledger-rewards` (`RewardPots`) | #3275 (reward pots and pool split as cardano-ledger; pledge owners as a set; breaking: `DesiredPools` required) | #3255, #3256 | open |
| `ledger-block-overlay` (`GovOverlay`) | #3285 (in-block committee proposals count as potential members; governance sequence walk) | #3257 | open |
| `ledger-block-overlay` (`VerifyBlockIssuer`) | #3277 (VerifyBlock applies the TPraos overlay; breaking: `VerifyConfig.TPraosOverlay`) | #3258 | open |
| `ledger-codec` (`ProtVerWidth`; coverage gaps 2, 7, 8) | #3278 (32-bit protocol minor in updates) | #3259 | open |
| `cbor-codec` (L25-L28, L31), `ledger-codec` (`CostModelLanguages`, `PreConwaySetTag`); coverage gaps `cbor`, `ledger/common` | #3279 (bignum multiasset quantities), #3280 (Alonzo PlutusV2 cost model), #3282 (one tag 30), #3283 (constructor fields a list), #3284 (tag 258 set members in Value), #3289 (pre-Conway tag 258 refused), #3290 (ConstructorEncoder indefinite fields; datum bytes change) | #3260, #3261, #3263, #3265, #3266, #3270, #3271 | open |
| `ledger-codec` (`TxOutValueData`; script context gap 1) | #3281 (zero ada kept in output Plutus data; TxInfo translation goldens) | #3262 | open |
| `localstatequery` (`LocalStateQueryCodec`; goldens, gaps 9, 10) | #3286 (era filter set encoding), #3287 (GetAccountState in every Shelley era), #3288 (GetFuturePParams decoded) | #3267, #3268, #3269 | open |
| `dmq` (`MessageValidityBatch`, N55) | #3298 (every counter re-checked at commit; merge 1 of 6) | #3291 | open |
| `dmq` (`MessageValidity`, `MessageIngress`, N54) | #3299 (body 90 to 2000 bytes, refused at decode; merge 2 of 6) | #3292 | open |
| `dmq` (`MessageValidity`, N52) | #3300 (KES at the claimed period; current slot dropped; merge 3 of 6) | #3293 | open |
| `dmq` (`MessageValidity` `ExtrasBug`, N56) | #3301 (counters compared only with earlier messages; merge 4 of 6) | #3294 | open |
| `dmq` (`MessageIngress`, N56) | #3302 (60 s per-pool rate limit; merge 5 of 6) | #3295 | open |
| `dmq` (`MessageIngress`, N58) | #3303 (per-message receipt; merge 6 of 6; depends on #3130) | #3296 | open |
| `ledger-leios` (`LeiosVoting` aged key, L21) | #3304 (aged-out voting keys refused; breaking) | #3297 | open |
| `dmq` (`MessageValidity`) | #3317 (counter, stake and cold signature tests) | #3305 | open |
| `ledger-leios` (`LeiosVoting`) | #3318 (reference-formed certificates; depends on #3304) | #3306 | open |
| localstatequery goldens (gaps 9, 10) | #3319 (query and result goldens), #3320 (BuildHeader goldens) | #3307, #3308 | open |
| `blockfetch` (`OversizedRefusal`) | #3316 (`fix/blockfetch-oversized-refusal` `11eee787`; Oversized cells accept the muxer's ingress-overflow refusal; test-only) | #3315 | open |
| coverage gaps 2, 7, 8 | #3321 (fee, size, min coin goldens), #3322 (update keys per era) | #3309, #3310 | open |
| `ledger-governance` | #3323 (rules-only conformance replay, network-id and return-address tables) | #3311 | open |
| `ledger-conway-dijkstra` (`SubCerts`, `SubGov`, `SubGuards`) | #3324 (sub-transaction cells) | #3312 | open |
| coverage gaps `cbor`, `ledger/common` | #3325 (cbor reference; depends on #3284), #3326 (ledger/common reference; depends on #3279) | #3313, #3314 | open |
| `dmq` (`MempoolExpiry`, `MessageValidity`, N53) | #3331 (expiry bounds and `IsValidAt` as dmq-node) | #3327 | open |
| `dmq` (`MessagePayloadBytes`, N57) | #3332 (payload bytes hashed as received) | #3328 | open |
| `ledger-leios` (`LeiosVoteShape`, L22) | #3333 (CIP-0164 vote shape; breaking) | #3329 | open |
| `consensus-nonce` (`EpochNonce`, GoBytes "Family") | #3334 (epoch nonce over whole chains) | #3330 | open |

## Merges 6 to 12 of 12 published (2026-11-24)

All seven are in the table above (#3253, #3254, #3264, #3272, #3273, #3274,
#3276), base `main`, each including its predecessors' commits. Before
publishing, merge 9 was extended to the six servers main had made restartable
(messagesubmission, localmessagesubmission, localmessagenotification,
localtxsubmission, localtxmonitor, perasvotes), and `KeepAliveLifecycle`
gained the reader that models the race it fixes.

## Not yet attributed

#3082 (null native script child lists), #3083 (MaxKesEvolutions before apply)
and #3084 (Byron PBFT certificate signature) merged as the modelling began.
Check whether a model drove them before listing them above.
