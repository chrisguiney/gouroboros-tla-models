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
| `engine` | #3159 (time only the receiver; no default node-to-client timeouts) | #3145, #3146 | open |
| `connection` (`ConnectionTeardown`) | local branches `fix/connection-close-during-dial` (`2ed2f1f3`), `fix/connection-late-forwarder` (`264dc5be`), not yet published | | local |
| `engine` (`EngineLifecycle`) | local branch `test/protocol-lifecycle` (`c5ab084c`), not yet published | | local |
| `chainsync` | #3092 (close the connection when Stop cannot send MsgDone) | #3091 | merged |
| `chainsync` | #3094 (GetCurrentTip waits for its own answer) | #3093 | open |
| `chainsync` | #3112 (MustReply timeout, node-to-node message size, state map tests) | #3096, #3097, #3101 | open |
| `handshake` | #3127 (negotiate before a query reply, simultaneous open, state map tests) | #3115, #3116, #3117 | open |
| `handshake` | #3194 (negotiated data in the accept, recognised key order) | #3181, #3182 | open |
| `blockfetch` | #3114 (Stop, refused requests, Busy timeout, state map tests) | #3107, #3108, #3109, #3110 | open |
| `txsubmission` | #3128 (txid request blocking rules, state map tests) | #3118, #3119, #3120 | open |
| `txsubmission` | #3195 (clamp over-window requests from V16) | #3183 | open |
| `peersharing` | #3133 (WithTimeout doc, state map tests) | #3131, #3132 | open |
| `localtx` | #3140 (no default submit timeout; Stop never waits on a submit) | #3134, #3135 | open |
| `localtx` | #3154 (re-acquire untimed; Stop never waits on the peer) | #3143, #3144 | open |
| `localtx` | #3196 (get-measures, opt-in await on await-acquire) | #3184, #3185 | open |
| `localtx`, `dmq`, `leios-peras` | #3197 (six servers restart after done) | #3186 | open |
| `localstatequery` | #3113 (acquire, release, restart, implicit acquire, state map tests) | #3098, #3102, #3103, #3104, #3105, #3106 | open |
| `dmq` | #3130 (interoperate with dmq-node, repeat requests, state map tests) | #3121, #3122, #3123 | open |
| `dmq` | #3142 (empty blocking replies, lost wakeup) | #3137, #3138, #3139 | merged |
| `leios-peras` | #3160 (quit, cancel, pipelined vote requests, state map tests) | #3150, #3151, #3152, #3153 | open |
| `leios-peras` | #3165 (await, server idle, timeouts) | #3162, #3163, #3164 | merged |
| `consensus` | #3111 (header envelope, first header after Origin) | #3095, #3099, #3100 | open |
| `ledger-shelley` | #3129 (epoch-aware pool registration) | #3124, #3125, #3126 | open |
| `ledger-governance` | #3155 (nil voter, governance lookup contract) | #3147, #3148, #3149 | open |
| `ledger-governance` | ouroboros-mock #368 (governance action expiry at the last slot) | ouroboros-mock #367 | approved |
| `pipeline-cbor` | #3161 (drain after the apply runner, lossless Results) | #3156, #3157, #3158 | open |
| `pipeline-cbor` | #3141 (transaction body id without stored CBOR) | #3136 | open |
| `ledger-utxo` | #3193 (BadInputs covers collateral and reference inputs) | #3179, #3180 | open |
| `consensus-genesis` | #3173 (exact window count, density table tests) | #3169, #3170 | open |
| `ledger-byron` | #3174 (empty transactions, heavyweight delegation activation) | #3171, #3172 | open |
| `ledger-leios` | #3192 (committee smaller than the parameter) | #3177, #3178 | open |
| `consensus-nonce` | reviewed and approved jtranq's #3053 (rolling nonce derivation; it reproduced the model's 15 mainnet vectors) | #3052 | merged |
| `consensus-eras` | #3201 (header check order, KES before the opcert start, TPraos overlay and envelope inputs) | #3198, #3199, #3200 | open |
| `consensus-eras` | #3205 (empty era history, Byron slot-to-epoch, era table tests) | #3202, #3203, #3204 | open |
| `ledger-bbody` | #3208 (Conway header protocol-version check, block body table tests) | #3206, #3207 | open |
| `ledger-witnesses` | #3211 (bootstrap witnesses in the genesis-delegate quorum, witness table tests) | #3209, #3210 | open |
| `ledger-ppup-mir` | #3216 (empty update, phase-2-invalid update and MIR quorum, table tests) | #3212, #3213, #3214, #3215 | open |
| `ledger-conway-dijkstra` | #3218 (table tests) | #3217 | open |
| `consensus-tachys` | #3220 (table tests against CIP-0177) | #3219 | open |
| `consensus-nonce` | #3223 (neutral epoch nonce and VRF input, as new functions) | #3221, #3222 | open |

## Not yet attributed

#3082 (null native script child lists), #3083 (MaxKesEvolutions before apply)
and #3084 (Byron PBFT certificate signature) merged as the modelling began.
Check whether a model drove them before listing them above.
