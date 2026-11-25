--------------------------- MODULE ChainSyncLimits ---------------------------
(***************************************************************************)
(* The node-to-node chain-sync size limit and timeout of each state, as a  *)
(* table: gOuroboros's state map against the specification and the         *)
(* reference.                                                              *)
(*                                                                         *)
(* An input is one state, the size of one message received in it, and the *)
(* timeout gOuroboros draws for it. The size is one of a few points that   *)
(* sit on each side of the two limits involved (65535 and 462000); every   *)
(* size between two points gets the same verdict, so the points stand for  *)
(* all sizes.                                                              *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex*)
(*        910-924 "Node-to-node size limits per state" (chain-sync): every *)
(*        state 65535; 940-950 "Node-to-node timeouts per state": StIdle   *)
(*        3673 s, StCanAwait 10 s, StIntersect 10 s, StMustReply random    *)
(*        between 601 s and 911 s.                                         *)
(*   [R1] ouroboros-network 5f356486ab3e .../Protocol/ChainSync/Codec.hs   *)
(*        43-49 byteLimitsChainSync (smallByteLimit in every state),       *)
(*        54-63 minChainSyncTimeout 601, maxChainSyncTimeout 911;          *)
(*        .../Network/Protocol/Limits.hs 110-111 smallByteLimit = 65535.   *)
(*                                                                         *)
(* gOuroboros protocol/chainsync/chainsync.go StateMapNtN:                 *)
(*   [G1] main before #3112 (d0b95845, lines 116-146, 233, 251-252):       *)
(*        PendingMessageByteLimit MaxPendingMessageBytes (462000) in every *)
(*        state; MustReplyTimeoutMin 135 s, MustReplyTimeoutMax 269 s,     *)
(*        drawn in [Min, Max).                                             *)
(*   [G2] #3112 (4217b6d7): SmallMaxPendingMessageBytes 65535 as each      *)
(*        state's message limit (462000 kept as the pending-receive        *)
(*        budget, not a per-message limit); MustReply 601 s to 911 s,      *)
(*        drawn in [Min, Max).                                             *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    GoRule  \* "main" [G1] or "fix" [G2]

VARIABLE input  \* the one input this behaviour checks: [state, size, draw]

\* In English: "The node-to-node states in which a message can arrive."
\* Literally: "States is defined as the set containing "Idle", "CanAwait",
\*   "Intersect" and "MustReply"."
States == {"Idle", "CanAwait", "Intersect", "MustReply"}

\* In English: "One size on each side of each limit."
\* Literally: "Sizes is defined as the set containing 1, 65535, 65536,
\*   462000 and 462001."
Sizes == {1, 65535, 65536, 462000, 462001}

\* In English: "The reference's message size limit: 65535 bytes in every
\*   state." [S1][R1]
\* Literally: "RefSizeLimit of s is defined as 65535."
RefSizeLimit(s) == 65535

\* In English: "The timeouts the reference may pick in state s: one fixed
\*   value, or for MustReply any whole second from 601 to 911." [S1][R1]
\* Literally: "RefTimeouts of s is defined as: if s equals "Idle" then the
\*   set containing 3673, else if s equals "MustReply" then the integers
\*   from 601 to 911, else the set containing 10."
RefTimeouts(s) ==
    IF s = "Idle" THEN {3673}
    ELSE IF s = "MustReply" THEN 601..911
    ELSE {10}

\* In English: "gOuroboros's message size limit in each state: 462000 on
\*   main, 65535 with the fix." [G1][G2]
\* Literally: "GoSizeLimit of s is defined as: if GoRule equals "main"
\*   then 462000, else 65535."
GoSizeLimit(s) == IF GoRule = "main" THEN 462000 ELSE 65535

\* In English: "The timeouts gOuroboros may draw in state s: MustReply is
\*   drawn from [135, 269) on main and [601, 911) with the fix; the other
\*   states are fixed and already match." [G1][G2]
\* Literally: "GoTimeouts of s is defined as: if s equals "MustReply" then
\*   (if GoRule equals "main" then the integers from 135 to 268, else the
\*   integers from 601 to 910), else RefTimeouts of s."
GoTimeouts(s) ==
    IF s = "MustReply"
    THEN IF GoRule = "main" THEN 135..268 ELSE 601..910
    ELSE RefTimeouts(s)

\* In English: "Every state, every size, and every timeout gOuroboros may
\*   draw in that state."
\* Literally: "Inputs is defined as the union, over every s in States, of
\*   the set of records whose state is s, whose size is a member of Sizes,
\*   and whose draw is a member of GoTimeouts of s."
Inputs == UNION {[state : {s}, size : Sizes, draw : GoTimeouts(s)] : s \in States}

\* In English: "Pick any one input; nothing changes after that."
\* Literally: "Init is defined as: input is a member of Inputs."
Init == input \in Inputs

\* In English: "A table has no steps: the input stays as it is."
\* Literally: "Next is defined as: input is unchanged."
Next == UNCHANGED input

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or input
\*   stays the same."
Spec == Init /\ [][Next]_input

\* In English: "gOuroboros accepts a message exactly when it fits the
\*   reference's byteLimitsChainSync."
\* Literally: "SizeAsByteLimitsChainSync is defined as: the size of input
\*   is at most GoSizeLimit of its state if and only if the size of input
\*   is at most RefSizeLimit of its state."
SizeAsByteLimitsChainSync ==
    (input.size <= GoSizeLimit(input.state))
        <=> (input.size <= RefSizeLimit(input.state))

\* In English: "Every timeout gOuroboros draws is one the reference's
\*   timeLimitsChainSync could draw, so gOuroboros never drops a peer
\*   sooner than the reference would."
\* Literally: "TimeoutAsTimeLimitsChainSync is defined as: the draw of
\*   input is a member of RefTimeouts of the state of input."
TimeoutAsTimeLimitsChainSync == input.draw \in RefTimeouts(input.state)
=============================================================================
