--------------------------- MODULE BlockFetchLimits ---------------------------
(***************************************************************************)
(* How long a block-fetch client waits in StBusy and StStreaming before    *)
(* dropping the server, as a table: gOuroboros's defaults against the      *)
(* specification and the reference.                                        *)
(*                                                                         *)
(* An input is one state and the whole seconds an honest server takes to  *)
(* send its next message there. The peer is dropped if that is longer than *)
(* the state's timeout.                                                    *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex*)
(*        1235-1237 block-fetch "Timeouts per state": StBusy 60 s,         *)
(*        StStreaming 60 s.                                                *)
(*   [R1] ouroboros-network 5f356486ab3e .../Protocol/BlockFetch/Codec.hs  *)
(*        54 timeLimitsBlockFetch (longWait in StBusy and StStreaming);    *)
(*        .../Network/Protocol/Limits.hs 116-117 longWait = Just 60.       *)
(*                                                                         *)
(* gOuroboros protocol/blockfetch/blockfetch.go. The state map has         *)
(* BusyTimeout and StreamingTimeout, but NewConfig's BatchStartTimeout and *)
(* BlockTimeout replace them in both client and server, so the effective   *)
(* timeout is NewConfig's default:                                         *)
(*   [G1] main before #3114 (d0b95845 line 282): BatchStartTimeout 5 s,    *)
(*        BlockTimeout 60 s.                                               *)
(*   [G2] #3114 (5a2a11c3 lines 229, 234, 287-288): BatchStartTimeout =    *)
(*        BusyTimeout = 60 s, BlockTimeout = StreamingTimeout = 60 s.      *)
(* A caller may still set either through an option; Dingo sets 60 s. This *)
(* model checks the defaults.                                              *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    GoRule,    \* "main" [G1] or "fix" [G2]
    MaxWait    \* the longest reply time checked, in seconds, e.g. 61

VARIABLE input  \* the one input this behaviour checks: [state, wait]

\* In English: "The server-agency states with a timeout."
\* Literally: "States is defined as the set containing "Busy" and
\*   "Streaming"."
States == {"Busy", "Streaming"}

\* In English: "The reference waits 60 seconds in both states." [S1][R1]
\* Literally: "RefTimeout of s is defined as 60."
RefTimeout(s) == 60

\* In English: "gOuroboros's effective timeout is NewConfig's default:
\*   StBusy 5 s on main and 60 s with the fix, StStreaming 60 s on both."
\*   [G1][G2]
\* Literally: "GoTimeout of s is defined as: if s equals "Busy" and GoRule
\*   equals "main" then 5, else 60."
GoTimeout(s) == IF s = "Busy" /\ GoRule = "main" THEN 5 ELSE 60

\* In English: "Every state with every reply time up to MaxWait."
\* Literally: "Inputs is defined as the set of records whose state is a
\*   member of States and whose wait is a member of 0 to MaxWait."
Inputs == [state : States, wait : 0..MaxWait]

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

\* In English: "gOuroboros drops the server exactly when the reference's
\*   timeLimitsBlockFetch would."
\* Literally: "DropsAsTimeLimitsBlockFetch is defined as: the wait of input
\*   is greater than GoTimeout of its state if and only if the wait of input
\*   is greater than RefTimeout of its state."
DropsAsTimeLimitsBlockFetch ==
    (input.wait > GoTimeout(input.state))
        <=> (input.wait > RefTimeout(input.state))
=============================================================================
