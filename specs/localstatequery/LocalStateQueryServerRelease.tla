------------------------ MODULE LocalStateQueryServerRelease ------------------------
(***************************************************************************)
(* Which client messages a local-state-query server accepts when the       *)
(* application gave it no callback for them, as a table: gOuroboros's     *)
(* server against the specification and the reference.                    *)
(*                                                                         *)
(* An input is one client message, legal in the state it arrives in, and  *)
(* whether the callback that message calls was configured.                 *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex*)
(*        2000-2010 local-state-query transition table: StAcquired         *)
(*        MsgRelease -> StIdle, with no reply.                             *)
(*   [R1] ouroboros-network 5f356486ab3e .../Protocol/LocalStateQuery/     *)
(*        Type.hs (MsgRelease carries nothing and has no answer) and       *)
(*        Server.hs (the server's release continuation returns it to       *)
(*        idle; there is nothing to refuse).                               *)
(*   Library contract (not a reference rule): MsgAcquire, MsgReAcquire and *)
(*   MsgQuery need an answer, and gOuroboros gets every answer from the    *)
(*   application's callback, so without one it cannot answer and refuses. *)
(*                                                                         *)
(* gOuroboros protocol/localstatequery/server.go:                          *)
(*   [G1] main before #3113 (d0b95845, handleRelease 345-351): every       *)
(*        handler returns an error when its callback is nil, ReleaseFunc   *)
(*        included, which tears down the connection.                       *)
(*   [G2] #3113 (5c4f31c1, handleRelease 386-390): MsgRelease without a    *)
(*        ReleaseFunc is accepted; the others are unchanged.               *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    GoRule  \* "main" [G1] or "fix" [G2]

VARIABLE input  \* the one input this behaviour checks: [msg, hasCallback]

\* In English: "The client messages the server receives."
\* Literally: "Messages is defined as the set containing "Acquire",
\*   "ReAcquire", "Query" and "Release"."
Messages == {"Acquire", "ReAcquire", "Query", "Release"}

\* In English: "Every message, with its callback configured or not."
\* Literally: "Inputs is defined as the set of records whose msg is a member
\*   of Messages and whose hasCallback is a member of BOOLEAN."
Inputs == [msg : Messages, hasCallback : BOOLEAN]

\* In English: "The reference accepts MsgRelease always [S1][R1]; a message
\*   that needs an answer is accepted only if something can answer it
\*   (the library contract)."
\* Literally: "RefAccepts of i is defined as: the msg of i equals "Release",
\*   or the hasCallback of i."
RefAccepts(i) == i.msg = "Release" \/ i.hasCallback

\* In English: "main refuses any message whose callback is missing [G1];
\*   the fix also accepts MsgRelease without one [G2]."
\* Literally: "GoAccepts of i is defined as: the hasCallback of i, or
\*   GoRule equals "fix" and the msg of i equals "Release"."
GoAccepts(i) == i.hasCallback \/ (GoRule = "fix" /\ i.msg = "Release")

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

\* In English: "gOuroboros's server accepts exactly the messages the
\*   reference accepts: MsgRelease always, StAcquired -> StIdle."
\* Literally: "ReleaseAcceptedAsStAcquired is defined as: GoAccepts of input
\*   if and only if RefAccepts of input."
ReleaseAcceptedAsStAcquired == GoAccepts(input) <=> RefAccepts(input)
=============================================================================
