-------------------------- MODULE TxSubmissionTable --------------------------
(***************************************************************************)
(* The tx-submission receive table: for every role, state, and kind of     *)
(* message from the peer, what the receiver does. It covers what           *)
(* TxSubmission.tla leaves out: messages sent in a state that does not     *)
(* expect them. The gOuroboros test                                        *)
(* protocol/txsubmission/statemap_model_test.go holds the same rows.       *)
(*                                                                         *)
(* Sources (IntersectMBO/ouroboros-network 5f356486ab3e; see README.md):   *)
(*   [S1] miniprotocols.tex 27-36: an unexpected message aborts the        *)
(*        connection.                                                      *)
(*   [S2] miniprotocols.tex 1285-1322, 1420-1432: states, agency,          *)
(*        transitions.                                                     *)
(*   [R1] TxSubmission2/Type.hs 196-317: the same transitions; StDone has  *)
(*        NobodyAgency.                                                    *)
(*   [R2] TxSubmission2/Codec.hs 392-456: a message is decoded against the *)
(*        reader's state, and fails if that state has no such message.     *)
(*   [R7] IntersectMBO/typed-protocols, Network/TypedProtocol/Driver.hs:   *)
(*        a side reads only when its peer has agency, so a message sent    *)
(*        early waits; this is how the reference client takes the         *)
(*        server's pipelined requests (cited as in Model 01, [S8] there).  *)
(*   [R8] connection-manager.tex 489-503 (Model 01's [S7]): a responder    *)
(*        that terminates cleanly is restarted in its initial state.       *)
(*                                                                         *)
(* ASSUME states a fact about constants; TLC evaluates it before checking  *)
(* anything. PrintT prints its argument and is always TRUE, so the ASSUME  *)
(* at the bottom exists only to print.                                     *)
(***************************************************************************)
EXTENDS TLC

\* Literally: "Roles is defined as the set containing "Client" and "Server"."
Roles  == {"Client", "Server"}
\* Literally: "States is defined as the set containing "StInit", "StIdle",
\*   "StTxIdsBlocking", "StTxIdsNonBlocking", "StTxs" and "StDone"."
States == {"StInit", "StIdle", "StTxIdsBlocking", "StTxIdsNonBlocking",
           "StTxs", "StDone"}
\* Literally: "Kinds is defined as the set containing "MsgInit",
\*   "MsgRequestTxIdsBlocking", "MsgRequestTxIdsNonBlocking", "MsgReplyTxIds",
\*   "MsgRequestTxs", "MsgReplyTxs" and "MsgDone"."
Kinds  == {"MsgInit", "MsgRequestTxIdsBlocking", "MsgRequestTxIdsNonBlocking",
           "MsgReplyTxIds", "MsgRequestTxs", "MsgReplyTxs", "MsgDone"}

\* In English: "Who may send in each state [S2]: the client in StInit and
\* while answering, the server in StIdle, nobody in StDone [R1]."
\* Literally: "Agency of s is defined as: in the case s equals "StIdle",
\*   "Server"; in the case s equals "StDone", "Nobody"; in every other case,
\*   "Client"."
Agency(s) ==
    CASE s = "StIdle" -> "Server"
      [] s = "StDone" -> "Nobody"
      [] OTHER        -> "Client"

\* In English: "The state message k leads to from state s, or "none" if s
\* has no such transition [S2][R1]."
\* Literally: "Step of s and k is defined as: in the case s equals "StInit" and
\*   k equals "MsgInit", "StIdle"; in the case s equals "StIdle" and k equals
\*   "MsgRequestTxIdsBlocking", "StTxIdsBlocking"; in the case s equals
\*   "StIdle" and k equals "MsgRequestTxIdsNonBlocking", "StTxIdsNonBlocking";
\*   in the case s equals "StIdle" and k equals "MsgRequestTxs", "StTxs"; in
\*   the case s equals "StTxIdsBlocking" and k equals "MsgReplyTxIds",
\*   "StIdle"; in the case s equals "StTxIdsBlocking" and k equals "MsgDone",
\*   "StDone"; in the case s equals "StTxIdsNonBlocking" and k equals
\*   "MsgReplyTxIds", "StIdle"; in the case s equals "StTxs" and k equals
\*   "MsgReplyTxs", "StIdle"; in every other case, "none"."
Step(s, k) ==
    CASE s = "StInit" /\ k = "MsgInit"                        -> "StIdle"
      [] s = "StIdle" /\ k = "MsgRequestTxIdsBlocking"        -> "StTxIdsBlocking"
      [] s = "StIdle" /\ k = "MsgRequestTxIdsNonBlocking"     -> "StTxIdsNonBlocking"
      [] s = "StIdle" /\ k = "MsgRequestTxs"                  -> "StTxs"
      [] s = "StTxIdsBlocking" /\ k = "MsgReplyTxIds"         -> "StIdle"
      [] s = "StTxIdsBlocking" /\ k = "MsgDone"               -> "StDone"
      [] s = "StTxIdsNonBlocking" /\ k = "MsgReplyTxIds"      -> "StIdle"
      [] s = "StTxs" /\ k = "MsgReplyTxs"                     -> "StIdle"
      [] OTHER                                                -> "none"

\* In English: "The peer of the client is the server, and vice versa."
\* Literally: "Other of r is defined as: if r equals "Client" then "Server",
\*   else "Client"."
Other(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "What receiver r does with message k from its peer while in
\* state s:
\*   - after MsgDone the server's next run judges it from StInit [R8], and
\*     the client, whose run is over, leaves it unread ("Held");
\*   - if r itself has agency, it does not read the message yet ("Waits")
\*     [R7];
\*   - if the peer has agency and s has a transition for k, r moves to the
\*     new state; otherwise r aborts the connection ("Violation") [S1][R2]."
\* Literally: "ReceiveTable of r, s and k is defined (recursively) as: in the
\*   case s equals "StDone" and r equals "Server", ReceiveTable of r, "StInit"
\*   and k; in the case s equals "StDone", "Held"; in the case Agency of s
\*   equals r, "Waits"; in the case Step of s and k does not equal "none", Step
\*   of s and k; in every other case, "Violation"."
RECURSIVE ReceiveTable(_, _, _)
ReceiveTable(r, s, k) ==
    CASE s = "StDone" /\ r = "Server" -> ReceiveTable(r, "StInit", k)
      [] s = "StDone"                 -> "Held"
      [] Agency(s) = r                -> "Waits"
      [] Step(s, k) /= "none"         -> Step(s, k)
      [] OTHER                        -> "Violation"

\* A one-state behaviour, so TLC has something to run; the table is the
\* point.
VARIABLE x
\* Literally: "Spec is defined as: x equals 0, and always, every step is a step
\*   in which x in the next state equals x, or a step that leaves x unchanged."
Spec == x = 0 /\ [][x' = x]_x

\* In English: "For every role, state and kind, print the four of them."
\* Literally: "Assume that for all r in Roles, s in States and k in Kinds,
\*   PrintT of the tuple of r, s, k and ReceiveTable of r, s and k."
ASSUME \A r \in Roles, s \in States, k \in Kinds :
         PrintT(<<r, s, k, ReceiveTable(r, s, k)>>)
=============================================================================
