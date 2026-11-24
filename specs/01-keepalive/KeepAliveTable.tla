--------------------------- MODULE KeepAliveTable ---------------------------
(***************************************************************************)
(* Prints the receive rule from KeepAlive.tla as a table: for every role,  *)
(* state, and incoming message, what the receiver must do. The gOuroboros  *)
(* test protocol/keepalive/statemap_model_test.go holds the same rows.     *)
(*                                                                         *)
(* ASSUME states a fact about constants; TLC evaluates it before checking  *)
(* anything. PrintT prints its argument and is always TRUE, so this ASSUME *)
(* exists only to print.                                                   *)
(***************************************************************************)
EXTENDS KeepAlive, TLC  \* everything in KeepAlive.tla, plus PrintT from TLC

\* In English: "For every role r, every state s, and every kind of message
\* k, print the four of them: role, state, kind, and what the receiver does."
\* \A x \in S : P reads "for all x in S, P is true".
\* Literally: "Assume that for all r in Roles, s in States and k in Kinds,
\*   PrintT of the tuple of r, s, k and ReceiveTable of r, s and k."
ASSUME \A r \in Roles, s \in States, k \in Kinds :
         PrintT(<<r, s, k, ReceiveTable(r, s, k)>>)
=============================================================================
