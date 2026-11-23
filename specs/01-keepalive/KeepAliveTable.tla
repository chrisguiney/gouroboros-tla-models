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
EXTENDS KeepAlive, TLC

ASSUME \A r \in Roles, s \in States, k \in Kinds :
         PrintT(<<r, s, k, ReceiveTable(r, s, k)>>)
=============================================================================
