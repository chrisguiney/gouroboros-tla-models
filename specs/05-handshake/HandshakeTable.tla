--------------------------- MODULE HandshakeTable ---------------------------
(***************************************************************************)
(* Prints the receive rule of Handshake.tla as a table: for every role,    *)
(* state, and kind of message, what the receiver does. The gOuroboros test *)
(* protocol/handshake/statemap_model_test.go holds the same rows.          *)
(*                                                                         *)
(* ASSUME states a fact about constants and is checked before anything     *)
(* else. PrintT prints its argument and is always TRUE, so this ASSUME     *)
(* exists only to print.                                                   *)
(***************************************************************************)
EXTENDS Handshake, TLC

\* In English: "For every role r, state s, and kind k, print the four of
\* them: role, state, kind, and what the receiver does."
ASSUME \A r \in Roles, s \in States, k \in Kinds :
         PrintT(<<r, s, k, ReceiveTable(r, s, k)>>)
=============================================================================
