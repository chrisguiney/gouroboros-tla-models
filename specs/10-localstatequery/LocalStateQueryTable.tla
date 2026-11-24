------------------------ MODULE LocalStateQueryTable ------------------------
(***************************************************************************)
(* Prints the receive rule from LocalStateQuery.tla as a table: for every  *)
(* role, state, and wire message kind, what the receiver must do. The      *)
(* gOuroboros test protocol/localstatequery/statemap_model_test.go holds   *)
(* the same rows. ASSUME with PrintT exists only to print (see             *)
(* specs/01-keepalive/KeepAliveTable.tla).                                 *)
(***************************************************************************)
EXTENDS LocalStateQuery, TLC

\* In English: "For every role r, state s and kind k, print the four of
\* them: role, state, kind, and what the receiver does."
ASSUME \A r \in Roles, s \in States, k \in Kinds :
         PrintT(<<r, s, k, ReceiveTable(r, s, k)>>)
=============================================================================
