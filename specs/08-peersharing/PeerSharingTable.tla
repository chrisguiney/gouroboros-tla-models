-------------------------- MODULE PeerSharingTable --------------------------
(***************************************************************************)
(* Prints the receive rule of PeerSharing.tla as a table: for every role,  *)
(* state, and kind of incoming message, what the receiver must do. The     *)
(* gOuroboros test protocol/peersharing/statemap_model_test.go holds the   *)
(* same 30 rows. ASSUME and PrintT are explained in KeepAliveTable.tla.    *)
(***************************************************************************)
EXTENDS PeerSharing, TLC

\* In English: "For every role r, state s, and kind k, print the four of
\* them: role, state, kind, and what the receiver does."
ASSUME \A r \in Roles, s \in States, k \in Kinds :
         PrintT(<<r, s, k, ReceiveTable(r, s, k)>>)
=============================================================================
