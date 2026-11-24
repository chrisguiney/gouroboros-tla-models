-------------------------- MODULE HandshakeSimOpen --------------------------
(***************************************************************************)
(* Simultaneous TCP open: both sides dial each other at once, so both run  *)
(* the handshake CLIENT. Each sends MsgProposeVersions and moves to        *)
(* StConfirm; each then reads the other's MsgProposeVersions in StConfirm, *)
(* where it decodes as MsgReplyVersions, and picks the version itself.     *)
(*                                                                         *)
(* Sources (see Handshake.tla and the README):                             *)
(*   [S2] miniprotocols.tex 479-484: MsgReplyVersions is MsgProposeVersions *)
(*        read in StConfirm.                                               *)
(*   [S6] miniprotocols.tex 704-759: both sides choose the highest         *)
(*        version; a side that does not accept may reset the connection;   *)
(*        both end in the same state.                                      *)
(*   [R1] Type.hs 98-105, 145-153: MsgReplyVersions; a refusing side       *)
(*        closes the connection without sending a reason.                  *)
(*   [R2] Client.hs 119-130: on MsgReplyVersions the client runs           *)
(*        acceptOrRefuse itself.                                           *)
(*   [R8] network-mux/src/Network/Mux/Types.hs 320-344: bearerAsChannel,  *)
(*        which carries the handshake, reads any segment regardless of its *)
(*        direction bit, so the peer's proposal reaches the client.        *)
(*                                                                         *)
(* gOuroboros: protocol/handshake/handshake.go has no StConfirm transition *)
(* for MsgProposeVersions, and muxer/muxer.go (readLoop) routes a segment  *)
(* by its direction bit, so a peer's proposal, sent as an initiator, goes  *)
(* to the handshake server role, which a dialling connection does not run. *)
(* HandleReplyVersions = FALSE models either refusal as a violation.       *)
(*                                                                         *)
(* The labels "Client" and "Server" from Handshake.tla are kept as names   *)
(* for the two sides; here both behave as clients.                         *)
(***************************************************************************)
EXTENDS Handshake

CONSTANT AsymmetricDecode   \* TRUE: a side's data may be undecodable by the other

\* Both sides' data never asks for a query. With AsymmetricDecode the `ok`
\* flag varies: one side may send data the other cannot decode.
SimParams == {p \in Params : ~p.query /\ (AsymmetricDecode \/ p.ok)}
SimTables == Tables(SimParams) \ {<<>>}

\* In English: "Both sides start in StPropose with any non-empty tables."
SimInit ==
    /\ view = [r \in Roles |-> "StPropose"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ table \in [Roles -> SimTables]
    /\ result = [r \in Roles |-> NoResult]
    /\ heard = <<>>
    /\ rogueLeft = 0

\* In English: "Side r in StPropose sends its table to its peer and moves
\* to StConfirm."
SimPropose(r) ==
    /\ view[r] = "StPropose"
    /\ view' = [view EXCEPT ![r] = "StConfirm"]
    /\ inbox' = [inbox EXCEPT ![Peer(r)] =
                   Append(@, Msg("MsgProposeVersions", table[r], 0, NoParams, "None", FALSE))]
    /\ UNCHANGED <<table, result, heard, rogueLeft>>

\* In English: "Side r in StConfirm reads the peer's proposal. If it is not
\* legal there (gOuroboros), r hangs up. Otherwise r is done, with the
\* result of negotiating its own table against the peer's [R2]."
SimRecv(r) ==
    /\ view[r] = "StConfirm"
    /\ inbox[r] /= <<>>
    /\ LET m == Head(inbox[r]) IN
       IF ~IsLegal("StConfirm", m.type)
       THEN /\ view' = [view EXCEPT ![r] = "Violation"]
            /\ UNCHANGED result
       ELSE /\ view' = [view EXCEPT ![r] = "StDone"]
            /\ result' = [result EXCEPT ![r] = ClientJudge(table[r], m)]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<table, heard, rogueLeft>>

SimNext ==
    \/ \E r \in Roles : SimPropose(r) \/ SimRecv(r)
    \/ Ended /\ UNCHANGED vars

SimSpec == SimInit /\ [][SimNext]_vars

-----------------------------------------------------------------------------

SimTypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ table \in [Roles -> SimTables]
    /\ result \in [Roles -> [kind : {"None", "Accept", "Refuse", "Query", "Error"},
                             v : Versions \cup {0}, reason : Reasons]]

\* In English: "When both sides are done, both accepted the same version or
\* both refused [S6]. A side that refuses closes the connection [R1], so a
\* lone refusal is safe only if the other side refused too or never
\* starts on the connection; this checks the stronger, symmetric claim."
SymmetricOutcome ==
    (\A r \in Roles : view[r] = "StDone") =>
        \/ /\ \A r \in Roles : result[r].kind = "Accept"
           /\ result["Client"].v = result["Server"].v
        \/ \A r \in Roles : result[r].kind = "Refuse"

\* In English: "A side that accepted v chose the highest version in both
\* tables [S6]."
SimAcceptsHighest ==
    \A r \in Roles :
        result[r].kind = "Accept" =>
            result[r].v = Max(DOMAIN table["Client"] \cap DOMAIN table["Server"])

\* In English: "With nothing in flight, both sides are in the same state
\* [S6 747-755]."
SameStateWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>>) => view["Client"] = view["Server"]
=============================================================================
