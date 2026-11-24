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
(* gOuroboros at 61046085: protocol/handshake/handshake.go has no         *)
(* StConfirm transition for MsgProposeVersions, and muxer/muxer.go         *)
(* (readLoop) routes a segment by its direction bit, so a peer's proposal, *)
(* sent as an initiator, goes to the handshake server role, which a        *)
(* dialling connection does not run. HandleReplyVersions = FALSE models    *)
(* either refusal as a violation.                                          *)
(*                                                                         *)
(* gOuroboros on branch fix/handshake-simultaneous-open: the muxer gives   *)
(* a handshake segment to whichever role is registered before Start, the   *)
(* client takes MsgProposeVersions in StConfirm, and Client.Start returns  *)
(* only once its own proposal has moved it to StConfirm                    *)
(* (protocol.Protocol.WaitForStateExit). Without that wait the connection  *)
(* starts reading while the client may still be in StPropose, where it     *)
(* holds agency and protocol.Protocol rejects any message on arrival.      *)
(* ReadsBeforeProposing = TRUE models that early read.                     *)
(*                                                                         *)
(* The labels "Client" and "Server" from Handshake.tla are kept as names   *)
(* for the two sides; here both behave as clients.                         *)
(***************************************************************************)
EXTENDS Handshake

CONSTANT AsymmetricDecode   \* TRUE: a side's data may be undecodable by the other
CONSTANT ReadsBeforeProposing \* TRUE: a side may read the peer's message while still in StPropose

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
    /\ view[r] = "StPropose"                         \* r has not proposed yet
    /\ view' = [view EXCEPT ![r] = "StConfirm"]      \* r now waits for an answer
    /\ inbox' = [inbox EXCEPT ![Peer(r)] =           \* the peer receives r's table
                   Append(@, Msg("MsgProposeVersions", table[r], 0, NoParams, "None", FALSE))]
    /\ UNCHANGED <<table, result, heard, rogueLeft>> \* nothing else changes

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

\* In English: "If reading can start before a side's own proposal has moved
\* it to StConfirm, side r in StPropose may read the peer's proposal. r
\* holds agency there, so the message is illegal and r hangs up." The
\* reference never does this: its client yields MsgProposeVersions before
\* it awaits anything [R2].
SimRecvEarly(r) ==
    /\ ReadsBeforeProposing                          \* only the early-reading variant
    /\ view[r] = "StPropose"                         \* r has not proposed yet
    /\ inbox[r] /= <<>>                              \* the peer's proposal has arrived
    /\ view' = [view EXCEPT ![r] = "Violation"]      \* r rejects it and hangs up
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]        \* the message is consumed
    /\ UNCHANGED <<table, result, heard, rogueLeft>> \* nothing else changes

SimNext ==
    \/ \E r \in Roles : SimPropose(r) \/ SimRecv(r) \/ SimRecvEarly(r)
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
