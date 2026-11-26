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
(* The version data a side ends with is what its connection derives the   *)
(* diffusion mode from. The reference returns the agreed data,             *)
(* acceptVersion vData vData' (Client.hs 201-215), the same on both sides. *)
(* The branch at 78792c96 hands each side the peer's raw data, so two     *)
(* sides with different diffusion modes end with opposite modes.          *)
(* RawPeerData = TRUE models that.                                         *)
(*                                                                         *)
(* The labels "Client" and "Server" from Handshake.tla are kept as names   *)
(* for the two sides; here both behave as clients.                         *)
(***************************************************************************)
EXTENDS Handshake

CONSTANT AsymmetricDecode   \* TRUE: a side's data may be undecodable by the other
CONSTANT ReadsBeforeProposing \* TRUE: a side may read the peer's message while still in StPropose
CONSTANT RawPeerData        \* TRUE: a side ends with the peer's raw data, not the agreed data

VARIABLE data   \* data[r]: the version data side r ends with, NoParams until it accepts

\* In English: "Every variable, the shared ones and data."
\* Literally: "simVars is defined as the tuple of vars and data."
simVars == <<vars, data>>

\* In English: "The data side r ends with after accepting version v: the
\* peer's own data for v under RawPeerData, else the agreement of r's data,
\* however it is held, with the peer's."
\* Literally: "EndData of r and v is defined as: if RawPeerData then table of
\*   Peer of r, applied to v; else AgreeHeld of table of r applied to v and
\*   table of Peer of r applied to v."
EndData(r, v) ==
    IF RawPeerData THEN table[Peer(r)][v]
    ELSE AgreeHeld(table[r][v], table[Peer(r)][v])

\* Both sides' data never asks for a query. With AsymmetricDecode the `ok`
\* flag varies: one side may send data the other cannot decode.
\* Literally: "SimParams is defined as the set of every p in Params such that
\*   p's query is not true, and (AsymmetricDecode is true or p's ok is true)."
SimParams == {p \in Params : ~p.query /\ (AsymmetricDecode \/ p.ok)}
\* Literally: "SimTables is defined as Tables of SimParams without the members
\*   of the set containing the empty sequence."
SimTables == Tables(SimParams) \ {<<>>}

\* In English: "Both sides start in StPropose with any non-empty tables."
\* Literally: "SimInit is defined as: view equals the function that maps every
\*   r in Roles to "StPropose", and inbox equals the function that maps every r
\*   in Roles to the empty sequence, and table is a member of the set of
\*   functions from Roles to SimTables, and result equals the function that
\*   maps every r in Roles to NoResult, and heard equals the empty sequence,
\*   and rogueLeft equals 0, and data equals the function that maps every r in
\*   Roles to NoParams."
SimInit ==
    /\ view = [r \in Roles |-> "StPropose"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ table \in [Roles -> SimTables]
    /\ result = [r \in Roles |-> NoResult]
    /\ heard = <<>>
    /\ rogueLeft = 0
    /\ data = [r \in Roles |-> NoParams]

\* In English: "Side r in StPropose sends its table to its peer, its keys in
\* one of the wire orders ClientKeyOrders allows, and moves to StConfirm."
\* Literally: "SimPropose of r is defined as: view of r equals "StPropose", and
\*   view in the next state equals view except that its r entry is "StConfirm",
\*   and there exists a k in KeyOrders of table of r such that inbox in the
\*   next state equals inbox except that its Peer of r entry is the old entry
\*   with MsgK of "MsgProposeVersions", table of r, 0, NoParams, "None",
\*   FALSE and k appended, and table, result, heard, rogueLeft and data are
\*   unchanged."
SimPropose(r) ==
    /\ view[r] = "StPropose"                         \* r has not proposed yet
    /\ view' = [view EXCEPT ![r] = "StConfirm"]      \* r now waits for an answer
    /\ \E k \in KeyOrders(table[r]) :                \* the keys' wire order
         inbox' = [inbox EXCEPT ![Peer(r)] =         \* the peer receives r's table
                     Append(@, MsgK("MsgProposeVersions", table[r], 0, NoParams, "None", FALSE, k))]
    /\ UNCHANGED <<table, result, heard, rogueLeft, data>> \* nothing else changes

\* In English: "Side r in StConfirm reads the peer's proposal. If it is not
\* legal there (gOuroboros), or (reference) its recognised keys are out of
\* order, as decodeVersions checks MsgReplyVersions too (Codec.hs 160-167,
\* [R10]), r hangs up. Otherwise r is done, with the
\* result of negotiating its own table against the peer's [R2], and, if it
\* accepted, the data EndData gives it."
\* Literally: "SimRecv of r is defined as: view of r equals "StConfirm", and
\*   inbox of r does not equal the empty sequence, and, letting m be the head
\*   of inbox of r: if IsLegal of "StConfirm" and m's type is not true, then
\*   (view in the next state equals view except that its r entry is
\*   "Violation", and result and data are unchanged), else, letting d be
\*   ClientJudge of table of r and m, (view in the next state equals view
\*   except that its r entry is "StDone", and result in the next state equals
\*   result except that its r entry is d, and data in the next state equals
\*   data except that its r entry is, if d's kind equals "Accept", EndData of
\*   r and d's v, else NoParams); and inbox in the next state equals inbox
\*   except that its r entry is the tail of the old entry, and table, heard and
\*   rogueLeft are unchanged."
SimRecv(r) ==
    /\ view[r] = "StConfirm"
    /\ inbox[r] /= <<>>
    /\ LET m == Head(inbox[r]) IN
       IF ~IsLegal("StConfirm", m.type) \/ BadKeyOrder(m)
       THEN /\ view' = [view EXCEPT ![r] = "Violation"]
            /\ UNCHANGED <<result, data>>
       ELSE LET d == ClientJudge(table[r], m) IN
            /\ view' = [view EXCEPT ![r] = "StDone"]
            /\ result' = [result EXCEPT ![r] = d]
            /\ data' = [data EXCEPT ![r] =
                           IF d.kind = "Accept" THEN EndData(r, d.v) ELSE NoParams]
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<table, heard, rogueLeft>>

\* In English: "If reading can start before a side's own proposal has moved
\* it to StConfirm, side r in StPropose may read the peer's proposal. r
\* holds agency there, so the message is illegal and r hangs up." The
\* reference never does this: its client yields MsgProposeVersions before
\* it awaits anything [R2].
\* Literally: "SimRecvEarly of r is defined as: ReadsBeforeProposing is true,
\*   and view of r equals "StPropose", and inbox of r does not equal the empty
\*   sequence, and view in the next state equals view except that its r entry
\*   is "Violation", and inbox in the next state equals inbox except that its r
\*   entry is the tail of the old entry, and table, result, heard, rogueLeft
\*   and data are unchanged."
SimRecvEarly(r) ==
    /\ ReadsBeforeProposing                          \* only the early-reading variant
    /\ view[r] = "StPropose"                         \* r has not proposed yet
    /\ inbox[r] /= <<>>                              \* the peer's proposal has arrived
    /\ view' = [view EXCEPT ![r] = "Violation"]      \* r rejects it and hangs up
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]        \* the message is consumed
    /\ UNCHANGED <<table, result, heard, rogueLeft, data>> \* nothing else changes

\* In English: "A step is some side proposing, reading, or reading early, or,
\* once the connection is over, nothing changing."
\* Literally: "SimNext is defined as: there exists an r in Roles such that
\*   SimPropose of r or SimRecv of r or SimRecvEarly of r; or Ended is true and
\*   simVars is unchanged."
SimNext ==
    \/ \E r \in Roles : SimPropose(r) \/ SimRecv(r) \/ SimRecvEarly(r)
    \/ Ended /\ UNCHANGED simVars

\* In English: "Start in SimInit, and from then on every step is a SimNext
\* step."
\* Literally: "SimSpec is defined as: SimInit holds at the start, and always,
\*   every step is a SimNext step or a step that leaves simVars unchanged."
SimSpec == SimInit /\ [][SimNext]_simVars

-----------------------------------------------------------------------------

\* In English: "Every variable the simultaneous-open model uses holds the kind
\* of value it should."
\* Literally: "SimTypeOK is defined as: view is a member of the set of
\*   functions from Roles to the union of States and Failures, and inbox is a
\*   member of the set of functions from Roles to the set of sequences of
\*   members of Messages, and table is a member of the set of functions from
\*   Roles to SimTables, and result is a member of the set of functions from
\*   Roles to the set of records whose field kind is a member of the set
\*   containing "None", "Accept", "Refuse", "Query" and "Error", field v is a
\*   member of the union of Versions and the set containing 0, and field reason
\*   is a member of Reasons; and data is a member of the set of functions from
\*   Roles to Params."
SimTypeOK ==
    /\ view \in [Roles -> States \cup Failures]
    /\ inbox \in [Roles -> Seq(Messages)]
    /\ table \in [Roles -> SimTables]
    /\ result \in [Roles -> [kind : {"None", "Accept", "Refuse", "Query", "Error"},
                             v : Versions \cup {0}, reason : Reasons]]
    /\ data \in [Roles -> Params]

\* In English: "When both sides are done, both accepted the same version or
\* both refused [S6]. A side that refuses closes the connection [R1], so a
\* lone refusal is safe only if the other side refused too or never
\* starts on the connection; this checks the stronger, symmetric claim."
\* Literally: "SymmetricOutcome is defined as: if, for all r in Roles, view of
\*   r equals "StDone", then either (for all r in Roles, result of r's kind
\*   equals "Accept"; and result of "Client"'s v equals result of "Server"'s
\*   v), or, for all r in Roles, result of r's kind equals "Refuse"."
SymmetricOutcome ==
    (\A r \in Roles : view[r] = "StDone") =>
        \/ /\ \A r \in Roles : result[r].kind = "Accept"
           /\ result["Client"].v = result["Server"].v
        \/ \A r \in Roles : result[r].kind = "Refuse"

\* In English: "A side that accepted v chose the highest version in both
\* tables [S6]."
\* Literally: "SimAcceptsHighest is defined as: for all r in Roles, if result
\*   of r's kind equals "Accept", then result of r's v equals Max of the
\*   intersection of the domain of table of "Client" and the domain of table of
\*   "Server"."
SimAcceptsHighest ==
    \A r \in Roles :
        result[r].kind = "Accept" =>
            result[r].v = Max(DOMAIN table["Client"] \cap DOMAIN table["Server"])

\* In English: "With nothing in flight, both sides are in the same state
\* [S6 747-755]."
\* Literally: "SameStateWhenQuiet is defined as: if, for all r in Roles, inbox
\*   of r equals the empty sequence, then view of "Client" equals view of
\*   "Server"."
SameStateWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>>) => view["Client"] = view["Server"]

\* In English: "When both sides accepted, both end with the same version
\* data, the agreement of the two sides' data for the chosen version, so
\* their connections derive the same diffusion mode [R2]. The reference
\* client returns acceptVersion vData vData' on MsgReplyVersions
\* (Client.hs 213-215), and every combined field is commutative."
\* Literally: "SimAgreedData is defined as: if, for all r in Roles, result of
\*   r's kind equals "Accept", then, for all r in Roles, data of r equals Agree
\*   of table of r applied to result of r's v and table of Peer of r applied
\*   to result of r's v; and data of "Client" equals data of "Server"."
SimAgreedData ==
    (\A r \in Roles : result[r].kind = "Accept") =>
        /\ \A r \in Roles :
               data[r] = Agree(table[r][result[r].v], table[Peer(r)][result[r].v])
        /\ data["Client"] = data["Server"]
=============================================================================
