-------------------------- MODULE ChainSyncProtocol --------------------------
(***************************************************************************)
(* Model 04, slice 4: the chain-sync protocol itself, both sides, as the   *)
(* specification's tables define it, with MsgRequestNext pipelined as the  *)
(* reference client does.                                                  *)
(*                                                                         *)
(* The earlier slices model gOuroboros' client code. This one models the   *)
(* protocol: what each side may send in each state, and what each side     *)
(* must accept. gOuroboros' state maps (StateMapNtN, StateMapNtC) are      *)
(* checked against the same table by statemap_model_test.go.               *)
(*                                                                         *)
(* The client keeps a list of the answers it is owed, oldest first: "RN"   *)
(* for each MsgRequestNext and "FI" for MsgFindIntersect. It may pipeline  *)
(* MsgRequestNext up to Limit, but sends MsgFindIntersect and MsgDone only *)
(* when it is owed nothing (the reference's Z rule). The server takes one  *)
(* message at a time, in order, and answers it before taking the next.     *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex:                                  *)
(*   [C1] 838-848: agencies. 893-908: messages and transitions.            *)
(*   [S1] 27-36: a message a state does not allow aborts the connection.   *)
(*   [P1] 2180-2208: pipelining; replies in request order.                 *)
(*   Reference, same commit, ouroboros-network/protocols/lib/Ouroboros/    *)
(*   Network/Protocol/ChainSync/:                                          *)
(*   [R2] ClientPipelined.hs 60-84: SendMsgRequestNextPipelined raises the *)
(*        outstanding count; SendMsgFindIntersect and SendMsgDone only at  *)
(*        Z; CollectResponse takes answers in order.                       *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Limit,          \* the most MsgRequestNext the client pipelines
    MaxRequests,    \* MsgRequestNext and MsgFindIntersect sent in total
    \* Each switch below is FALSE in the specification and the reference;
    \* TRUE breaks one rule to show the invariants notice (*Bug.cfg).
    FindWhilePipelined,  \* the client sends MsgFindIntersect while owed answers
    DoneWhilePipelined,  \* the client sends MsgDone while owed answers
    AwaitTwice           \* the server sends MsgAwaitReply again from MustReply

VARIABLES
    owed,       \* answers the client is owed, oldest first: "RN" or "FI"
    awaited,    \* TRUE once the oldest RN has been answered MsgAwaitReply
    cdone,      \* TRUE once the client has sent MsgDone
    sent,       \* requests sent so far (model bound)
    sv,         \* the server: "Idle", "CanAwait", "MustReply", "Intersect", "Done"
    toServer,   \* client messages in flight, in order
    toClient,   \* server messages in flight, in order
    violation,  \* a side received a message its state does not allow
    early       \* the client sent MsgFindIntersect or MsgDone while owed answers

vars == <<owed, awaited, cdone, sent, sv, toServer, toClient, violation, early>>

\* In English: "Both sides start in StIdle with nothing in flight."
Init ==
    /\ owed = <<>> /\ awaited = FALSE /\ cdone = FALSE /\ sent = 0
    /\ sv = "Idle" /\ toServer = <<>> /\ toClient = <<>>
    /\ violation = FALSE /\ early = FALSE

-----------------------------------------------------------------------------
(* The client [R2]. *)

\* In English: "Pipeline a MsgRequestNext if fewer than Limit are owed and
\* no MsgFindIntersect is."
SendRequestNext ==
    /\ ~cdone /\ sent < MaxRequests
    /\ Len(owed) < Limit
    /\ \A i \in 1..Len(owed) : owed[i] = "RN"
    /\ toServer' = Append(toServer, "RequestNext")
    /\ owed' = Append(owed, "RN") /\ sent' = sent + 1
    /\ UNCHANGED <<awaited, cdone, sv, toClient, violation, early>>

\* In English: "Send MsgFindIntersect when owed nothing (or, with the
\* mutation, at any time)."
SendFindIntersect ==
    /\ ~cdone /\ sent < MaxRequests
    /\ owed = <<>> \/ FindWhilePipelined
    /\ toServer' = Append(toServer, "FindIntersect")
    /\ early' = (early \/ owed /= <<>>)
    /\ owed' = Append(owed, "FI") /\ sent' = sent + 1
    /\ UNCHANGED <<awaited, cdone, sv, toClient, violation>>

\* In English: "Send MsgDone when owed nothing (or, with the mutation, at
\* any time); the client's run is then over."
SendDone ==
    /\ ~cdone
    /\ owed = <<>> \/ DoneWhilePipelined
    /\ toServer' = Append(toServer, "Done")
    /\ early' = (early \/ owed /= <<>>)
    /\ cdone' = TRUE
    /\ UNCHANGED <<owed, awaited, sent, sv, toClient, violation>>

\* In English: "Take the server's next message. It must answer the oldest
\* request owed: MsgAwaitReply (once) or a roll for RN, an intersect answer
\* for FI. A client whose run is over reads nothing more, so any message
\* to it is a violation too [S1]."
ClientRecv ==
    /\ toClient /= <<>>
    /\ LET m == Head(toClient)
           ok == /\ ~cdone /\ owed /= <<>>
                 /\ \/ Head(owed) = "RN" /\ m = "AwaitReply" /\ ~awaited
                    \/ Head(owed) = "RN" /\ m \in {"RollForward", "RollBackward"}
                    \/ Head(owed) = "FI" /\ m \in {"IntersectFound",
                                                     "IntersectNotFound"}
       IN /\ violation' = (violation \/ ~ok)
          /\ IF ok /\ m /= "AwaitReply"
                THEN owed' = Tail(owed) /\ awaited' = FALSE
                ELSE IF ok THEN awaited' = TRUE /\ UNCHANGED owed
                ELSE UNCHANGED <<owed, awaited>>
    /\ toClient' = Tail(toClient)
    /\ UNCHANGED <<cdone, sent, sv, toServer, early>>

-----------------------------------------------------------------------------
(* The server [C1][P1]. *)

\* In English: "In StIdle, take the next request; a message StIdle does not
\* allow is a violation. In any other state the server holds agency and
\* reads nothing: pipelined requests wait in order."
ServerTake ==
    /\ sv = "Idle" /\ toServer /= <<>>
    /\ LET m == Head(toServer) IN
       /\ sv' = CASE m = "RequestNext"   -> "CanAwait"
                  [] m = "FindIntersect" -> "Intersect"
                  [] m = "Done"          -> "Done"
       /\ UNCHANGED violation
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<owed, awaited, cdone, sent, toClient, early>>

\* In English: "Answer, as the messages table allows: from StCanAwait
\* MsgAwaitReply (to StMustReply) or a roll; from StMustReply a roll (or,
\* with the mutation, MsgAwaitReply again); from StIntersect either
\* intersect answer."
ServerSend(m) ==
    /\ \/ sv = "CanAwait" /\ m = "AwaitReply" /\ sv' = "MustReply"
       \/ sv = "MustReply" /\ m = "AwaitReply" /\ AwaitTwice /\ sv' = "MustReply"
       \/ sv \in {"CanAwait", "MustReply"}
          /\ m \in {"RollForward", "RollBackward"} /\ sv' = "Idle"
       \/ sv = "Intersect" /\ m \in {"IntersectFound", "IntersectNotFound"}
          /\ sv' = "Idle"
    /\ toClient' = Append(toClient, m)
    /\ UNCHANGED <<owed, awaited, cdone, sent, toServer, violation, early>>

-----------------------------------------------------------------------------

\* In English: "Finished: the client has ended its run, or has stopped
\* sending, and nothing is in flight."
Finished ==
    /\ toServer = <<>> /\ toClient = <<>> /\ sv \in {"Idle", "Done"}
    /\ owed = <<>>
    /\ UNCHANGED vars

Messages == {"AwaitReply", "RollForward", "RollBackward", "IntersectFound",
             "IntersectNotFound"}

Next ==
    \/ SendRequestNext \/ SendFindIntersect \/ SendDone \/ ClientRecv
    \/ ServerTake \/ \E m \in Messages : ServerSend(m)
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Neither side ever receives a message its state does not
\* allow."
NoViolation == ~violation

\* In English: "MsgFindIntersect and MsgDone are sent only when the client
\* is owed nothing" - the reference's Z rule.
OnlyAtZero == ~early

\* In English: "When nothing is in flight, the two sides agree on the
\* state: the server is in StIdle exactly when the client is owed nothing."
AgreeWhenQuiet ==
    (toServer = <<>> /\ toClient = <<>> /\ ~cdone)
        => ((sv = "Idle") <=> (owed = <<>>))

\* In English: "The client is never owed more than Limit MsgRequestNext."
WindowBound == Len(owed) <= Limit

\* Probes, each EXPECTED to be violated.
\* "The window is never full." Violated = pipelining reaches Limit.
ProbeWindowNeverFull == Len(owed) < Limit
\* "The server never reaches StMustReply." Violated = MsgAwaitReply happens.
ProbeNeverMustReply == sv /= "MustReply"
\* "A pipelined request never waits at the server." Violated = it does.
ProbeNoRequestWaits == ~(sv \in {"CanAwait", "MustReply"} /\ toServer /= <<>>)
=============================================================================
