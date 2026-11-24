-------------------------- MODULE ChainSyncProtocol --------------------------
(***************************************************************************)
(* Model `chainsync`, slice 4: the chain-sync protocol itself, both sides, as the   *)
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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
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

\* Literally: "vars is defined as the tuple of all nine variables."
vars == <<owed, awaited, cdone, sent, sv, toServer, toClient, violation, early>>

\* In English: "Both sides start in StIdle with nothing in flight."
\* Literally: "Init is defined as: owed equals the empty sequence, and awaited
\*   equals FALSE, and cdone equals FALSE, and sent equals 0, and sv equals
\*   "Idle", and toServer equals the empty sequence, and toClient equals the
\*   empty sequence, and violation equals FALSE, and early equals FALSE."
Init ==
    /\ owed = <<>> /\ awaited = FALSE /\ cdone = FALSE /\ sent = 0
    /\ sv = "Idle" /\ toServer = <<>> /\ toClient = <<>>
    /\ violation = FALSE /\ early = FALSE

-----------------------------------------------------------------------------
(* The client [R2]. *)

\* In English: "Pipeline a MsgRequestNext if fewer than Limit are owed and
\* no MsgFindIntersect is."
\* Literally: "SendRequestNext is defined as: cdone is not true, and sent is
\*   less than MaxRequests, and the length of owed is less than Limit, and for
\*   all i in 1 through the length of owed, element i of owed equals "RN"; and
\*   toServer in the next state equals toServer with "RequestNext" appended,
\*   and owed in the next state equals owed with "RN" appended, and sent in the
\*   next state equals sent plus 1, and the other six variables are unchanged."
SendRequestNext ==
    /\ ~cdone /\ sent < MaxRequests
    /\ Len(owed) < Limit
    /\ \A i \in 1..Len(owed) : owed[i] = "RN"
    /\ toServer' = Append(toServer, "RequestNext")
    /\ owed' = Append(owed, "RN") /\ sent' = sent + 1
    /\ UNCHANGED <<awaited, cdone, sv, toClient, violation, early>>

\* In English: "Send MsgFindIntersect when owed nothing (or, with the
\* mutation, at any time)."
\* Literally: "SendFindIntersect is defined as: cdone is not true, and sent is
\*   less than MaxRequests, and (owed equals the empty sequence, or
\*   FindWhilePipelined is true), and toServer in the next state equals
\*   toServer with "FindIntersect" appended, and early in the next state equals
\*   (early is true or owed does not equal the empty sequence), and owed in the
\*   next state equals owed with "FI" appended, and sent in the next state
\*   equals sent plus 1, and the other five variables are unchanged."
SendFindIntersect ==
    /\ ~cdone /\ sent < MaxRequests
    /\ owed = <<>> \/ FindWhilePipelined
    /\ toServer' = Append(toServer, "FindIntersect")
    /\ early' = (early \/ owed /= <<>>)
    /\ owed' = Append(owed, "FI") /\ sent' = sent + 1
    /\ UNCHANGED <<awaited, cdone, sv, toClient, violation>>

\* In English: "Send MsgDone when owed nothing (or, with the mutation, at
\* any time); the client's run is then over."
\* Literally: "SendDone is defined as: cdone is not true, and (owed equals the
\*   empty sequence, or DoneWhilePipelined is true), and toServer in the next
\*   state equals toServer with "Done" appended, and early in the next state
\*   equals (early is true or owed does not equal the empty sequence), and
\*   cdone in the next state equals TRUE, and the other six variables are
\*   unchanged."
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
\* Literally: "ClientRecv is defined as: toClient does not equal the empty
\*   sequence, and, letting m be the head of toClient, and ok be (cdone is not
\*   true, and owed does not equal the empty sequence, and (the head of owed
\*   equals "RN" and m equals "AwaitReply" and awaited is not true, or the head
\*   of owed equals "RN" and m is a member of the set containing "RollForward"
\*   and "RollBackward", or the head of owed equals "FI" and m is a member of
\*   the set containing "IntersectFound" and "IntersectNotFound")): violation
\*   in the next state equals (violation is true or ok is not true), and if ok
\*   is true and m does not equal "AwaitReply", then owed in the next state
\*   equals the tail of owed and awaited in the next state equals FALSE; else
\*   if ok is true, then awaited in the next state equals TRUE and owed is
\*   unchanged; else owed and awaited are unchanged; and toClient in the next
\*   state equals the tail of toClient, and cdone, sent, sv, toServer and early
\*   are unchanged."
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
\* Literally: "ServerTake is defined as: sv equals "Idle", and toServer does
\*   not equal the empty sequence, and, letting m be the head of toServer: sv
\*   in the next state equals (in the case m equals "RequestNext", "CanAwait";
\*   in the case m equals "FindIntersect", "Intersect"; in the case m equals
\*   "Done", "Done"), and violation is unchanged; and toServer in the next
\*   state equals the tail of toServer, and owed, awaited, cdone, sent,
\*   toClient and early are unchanged."
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
\* Literally: "ServerSend of m is defined as: (sv equals "CanAwait" and m
\*   equals "AwaitReply" and sv in the next state equals "MustReply"; or sv
\*   equals "MustReply" and m equals "AwaitReply" and AwaitTwice is true and sv
\*   in the next state equals "MustReply"; or sv is a member of the set
\*   containing "CanAwait" and "MustReply", and m is a member of the set
\*   containing "RollForward" and "RollBackward", and sv in the next state
\*   equals "Idle"; or sv equals "Intersect", and m is a member of the set
\*   containing "IntersectFound" and "IntersectNotFound", and sv in the next
\*   state equals "Idle"), and toClient in the next state equals toClient with
\*   m appended, and the other seven variables are unchanged."
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
\* Literally: "Finished is defined as: toServer equals the empty sequence, and
\*   toClient equals the empty sequence, and sv is a member of the set
\*   containing "Idle" and "Done", and owed equals the empty sequence, and vars
\*   is unchanged."
Finished ==
    /\ toServer = <<>> /\ toClient = <<>> /\ sv \in {"Idle", "Done"}
    /\ owed = <<>>
    /\ UNCHANGED vars

\* In English: "Every message the server can send."
\* Literally: "Messages is defined as the set containing "AwaitReply",
\*   "RollForward", "RollBackward", "IntersectFound" and "IntersectNotFound"."
Messages == {"AwaitReply", "RollForward", "RollBackward", "IntersectFound",
             "IntersectNotFound"}

\* In English: "A step is any one client or server step, or staying finished."
\* Literally: "Next is defined as: SendRequestNext, or SendFindIntersect, or
\*   SendDone, or ClientRecv, or ServerTake, or there exists an m in Messages
\*   such that ServerSend of m, or Finished."
Next ==
    \/ SendRequestNext \/ SendFindIntersect \/ SendDone \/ ClientRecv
    \/ ServerTake \/ \E m \in Messages : ServerSend(m)
    \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Neither side ever receives a message its state does not
\* allow."
\* Literally: "NoViolation is defined as: violation is not true."
NoViolation == ~violation

\* In English: "MsgFindIntersect and MsgDone are sent only when the client
\* is owed nothing" - the reference's Z rule.
\* Literally: "OnlyAtZero is defined as: early is not true."
OnlyAtZero == ~early

\* In English: "When nothing is in flight, the two sides agree on the
\* state: the server is in StIdle exactly when the client is owed nothing."
\* Literally: "AgreeWhenQuiet is defined as: if toServer equals the empty
\*   sequence and toClient equals the empty sequence and cdone is not true,
\*   then (sv equals "Idle") if and only if (owed equals the empty sequence)."
AgreeWhenQuiet ==
    (toServer = <<>> /\ toClient = <<>> /\ ~cdone)
        => ((sv = "Idle") <=> (owed = <<>>))

\* In English: "The client is never owed more than Limit MsgRequestNext."
\* Literally: "WindowBound is defined as: the length of owed is less than or
\*   equal to Limit."
WindowBound == Len(owed) <= Limit

\* Probes, each EXPECTED to be violated.
\* "The window is never full." Violated = pipelining reaches Limit.
\* Literally: "ProbeWindowNeverFull is defined as: the length of owed is less
\*   than Limit."
ProbeWindowNeverFull == Len(owed) < Limit
\* "The server never reaches StMustReply." Violated = MsgAwaitReply happens.
\* Literally: "ProbeNeverMustReply is defined as: sv does not equal
\*   "MustReply"."
ProbeNeverMustReply == sv /= "MustReply"
\* "A pipelined request never waits at the server." Violated = it does.
\* Literally: "ProbeNoRequestWaits is defined as: it is not the case that sv is
\*   a member of the set containing "CanAwait" and "MustReply" and toServer
\*   does not equal the empty sequence."
ProbeNoRequestWaits == ~(sv \in {"CanAwait", "MustReply"} /\ toServer /= <<>>)
=============================================================================
