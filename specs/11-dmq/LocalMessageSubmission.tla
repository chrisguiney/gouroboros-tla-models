------------------------ MODULE LocalMessageSubmission ------------------------
(***************************************************************************)
(* Model 11, part 2: DMQ local message submission (node-to-client).        *)
(*                                                                         *)
(* A local client submits one message at a time (MsgSubmitMessage); the    *)
(* node answers MsgAcceptMessage or MsgRejectMessage(reason); MsgDone from *)
(* StIdle ends the run. In the reference this is LocalTxSubmission with    *)
(* DMQ messages: each answer goes to the continuation of the submit that   *)
(* sent it.                                                                *)
(*                                                                         *)
(* gOuroboros (protocol/localmessagesubmission/client.go) is different:    *)
(* SubmitMessage only QUEUES the message (Protocol.SendMessage) and        *)
(* returns. The protocol's send loop sends queued messages in order, each  *)
(* once the client has agency again. Answers arrive at AcceptMessageFunc   *)
(* or RejectMessageFunc, which receive no message and no id. An            *)
(* application calling SubmitMessage from several goroutines can only     *)
(* pair answers with calls by order: here, the order in which its calls    *)
(* returned.                                                               *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoViolation      no side receives a message its state forbids.       *)
(*   AnswerReachesAsker  the answer the application attributes to a call   *)
(*                    is the answer to that call's message.                *)
(*   NoAbandon        Stop (MsgDone) never leaves a submission unanswered; *)
(*                    checked as part of Quiet (deadlock).                 *)
(*                                                                         *)
(* Sources:                                                                *)
(*   CIP-0137 (cardano-foundation/CIPs 03387471), CIP-0137/README.md:      *)
(*   [C1] 552-614: states, agency, transitions, CDDL.                      *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e:           *)
(*   [S1] docs/network-spec/miniprotocols.tex 27-36: an unexpected message *)
(*        aborts the connection.                                           *)
(*   Reference, IntersectMBO/dmq-node a267003c:                            *)
(*   [R1] dmq-node/src/DMQ/Protocol/LocalMsgSubmission/Type.hs 20-22: an   *)
(*        alias of LocalTxSubmission.                                      *)
(*   [R2] dmq-node/src/DMQ/NodeToClient.hs 157-172: the server, run with   *)
(*        runAnnotatedPeer (no time limits).                               *)
(*   gOuroboros, blinklabs-io/gouroboros 61046085:                         *)
(*   [G1] protocol/localmessagesubmission/client.go: SubmitMessage, Stop,  *)
(*        handleAcceptMessage, handleRejectMessage.                        *)
(*   [G2] protocol/localmessagesubmission/server.go: handleSubmitMessage   *)
(*        answers every submission once (accept, reject, or refuse).       *)
(*   [G3] protocol/protocol.go: enqueueMessage; a queued message waits for *)
(*        agency and messages go out in queue order.                       *)
(*                                                                         *)
(* Not modelled: validation, authentication and the replay cache (they     *)
(* only choose accept or reject), timeouts, and the run after MsgDone.     *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Calls,       \* the application's concurrent SubmitMessage calls
    \* TRUE: the application serialises its calls (one at a time, answer
    \* before the next), so queue order and return order agree.
    Serialised,
    \* TRUE as in the reference: the answer carries the call it answers.
    \* FALSE in gOuroboros: callbacks get no message.
    TaggedAnswers,
    UseStop,     \* TRUE: the application may call Stop
    \* Mutation, FALSE normally. TRUE: the send loop sends without waiting
    \* for agency, to prove NoViolation can fail.
    NoAgencyWait

None == "none"

VARIABLES
    cpc,       \* each call's step: "start", "queued", "returned"
    lock,      \* the application's lock when Serialised: None or a call
    sendQ,     \* the protocol's send queue: calls' messages, or "Done"
    cs,        \* the client's protocol state: "Idle", "Busy", "Done"
    toClient,  \* the answer in flight: <<>> or <<call>> (the call answered)
    pending,   \* the application's list of returned calls, oldest first
    answered,  \* calls the application has matched with an answer
    misrouted, \* TRUE once an answer is attributed to the wrong call
    violation  \* TRUE once a side receives a message its state forbids

vars == <<cpc, lock, sendQ, cs, toClient, pending, answered, misrouted,
          violation>>

Init ==
    /\ cpc = [c \in Calls |-> "start"]
    /\ lock = None
    /\ sendQ = <<>> /\ cs = "Idle" /\ toClient = <<>>
    /\ pending = <<>> /\ answered = {}
    /\ misrouted = FALSE /\ violation = FALSE

-----------------------------------------------------------------------------
(* The application's calls [G1].                                           *)

\* In English: "A call (taking the application's lock if it serialises)
\* queues its MsgSubmitMessage [G3]."
CallQueue(c) ==
    /\ cpc[c] = "start"
    /\ Serialised => lock = None
    /\ lock' = IF Serialised THEN c ELSE lock
    /\ sendQ' = Append(sendQ, c)
    /\ cpc' = [cpc EXCEPT ![c] = "queued"]
    /\ UNCHANGED <<cs, toClient, pending, answered, misrouted, violation>>

\* In English: "SubmitMessage returns, and the application records the call
\* as waiting for the next answer."
CallReturn(c) ==
    /\ cpc[c] = "queued"
    /\ cpc' = [cpc EXCEPT ![c] = "returned"]
    /\ pending' = Append(pending, c)
    /\ UNCHANGED <<lock, sendQ, cs, toClient, answered, misrouted, violation>>

\* In English: "Once every call has queued its message, Stop queues MsgDone
\* behind them [G1]. (A call made after Stop is not modelled.)"
Stop ==
    /\ UseStop /\ \A c \in Calls : cpc[c] /= "start"
    /\ "Done" \notin {sendQ[i] : i \in 1..Len(sendQ)}
    /\ cs /= "Done"
    /\ sendQ' = Append(sendQ, "Done")
    /\ UNCHANGED <<cpc, lock, cs, toClient, pending, answered, misrouted,
                   violation>>

-----------------------------------------------------------------------------
(* The protocol and the server.                                            *)

\* In English: "With agency (StIdle), the send loop sends the oldest queued
\* message: a submission moves to StBusy, and the server answers it (the
\* answer names the call only to the model); MsgDone moves to StDone."
SendNext ==
    /\ (cs = "Idle" \/ (NoAgencyWait /\ cs = "Busy")) /\ sendQ /= <<>>
    /\ LET m == Head(sendQ) IN
       IF m = "Done"
          THEN /\ cs' = "Done" /\ UNCHANGED toClient
       ELSE IF cs = "Busy"
          \* "The server, in StBusy, receives a submission [S1]."
          THEN UNCHANGED <<cs, toClient>>
          ELSE /\ cs' = "Busy" /\ toClient' = <<m>>
    /\ sendQ' = Tail(sendQ)
    /\ violation' = (violation \/ (cs = "Busy" /\ Head(sendQ) /= "Done"))
    /\ UNCHANGED <<cpc, lock, pending, answered, misrouted>>

\* In English: "The answer arrives. It is legal only in StBusy [S1]. The
\* callback hands it to the oldest call the application is waiting on;
\* with tagged answers, to the call it names. A serialising application
\* then releases its lock. The callback waits until some call has returned
\* (an application that pairs answers with calls must)."
Receive ==
    /\ toClient /= <<>>
    /\ IF cs /= "Busy"
          THEN /\ violation' = TRUE /\ UNCHANGED <<cs, pending, answered, misrouted>>
       ELSE IF TaggedAnswers
          THEN /\ answered' = answered \cup {Head(toClient)}
               /\ pending' = SelectSeq(pending, LAMBDA x : x /= Head(toClient))
               /\ cs' = "Idle"
               /\ UNCHANGED <<misrouted, violation>>
       ELSE /\ pending /= <<>>
            /\ answered' = answered \cup {Head(pending)}
            /\ misrouted' = (misrouted \/ Head(pending) /= Head(toClient))
            /\ pending' = Tail(pending)
            /\ cs' = "Idle"
            /\ UNCHANGED violation
    /\ toClient' = <<>>
    /\ lock' = IF Serialised THEN None ELSE lock
    /\ UNCHANGED <<cpc, sendQ>>

-----------------------------------------------------------------------------

\* In English: "Done: every call has had its answer, and nothing is left to
\* send - or the run has ended with MsgDone after them."
Quiet ==
    /\ answered = Calls \/ violation
    /\ sendQ = <<>> /\ toClient = <<>>
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Calls : CallQueue(c) \/ CallReturn(c)
    \/ Stop \/ SendNext \/ Receive \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "No side receives a message its state forbids."
NoViolation == ~violation

\* In English: "Every answer the application attributes to a call is the
\* answer to that call's own message."
AnswerReachesAsker == ~misrouted

\* Probes, each EXPECTED to be violated.
\* In English: "Two submissions are never queued at once." Violated = they
\* are, so the send queue really orders concurrent calls.
ProbeNeverTwoQueued == Len(sendQ) < 2
\* In English: "MsgDone is never sent." Violated = Stop completes.
ProbeNeverDone == cs /= "Done"
=============================================================================
