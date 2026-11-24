------------------------ MODULE LocalMessageSubmission ------------------------
(***************************************************************************)
(* Model `dmq`, part 2: DMQ local message submission (node-to-client).        *)
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
(* With OwnAnswer, the model is gOuroboros after the change that follows  *)
(* the reference: SubmitMessage takes the client's submit lock, registers  *)
(* as the waiter, queues its message, and returns the answer to that       *)
(* message; the lock is released when the answer arrives.                  *)
(*   [R3] ouroboros-network 5f356486ab3e, ouroboros-network/protocols/lib/ *)
(*        Ouroboros/Network/Protocol/LocalTxSubmission/Client.hs 46-56:    *)
(*        SendMsgSubmitTx tx k hands the result to k.                      *)
(*                                                                         *)
(* Not modelled: validation, authentication and the replay cache (they     *)
(* only choose accept or reject), timeouts, and the run after MsgDone.     *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
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
    \* TRUE: SubmitMessage waits for and returns its own answer [R3]; the
    \* callbacks are not used to pair answers with calls.
    OwnAnswer,
    \* With OwnAnswer: TRUE, SubmitMessage holds the client's submit lock
    \* from registering until its answer arrives. FALSE is a mutation that
    \* proves the lock is what keeps registration and queue order equal.
    OwnAnswerLock,
    \* Mutation, FALSE normally. TRUE: the send loop sends without waiting
    \* for agency, to prove NoViolation can fail.
    NoAgencyWait

\* Literally: "None is defined as "none"."
None == "none"

VARIABLES
    cpc,       \* each call's step: "start", "registered" (OwnAnswer only),
               \* "queued", "returned"
    lock,      \* the application's lock when Serialised, or the client's
               \* submit lock with OwnAnswer: None or a call
    sendQ,     \* the protocol's send queue: calls' messages, or "Done"
    cs,        \* the client's protocol state: "Idle", "Busy", "Done"
    toClient,  \* the answer in flight: <<>> or <<call>> (the call answered)
    pending,   \* the calls waiting for an answer, oldest first: those that
               \* returned, or with OwnAnswer those that registered
    answered,  \* calls the application has matched with an answer
    misrouted, \* TRUE once an answer is attributed to the wrong call
    violation  \* TRUE once a side receives a message its state forbids

\* Literally: "vars is defined as the tuple of all nine variables."
vars == <<cpc, lock, sendQ, cs, toClient, pending, answered, misrouted,
          violation>>

\* In English: "Every call is about to start, nobody holds the lock, nothing is
\* queued, in flight or waiting, the client is in StIdle, and nothing has gone
\* wrong."
\* Literally: "Init is defined as: cpc equals the function that maps every c in
\*   Calls to "start", and lock equals None, and sendQ equals the empty
\*   sequence and cs equals "Idle" and toClient equals the empty sequence, and
\*   pending equals the empty sequence and answered equals the empty set, and
\*   misrouted equals FALSE and violation equals FALSE."
Init ==
    /\ cpc = [c \in Calls |-> "start"]
    /\ lock = None
    /\ sendQ = <<>> /\ cs = "Idle" /\ toClient = <<>>
    /\ pending = <<>> /\ answered = {}
    /\ misrouted = FALSE /\ violation = FALSE

-----------------------------------------------------------------------------
(* The application's calls [G1].                                           *)

\* In English: "With OwnAnswer, a call takes the client's submit lock (unless
\* the lock is mutated away) and registers as the next call waiting for an
\* answer [R3]."
\* Literally: "CallRegister of c is defined as: OwnAnswer is true, and cpc of
\*   c equals "start", and if OwnAnswerLock is true, then lock equals None,
\*   and lock in the next state equals (if OwnAnswerLock then c, else lock),
\*   and pending in the next state equals pending with c appended, and cpc in
\*   the next state equals cpc except that its c entry is "registered", and
\*   sendQ, cs, toClient, answered, misrouted and violation are unchanged."
CallRegister(c) ==
    /\ OwnAnswer
    /\ cpc[c] = "start"
    /\ OwnAnswerLock => lock = None
    /\ lock' = IF OwnAnswerLock THEN c ELSE lock
    /\ pending' = Append(pending, c)
    /\ cpc' = [cpc EXCEPT ![c] = "registered"]
    /\ UNCHANGED <<sendQ, cs, toClient, answered, misrouted, violation>>

\* In English: "A call (taking the application's lock if it serialises; with
\* OwnAnswer, once registered) queues its MsgSubmitMessage [G3]."
\* Literally: "CallQueue of c is defined as: cpc of c equals (if OwnAnswer
\*   then "registered", else "start"), and if Serialised is true and
\*   OwnAnswer is not true, then lock equals None, and lock in the next state
\*   equals (if Serialised and OwnAnswer is not true, then c, else lock), and
\*   sendQ in the next state equals sendQ with c appended, and cpc in the next
\*   state equals cpc except that its c entry is "queued", and cs, toClient,
\*   pending, answered, misrouted and violation are unchanged."
CallQueue(c) ==
    /\ cpc[c] = IF OwnAnswer THEN "registered" ELSE "start"
    /\ (Serialised /\ ~OwnAnswer) => lock = None
    /\ lock' = IF Serialised /\ ~OwnAnswer THEN c ELSE lock
    /\ sendQ' = Append(sendQ, c)
    /\ cpc' = [cpc EXCEPT ![c] = "queued"]
    /\ UNCHANGED <<cs, toClient, pending, answered, misrouted, violation>>

\* In English: "SubmitMessage returns. Without OwnAnswer it returns at once
\* and the application records the call as waiting for the next answer;
\* with OwnAnswer it returns once its answer has arrived."
\* Literally: "CallReturn of c is defined as: cpc of c equals "queued", and if
\*   OwnAnswer is true, then c is a member of answered, and cpc in the next
\*   state equals cpc except that its c entry is "returned", and pending in
\*   the next state equals (if OwnAnswer then pending, else pending with c
\*   appended), and lock, sendQ, cs, toClient, answered, misrouted and
\*   violation are unchanged."
CallReturn(c) ==
    /\ cpc[c] = "queued"
    /\ OwnAnswer => c \in answered
    /\ cpc' = [cpc EXCEPT ![c] = "returned"]
    /\ pending' = IF OwnAnswer THEN pending ELSE Append(pending, c)
    /\ UNCHANGED <<lock, sendQ, cs, toClient, answered, misrouted, violation>>

\* In English: "Once every call has queued its message, Stop queues MsgDone
\* behind them [G1]. (A call made after Stop is not modelled.)"
\* Literally: "Stop is defined as: UseStop is true and, for all c in Calls, cpc
\*   of c is a member of the set containing "queued" and "returned", and
\*   "Done" is not a member of the set of
\*   element i of sendQ, for every i that is a member of 1 through the length
\*   of sendQ, and cs does not equal "Done", and sendQ in the next state equals
\*   sendQ with "Done" appended, and cpc, lock, cs, toClient, pending,
\*   answered, misrouted and violation are unchanged."
Stop ==
    /\ UseStop /\ \A c \in Calls : cpc[c] \in {"queued", "returned"}
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
\* Literally: "SendNext is defined as: (cs equals "Idle", or (NoAgencyWait is
\*   true and cs equals "Busy")) and sendQ does not equal the empty sequence,
\*   and, letting m be the head of sendQ: if m equals "Done", then cs in the
\*   next state equals "Done" and toClient is unchanged; else if cs equals
\*   "Busy", then cs and toClient are unchanged; else cs in the next state
\*   equals "Busy" and toClient in the next state equals the tuple of m; and
\*   sendQ in the next state equals the tail of sendQ, and violation in the
\*   next state equals (violation, or (cs equals "Busy" and the head of sendQ
\*   does not equal "Done")), and cpc, lock, pending, answered and misrouted
\*   are unchanged."
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
\* (an application that pairs answers with calls must). With OwnAnswer the
\* answer goes to the oldest registered call, which then holds the answer
\* its SubmitMessage returns, and the submit lock is released."
\* Literally: "Receive is defined as: toClient does not equal the empty
\*   sequence, and if cs does not equal "Busy", then violation in the next
\*   state equals TRUE, and cs, pending, answered and misrouted are unchanged;
\*   else if TaggedAnswers is true, then answered in the next state equals the
\*   union of answered and the set containing the head of toClient, and pending
\*   in the next state equals the subsequence of pending made of every x such
\*   that x does not equal the head of toClient, and cs in the next state
\*   equals "Idle", and misrouted and violation are unchanged; else pending
\*   does not equal the empty sequence, and answered in the next state equals
\*   the union of answered and the set containing the head of pending, and
\*   misrouted in the next state equals (misrouted, or the head of pending does
\*   not equal the head of toClient), and pending in the next state equals the
\*   tail of pending, and cs in the next state equals "Idle", and violation is
\*   unchanged; and toClient in the next state equals the empty sequence, and
\*   lock in the next state equals (if Serialised, or OwnAnswer and
\*   OwnAnswerLock are true, then None, else lock), and cpc and sendQ are
\*   unchanged."
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
    /\ lock' = IF Serialised \/ (OwnAnswer /\ OwnAnswerLock) THEN None ELSE lock
    /\ UNCHANGED <<cpc, sendQ>>

-----------------------------------------------------------------------------

\* In English: "Done: every call has had its answer, and nothing is left to
\* send - or the run has ended with MsgDone after them."
\* Literally: "Quiet is defined as: (answered equals Calls, or violation is
\*   true), and sendQ equals the empty sequence and toClient equals the empty
\*   sequence, and vars is unchanged."
Quiet ==
    /\ answered = Calls \/ violation
    /\ sendQ = <<>> /\ toClient = <<>>
    /\ UNCHANGED vars

\* In English: "A step is a call registering, queueing or returning, Stop,
\* the send loop sending, an answer arriving, or, once all is done, nothing."
\* Literally: "Next is defined as: there exists a c in Calls such that
\*   CallRegister of c or CallQueue of c or CallReturn of c; or Stop, or
\*   SendNext, or Receive, or Quiet."
Next ==
    \/ \E c \in Calls : CallRegister(c) \/ CallQueue(c) \/ CallReturn(c)
    \/ Stop \/ SendNext \/ Receive \/ Quiet

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "No side receives a message its state forbids."
\* Literally: "NoViolation is defined as: violation is not true."
NoViolation == ~violation

\* In English: "Every answer the application attributes to a call is the
\* answer to that call's own message."
\* Literally: "AnswerReachesAsker is defined as: misrouted is not true."
AnswerReachesAsker == ~misrouted

\* Probes, each EXPECTED to be violated.
\* In English: "Two submissions are never queued at once." Violated = they
\* are, so the send queue really orders concurrent calls.
\* Literally: "ProbeNeverTwoQueued is defined as: the length of sendQ is less
\*   than 2."
ProbeNeverTwoQueued == Len(sendQ) < 2
\* In English: "MsgDone is never sent." Violated = Stop completes.
\* Literally: "ProbeNeverDone is defined as: cs does not equal "Done"."
ProbeNeverDone == cs /= "Done"
=============================================================================
