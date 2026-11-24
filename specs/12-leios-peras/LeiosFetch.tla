----------------------------- MODULE LeiosFetch ------------------------------
(***************************************************************************)
(* Model 12, LeiosFetch: the gOuroboros client's request slot, callers     *)
(* that give up, Stop, and a server that answers in order.                 *)
(*                                                                         *)
(* The protocol is not in the network specification. Its block and block  *)
(* transactions exchanges follow the reference node (ouroboros-consensus)  *)
(* and CIP-0164; votes and block ranges are gOuroboros extensions with no  *)
(* reference. README.md says how authoritative each source is.             *)
(*                                                                         *)
(* The client (protocol/leiosfetch/client.go) keeps ONE request slot.      *)
(* Each call (BlockRequest, BlockTxsRequest, VotesRequest,                 *)
(* BlockRangeRequest; one shape here) acquires it, sends its request, and  *)
(* waits on its own waiter channel. A call whose context ends abandons the *)
(* slot: the slot stays busy until the late reply arrives and is dropped.  *)
(* A call that finds the slot abandoned waits up to abandonedRequestWait   *)
(* (one second) and then fails the connection. Replies carry no request    *)
(* identifier, so the slot is what binds a reply to its call.              *)
(*                                                                         *)
(* Questions:                                                              *)
(*   OwnAnswer          does a call ever receive another call's reply?     *)
(*   OneOutstanding     is more than one request ever unanswered?          *)
(*   DoneOnlyWhenIdle   is MsgDone written with a reply still owed?        *)
(*   NoStrayReply       does a reply arrive with no call waiting and no   *)
(*                      abandoned request to account for it?               *)
(*   Deadlock           TLC checks it.                                     *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [R1] ouroboros-consensus ec239d57f618, .../LeiosFetch/Type.hs         *)
(*        164-183: Idle(client) -request-> Block or BlockTxs (server)      *)
(*        -reply-> Idle; MsgDone only from Idle.                           *)
(*   [R2] .../LeiosFetch/Client.hs 70-168: each reply goes to the job      *)
(*        that sent it (its own receiver); on stop, outstanding replies    *)
(*        are collected and ignored, then MsgDone.                         *)
(*   [G1] gOuroboros 61046085, protocol/leiosfetch/client.go: requestSlot  *)
(*        (acquire, abandon, release, deliver), BlockRequest, Stop.        *)
(*   [G2] protocol/protocol.go sendLoop: MsgDone, and a request after it,  *)
(*        waits for agency; a request sent after MsgDone is never written. *)
(*                                                                         *)
(* Not modelled: reply validation (validateResponse), range streams (one   *)
(* reply stands for the terminal one), byte and count limits, timeouts.    *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Calls,          \* the calls, e.g. {"a", "b"}; each makes one request
    AbandonFrees,   \* FALSE in gOuroboros; TRUE is a mutation: abandon frees the slot
    GraceExpires    \* TRUE: a call waiting on an abandoned slot may give up (fails the connection)

\* Literally: "None is defined as "none"."
None == "none"   \* no call

VARIABLES
    pc,         \* pc[c]: "start", "send", "wait", "got", "gaveUp", "shutdown"
    got,        \* got[c]: whose reply call c received, or None
    busy,       \* the slot is held
    waiter,     \* the call the slot will hand the next reply to, or None
    abandoned,  \* the slot's request was abandoned and its reply is still due
    stopping,   \* Stop has run: MsgDone is queued
    c2s,        \* client-to-server messages in flight
    s2c,        \* server replies in flight, each naming the call it answers
    owed,       \* requests written and not yet answered
    srvQueue,   \* requests the server has read and not answered
    cli,        \* "Run", "Done", "Failed"
    stray,      \* a reply arrived that nothing accounted for
    doneEarly   \* MsgDone was written while a reply was owed

\* Literally: "vars is defined as the tuple of all thirteen variables."
vars == <<pc, got, busy, waiter, abandoned, stopping, c2s, s2c, owed,
          srvQueue, cli, stray, doneEarly>>

\* In English: "Every call is about to start with no reply, the slot is free,
\* Stop has not run, nothing is in flight or owed, and the client is running."
\* Literally: "Init is defined as: pc equals the function that maps every c in
\*   Calls to "start" and got equals the function that maps every c in Calls to
\*   None, and busy equals FALSE and waiter equals None and abandoned equals
\*   FALSE, and stopping equals FALSE and c2s equals the empty sequence and s2c
\*   equals the empty sequence and owed equals 0, and srvQueue equals the empty
\*   sequence and cli equals "Run" and stray equals FALSE and doneEarly equals
\*   FALSE."
Init ==
    /\ pc = [c \in Calls |-> "start"] /\ got = [c \in Calls |-> None]
    /\ busy = FALSE /\ waiter = None /\ abandoned = FALSE
    /\ stopping = FALSE /\ c2s = <<>> /\ s2c = <<>> /\ owed = 0
    /\ srvQueue = <<>> /\ cli = "Run" /\ stray = FALSE /\ doneEarly = FALSE

\* In English: "Call c takes the free slot and becomes its waiter [G1]."
\* Literally: "Acquire of c is defined as: cli equals "Run" and pc of c equals
\*   "start" and busy is not true, and busy in the next state equals TRUE and
\*   waiter in the next state equals c and abandoned in the next state equals
\*   FALSE, and pc in the next state equals pc except that its c entry is
\*   "send", and got, stopping, c2s, s2c, owed, srvQueue, cli, stray and
\*   doneEarly are unchanged."
Acquire(c) ==
    /\ cli = "Run" /\ pc[c] = "start" /\ ~busy
    /\ busy' = TRUE /\ waiter' = c /\ abandoned' = FALSE
    /\ pc' = [pc EXCEPT ![c] = "send"]
    /\ UNCHANGED <<got, stopping, c2s, s2c, owed, srvQueue, cli, stray, doneEarly>>

\* In English: "Call c finds the slot abandoned and gives up after the
\* grace period: it fails the connection [G1]."
\* Literally: "GiveUpOnAbandoned of c is defined as: GraceExpires is true and
\*   cli equals "Run" and pc of c equals "start" and busy is true and abandoned
\*   is true, and cli in the next state equals "Failed", and pc, got, busy,
\*   waiter, abandoned, stopping, c2s, s2c, owed, srvQueue, stray and doneEarly
\*   are unchanged."
GiveUpOnAbandoned(c) ==
    /\ GraceExpires /\ cli = "Run" /\ pc[c] = "start" /\ busy /\ abandoned
    /\ cli' = "Failed"
    /\ UNCHANGED <<pc, got, busy, waiter, abandoned, stopping, c2s, s2c, owed,
                   srvQueue, stray, doneEarly>>

\* In English: "Call c sends its request. It is written once the client
\* holds agency (no reply owed) [G2]. After MsgDone it is held for agency
\* that never returns, so it is not written."
\* Literally: "Send of c is defined as: cli equals "Run" and pc of c equals
\*   "send", and (stopping is true, or owed equals 0), and if stopping is true,
\*   then c2s and owed are unchanged, else c2s in the next state equals c2s
\*   with c appended and owed in the next state equals owed plus 1; and pc in
\*   the next state equals pc except that its c entry is "wait", and got, busy,
\*   waiter, abandoned, stopping, s2c, srvQueue, cli, stray and doneEarly are
\*   unchanged."
Send(c) ==
    /\ cli = "Run" /\ pc[c] = "send"
    /\ stopping \/ owed = 0                       \* the send loop waits for Idle
    /\ IF stopping
       THEN UNCHANGED <<c2s, owed>>
       ELSE c2s' = Append(c2s, c) /\ owed' = owed + 1
    /\ pc' = [pc EXCEPT ![c] = "wait"]
    /\ UNCHANGED <<got, busy, waiter, abandoned, stopping, s2c, srvQueue, cli,
                   stray, doneEarly>>

\* In English: "Call c's context ends while it waits: it abandons the
\* slot. In gOuroboros the slot stays busy until the late reply drains it;
\* the AbandonFrees mutation frees it at once."
\* Literally: "Abandon of c is defined as: cli equals "Run" and pc of c equals
\*   "wait" and waiter equals c, and waiter in the next state equals None, and
\*   if AbandonFrees is true, then busy in the next state equals FALSE and
\*   abandoned is unchanged, else abandoned in the next state equals TRUE and
\*   busy is unchanged; and pc in the next state equals pc except that its c
\*   entry is "gaveUp", and got, stopping, c2s, s2c, owed, srvQueue, cli, stray
\*   and doneEarly are unchanged."
Abandon(c) ==
    /\ cli = "Run" /\ pc[c] = "wait" /\ waiter = c
    /\ waiter' = None
    /\ IF AbandonFrees
       THEN busy' = FALSE /\ UNCHANGED abandoned
       ELSE abandoned' = TRUE /\ UNCHANGED busy
    /\ pc' = [pc EXCEPT ![c] = "gaveUp"]
    /\ UNCHANGED <<got, stopping, c2s, s2c, owed, srvQueue, cli, stray, doneEarly>>

\* In English: "Stop, once: MsgDone is queued. It is written when no reply
\* is owed (Idle) [R1][G2]."
\* Literally: "Stop is defined as: cli equals "Run" and stopping is not true,
\*   and stopping in the next state equals TRUE, and pc, got, busy, waiter,
\*   abandoned, c2s, s2c, owed, srvQueue, cli, stray and doneEarly are
\*   unchanged."
Stop ==
    /\ cli = "Run" /\ ~stopping
    /\ stopping' = TRUE
    /\ UNCHANGED <<pc, got, busy, waiter, abandoned, c2s, s2c, owed, srvQueue,
                   cli, stray, doneEarly>>

\* In English: "The queued MsgDone goes out once the client is in Idle."
\* Literally: "WriteDone is defined as: cli equals "Run" and stopping is true
\*   and owed equals 0, and for all i in 1 through the length of c2s, element i
\*   of c2s does not equal "Done", and c2s in the next state equals c2s with
\*   "Done" appended, and cli in the next state equals "Done", and doneEarly in
\*   the next state equals (doneEarly, or owed is greater than 0), and pc, got,
\*   busy, waiter, abandoned, stopping, s2c, owed, srvQueue and stray are
\*   unchanged."
WriteDone ==
    /\ cli = "Run" /\ stopping /\ owed = 0
    /\ \A i \in 1..Len(c2s) : c2s[i] /= "Done"
    /\ c2s' = Append(c2s, "Done")
    /\ cli' = "Done"
    /\ doneEarly' = (doneEarly \/ owed > 0)
    /\ UNCHANGED <<pc, got, busy, waiter, abandoned, stopping, s2c, owed,
                   srvQueue, stray>>

\* In English: "The server reads the oldest request and answers it later,
\* in order. MsgDone ends its run."
\* Literally: "ServerRead is defined as: c2s does not equal the empty sequence
\*   and the head of c2s does not equal "Done", and srvQueue in the next state
\*   equals srvQueue with the head of c2s appended, and c2s in the next state
\*   equals the tail of c2s, and pc, got, busy, waiter, abandoned, stopping,
\*   s2c, owed, cli, stray and doneEarly are unchanged."
ServerRead ==
    /\ c2s /= <<>> /\ Head(c2s) /= "Done"
    /\ srvQueue' = Append(srvQueue, Head(c2s))
    /\ c2s' = Tail(c2s)
    /\ UNCHANGED <<pc, got, busy, waiter, abandoned, stopping, s2c, owed, cli,
                   stray, doneEarly>>

\* In English: "The server answers the oldest request it has read."
\* Literally: "ServerAnswer is defined as: srvQueue does not equal the empty
\*   sequence, and s2c in the next state equals s2c with the head of srvQueue
\*   appended, and srvQueue in the next state equals the tail of srvQueue, and
\*   pc, got, busy, waiter, abandoned, stopping, c2s, owed, cli, stray and
\*   doneEarly are unchanged."
ServerAnswer ==
    /\ srvQueue /= <<>>
    /\ s2c' = Append(s2c, Head(srvQueue))
    /\ srvQueue' = Tail(srvQueue)
    /\ UNCHANGED <<pc, got, busy, waiter, abandoned, stopping, c2s, owed, cli,
                   stray, doneEarly>>

\* In English: "The client handles the oldest reply (deliver): it goes to
\* the slot's waiter and frees the slot; with no waiter but an abandoned
\* request, it is dropped and frees the slot; otherwise it is stray."
\* Literally: "ClientRecv is defined as: cli equals "Run" and s2c does not
\*   equal the empty sequence, and, letting r be the head of s2c: if waiter
\*   does not equal None, then got in the next state equals got except that its
\*   waiter entry is r, and busy in the next state equals FALSE and waiter in
\*   the next state equals None, and abandoned and stray are unchanged; else if
\*   busy is true and abandoned is true, then busy in the next state equals
\*   FALSE and abandoned in the next state equals FALSE, and got, waiter and
\*   stray are unchanged; else stray in the next state equals TRUE, and got,
\*   busy, waiter and abandoned are unchanged; and s2c in the next state equals
\*   the tail of s2c, and owed in the next state equals owed minus 1, and pc,
\*   stopping, c2s, srvQueue, cli and doneEarly are unchanged."
ClientRecv ==
    /\ cli = "Run" /\ s2c /= <<>>
    /\ LET r == Head(s2c) IN
       IF waiter /= None
       THEN /\ got' = [got EXCEPT ![waiter] = r]
            /\ busy' = FALSE /\ waiter' = None
            /\ UNCHANGED <<abandoned, stray>>
       ELSE IF busy /\ abandoned
            THEN /\ busy' = FALSE /\ abandoned' = FALSE
                 /\ UNCHANGED <<got, waiter, stray>>
            ELSE /\ stray' = TRUE
                 /\ UNCHANGED <<got, busy, waiter, abandoned>>
    /\ s2c' = Tail(s2c)
    /\ owed' = owed - 1
    /\ UNCHANGED <<pc, stopping, c2s, srvQueue, cli, doneEarly>>

\* In English: "A call with a reply returns."
\* Literally: "Return of c is defined as: pc of c equals "wait" and got of c
\*   does not equal None, and pc in the next state equals pc except that its c
\*   entry is "got", and got, busy, waiter, abandoned, stopping, c2s, s2c,
\*   owed, srvQueue, cli, stray and doneEarly are unchanged."
Return(c) ==
    /\ pc[c] = "wait" /\ got[c] /= None
    /\ pc' = [pc EXCEPT ![c] = "got"]
    /\ UNCHANGED <<got, busy, waiter, abandoned, stopping, c2s, s2c, owed,
                   srvQueue, cli, stray, doneEarly>>

\* In English: "Once the protocol is over, a waiting call returns
\* ErrProtocolShuttingDown (DoneChan)."
\* Literally: "Shutdown of c is defined as: cli does not equal "Run" and pc of
\*   c is a member of the set containing "start", "send" and "wait" and got of
\*   c equals None, and pc in the next state equals pc except that its c entry
\*   is "shutdown", and got, busy, waiter, abandoned, stopping, c2s, s2c, owed,
\*   srvQueue, cli, stray and doneEarly are unchanged."
Shutdown(c) ==
    /\ cli /= "Run" /\ pc[c] \in {"start", "send", "wait"} /\ got[c] = None
    /\ pc' = [pc EXCEPT ![c] = "shutdown"]
    /\ UNCHANGED <<got, busy, waiter, abandoned, stopping, c2s, s2c, owed,
                   srvQueue, cli, stray, doneEarly>>

\* In English: "Every call has returned and the protocol is over."
\* Literally: "Finished is defined as: for all c in Calls, pc of c is a member
\*   of the set containing "got", "gaveUp" and "shutdown", and cli does not
\*   equal "Run"."
Finished ==
    /\ \A c \in Calls : pc[c] \in {"got", "gaveUp", "shutdown"}
    /\ cli /= "Run"

\* In English: "A step is some call's step, Stop, MsgDone being written, a
\* server step, the client reading a reply, or, once finished, nothing."
\* Literally: "Next is defined as: there exists a c in Calls such that Acquire
\*   of c, or GiveUpOnAbandoned of c, or Send of c, or Abandon of c, or Return
\*   of c, or Shutdown of c; or Stop, or WriteDone, or ServerRead, or
\*   ServerAnswer, or ClientRecv; or Finished is true and vars is unchanged."
Next ==
    \/ \E c \in Calls : Acquire(c) \/ GiveUpOnAbandoned(c) \/ Send(c)
                         \/ Abandon(c) \/ Return(c) \/ Shutdown(c)
    \/ Stop \/ WriteDone \/ ServerRead \/ ServerAnswer \/ ClientRecv
    \/ Finished /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Whatever reply a call received answers its own request."
\* Literally: "OwnAnswer is defined as: for all c in Calls, got of c is a
\*   member of the set containing None and c."
OwnAnswer == \A c \in Calls : got[c] \in {None, c}

\* In English: "At most one request is unanswered at a time [R1]: the
\* client never writes without agency."
\* Literally: "OneOutstanding is defined as: owed is less than or equal to 1."
OneOutstanding == owed <= 1

\* In English: "MsgDone was never written with a reply owed [R1]."
\* Literally: "DoneOnlyWhenIdle is defined as: doneEarly is not true."
DoneOnlyWhenIdle == ~doneEarly

\* In English: "Every reply was accounted for."
\* Literally: "NoStrayReply is defined as: stray is not true."
NoStrayReply == ~stray

\* Probes, EXPECTED to be violated.
\* In English: "No call ever abandons the slot and has its late reply
\* dropped while another call waits for the slot."
\* Literally: "ProbeNoLateDrain is defined as: it is not the case that
\*   (abandoned is true and there exists a c in Calls such that pc of c equals
\*   "start")."
ProbeNoLateDrain == ~(abandoned /\ \E c \in Calls : pc[c] = "start")
\* In English: "No call ever gets its reply."
\* Literally: "ProbeNoReply is defined as: for all c in Calls, pc of c does not
\*   equal "got"."
ProbeNoReply == \A c \in Calls : pc[c] /= "got"
=============================================================================
