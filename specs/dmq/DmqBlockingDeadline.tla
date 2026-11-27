-------------------------- MODULE DmqBlockingDeadline --------------------------
(***************************************************************************)
(* DMQ message submission's time limits as ordered deadlines: does a side *)
(* ever time out a peer that is waiting as the reference allows?           *)
(*                                                                         *)
(* One round, between a requesting side (the inbound) and an answering     *)
(* side (the outbound). The inbound stays in StIdle for IdleWait, then     *)
(* sends a blocking request for ids. The outbound answers when a message   *)
(* arrives in its mempool, or, in V2, with MsgReplyNoSigIds after          *)
(* AnswerNoneAt. Each side's protocol engine times only the states in      *)
(* which the other side has agency: the outbound times StIdle (IdleLimit),*)
(* the inbound times the blocking request (WaitLimit). Zero means untimed.*)
(*                                                                         *)
(* Two pairings:                                                           *)
(*   the gOuroboros Server as the inbound against dmq-node's outbound:     *)
(*     WaitLimit is the Server's MessageIdsBlockingTimeout (30 s in both   *)
(*     state maps on 7cd17437); dmq-node's outbound answers V2 with none   *)
(*     after 17 s and in V1 waits until it has an id; it does not time    *)
(*     StIdle.                                                             *)
(*   dmq-node's inbound against the gOuroboros Client as the outbound:     *)
(*     WaitLimit is dmq-node's (V2 20 s, V1 none); the Client's            *)
(*     application answers none (ReplyNoMessageIds) after AnswerNoneAt;    *)
(*     the Client times StIdle at IdleTimeout (300 s).                     *)
(*                                                                         *)
(* Time. `now` is in seconds and moves straight to the next deadline (an   *)
(* event-driven clock), so long durations cost no states. Deadlines that   *)
(* coincide fire in either order.                                          *)
(*                                                                         *)
(* Invariant: NoTimeoutOfConformingPeer: neither timer fires.              *)
(*                                                                         *)
(* Sources.                                                                *)
(*   [R1] dmq-node a267003c dmq-node/src/DMQ/Protocol/SigSubmission/       *)
(*        Codec.hs 60-78: V1 limits: StIdle and blocking StTxIds           *)
(*        waitForever, non-blocking and StTxs shortWait.                   *)
(*   [R2] dmq-node a267003c dmq-node/src/DMQ/Protocol/SigSubmissionV2/     *)
(*        Codec.hs 70-95: V2 limits: StIdle waitForever, blocking 20 s.    *)
(*   [R3] dmq-node a267003c dmq-node/src/DMQ/SigSubmissionV2/Outbound.hs   *)
(*        121-155: the V2 outbound answers a blocking request with         *)
(*        MsgReplyNoSigIds after 17 s; NodeToNode.hs 290-307: the V1       *)
(*        outbound is ouroboros-network's txSubmissionOutbound, which      *)
(*        blocks until its mempool has an id (ouroboros-network 4646039f   *)
(*        .../TxSubmission/Outbound.hs 138-160) and has no such answer.    *)
(*   [G1] gOuroboros 7cd17437 protocol/messagesubmission/                  *)
(*        messagesubmission.go 36-41 (timeouts), stateMapV1 and stateMapV2 *)
(*        (StMessageIdsBlocking: MessageIdsBlockingTimeout, 30 s); the     *)
(*        Server installs the state map as is (server.go initProtocol),    *)
(*        the Client copies it with its Config's timeouts (client.go       *)
(*        NewClient).                                                      *)
(*   [G2] gOuroboros 7cd17437 protocol/protocol.go stateLoop armTimeout:   *)
(*        a state's Timeout is armed only while the peer has agency, and a *)
(*        timeout fails the protocol (SendError).                          *)
(*   UNSOURCED: how long dmq-node's inbound may stay in StIdle. Its        *)
(*        scheduler parks on awaitSharedChange (SigSubmissionV2/Inbound.hs *)
(*        122-136) with no upper bound in the source; IdleWait is a        *)
(*        parameter, and the configs show both sides of IdleLimit.         *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    IdleWait,     \* when the inbound sends its blocking request
    IdleLimit,    \* the outbound's timer on StIdle (0: untimed)
    WaitLimit,    \* the inbound's timer on the blocking request, from when it is sent (0: untimed)
    AnswerNoneAt, \* how long after the request the outbound answers with none (0: never; V1 has no such answer)
    Arrivals,     \* times at which a message may first enter the outbound's mempool
    Never         \* a time after every deadline: "this does not happen"

VARIABLES
    now,      \* the clock
    phase,    \* "idle", "blocking", "answered" or "timedOut"
    sentAt,   \* when the blocking request was sent
    arrival,  \* when a message enters the outbound's mempool (Never: not in this round)
    who       \* which timer fired: "", "outbound" (StIdle) or "inbound" (blocking)

vars == <<now, phase, sentAt, arrival, who>>

\* In English: "A deadline d after `from`, or Never when the duration is
\* zero (untimed)."
Deadline(from, d) == IF d = 0 THEN Never ELSE from + d

\* In English: "The times at which something is due in the current phase."
Due ==
    IF phase = "idle" THEN {IdleWait, Deadline(0, IdleLimit)}
    ELSE IF phase = "blocking"
         THEN {Deadline(sentAt, WaitLimit), Deadline(sentAt, AnswerNoneAt),
               IF arrival < sentAt THEN sentAt ELSE arrival}
    ELSE {}

\* In English: "The earliest time something is due, or Never."
NextDue == IF Due = {} THEN Never ELSE CHOOSE t \in Due : \A u \in Due : t <= u

\* In English: "Start at time 0 in StIdle; a message arrives at one of the
\* Arrivals, or never."
Init ==
    /\ now = 0 /\ phase = "idle" /\ sentAt = 0 /\ who = ""
    /\ arrival \in Arrivals \cup {Never}

\* In English: "The clock moves to the next deadline when nothing is due
\* now."
Tick ==
    /\ phase \in {"idle", "blocking"}
    /\ NextDue < Never /\ now < NextDue
    /\ now' = NextDue
    /\ UNCHANGED <<phase, sentAt, arrival, who>>

\* In English: "The inbound sends its blocking request at IdleWait."
SendRequest ==
    /\ phase = "idle" /\ now = IdleWait
    /\ phase' = "blocking" /\ sentAt' = now
    /\ UNCHANGED <<now, arrival, who>>

\* In English: "The outbound's timer on StIdle fires [G2]."
IdleTimeout ==
    /\ phase = "idle" /\ now = Deadline(0, IdleLimit)
    /\ phase' = "timedOut" /\ who' = "outbound"
    /\ UNCHANGED <<now, sentAt, arrival>>

\* In English: "The outbound answers with ids once a message has arrived
\* [R3]."
AnswerIds ==
    /\ phase = "blocking" /\ arrival <= now
    /\ phase' = "answered"
    /\ UNCHANGED <<now, sentAt, arrival, who>>

\* In English: "In V2 the outbound answers with none after AnswerNoneAt
\* [R3]."
AnswerNone ==
    /\ phase = "blocking" /\ now = Deadline(sentAt, AnswerNoneAt)
    /\ phase' = "answered"
    /\ UNCHANGED <<now, sentAt, arrival, who>>

\* In English: "The inbound's timer on the blocking request fires [G2]."
WaitTimeout ==
    /\ phase = "blocking" /\ now = Deadline(sentAt, WaitLimit)
    /\ phase' = "timedOut" /\ who' = "inbound"
    /\ UNCHANGED <<now, sentAt, arrival>>

\* In English: "The round is over, or nothing is ever due again."
Quiet ==
    /\ phase \in {"answered", "timedOut"} \/ NextDue = Never
    /\ UNCHANGED vars

Next ==
    \/ Tick \/ SendRequest \/ IdleTimeout
    \/ AnswerIds \/ AnswerNone \/ WaitTimeout
    \/ Quiet

Spec == Init /\ [][Next]_vars

\* In English: "Every variable holds a value of the expected kind."
TypeOK ==
    /\ now \in 0..Never
    /\ phase \in {"idle", "blocking", "answered", "timedOut"}
    /\ who \in {"", "outbound", "inbound"}

\* In English: "No timer fires: each side waits as long as the reference
\* allows the other to take."
NoTimeoutOfConformingPeer == phase # "timedOut"
=============================================================================
