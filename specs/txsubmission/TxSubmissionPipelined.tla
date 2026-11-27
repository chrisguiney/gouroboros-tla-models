------------------------- MODULE TxSubmissionPipelined -------------------------
(***************************************************************************)
(* A PIPELINED inbound side against the gOuroboros outbound side, for     *)
(* tx-submission and for DMQ message submission, which shares its window  *)
(* rules (DMQ V1 is tx-submission; V2 keeps the same request rules).      *)
(*                                                                         *)
(* TxSubmission.tla checks one request at a time, because the gOuroboros  *)
(* inbound (Server) never pipelines. The reference inbound does: it sends *)
(* further requests for ids and for bodies before the replies to earlier   *)
(* ones arrive, and the outbound answers them in order. The inbound must  *)
(* then compute every acknowledgement and every request count from a view *)
(* that lacks the replies still in flight. This module asks whether the    *)
(* gOuroboros outbound (Client) accepts every request such an inbound      *)
(* sends, and whether the two views stay consistent.                       *)
(*                                                                         *)
(* Questions (invariants):                                                 *)
(*   HonestNeverRefused  the outbound never refuses a request of an honest *)
(*                       inbound, so the connection is not torn down.     *)
(*   OutboundWithinWindow, InboundWithinWindow  neither window is exceeded.*)
(*   ViewIsPrefix        the inbound's queue is a prefix of the outbound's *)
(*                       once the acknowledgements in flight are applied.  *)
(*   AckedAtMostOnce     an id leaves the outbound's window once.          *)
(*   AckedOnlyAnnounced  only announced ids are ever acknowledged.         *)
(*   NothingBehindBlocking  a blocking request is the only one outstanding.*)
(*   DoneOnlyWhenIdle    MsgDone is sent only with nothing outstanding.    *)
(*                                                                         *)
(* Sources.                                                                *)
(*   Reference inbound, IntersectMBO/ouroboros-network 4646039f05eb (the   *)
(*   ouroboros-network 2.0.0.0 that dmq-node a267003c builds against):     *)
(*   [R1] ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/    *)
(*        V2/State.hs 480-561 pickRequestTxIdsAction: ack the longest      *)
(*        ackable prefix; while pipelining keep one id unacknowledged     *)
(*        whenever ids or bodies are in flight (538-548); a pipelined      *)
(*        request must ask for something (501) and needs a non-empty queue *)
(*        (508); request min(window - (unacked + requested) + acked,       *)
(*        maxNumTxIdsToRequest - requested) (558-561).                     *)
(*   [R2] dmq-node a267003c dmq-node/src/DMQ/SigSubmissionV2/Inbound.hs    *)
(*        103-142 serverIdle: MsgDone only at depth zero (106, 135);       *)
(*        258-301 serverReqSigIds: a blocking request only at depth zero   *)
(*        with an empty queue after the acknowledgement (274-289), every   *)
(*        other request pipelined; 199-218 body requests are pipelined;    *)
(*        304-363 replies are collected in order.                          *)
(*   [R3] dmq-node a267003c dmq-node/src/DMQ/Policy.hs 83-102:            *)
(*        maxSigIdsInflight = 33, maxUnacknowledgedTxIds = 4 * 33 = 132,   *)
(*        maxOutstandingTxBatchesPerPeer = 4. NodeToNode.hs 229, 305, 326: *)
(*        the same 132 is the inbound's window and the window its V1 and   *)
(*        V2 outbounds check.                                              *)
(*   [R4] dmq-node a267003c dmq-node/src/DMQ/SigSubmissionV2/Outbound.hs   *)
(*        90-169 and ouroboros-network 4646039f .../TxSubmission/          *)
(*        Outbound.hs: the outbound's checks (AckedTooMany, RequestedTooMany*)
(*        against its own window, RequestedNothing, RequestBlocking,       *)
(*        RequestNonBlocking); 171-211 bodies must be unacknowledged ids,  *)
(*        distinct, and (V2) not asked for before.                         *)
(*   [R5] ouroboros-network 4646039f .../Protocol/TxSubmission2/Type.hs    *)
(*        and dmq-node .../Protocol/SigSubmissionV2/Type.hs 162-208: ids   *)
(*        are acknowledged in FIFO order; blocking MUST be used exactly    *)
(*        when no ids remain.                                              *)
(*   gOuroboros 7cd17437:                                                  *)
(*   [G1] protocol/messagesubmission/client.go handleRequestMessageIds,    *)
(*        handleRequestMessages, ReplyMessageIds, ReplyNoMessageIds,       *)
(*        ReplyMessages; validation.go validateMessageIDRequest,           *)
(*        requestedMessagesAreOutstanding, forgetAcknowledgedIDs;          *)
(*        messagesubmission.go DefaultMaxUnacknowledgedMessageIDs = 100.   *)
(*   [G2] protocol/txsubmission/client.go handleRequestTxIds,              *)
(*        handleRequestTxs (MaxUnackedTxIds = 10, the reference's          *)
(*        txSubmissionMaxUnacked).                                         *)
(*   [G3] protocol/protocol.go recvLoop: a request the peer pipelined is   *)
(*        handled only once the peer holds agency again, that is after     *)
(*        the reply to the request before it was sent.                     *)
(*   [G4] protocol/messagesubmission/server.go requestMessageIDs,          *)
(*        RequestMessages, Done: one request at a time; MsgDone is sent    *)
(*        by the engine only from StIdle.                                  *)
(*   UNSOURCED: the reference inbound's back-off after an empty reply      *)
(*        (State.hs 510-515) and its scheduling (which peer downloads a    *)
(*        body) only suppress requests, so the model leaves them out and   *)
(*        lets the inbound send any request [R1] allows: a superset.       *)
(*                                                                         *)
(* The outbound here refuses an oversized request, as before NodeToNodeV_16*)
(* and as DMQ does; a tx-submission client from V16 clamps instead         *)
(* (TxSubmission.tla), which only accepts more.                            *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    InWindow,    \* the inbound's window: 132 in dmq-node, 10 in cardano-node
    OutWindow,   \* the outbound's window: 100 in gOuroboros DMQ, 10 for tx-submission
    MaxReq,      \* ids the inbound may have requested and not yet received (33 in dmq-node)
    MaxBatches,  \* body requests the inbound may have outstanding (4)
    MaxIds,      \* fresh ids the outbound's mempool can offer in total
    Version,     \* "V1": no MsgReplyNoSigIds; "V2": the outbound may answer a blocking request with none
    Inbound,     \* "reference": pipelines as [R1]/[R2]; "gouroboros": the Server [G4], one at a time
    \* Mutations that remove one safeguard, to show an invariant can fail:
    \* "ackAll" (the inbound acknowledges its whole ackable prefix while
    \* pipelining), "noDefer" (the outbound handles a pipelined request
    \* before it has answered the one before), "doneAnyTime" (MsgDone leaves
    \* while requests are outstanding).
    Mutation

\* In English: "The ids a queue holds, as a set."
Range(s) == {s[i] : i \in 1..Len(s)}

\* In English: "The queue without its first a ids."
Drop(s, a) == SubSeq(s, a + 1, Len(s))

\* In English: "The smaller and the larger of two numbers."
Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

\* In English: "The sum of a function's values over a finite set of keys."
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

\* In English: "k fresh ids, starting at `from`."
Fresh(from, k) == [i \in 1..k |-> from + i - 1]

\* In English: "Nothing is being answered."
None == [kind |-> "none", blocking |-> FALSE, ack |-> 0, req |-> 0, ids |-> {}]

\* In English: "A request for ids, and a request for bodies, as one record
\* shape so that both fit in one queue."
IdsReq(b, a, n) == [kind |-> "ids", blocking |-> b, ack |-> a, req |-> n, ids |-> {}]
BodiesReq(S)    == [kind |-> "bodies", blocking |-> FALSE, ack |-> 0, req |-> 0, ids |-> S]

VARIABLES
    toOut,     \* requests sent by the inbound and not yet handled, oldest first
    pending,   \* the request the outbound has handled and not yet answered, or None
    toIn,      \* replies sent by the outbound and not yet collected, oldest first
    inQ,       \* the inbound's queue of unacknowledged ids, after its own acknowledgements
    inReq,     \* ids the inbound has requested and not yet received ("requested" in [R1])
    inBatches, \* body requests the inbound has outstanding
    ackable,   \* ids the inbound has resolved (body received or not wanted) and may acknowledge
    asked,     \* ids whose bodies the inbound has requested
    outQ,      \* the outbound's window (gO Client.pendingMessageIDs / unackedTxIds)
    delivered, \* ids whose bodies the outbound was asked for and are unacknowledged (gO requestedIDs)
    nextId,    \* the next fresh id the outbound's mempool offers
    ackCount,  \* how many times the outbound dropped each id from its window
    refused,   \* "" or why the outbound refused a request (the connection then ends)
    done       \* the inbound has sent MsgDone

vars == <<toOut, pending, toIn, inQ, inReq, inBatches, ackable, asked,
          outQ, delivered, nextId, ackCount, refused, done>>

Ids == 1..MaxIds

\* In English: "Requests and replies outstanding: the pipelining depth."
Depth == Len(toOut) + (IF pending = None THEN 0 ELSE 1) + Len(toIn)

\* In English: "The number of ids at the front of the inbound's queue that
\* it has resolved: the longest prefix it may acknowledge [R1]."
AckablePrefix ==
    CHOOSE n \in 0..Len(inQ) :
        /\ \A i \in 1..n : inQ[i] \in ackable
        /\ (n = Len(inQ) \/ inQ[n + 1] \notin ackable)

\* In English: "Nothing has happened yet: both queues are empty."
Init ==
    /\ toOut = <<>> /\ pending = None /\ toIn = <<>>
    /\ inQ = <<>> /\ inReq = 0 /\ inBatches = 0
    /\ ackable = {} /\ asked = {}
    /\ outQ = <<>> /\ delivered = {}
    /\ nextId = 1
    /\ ackCount = [i \in Ids |-> 0]
    /\ refused = ""
    /\ done = FALSE

\* In English: "The inbound may act: no refusal ended the connection and it
\* has not sent MsgDone."
Live == refused = "" /\ ~done

-----------------------------------------------------------------------------
(* The inbound. *)

\* In English: "Send a request with this blocking flag, acknowledgement and
\* count: apply the acknowledgement to the inbound's own queue at once, count
\* the ids requested, and put the request on the wire."
SendIds(b, a, n) ==
    /\ inQ' = Drop(inQ, a)
    /\ inReq' = inReq + n
    /\ toOut' = Append(toOut, IdsReq(b, a, n))

\* In English: "The reference inbound asks for ids [R1], [R2]. With nothing
\* outstanding it is not pipelining and may acknowledge its whole ackable
\* prefix; the request is blocking exactly when that leaves its queue
\* empty. Otherwise it pipelines a non-blocking request, which must ask for
\* something, needs a non-empty queue, and keeps one id unacknowledged
\* while ids or bodies are in flight."
RefSendIds ==
    /\ Live
    /\ LET pipelining == Depth > 0
           keepOne    == pipelining /\ (inReq > 0 \/ inBatches > 0)    \* [R1] 538-540
           acked      == IF keepOne /\ "ackAll" \notin Mutation
                         THEN Min(AckablePrefix, Max(0, Len(inQ) - 1))   \* [R1] 546-547
                         ELSE AckablePrefix
           n          == Max(0, Min(InWindow - (Len(inQ) + inReq) + acked,
                                    MaxReq - inReq))                     \* [R1] 558-561
           blocking   == ~pipelining /\ Len(inQ) - acked = 0              \* [R2] 274-289
       IN /\ ~(acked = 0 /\ n = 0)                                       \* [R1] 484
          /\ pipelining => n > 0 /\ Len(inQ) > 0                         \* [R1] 501, 508
          /\ SendIds(blocking, acked, n)
    /\ UNCHANGED <<pending, toIn, inBatches, ackable, asked, outQ, delivered,
                   nextId, ackCount, refused, done>>

\* In English: "The reference inbound asks for the bodies of some ids in its
\* queue it has neither resolved nor asked for, pipelined, while fewer than
\* MaxBatches body requests are outstanding [R2] 199-218."
RefSendBodies ==
    /\ Live
    /\ inBatches < MaxBatches
    /\ \E S \in SUBSET (Range(inQ) \ (ackable \cup asked)) :
        /\ S # {}
        /\ asked' = asked \cup S
        /\ inBatches' = inBatches + 1
        /\ toOut' = Append(toOut, BodiesReq(S))
    /\ UNCHANGED <<pending, toIn, inQ, inReq, ackable, outQ, delivered,
                   nextId, ackCount, refused, done>>

\* In English: "The inbound resolves an id without its body: already in its
\* mempool, or fetched from another peer. It may then acknowledge it."
RefResolve ==
    /\ Live
    /\ \E i \in Range(inQ) \ (ackable \cup asked) :
        ackable' = ackable \cup {i}
    /\ UNCHANGED <<toOut, pending, toIn, inQ, inReq, inBatches, asked, outQ,
                   delivered, nextId, ackCount, refused, done>>

\* In English: "The gOuroboros Server asks for ids only with nothing
\* outstanding [G4], with any counts its own check
\* (validateMessageIDRequest) allows against its window."
GoSendIds ==
    /\ Live
    /\ Depth = 0
    /\ \E b \in BOOLEAN, a \in 0..Len(inQ), n \in 0..InWindow :
        /\ n > 0 \/ (~b /\ a > 0)                 \* counts rule
        /\ b => Len(inQ) - a = 0                  \* blocking leaves nothing
        /\ ~b => Len(inQ) - a > 0                 \* non-blocking leaves something
        /\ Len(inQ) - a + n <= InWindow           \* the window
        /\ SendIds(b, a, n)
    /\ UNCHANGED <<pending, toIn, inBatches, ackable, asked, outQ, delivered,
                   nextId, ackCount, refused, done>>

\* In English: "The gOuroboros Server asks for bodies of ids in its queue,
\* only with nothing outstanding; in V2 not for an id it asked for before
\* (requestedMessagesAreOutstanding with requestedIDs) [G4]."
GoSendBodies ==
    /\ Live
    /\ Depth = 0
    /\ \E S \in SUBSET (Range(inQ) \ (IF Version = "V2" THEN asked ELSE {})) :
        /\ S # {}
        /\ asked' = asked \cup S
        /\ inBatches' = inBatches + 1
        /\ toOut' = Append(toOut, BodiesReq(S))
    /\ UNCHANGED <<pending, toIn, inQ, inReq, ackable, outQ, delivered,
                   nextId, ackCount, refused, done>>

\* In English: "The inbound collects the oldest reply. New ids join the end
\* of its queue and stop counting as requested; a body reply resolves every
\* id it was asked for, received or not."
Collect ==
    /\ refused = ""
    /\ toIn # <<>>
    /\ LET r == Head(toIn) IN
        /\ toIn' = Tail(toIn)
        /\ inQ' = inQ \o r.new
        /\ inReq' = inReq - r.req
        /\ inBatches' = IF r.kind = "bodies" THEN inBatches - 1 ELSE inBatches
        /\ ackable' = IF r.kind = "bodies" THEN ackable \cup r.ids ELSE ackable
    /\ UNCHANGED <<toOut, pending, asked, outQ, delivered, nextId, ackCount,
                   refused, done>>

\* In English: "The inbound ends the run with MsgDone (V2): only from StIdle
\* with nothing outstanding [R2] 106, 135; the gOuroboros engine holds a
\* MsgDone sent earlier until then [G4]."
SendDone ==
    /\ Live
    /\ Version = "V2"
    /\ Depth = 0 \/ "doneAnyTime" \in Mutation
    /\ done' = TRUE
    /\ UNCHANGED <<toOut, pending, toIn, inQ, inReq, inBatches, ackable, asked,
                   outQ, delivered, nextId, ackCount, refused>>

-----------------------------------------------------------------------------
(* The gOuroboros outbound (Client). *)

\* In English: "Why the outbound refuses MsgRequestIds(b, a, n), or "" if it
\* accepts it. validateMessageIDRequest [G1] and handleRequestTxIds [G2]
\* make the reference outbound's checks [R4], against OutWindow."
IdsRefusal(r) ==
    LET remaining == Len(outQ) - r.ack IN
    IF r.ack > Len(outQ) THEN "ackedTooMany"
    ELSE IF (r.blocking /\ r.req = 0) \/ (~r.blocking /\ r.ack = 0 /\ r.req = 0)
         THEN "requestedNothing"
    ELSE IF r.blocking /\ remaining # 0 THEN "requestBlocking"
    ELSE IF ~r.blocking /\ remaining = 0 THEN "requestNonBlocking"
    ELSE IF remaining + r.req > OutWindow THEN "requestedTooMany"
    ELSE ""

\* In English: "Why the outbound refuses a request for bodies, or "": the
\* ids must be in its window and, in V2, not asked for before
\* (requestedMessagesAreOutstanding [G1], [R4] 171-211)."
BodiesRefusal(r) ==
    IF ~(r.ids \subseteq Range(outQ)) THEN "unavailable"
    ELSE IF Version = "V2" /\ r.ids \cap delivered # {} THEN "duplicateRequest"
    ELSE ""

\* In English: "The outbound's handler takes the oldest request. The engine
\* runs it only after the previous request was answered [G3]; a handler that
\* ran earlier finds that request still pending and refuses ("a request is
\* already pending" [G1]). Otherwise it judges the request, and a refusal
\* ends the connection."
Handle ==
    /\ refused = ""
    /\ toOut # <<>>
    /\ pending = None \/ "noDefer" \in Mutation
    /\ LET r   == Head(toOut)
           why == IF pending # None THEN "alreadyPending"
                  ELSE IF r.kind = "ids" THEN IdsRefusal(r)
                  ELSE BodiesRefusal(r)
       IN /\ toOut' = Tail(toOut)
          /\ IF why = ""
             THEN /\ pending' = r
                  /\ refused' = ""
                  /\ delivered' = IF r.kind = "bodies" THEN delivered \cup r.ids
                                  ELSE delivered
             ELSE /\ refused' = why
                  /\ UNCHANGED <<pending, delivered>>
    /\ UNCHANGED <<toIn, inQ, inReq, inBatches, ackable, asked, outQ, nextId,
                   ackCount, done>>

\* In English: "Fresh ids the mempool can still offer."
Available == MaxIds + 1 - nextId

\* In English: "The outbound answers a request for ids with k fresh ids: it
\* drops the acknowledged ids from the front of its window (and forgets that
\* their bodies were asked for, forgetAcknowledgedIDs [G1]) and appends the
\* new ones. A blocking request is answered with at least one id; in V2 it
\* may instead be answered with none (MsgReplyNoSigIds)."
ReplyIds ==
    /\ refused = ""
    /\ pending.kind = "ids"
    /\ \E k \in 0..Min(pending.req, Available) :
        /\ pending.blocking => (k > 0 \/ Version = "V2")
        /\ LET acked == SubSeq(outQ, 1, pending.ack)
               new   == Fresh(nextId, k)
           IN /\ outQ' = Drop(outQ, pending.ack) \o new
              /\ delivered' = delivered \ Range(acked)
              /\ ackCount' = [i \in Ids |-> IF i \in Range(acked)
                                            THEN ackCount[i] + 1
                                            ELSE ackCount[i]]
              /\ nextId' = nextId + k
              /\ toIn' = Append(toIn, [kind |-> IF k = 0 /\ pending.blocking
                                                THEN "noids" ELSE "ids",
                                       req |-> pending.req, new |-> new,
                                       ids |-> {}])
    /\ pending' = None
    /\ UNCHANGED <<toOut, inQ, inReq, inBatches, ackable, asked, refused, done>>

\* In English: "The outbound answers a request for bodies with the bodies
\* it still has (any of them may have left its mempool)."
ReplyBodies ==
    /\ refused = ""
    /\ pending.kind = "bodies"
    /\ toIn' = Append(toIn, [kind |-> "bodies", req |-> 0, new |-> <<>>,
                             ids |-> pending.ids])
    /\ pending' = None
    /\ UNCHANGED <<toOut, inQ, inReq, inBatches, ackable, asked, outQ,
                   delivered, nextId, ackCount, refused, done>>

\* In English: "The run is over (a refusal or MsgDone), or a V1 blocking
\* request waits for ids the mempool will never have: legitimate waits."
Quiet ==
    /\ \/ refused # ""
       \/ done /\ Depth = 0
       \/ pending.kind = "ids" /\ pending.blocking /\ Available = 0
    /\ UNCHANGED vars

InboundNext ==
    IF Inbound = "reference"
    THEN RefSendIds \/ RefSendBodies \/ RefResolve
    ELSE GoSendIds \/ GoSendBodies

Next ==
    \/ InboundNext \/ Collect \/ SendDone
    \/ Handle \/ ReplyIds \/ ReplyBodies
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "Every variable holds a value of the expected kind."
TypeOK ==
    /\ inReq \in 0..MaxReq + InWindow
    /\ inBatches \in 0..MaxBatches
    /\ nextId \in 1..MaxIds + 1
    /\ ackable \subseteq Ids /\ asked \subseteq Ids /\ delivered \subseteq Ids
    /\ done \in BOOLEAN

\* In English: "The outbound never refuses a request: the connection is
\* never torn down by a request an honest inbound sent."
HonestNeverRefused == refused = ""

\* In English: "The outbound's window never exceeds its own limit."
OutboundWithinWindow == Len(outQ) <= OutWindow

\* In English: "The inbound's queue plus the ids it has requested never
\* exceed its window [R1]."
InboundWithinWindow == Len(inQ) + inReq <= InWindow

\* In English: "The acknowledgements the inbound has sent and the outbound
\* has not yet applied."
AcksInFlight ==
    LET reqs == IF pending = None THEN toOut ELSE <<pending>> \o toOut
        acks == [i \in 1..Len(reqs) |-> reqs[i].ack]
    IN SumOver(acks, DOMAIN acks)

\* In English: "Once the acknowledgements in flight are applied, the
\* inbound's queue is the front of the outbound's window: the rest are ids
\* in replies the inbound has not collected yet [R5]."
ViewIsPrefix ==
    refused = "" =>
        LET after == Drop(outQ, AcksInFlight) IN
        /\ AcksInFlight <= Len(outQ)
        /\ Len(inQ) <= Len(after)
        /\ SubSeq(after, 1, Len(inQ)) = inQ

\* In English: "No id leaves the outbound's window twice."
AckedAtMostOnce == \A i \in Ids : ackCount[i] <= 1

\* In English: "Only ids the outbound announced were acknowledged."
AckedOnlyAnnounced == \A i \in Ids : ackCount[i] > 0 => i < nextId

\* In English: "A blocking request in flight is the only thing outstanding
\* [R2] 274-289."
NothingBehindBlocking ==
    LET reqs == IF pending = None THEN toOut ELSE <<pending>> \o toOut IN
    \A i \in 1..Len(reqs) :
        (reqs[i].kind = "ids" /\ reqs[i].blocking) => Depth = 1

\* In English: "MsgDone was sent only with nothing outstanding."
DoneOnlyWhenIdle == done => Depth = 0

-----------------------------------------------------------------------------
(* Reachability probes: each claims something never happens; each is       *)
(* expected to be violated (TxSubmissionPipelinedProbesBug.cfg).           *)

ProbeNoDepthThree == Depth < 3
ProbeOutboundNeverFull == Len(outQ) < OutWindow
ProbeNoBodiesBehindIds ==
    ~(\E i, j \in 1..Len(toOut) : i < j /\ toOut[i].kind = "ids"
                                       /\ toOut[j].kind = "bodies")
=============================================================================
