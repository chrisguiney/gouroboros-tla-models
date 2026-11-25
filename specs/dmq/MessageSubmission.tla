-------------------------- MODULE MessageSubmission --------------------------
(***************************************************************************)
(* Model `dmq`, part 1: DMQ message submission (node-to-node), the            *)
(* acknowledgement window shared by the two sides.                         *)
(*                                                                         *)
(* Message submission is tx-submission with DMQ messages in place of       *)
(* transactions. The INBOUND side (it wants messages) asks for message ids *)
(* and then for message bodies; the OUTBOUND side (it has them) answers.   *)
(* Both sides keep the same FIFO of ids announced but not yet              *)
(* acknowledged, the "window". A request for ids acknowledges the oldest   *)
(* ack ids and asks for up to req new ones:                                *)
(*   - ack may not exceed the window;                                      *)
(*   - what is left plus req may not exceed MaxUnacked;                    *)
(*   - blocking exactly when nothing is left, asking for at least one;     *)
(*   - non-blocking only when something is left, ack or req non-zero;      *)
(*   - a blocking reply is non-empty, a reply never exceeds req.           *)
(* Bodies may be asked only for ids in the window, each at most once.      *)
(*                                                                         *)
(* In gOuroboros (protocol/messagesubmission) the OUTBOUND side is the     *)
(* Client and the INBOUND side is the Server, in both versions. Which of   *)
(* them is the connection's initiator depends on the version: in V1 the    *)
(* outbound (tx-submission's client) and in V2 the inbound, as dmq-node    *)
(* runs them [R6]. Before the wire fix gOuroboros made the outbound the    *)
(* initiator in V2 too, so against dmq-node both ends ran the outbound and *)
(* neither could leave StIdle (RolesMatch = FALSE). In V2 the outbound may *)
(* answer a blocking request with MsgReplyNoSigIds [R1][R5], which         *)
(* dmq-node's outbound does after 17 s; the requester gives up after 20 s. *)
(* gOuroboros had no such message before the fix (NoIdsReply = FALSE).    *)
(* Both sides *)
(* check a request with validateMessageIDRequest and a reply with          *)
(* reconcileMessageIDs (validation.go): the Server before it sends         *)
(* (requestMessageIDs, RequestMessages), the Client when it receives       *)
(* (handleRequestMessageIds, handleRequestMessages).                       *)
(*                                                                         *)
(* Questions:                                                              *)
(*   WindowBound     the window never exceeds MaxUnacked on either side.   *)
(*   ViewsAgree      both sides always hold the same window.               *)
(*   BlockingRule    a request is in StMessageIdsBlocking only with        *)
(*                   nothing left, in ...NonBlocking only with something.  *)
(*   NoRepeatServe   the outbound never serves a body for an id it has     *)
(*                   already served while the id is unacknowledged.        *)
(*   HonestNeverRefused  the outbound refuses only a peer that broke the   *)
(*                   rules: the gOuroboros Server's own checks keep it     *)
(*                   inside what the outbound accepts.                     *)
(*   Deadlock        only Quiet may stand still: in V2 a blocking request  *)
(*                   must be answered, because the requester gives up      *)
(*                   after 20 s, and someone must run the inbound side.    *)
(*                                                                         *)
(* Sources:                                                                *)
(*   CIP-0137 (cardano-foundation/CIPs 03387471), CIP-0137/README.md:      *)
(*   [C1] 87-134: V2 states, agency, transitions; MsgDone from StIdle by   *)
(*        the inbound side.                                                *)
(*   [C2] 189-238: V1 states; StInit/MsgInit; MsgDone from                 *)
(*        StMessageIdsBlocking by the outbound side.                       *)
(*   [C3] 313-328: blocking iff the window is empty; never request 0 ids.  *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex (tx-submission, which DMQ V1 is): *)
(*   [S1] 27-36: an unexpected message aborts the connection.              *)
(*   [S2] 1326-1377: ack/req rules, blocking iff nothing remains, window   *)
(*        limit, blocking reply non-empty.                                 *)
(*   [S3] 1386-1400: bodies only for announced, outstanding ids not        *)
(*        "already asked for", no duplicates in one request.               *)
(*   Reference, IntersectMBO/dmq-node a267003c:                            *)
(*   [R1] dmq-node/src/DMQ/Protocol/SigSubmissionV2/Type.hs 165-275: V2    *)
(*        messages and rules; ids requested "at most once" (165-171,       *)
(*        248-252); MsgReplyNoSigIds (236-240).                            *)
(*   [R2] dmq-node/src/DMQ/SigSubmissionV2/Outbound.hs 90-211: the V2      *)
(*        outbound's checks, including ProtocolErrorDuplicateRequest for   *)
(*        an id already delivered (196-211).                               *)
(*   [R5] dmq-node/src/DMQ/Protocol/SigSubmissionV2/Codec.hs 91: the V2    *)
(*        blocking time limit, 20 s; 139-180: the V2 tags, MsgReplyNoSigIds *)
(*        is [3]. DMQ/Protocol/SigSubmissionV2/Inbound.hs 99-100: the       *)
(*        inbound treats it as an empty reply. Outbound.hs 103, 129-153:    *)
(*        the acknowledgement still applies, the answer comes after 17 s.  *)
(*   [R6] dmq-node/src/DMQ/NodeToNode.hs 242-308: the initiator runs the   *)
(*        V2 inbound and the V1 outbound; 311-357: the responder runs the  *)
(*        V2 outbound and the V1 inbound.                                  *)
(*   [R7] dmq-node/src/DMQ/Protocol/SigSubmission/Codec.hs 68-78: V1 time *)
(*        limits; a blocking request may wait forever.                     *)
(*   [R8] dmq-node/src/DMQ/SigSubmissionV2/Inbound.hs: the V2 inbound      *)
(*        sends SendMsgRequestSigsPipelined, then                          *)
(*        SendMsgRequestSigIdsPipelined before the bodies arrive;          *)
(*        DMQ/NodeToNode.hs 335-357 runs the V1 inbound as                 *)
(*        txSubmissionServerPeerPipelined. A pipelined request for ids is  *)
(*        non-blocking (ids are still outstanding).                        *)
(*   [R3] IntersectMBO/ouroboros-network 4646039f (ouroboros-network       *)
(*        2.0.0.0, the version dmq-node builds against),                   *)
(*        ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs *)
(*        106-220: the V1 outbound's checks; no repeat check across        *)
(*        requests.                                                        *)
(*   gOuroboros, blinklabs-io/gouroboros 61046085:                         *)
(*   [G1] protocol/messagesubmission/validation.go:                        *)
(*        validateMessageIDRequest, reconcileMessageIDs,                   *)
(*        requestedMessagesAreOutstanding.                                 *)
(*   [G2] protocol/messagesubmission/client.go: handleRequestMessageIds,   *)
(*        handleRequestMessages, ReplyMessageIds, Stop (V1 MsgDone).       *)
(*   [G3] protocol/messagesubmission/server.go: requestMessageIDs,         *)
(*        RequestMessages, handleReplyMessageIds, Done (V2 MsgDone).       *)
(*   [G4] protocol/messagesubmission/messagesubmission.go: stateMapV1,     *)
(*        stateMapV2, roleFor (which side is the initiator).               *)
(*   [G5] gOuroboros branch fix/messagesubmission-reference-wire:          *)
(*        Client.ReplyNoMessageIds, Server.handleReplyNoMessageIds,        *)
(*        acknowledgeMessageIDs (validation.go).                           *)
(*                                                                         *)
(* Message exchange is modelled as one step per message: the sender's      *)
(* check and the receiver's check happen together. Strict alternation      *)
(* means at most one message is ever in flight, so nothing is lost.        *)
(*                                                                         *)
(* Not modelled: message bodies and sizes, authentication, TTLs, the       *)
(* replay cache, and the enqueue-failure rollback in ReplyMessageIds       *)
(* (existing tests cover it).                                              *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Version,       \* 1 or 2: the negotiated message-submission version
    MaxUnacked,    \* the window: MaxUnacknowledgedMessageIDs
    MaxIds,        \* how many ids the outbound's queue ever holds (finite)
    \* TRUE: the inbound peer may send any request, legal or not. FALSE: it
    \* is the gOuroboros Server, which checks its own requests first.
    Rogue,
    \* FALSE in gOuroboros. TRUE: the outbound (Client) refuses a body
    \* request naming an id it already served, as the V2 reference does [R2].
    OutRefusesRepeat,
    \* FALSE in gOuroboros. TRUE: the inbound (Server) RequestMessages
    \* refuses to name an id it already asked for.
    InRefusesRepeat,
    \* TRUE: in V2 the two ends run complementary sides, the initiator the
    \* inbound and the responder the outbound, as dmq-node does [R6] and
    \* gOuroboros does after the wire fix [G4]. FALSE: gOuroboros before the
    \* fix, connected to dmq-node, where both ends run the outbound in V2.
    \* V1 is unaffected: there both put the outbound on the initiator.
    RolesMatch,
    \* TRUE: in V2 the outbound can answer a blocking request with
    \* MsgReplyNoSigIds, as dmq-node does and gOuroboros does after the fix
    \* [G5]. FALSE: gOuroboros before the fix, which had no such message.
    NoIdsReply,
    \* "none", or a check removed from the outbound to prove an invariant
    \* can fail: "noWindow" (the MaxUnacked limit), "noBlockRule" (blocking
    \* iff nothing is left).
    Mutation,
    \* How many V1 runs one connection may carry. After the outbound's
    \* MsgDone the inbound (the gOuroboros Server, the V1 responder)
    \* restarts in StInit, as dmq-node's inbound governor restarts a
    \* responder that ended cleanly [R6]; 1 means no restart.
    MaxRuns,
    \* TRUE: the restart drops the ids the inbound asked bodies for along
    \* with its window (Server.handleDone resets requestedIDs). FALSE: it
    \* keeps them, so with InRefusesRepeat an id announced again in the next
    \* run could never have its body asked for.
    ForgetAskedOnRestart,
    \* TRUE: the inbound is the reference's pipelined requester [R8]: while
    \* the outbound owes MsgReplyMessages it already sends its next
    \* (non-blocking) request for ids. FALSE: strict alternation.
    PeerPipelines,
    \* TRUE: the fix: the outbound's StMessages admits that request
    \* (PipelinedMessageTypes) and handles it once it has replied. FALSE:
    \* 4f710823, whose state map refuses a message arriving without the
    \* peer's agency, which closes the connection [S1].
    OutAdmitsPipelined

\* In English: "Id 0 is an id the outbound never announced; real ids are
\* 1..MaxIds, handed out in order."
\* Literally: "Unannounced is defined as 0."
Unannounced == 0

\* In English: "The set of ids in sequence s."
\* Literally: "Range of s is defined as the set of element i of s, for every i
\*   that is a member of 1 through the length of s."
Range(s) == {s[i] : i \in 1..Len(s)}

\* In English: "The first n ids of s, and everything after them."
\* Literally: "Front of s and n is defined as the subsequence of s from element
\*   1 through element n."
Front(s, n) == SubSeq(s, 1, n)
\* Literally: "Rest of s and n is defined as the subsequence of s from element
\*   n plus 1 through element the length of s."
Rest(s, n)  == SubSeq(s, n + 1, Len(s))

\* The request-for-ids rule [S2][C3][R2][G1], as validateMessageIDRequest
\* writes it, with q the window before the request. The two switchable
\* clauses are the ones the mutations remove from the outbound.
\* In English: "ack fits the window; a blocking request asks for at least
\* one, a non-blocking one acknowledges or asks for something; (rule)
\* blocking exactly when nothing is left; (window) what is left plus what
\* is asked for fits in MaxUnacked."
\* Literally: "IdsRequestOK of q, blocking, ack, req, checkBlockRule and
\*   checkWindow is defined as: ack is less than or equal to the length of q,
\*   and it is not the case that (blocking is true and req equals 0), and it is
\*   not the case that (blocking is not true and ack equals 0 and req equals
\*   0), and if checkBlockRule is true, then (blocking is true if and only if
\*   the length of q minus ack equals 0), and if checkWindow is true, then the
\*   length of q minus ack plus req is less than or equal to MaxUnacked."
IdsRequestOK(q, blocking, ack, req, checkBlockRule, checkWindow) ==
    /\ ack <= Len(q)
    /\ ~(blocking /\ req = 0)
    /\ ~(~blocking /\ ack = 0 /\ req = 0)
    /\ checkBlockRule => (blocking <=> Len(q) - ack = 0)
    /\ checkWindow => Len(q) - ack + req <= MaxUnacked

VARIABLES
    st,        \* the protocol state both sides agree on: "Init", "Idle",
               \* "IdsBlocking", "IdsNonBlocking", "Messages", "Done"
    req,       \* the open request: [blocking, ack, n] for ids
    inQ,       \* the inbound's window (Server.pendingMessageIDs)
    outQ,      \* the outbound's window (Client.pendingMessageIDs)
    inAsked,   \* ids the inbound has asked bodies for, still unacknowledged
    outServed, \* ids the outbound has served bodies for, still unacknowledged
    nextId,    \* the next id the outbound's queue will announce
    refused,   \* "none", or why the outbound refused a request [S1]
    servedTwice, \* TRUE once the outbound served one id's body twice
    runs,      \* how many runs have started on the connection
    pipe       \* a request for ids pipelined behind an unanswered body
               \* request and held by the outbound, or NoReq

\* Literally: "vars is defined as the tuple of all eleven variables."
vars == <<st, req, inQ, outQ, inAsked, outServed, nextId, refused,
          servedTwice, runs, pipe>>

\* In English: "The empty request: not blocking, acknowledging nothing, asking
\* for nothing."
\* Literally: "NoReq is defined as the record whose field blocking is FALSE,
\*   whose field ack is 0, and whose field n is 0."
NoReq == [blocking |-> FALSE, ack |-> 0, n |-> 0]

\* In English: "V1 starts in StInit, V2 in StIdle [C1][C2]; both windows
\* are empty."
\* Literally: "Init is defined as: st equals (if Version equals 1 then "Init",
\*   else "Idle"), and req equals NoReq, and inQ equals the empty sequence and
\*   outQ equals the empty sequence, and inAsked equals the empty set and
\*   outServed equals the empty set, and nextId equals 1, and refused equals
\*   "none", and servedTwice equals FALSE, and runs equals 1, and pipe
\*   equals NoReq."
Init ==
    /\ st = IF Version = 1 THEN "Init" ELSE "Idle"
    /\ req = NoReq
    /\ inQ = <<>> /\ outQ = <<>>
    /\ inAsked = {} /\ outServed = {}
    /\ nextId = 1
    /\ refused = "none"
    /\ servedTwice = FALSE
    /\ runs = 1
    /\ pipe = NoReq

\* In English: "Some end of the connection runs the inbound side, the one
\* that asks. In V1 it always does; in V2 only when the two ends agree that
\* the initiator asks [R6]."
\* Literally: "InboundRuns is defined as: Version equals 1, or RolesMatch is
\*   true."
InboundRuns == Version = 1 \/ RolesMatch

-----------------------------------------------------------------------------
(* Version 1 only: the outbound opens with MsgInit [C2].                   *)

\* In English: "In StInit the outbound sends MsgInit and the inbound may
\* start asking."
\* Literally: "SendInit is defined as: Version equals 1 and st equals "Init",
\*   and st in the next state equals "Idle", and req, inQ, outQ, inAsked,
\*   outServed, nextId, refused and servedTwice are unchanged."
SendInit ==
    /\ Version = 1 /\ st = "Init"
    /\ st' = "Idle"
    /\ UNCHANGED <<runs, req, inQ, outQ, inAsked, outServed, nextId, refused,
                   servedTwice, pipe>>

-----------------------------------------------------------------------------
(* Ids.                                                                    *)

\* In English: "In StIdle the inbound asks for ids. An honest inbound
\* (the gOuroboros Server) sends only a request its own check passes; a
\* rogue one sends anything. The outbound checks the request against its
\* own window: it accepts and moves to the blocking or non-blocking state,
\* or refuses, which ends the connection [S1]."
\* Literally: "RequestIds is defined as: InboundRuns is true, and st equals
\*   "Idle" and refused equals "none", and there exists a blocking in BOOLEAN,
\*   an ack in 0 through the length of inQ plus 1, and an n in 0 through
\*   MaxUnacked plus 1, such that (Rogue is true, or IdsRequestOK of inQ,
\*   blocking, ack, n, TRUE and TRUE), and if IdsRequestOK of outQ, blocking,
\*   ack, n, (Mutation does not equal "noBlockRule"), and (Mutation does not
\*   equal "noWindow"), then st in the next state equals (if blocking then
\*   "IdsBlocking", else "IdsNonBlocking"), and req in the next state equals
\*   the record whose field blocking is blocking, whose field ack is ack, and
\*   whose field n is n, and refused is unchanged; else refused in the next
\*   state equals "ids request", and st and req are unchanged; and inQ, outQ,
\*   inAsked, outServed, nextId and servedTwice are unchanged."
RequestIds ==
    /\ InboundRuns
    /\ st = "Idle" /\ refused = "none"
    /\ \E blocking \in BOOLEAN, ack \in 0..(Len(inQ) + 1),
          n \in 0..(MaxUnacked + 1) :
        /\ Rogue \/ IdsRequestOK(inQ, blocking, ack, n, TRUE, TRUE)
        /\ IF IdsRequestOK(outQ, blocking, ack, n,
                           Mutation /= "noBlockRule", Mutation /= "noWindow")
              THEN /\ st' = IF blocking THEN "IdsBlocking" ELSE "IdsNonBlocking"
                   /\ req' = [blocking |-> blocking, ack |-> ack, n |-> n]
                   /\ UNCHANGED refused
              ELSE /\ refused' = "ids request"
                   /\ UNCHANGED <<st, req, pipe>>
    /\ UNCHANGED <<runs, inQ, outQ, inAsked, outServed, nextId, servedTwice, pipe>>

\* In English: "The outbound answers with k fresh ids from its queue: no
\* more than asked for, at least one if blocking [S2]. Both sides drop the
\* ack oldest ids and append the new ones (reconcileMessageIDs). Bodies
\* served or asked for among the dropped ids are forgotten with them."
\* Literally: "ReplyIds is defined as: st is a member of the set containing
\*   "IdsBlocking" and "IdsNonBlocking", and there exists a k in 0 through
\*   req's n such that nextId plus k minus 1 is less than or equal to MaxIds,
\*   and if req's blocking is true, then k is greater than or equal to 1, and,
\*   letting fresh be the function that maps every i in 1 through k to nextId
\*   plus i minus 1, and dropped be Range of Front of outQ and req's ack: outQ
\*   in the next state equals Rest of outQ and req's ack, followed by fresh;
\*   and inQ in the next state equals Rest of inQ and req's ack, followed by
\*   fresh; and outServed in the next state equals outServed without the
\*   members of dropped; and inAsked in the next state equals inAsked without
\*   the members of dropped; and nextId in the next state equals nextId plus k;
\*   and st in the next state equals "Idle" and req in the next state equals
\*   NoReq, and refused and servedTwice are unchanged."
ReplyIds ==
    /\ st \in {"IdsBlocking", "IdsNonBlocking"}
    /\ \E k \in 0..req.n :
        /\ nextId + k - 1 <= MaxIds
        /\ req.blocking => k >= 1
        /\ LET fresh == [i \in 1..k |-> nextId + i - 1]
               dropped == Range(Front(outQ, req.ack))
           IN /\ outQ' = Rest(outQ, req.ack) \o fresh
              /\ inQ' = Rest(inQ, req.ack) \o fresh
              /\ outServed' = outServed \ dropped
              /\ inAsked' = inAsked \ dropped
              /\ nextId' = nextId + k
    /\ st' = "Idle" /\ req' = NoReq
    /\ UNCHANGED <<runs, refused, servedTwice, pipe>>

\* In English: "In V2, when the outbound can say so, it answers a blocking
\* request with no ids: both sides drop the ack oldest ids (all of them,
\* since a blocking request acknowledges the whole window) and add none
\* [R5][G5]. Bodies served or asked for among the dropped ids are forgotten
\* with them. The reference does this when 17 s pass without a new id; the
\* model lets it happen at any time, which covers that."
\* Literally: "ReplyNoIds is defined as: Version equals 2 and NoIdsReply is
\*   true, and st equals "IdsBlocking", and, letting dropped be Range of Front
\*   of outQ and req's ack: outQ in the next state equals Rest of outQ and
\*   req's ack, and inQ in the next state equals Rest of inQ and req's ack, and
\*   outServed in the next state equals outServed without the members of
\*   dropped, and inAsked in the next state equals inAsked without the members
\*   of dropped; and st in the next state equals "Idle" and req in the next
\*   state equals NoReq, and nextId, refused and servedTwice are unchanged."
ReplyNoIds ==
    /\ Version = 2 /\ NoIdsReply
    /\ st = "IdsBlocking"
    /\ LET dropped == Range(Front(outQ, req.ack))
       IN /\ outQ' = Rest(outQ, req.ack)
          /\ inQ' = Rest(inQ, req.ack)
          /\ outServed' = outServed \ dropped
          /\ inAsked' = inAsked \ dropped
    /\ st' = "Idle" /\ req' = NoReq
    /\ UNCHANGED <<runs, nextId, refused, servedTwice, pipe>>

-----------------------------------------------------------------------------
(* Bodies.                                                                 *)

\* In English: "In StIdle the inbound asks for the bodies of a set of ids.
\* The honest inbound names only ids in its window (and, with
\* InRefusesRepeat, none it already asked for); a rogue one may also name
\* an unannounced id. The outbound refuses ids outside its window [S3]
\* and, with OutRefusesRepeat, ids it already served [R2]. Otherwise it
\* moves to StMessages, noting any id served a second time."
\* Literally: "RequestBodies is defined as: InboundRuns is true, and st equals
\*   "Idle" and refused equals "none", and there exists an ids in the set of
\*   subsets of the union of Range of inQ and the set containing Unannounced,
\*   such that (Rogue is true, or (ids is a subset of Range of inQ, and if
\*   InRefusesRepeat is true, then the intersection of ids and inAsked equals
\*   the empty set)), and inAsked in the next state equals the union of inAsked
\*   and (ids without the members of the set containing Unannounced), and if it
\*   is not the case that ids is a subset of Range of outQ, then refused in the
\*   next state equals "unannounced id", and st, outServed and servedTwice are
\*   unchanged; else if OutRefusesRepeat is true and the intersection of ids
\*   and outServed does not equal the empty set, then refused in the next state
\*   equals "repeated id", and st, outServed and servedTwice are unchanged;
\*   else st in the next state equals "Messages", and servedTwice in the next
\*   state equals (servedTwice, or the intersection of ids and outServed does
\*   not equal the empty set), and outServed in the next state equals the union
\*   of outServed and ids, and refused is unchanged; and req, inQ, outQ and
\*   nextId are unchanged."
RequestBodies ==
    /\ InboundRuns
    /\ st = "Idle" /\ refused = "none"
    /\ \E ids \in SUBSET (Range(inQ) \cup {Unannounced}) :
        /\ Rogue \/ /\ ids \subseteq Range(inQ)
                    /\ InRefusesRepeat => ids \cap inAsked = {}
        /\ inAsked' = inAsked \cup (ids \ {Unannounced})
        /\ IF ~(ids \subseteq Range(outQ))
              THEN /\ refused' = "unannounced id"
                   /\ UNCHANGED <<st, outServed, servedTwice, pipe>>
           ELSE IF OutRefusesRepeat /\ ids \cap outServed /= {}
              THEN /\ refused' = "repeated id"
                   /\ UNCHANGED <<st, outServed, servedTwice, pipe>>
           ELSE /\ st' = "Messages"
                /\ servedTwice' = (servedTwice \/ ids \cap outServed /= {})
                /\ outServed' = outServed \cup ids
                /\ UNCHANGED refused
    /\ UNCHANGED <<runs, req, inQ, outQ, nextId, pipe>>

\* In English: "The outbound answers with the bodies it still has (it may
\* omit some) and the inbound is back in StIdle. A request for ids held
\* behind the reply is then handled as if it had just arrived: the outbound
\* checks it against its window and moves to StMessageIdsNonBlocking, or
\* refuses it."
\* Literally: "ReplyBodies is defined as: st equals "Messages", and if pipe
\*   equals NoReq, then st in the next state equals "Idle" and req and refused
\*   are unchanged; else if IdsRequestOK of outQ, FALSE, pipe's ack, pipe's n,
\*   TRUE and TRUE, then st in the next state equals "IdsNonBlocking" and req
\*   in the next state equals pipe and refused is unchanged; else st in the
\*   next state equals "Idle" and refused in the next state equals "ids
\*   request" and req is unchanged; and pipe in the next state equals NoReq;
\*   and runs, inQ, outQ, inAsked, outServed, nextId and servedTwice are
\*   unchanged."
ReplyBodies ==
    /\ st = "Messages"
    /\ IF pipe = NoReq
          THEN /\ st' = "Idle" /\ UNCHANGED <<req, refused>>
       ELSE IF IdsRequestOK(outQ, FALSE, pipe.ack, pipe.n, TRUE, TRUE)
          THEN /\ st' = "IdsNonBlocking" /\ req' = pipe /\ UNCHANGED refused
       ELSE /\ st' = "Idle" /\ refused' = "ids request" /\ UNCHANGED req
    /\ pipe' = NoReq
    /\ UNCHANGED <<runs, inQ, outQ, inAsked, outServed, nextId, servedTwice>>

\* In English: "With PeerPipelines, while the outbound owes the bodies the
\* inbound sends its next request for ids, non-blocking and checked against
\* its own window [R8]. With OutAdmitsPipelined the outbound holds it until
\* it has replied; without, it arrives with no agency for the inbound and
\* the outbound refuses it [S1]."
\* Literally: "PipelineRequestIds is defined as: PeerPipelines is true, and
\*   InboundRuns is true, and st equals "Messages", and refused equals
\*   "none", and pipe equals NoReq, and there exists an ack in 0 through the
\*   length of inQ and an n in 0 through MaxUnacked such that IdsRequestOK of
\*   inQ, FALSE, ack, n, TRUE and TRUE, and if OutAdmitsPipelined then pipe in
\*   the next state equals the record whose field blocking is FALSE, whose
\*   field ack is ack and whose field n is n, and refused is unchanged; else
\*   refused in the next state equals "pipelined request" and pipe is
\*   unchanged; and the other variables are unchanged."
PipelineRequestIds ==
    /\ PeerPipelines /\ InboundRuns
    /\ st = "Messages" /\ refused = "none" /\ pipe = NoReq
    /\ \E ack \in 0..Len(inQ), n \in 0..MaxUnacked :
        /\ IdsRequestOK(inQ, FALSE, ack, n, TRUE, TRUE)
        /\ IF OutAdmitsPipelined
              THEN /\ pipe' = [blocking |-> FALSE, ack |-> ack, n |-> n]
                   /\ UNCHANGED refused
              ELSE /\ refused' = "pipelined request"
                   /\ UNCHANGED pipe
    /\ UNCHANGED <<st, runs, req, inQ, outQ, inAsked, outServed, nextId,
                   servedTwice>>

-----------------------------------------------------------------------------
(* Ending. V1: the outbound sends MsgDone instead of answering a blocking  *)
(* request [C2] (gOuroboros Client.Stop). V2: the inbound sends MsgDone    *)
(* from StIdle [C1] (gOuroboros Server.Done).                              *)

\* In English: "In V1 the outbound may end the run from StMessageIdsBlocking;
\* in V2 the inbound may end it from StIdle."
\* Literally: "SendDone is defined as: refused equals "none", and (Version
\*   equals 1 and st equals "IdsBlocking", or Version equals 2 and st equals
\*   "Idle" and InboundRuns is true), and st in the next state equals "Done",
\*   and req, inQ, outQ, inAsked, outServed, nextId, refused and servedTwice
\*   are unchanged."
SendDone ==
    /\ refused = "none"
    /\ \/ Version = 1 /\ st = "IdsBlocking"
       \/ Version = 2 /\ st = "Idle" /\ InboundRuns
    /\ st' = "Done"
    /\ UNCHANGED <<runs, req, inQ, outQ, inAsked, outServed, nextId, refused,
                   servedTwice, pipe>>

\* In English: "In V1, after the outbound's MsgDone, the inbound restarts
\* in StInit for a new run on the same connection [R6]. The windows and
\* the bodies served belong to the run and start empty; the outbound
\* announces again from its queue, so the same ids may come back. With
\* ForgetAskedOnRestart the inbound's record of ids it asked for goes too."
\* Literally: "Restart is defined as: Version equals 1, and st equals
\*   "Done", and refused equals "none", and runs is less than MaxRuns, and st
\*   in the next state equals "Init", and req in the next state equals NoReq,
\*   and inQ and outQ in the next state equal the empty sequence, and
\*   outServed in the next state equals the empty set, and inAsked in the
\*   next state equals (if ForgetAskedOnRestart then the empty set else
\*   inAsked), and nextId in the next state equals 1, and runs in the next
\*   state equals runs plus 1, and refused and servedTwice are unchanged."
Restart ==
    /\ Version = 1 /\ st = "Done" /\ refused = "none" /\ runs < MaxRuns
    /\ st' = "Init" /\ req' = NoReq
    /\ inQ' = <<>> /\ outQ' = <<>>
    /\ outServed' = {}
    /\ inAsked' = IF ForgetAskedOnRestart THEN {} ELSE inAsked
    /\ nextId' = 1
    /\ runs' = runs + 1
    /\ UNCHANGED <<refused, servedTwice, pipe>>

-----------------------------------------------------------------------------

\* In English: "Nothing more happens: the run is over, the connection was
\* closed by a refusal, or, in V1 only, a blocking request waits for ids
\* that will never come (the queue is finite here, and V1 lets a blocking
\* request wait forever [R7]). In V2 a blocking request that is never
\* answered is not quiet: the requester gives up after 20 s and closes the
\* connection [R5], so it is reported as a deadlock."
\* Literally: "Quiet is defined as: (st equals "Done", or refused does not
\*   equal "none", or Version equals 1 and st equals "IdsBlocking" and nextId
\*   is greater than MaxIds), and vars is unchanged."
Quiet ==
    /\ \/ st = "Done"
       \/ refused /= "none"
       \/ Version = 1 /\ st = "IdsBlocking" /\ nextId > MaxIds
    /\ UNCHANGED vars

\* In English: "A step is MsgInit, a request or reply for ids, a request or
\* reply for bodies, done, or, once nothing more happens, nothing."
\* Literally: "Next is defined as: SendInit, or RequestIds, or ReplyIds, or
\*   ReplyNoIds, or RequestBodies, or ReplyBodies, or PipelineRequestIds, or
\*   SendDone, or Restart, or Quiet."
Next ==
    \/ SendInit \/ RequestIds \/ ReplyIds \/ ReplyNoIds
    \/ RequestBodies \/ ReplyBodies \/ PipelineRequestIds
    \/ SendDone \/ Restart \/ Quiet

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Neither side's window ever holds more than MaxUnacked ids."
\* Literally: "WindowBound is defined as: the length of outQ is less than or
\*   equal to MaxUnacked, and the length of inQ is less than or equal to
\*   MaxUnacked."
WindowBound == Len(outQ) <= MaxUnacked /\ Len(inQ) <= MaxUnacked

\* In English: "The two sides always hold the same window."
\* Literally: "ViewsAgree is defined as: inQ equals outQ."
ViewsAgree == inQ = outQ

\* In English: "A blocking request is open only when it acknowledges the
\* whole window; a non-blocking one only when it leaves some ids [S2]."
\* Literally: "BlockingRule is defined as: if st equals "IdsBlocking", then the
\*   length of outQ equals req's ack; and if st equals "IdsNonBlocking", then
\*   the length of outQ is greater than req's ack."
BlockingRule ==
    /\ st = "IdsBlocking" => Len(outQ) = req.ack
    /\ st = "IdsNonBlocking" => Len(outQ) > req.ack

\* In English: "No id's body is served twice while it is unacknowledged
\* [S3][R1]."
\* Literally: "NoRepeatServe is defined as: servedTwice is not true."
NoRepeatServe == ~servedTwice

\* In English: "The outbound refuses only a peer that broke the rules."
\* Literally: "HonestNeverRefused is defined as: if refused does not equal
\*   "none", then Rogue is true."
HonestNeverRefused == refused /= "none" => Rogue

\* In English: "The inbound has asked bodies only for ids in its current
\* window, so every id it is announced it may still ask for once."
\* Literally: "AskedInWindow is defined as: inAsked is a subset of Range of
\*   inQ."
AskedInWindow == inAsked \subseteq Range(inQ)

\* Probes, each EXPECTED to be violated.
\* In English: "The window never fills." Violated = it does.
\* Literally: "ProbeWindowNeverFull is defined as: the length of outQ is less
\*   than MaxUnacked."
ProbeWindowNeverFull == Len(outQ) < MaxUnacked
\* In English: "Nothing is ever refused." Violated = a refusal happens.
\* Literally: "ProbeNeverRefused is defined as: refused equals "none"."
ProbeNeverRefused == refused = "none"
\* In English: "No non-blocking request is ever open." Violated = one is.
\* Literally: "ProbeNeverNonBlocking is defined as: st does not equal
\*   "IdsNonBlocking"."
ProbeNeverNonBlocking == st /= "IdsNonBlocking"
\* In English: "The run never ends with MsgDone." Violated = it does.
\* Literally: "ProbeNeverDone is defined as: st does not equal "Done"."
ProbeNeverDone == st /= "Done"
=============================================================================
