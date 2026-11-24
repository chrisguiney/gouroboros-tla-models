---------------------------- MODULE TxSubmission ----------------------------
(***************************************************************************)
(* Model 07: node-to-node tx-submission (version 2) and its outstanding    *)
(* window.                                                                 *)
(*                                                                         *)
(* Agency is inverted: the SERVER (the inbound side, which wants           *)
(* transactions) asks, and the CLIENT (the outbound side, which holds a    *)
(* mempool) answers. The client keeps a FIFO of the transaction ids it     *)
(* has announced and the server has not yet acknowledged. Each             *)
(* MsgRequestTxIds(blocking, ack, req) first drops `ack` ids from the      *)
(* front of that FIFO, then asks for up to `req` more.                     *)
(*                                                                         *)
(* Questions: does each side refuse every message the reference refuses,   *)
(* and only those? Does each side, when honest, send only messages the     *)
(* reference accepts? Do both sides always agree on the FIFO, and does it  *)
(* stay within the window?                                                 *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e;            *)
(* specs/07-txsubmission/README.md has links and quotes.                   *)
(*   Specification, docs/network-spec/miniprotocols.tex:                   *)
(*   [S1] 27-36: a message the state does not expect aborts the            *)
(*        connection.                                                      *)
(*   [S2] 1285-1322, 1420-1432: states, agency, transitions.               *)
(*   [S3] 1323-1418: message rules. Non-blocking: ack or req non-zero, and *)
(*        MUST be used when ids remain unacknowledged; blocking: req > 0,  *)
(*        MUST be used when none remain, reply non-empty; MsgRequestTxs    *)
(*        only for announced, outstanding ids, no duplicates; MsgDone only *)
(*        answers a blocking request.                                      *)
(*   [S4] 1455-1475: the window; before NodeToNodeV_16 exceeding it is a   *)
(*        protocol error, from V16 the client replies with fewer ids.      *)
(*   [S5] 1527-1557: both sides agree on the FIFO at all times.            *)
(*   Reference, ouroboros-network/protocols/lib/Ouroboros/Network/         *)
(*   Protocol/TxSubmission2/ and ouroboros-network/lib/Ouroboros/Network/  *)
(*   TxSubmission/:                                                        *)
(*   [R1] Type.hs 196-307: the same rules as [S3], 214-241.                *)
(*   [R2] Codec.hs 392-425: messages are decoded against the state; an     *)
(*        empty reply to a blocking request fails to decode.               *)
(*   [R3] Outbound.hs 131-228: the client's checks on MsgRequestTxIds      *)
(*        (AckedTooManyTxids, RequestedTooManyTxids, RequestedNothing,     *)
(*        RequestBlocking, RequestNonBlocking); 230-260: MsgRequestTxs     *)
(*        must name distinct ids from the unacknowledged FIFO.             *)
(*   [R4] Outbound.hs 95-104, 136-158 and cardano-diffusion/lib/Cardano/   *)
(*        Network/NodeToNode.hs 389-391: from NodeToNodeV_16 an oversized  *)
(*        request is clamped (TxOutboundV_2), not refused.                 *)
(*   [R5] Server.hs 112-130: a blocking request is answered by MsgDone or  *)
(*        a non-empty MsgReplyTxIds.                                       *)
(*   [R6] Inbound/V2.hs 334-358: the reference server sends a blocking     *)
(*        request exactly when its FIFO is empty; 386-425: a reply may not *)
(*        carry more ids than requested, nor bodies not requested.         *)
(*                                                                         *)
(* gOuroboros (blinklabs-io/gouroboros 61046085), protocol/txsubmission/:  *)
(*   [G1] txsubmission.go StateMap.                                        *)
(*   [G2] client.go handleRequestTxIds, handleRequestTxs.                  *)
(*   [G3] server.go RequestTxIds, RequestTxs, handleReplyTxIds,            *)
(*        handleReplyTxs, handleDone.                                      *)
(*   [G4] validation.go reconcileTxIds, requestedTxIdsAreOutstanding.      *)
(*                                                                         *)
(* One step is one message, sent and judged by its receiver at once. The   *)
(* gOuroboros server never pipelines (one pending request at a time [G3]), *)
(* and the client reads in order, so this loses nothing for the window.    *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxUnacked,   \* the window: 10 in both implementations, smaller here
    MaxIds,       \* fresh ids the client's mempool can offer in total
    MaxRequests,  \* requests the server may send in total (keeps it finite)
    V16,          \* TRUE: NodeToNodeV_16 or later, where [R4] clamps
    \* Who each side is. "reference": behaves and checks as [R3]/[R6] do.
    \* "gouroboros": as the code is today. "fixed": gouroboros plus the
    \* checks this model shows are missing. "rogue": sends anything, so the
    \* other side's checks are exercised.
    Server,
    Client,
    \* A mutation that removes one safeguard, to prove an invariant can
    \* fail: "none", "noWindowCheck" (the client forgets the window check),
    \* or "serverKeepsAcked" (the server forgets to drop acknowledged ids).
    Mutation

Honest == {"reference", "gouroboros", "fixed"}

\* In English: "The FIFO's contents as a set."
Range(s) == {s[i] : i \in 1..Len(s)}

\* In English: "The FIFO without its first a ids." SubSeq(s, m, n) is the
\* part of s from position m to n.
Drop(s, a) == SubSeq(s, a + 1, Len(s))

\* In English: "The list of k fresh ids starting at `from`."
Fresh(from, k) == [i \in 1..k |-> from + i - 1]

Min(a, b) == IF a < b THEN a ELSE b

NoRequest == [kind |-> "none"]

VARIABLES
    st,       \* the protocol state; "StError" once a side refused a message
    cU,       \* the client's FIFO of unacknowledged ids (gO Client.unackedTxIds)
    sU,       \* the server's FIFO (gO Server.outstandingTxIds)
    sAck,     \* gO Server.ackCount: what the server's next request acknowledges
    pend,     \* the request being answered
    nextId,   \* the next fresh id the client's mempool offers
    nReq,     \* requests sent so far (model bound only)
    faults    \* what went wrong, as a set of names (see the invariants)

vars == <<st, cU, sU, sAck, pend, nextId, nReq, faults>>

\* In English: "Nothing sent yet; both FIFOs empty."
Init ==
    /\ st = "StInit"
    /\ cU = <<>> /\ sU = <<>> /\ sAck = 0
    /\ pend = NoRequest
    /\ nextId = 1 /\ nReq = 0
    /\ faults = {}

-----------------------------------------------------------------------------
(* What the reference accepts. *)

\* In English: "The blocking-style rules of [S3]/[R1], checked by [R3]:
\* blocking exactly when nothing remains after the acknowledgement, and a
\* request that asks for something."
StyleRules(b, a, n, U) ==
    IF b THEN /\ n > 0                         \* RequestedNothing [R3]
              /\ Len(U) - a = 0                \* RequestBlocking [R3]
         ELSE /\ n > 0 \/ a > 0                \* RequestedNothing [R3]
              /\ Len(U) - a > 0                \* RequestNonBlocking [R3]

\* In English: "The reference client accepts MsgRequestTxIds(b, a, n) when
\* it holds FIFO U: it cannot acknowledge more than it holds; before V16 the
\* request must fit the window; and the style rules hold."
RefAcceptsIds(b, a, n, U) ==
    /\ a <= Len(U)                             \* AckedTooManyTxids [R3]
    /\ V16 \/ Len(U) - a + n <= MaxUnacked     \* RequestedTooManyTxids [R3]; V16 clamps [R4]
    /\ StyleRules(b, a, n, U)

\* In English: "The most ids the reference client may put in its reply:
\* what was asked, or from V16 only what still fits the window [R4]."
RefRoom(a, n, U) ==
    IF V16 THEN Min(n, MaxUnacked - (Len(U) - a)) ELSE n

\* In English: "The reference client accepts MsgRequestTxs when the ids are
\* distinct and all in its FIFO [R3]."
RefAcceptsTxs(ids, dup, U) == ~dup /\ ids \subseteq Range(U)

\* In English: "The reference server accepts a reply of k ids to a request
\* for n: no more than asked [R6], and at least one if blocking [R2]."
RefAcceptsReply(b, n, k) == k <= n /\ (b => k >= 1)

-----------------------------------------------------------------------------
(* What each implementation does. *)

\* In English: "Does the client accept MsgRequestTxIds(b, a, n)? gOuroboros
\* checks the acknowledgement and the window [G2]; the fix adds the style
\* rules; a rogue client accepts anything."
ClientAcceptsIds(b, a, n, U) ==
    LET window == Mutation = "noWindowCheck" \/ Len(U) - a + n <= MaxUnacked
        goOK   == a <= Len(U) /\ window
    IN CASE Client = "reference"  -> RefAcceptsIds(b, a, n, U)
         [] Client = "gouroboros" -> goOK
         [] Client = "fixed"      -> goOK /\ StyleRules(b, a, n, U)
         [] Client = "rogue"      -> TRUE

\* In English: "May the server send MsgRequestTxIds(b, a, n)? gOuroboros
\* always acknowledges sAck, the length of the last reply, and refuses
\* locally only an over-long acknowledgement or window [G3]; the fix adds
\* the style rules. The reference server picks any acknowledgement and
\* follows the style rules [R6]; from V16 its window may be larger than the
\* client's [S4]. A rogue server sends anything."
ServerMaySendIds(b, a, n) ==
    LET goOK == a = sAck /\ a <= Len(sU) /\ Len(sU) - a + n <= MaxUnacked
    IN CASE Server = "reference"  -> /\ a <= Len(sU)
                                     /\ Len(sU) - a + n <=
                                          MaxUnacked + (IF V16 THEN 1 ELSE 0)
                                     /\ StyleRules(b, a, n, sU)
         [] Server = "gouroboros" -> goOK
         [] Server = "fixed"      -> goOK /\ StyleRules(b, a, n, sU)
         [] Server = "rogue"      -> TRUE

\* In English: "Does the server accept a reply of k ids? gOuroboros
\* (reconcileTxIds [G4]) refuses more than asked, an empty reply to a
\* blocking request for at least one, and a reply past the window. Others
\* judge as the reference."
ServerAcceptsReply(b, a, n, k) ==
    IF Server \in {"gouroboros", "fixed"}
       THEN /\ k <= n
            /\ ~(b /\ n > 0 /\ k = 0)
            /\ Len(Drop(sU, a)) + k <= MaxUnacked
       ELSE RefAcceptsReply(b, n, k)

\* In English: "The faults a request reveals: a client accepting what the
\* reference refuses, a client refusing what the reference accepts, and an
\* honest server sending what the reference refuses."
RequestFaults(accepted, legal) ==
    (IF Client \in Honest /\ accepted /\ ~legal
        THEN {"clientAcceptedIllegal"} ELSE {})
    \cup (IF Client \in Honest /\ ~accepted /\ legal
             THEN {"clientRefusedLegal"} ELSE {})
    \cup (IF Server \in Honest /\ ~legal THEN {"serverSentIllegal"} ELSE {})

\* In English: "The faults a reply reveals: a server accepting what the
\* reference refuses, and an honest client sending it."
ReplyFaults(accepted, legal) ==
    (IF Server \in Honest /\ accepted /\ ~legal
        THEN {"serverAcceptedIllegal"} ELSE {})
    \cup (IF Client \in Honest /\ ~legal THEN {"clientSentIllegal"} ELSE {})

-----------------------------------------------------------------------------
(* Steps. *)

\* In English: "The client opens the protocol with MsgInit [S2]."
ClientInit ==
    /\ st = "StInit"
    /\ st' = "StIdle"
    /\ UNCHANGED <<cU, sU, sAck, pend, nextId, nReq, faults>>

\* In English: "The server asks for up to n ids, acknowledging a, blocking
\* or not. The client judges the request against its FIFO."
ServerRequestIds ==
    /\ st = "StIdle" /\ nReq < MaxRequests
    /\ \E b \in BOOLEAN, a \in 0..MaxUnacked + 1, n \in 0..MaxUnacked + 1 :
         /\ ServerMaySendIds(b, a, n)
         /\ LET accepted == ClientAcceptsIds(b, a, n, cU)
                legal    == RefAcceptsIds(b, a, n, cU)
            IN /\ st' = IF ~accepted THEN "StError"
                        ELSE IF b THEN "StTxIdsBlocking"
                        ELSE "StTxIdsNonBlocking"
               /\ pend' = [kind |-> "ids", b |-> b, a |-> a, n |-> n]
               /\ faults' = faults \cup RequestFaults(accepted, legal)
    /\ nReq' = nReq + 1
    /\ UNCHANGED <<cU, sU, sAck, nextId>>

\* In English: "The server asks for the bodies of `ids`; `dup` means the
\* list names one id twice. Every client checks this the same way [G2][R3]."
ServerRequestTxs ==
    /\ st = "StIdle" /\ nReq < MaxRequests
    /\ \E ids \in SUBSET (1..MaxIds), dup \in BOOLEAN :
         /\ dup => ids /= {}
         /\ Server = "rogue" \/ (~dup /\ ids \subseteq Range(sU))
         /\ LET ok == RefAcceptsTxs(ids, dup, cU)
            IN /\ st' = IF ok THEN "StTxs" ELSE "StError"
               /\ pend' = [kind |-> "txs", ids |-> ids]
               /\ faults' = faults \cup
                    (IF Server \in Honest /\ ~ok
                        THEN {"serverSentIllegal"} ELSE {})
    /\ nReq' = nReq + 1
    /\ UNCHANGED <<cU, sU, sAck, nextId>>

\* In English: "The client replies with k fresh ids. An honest client sends
\* at least one to a blocking request for at least one (gOuroboros refuses
\* to send an empty one [G4]) and no more than it may; a rogue client sends
\* up to one more than asked. Each side drops the acknowledged ids and
\* appends the new ones; the gOuroboros server then acknowledges this reply
\* next time [G3]."
ClientReplyIds ==
    /\ st \in {"StTxIdsBlocking", "StTxIdsNonBlocking"}
    /\ LET b  == pend.b
           a  == pend.a
           n  == pend.n
           hi == IF Client = "rogue" THEN n + 1
                 ELSE IF Client = "reference" THEN RefRoom(a, n, cU)
                 ELSE n
           lo == IF Client # "rogue" /\ b /\ n > 0 THEN 1 ELSE 0
       IN \E k \in lo..Min(hi, MaxIds + 1 - nextId) :
            LET reply    == Fresh(nextId, k)
                accepted == ServerAcceptsReply(b, a, n, k)
                legal    == RefAcceptsReply(b, n, k)
            IN /\ st' = IF accepted THEN "StIdle" ELSE "StError"
               /\ cU' = Drop(cU, a) \o reply
               /\ sU' = IF Mutation = "serverKeepsAcked"
                           THEN sU \o reply ELSE Drop(sU, a) \o reply
               /\ sAck' = k
               /\ nextId' = nextId + k
               /\ faults' = faults \cup ReplyFaults(accepted, legal)
    /\ pend' = NoRequest
    /\ UNCHANGED nReq

\* In English: "The client ends the protocol with MsgDone. An honest client
\* does so only in answer to a blocking request [S3][R5]; it is the only
\* way out when its mempool has nothing to offer. A rogue client may try
\* in any state it has agency in; every server refuses it outside
\* StTxIdsBlocking [G1][G3][R2]."
ClientDone ==
    /\ st \in {"StTxIdsBlocking", "StTxIdsNonBlocking", "StTxs"}
    /\ Client = "rogue" \/ st = "StTxIdsBlocking"
    /\ st' = IF st = "StTxIdsBlocking" THEN "StDone" ELSE "StError"
    /\ pend' = NoRequest
    /\ UNCHANGED <<cU, sU, sAck, nextId, nReq, faults>>

\* In English: "The client replies with bodies for some of the requested
\* ids; a rogue client may add one nobody asked for. Every server refuses
\* that [G3][R6]."
ClientReplyTxs ==
    /\ st = "StTxs"
    /\ \E extra \in IF Client = "rogue" THEN BOOLEAN ELSE {FALSE} :
         /\ st' = IF extra THEN "StError" ELSE "StIdle"
    /\ pend' = NoRequest
    /\ UNCHANGED <<cU, sU, sAck, nextId, nReq, faults>>

\* In English: "The run is over: done, refused, or out of requests. Nothing
\* changes any more; this stutter step tells TLC that stopping here is not
\* a deadlock."
Finished ==
    /\ \/ st \in {"StDone", "StError"}
       \/ st = "StIdle" /\ nReq = MaxRequests
    /\ UNCHANGED vars

Next ==
    \/ ClientInit
    \/ ServerRequestIds \/ ServerRequestTxs
    \/ ClientReplyIds \/ ClientDone \/ ClientReplyTxs
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "The client never answers a request the reference client
\* would refuse."
ClientRefusesIllegal == "clientAcceptedIllegal" \notin faults

\* In English: "The client never refuses a request the reference client
\* would answer."
ClientRefusesOnlyIllegal == "clientRefusedLegal" \notin faults

\* In English: "An honest server never sends a request the reference
\* client refuses."
ServerSendsLegal == "serverSentIllegal" \notin faults

\* In English: "The server never accepts a reply the reference server
\* would refuse."
ServerRefusesIllegal == "serverAcceptedIllegal" \notin faults

\* In English: "An honest client never sends a reply the reference server
\* refuses."
ClientSendsLegal == "clientSentIllegal" \notin faults

\* In English: "Whenever a blocking request is being answered, nothing
\* remained unacknowledged after its acknowledgement; whenever a
\* non-blocking one is, something did [S3][S5]."
BlockingRule ==
    st = "StTxIdsBlocking" => Len(cU) - pend.a = 0
NonBlockingRule ==
    st = "StTxIdsNonBlocking" => Len(cU) - pend.a > 0

\* In English: "The client's FIFO never holds more than the window."
WindowBound == Len(cU) <= MaxUnacked

\* In English: "Between messages, with both sides honest, the two FIFOs
\* are the same list of ids [S5]."
ViewsAgree ==
    (Server \in Honest /\ Client \in Honest /\ st = "StIdle") => sU = cU

\* In English: "Two honest sides never refuse each other."
HonestNeverRefused ==
    (Server \in Honest /\ Client \in Honest) => st /= "StError"

-----------------------------------------------------------------------------
(* Reachability probes, each EXPECTED to be violated, so that a passing     *)
(* invariant is not passing only because the model never got near the     *)
(* edge. Run each alone with TxSubmissionProbesBug.cfg (keep one line).  *)

ProbeNoBlocking    == st /= "StTxIdsBlocking"
ProbeNoNonBlocking == st /= "StTxIdsNonBlocking"
ProbeNoTxs         == st /= "StTxs"
ProbeNoDone        == st /= "StDone"
ProbeWindowNeverFull == Len(cU) < MaxUnacked
\* "No request ever both acknowledges and leaves ids outstanding."
ProbeNoPartialAck ==
    ~(st = "StTxIdsNonBlocking" /\ pend.a > 0)
=============================================================================
