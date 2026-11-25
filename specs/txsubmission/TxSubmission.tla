---------------------------- MODULE TxSubmission ----------------------------
(***************************************************************************)
(* node-to-node tx-submission (version 2) and its outstanding    *)
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
(* specs/txsubmission/README.md has links and quotes.                   *)
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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxUnacked,   \* the window: 10 in both implementations, smaller here
    MaxIds,       \* fresh ids the client's mempool can offer in total
    MaxRequests,  \* requests the server may send in total (keeps it finite)
    V16,          \* TRUE: NodeToNodeV_16 or later, where [R4] clamps
    \* TRUE: the gOuroboros client ("gouroboros" or "fixed") clamps an
    \* oversized request from V16 as [R4] does, instead of refusing it
    \* [G2]. FALSE: gOuroboros main, which refuses it in every version.
    ClientClamps,
    \* Who each side is. "reference": behaves and checks as [R3]/[R6] do.
    \* "gouroboros": as the code is today. "fixed": gouroboros plus the
    \* checks this model shows are missing. "rogue": sends anything, so the
    \* other side's checks are exercised.
    Server,
    Client,
    \* A mutation that removes one safeguard, to prove an invariant can
    \* fail: "none", "noWindowCheck" (the client forgets the window check),
    \* "serverKeepsAcked" (the server forgets to drop acknowledged ids), or
    \* "clampBlocking" (a clamping gOuroboros client clamps a blocking
    \* request that leaves ids unacknowledged instead of refusing it first,
    \* as the clamp's first draft did), or "refuseAckedBlocking" (the
    \* client counts the ids left before the acknowledgement, so it also
    \* refuses a blocking request that acknowledges the whole window).
    Mutation

\* In English: "The roles that behave honestly: every role except "rogue"."
\* Literally: "Honest is defined as the set containing "reference",
\*   "gouroboros" and "fixed"."
Honest == {"reference", "gouroboros", "fixed"}

\* In English: "The FIFO's contents as a set."
\* Literally: "Range of s is defined as the set of element i of s, for every i
\*   that is a member of 1 through the length of s."
Range(s) == {s[i] : i \in 1..Len(s)}

\* In English: "The FIFO without its first a ids." SubSeq(s, m, n) is the
\* part of s from position m to n.
\* Literally: "Drop of s and a is defined as the subsequence of s from element
\*   a plus 1 through element the length of s."
Drop(s, a) == SubSeq(s, a + 1, Len(s))

\* In English: "The list of k fresh ids starting at `from`."
\* Literally: "Fresh of from and k is defined as the function that maps every i
\*   in 1 through k to from plus i minus 1."
Fresh(from, k) == [i \in 1..k |-> from + i - 1]

\* In English: "The smaller of a and b."
\* Literally: "Min of a and b is defined as: if a is less than b then a, else
\*   b."
Min(a, b) == IF a < b THEN a ELSE b

\* In English: "No request is being answered."
\* Literally: "NoRequest is defined as the record whose field kind is "none"."
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

\* Literally: "vars is defined as the tuple of all eight variables."
vars == <<st, cU, sU, sAck, pend, nextId, nReq, faults>>

\* In English: "Nothing sent yet; both FIFOs empty."
\* Literally: "Init is defined as: st equals "StInit", and cU equals the empty
\*   sequence, and sU equals the empty sequence, and sAck equals 0, and pend
\*   equals NoRequest, and nextId equals 1, and nReq equals 0, and faults
\*   equals the empty set."
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
\* Literally: "StyleRules of b, a, n and U is defined as: if b, then (n is
\*   greater than 0, and the length of U minus a equals 0), else (n is greater
\*   than 0 or a is greater than 0, and the length of U minus a is greater than
\*   0)."
StyleRules(b, a, n, U) ==
    IF b THEN /\ n > 0                         \* RequestedNothing [R3]
              /\ Len(U) - a = 0                \* RequestBlocking [R3]
         ELSE /\ n > 0 \/ a > 0                \* RequestedNothing [R3]
              /\ Len(U) - a > 0                \* RequestNonBlocking [R3]

\* In English: "The reference client accepts MsgRequestTxIds(b, a, n) when
\* it holds FIFO U: it cannot acknowledge more than it holds; before V16 the
\* request must fit the window; and the style rules hold."
\* Literally: "RefAcceptsIds of b, a, n and U is defined as: a is less than or
\*   equal to the length of U, and (V16 is true, or the length of U minus a
\*   plus n is less than or equal to MaxUnacked), and StyleRules of b, a, n and
\*   U."
RefAcceptsIds(b, a, n, U) ==
    /\ a <= Len(U)                             \* AckedTooManyTxids [R3]
    /\ V16 \/ Len(U) - a + n <= MaxUnacked     \* RequestedTooManyTxids [R3]; V16 clamps [R4]
    /\ StyleRules(b, a, n, U)

\* In English: "The most ids the reference client may put in its reply:
\* what was asked, or from V16 only what still fits the window [R4]."
\* Literally: "RefRoom of a, n and U is defined as: if V16 then Min of n and
\*   (MaxUnacked minus (the length of U minus a)), else n."
RefRoom(a, n, U) ==
    IF V16 THEN Min(n, MaxUnacked - (Len(U) - a)) ELSE n

\* In English: "The reference client accepts MsgRequestTxs when the ids are
\* distinct and all in its FIFO [R3]."
\* Literally: "RefAcceptsTxs of ids, dup and U is defined as: dup is not true,
\*   and ids is a subset of Range of U."
RefAcceptsTxs(ids, dup, U) == ~dup /\ ids \subseteq Range(U)

\* In English: "The reference server accepts a reply of k ids to a request
\* for n: no more than asked [R6], and at least one if blocking [R2]."
\* Literally: "RefAcceptsReply of b, n and k is defined as: k is less than or
\*   equal to n, and if b, then k is greater than or equal to 1."
RefAcceptsReply(b, n, k) == k <= n /\ (b => k >= 1)

-----------------------------------------------------------------------------
(* What each implementation does. *)

\* In English: "Does the client accept MsgRequestTxIds(b, a, n)? gOuroboros
\* checks the acknowledgement and the window [G2]; the fix adds the style
\* rules; a rogue client accepts anything. With ClientClamps, from V16 the
\* window is not a reason to refuse: the reply is clamped instead [R4].
\* A clamping client also refuses, in every version and before it clamps,
\* a blocking request for no ids (RequestedNothing [R3]) or one that leaves
\* ids unacknowledged (RequestBlocking [R3]), so a blocking request it
\* answers is never clamped to zero ids; the mutation "clampBlocking"
\* removes the second refusal, which the clamp's first draft lacked, and
\* "refuseAckedBlocking" counts the ids left before the acknowledgement,
\* refusing the legal blocking request that acknowledges the whole window."
\* Literally: "ClientAcceptsIds of b, a, n and U is defined as: letting window
\*   be (Mutation equals "noWindowCheck", or V16 is true and ClientClamps is
\*   true, or the length of U minus a plus n is less than or equal to
\*   MaxUnacked), blockOK be (if ClientClamps is true, then it is not the case
\*   that b is true and n equals 0, and if Mutation does not equal
\*   "clampBlocking", it is not the case that b is true and the length of U
\*   minus (if Mutation equals "refuseAckedBlocking" then 0, else a) is
\*   greater than 0), and goOK be (a is less than or
\*   equal to the length of U, and window, and blockOK): in the case Client
\*   equals "reference", RefAcceptsIds of b, a, n and U; in the case Client
\*   equals "gouroboros", goOK; in the case Client equals "fixed", goOK and
\*   StyleRules of b, a, n and U; in the case Client equals "rogue", TRUE."
ClientAcceptsIds(b, a, n, U) ==
    LET window  == \/ Mutation = "noWindowCheck"
                   \/ V16 /\ ClientClamps                \* clamped, not refused [R4]
                   \/ Len(U) - a + n <= MaxUnacked
        blockOK == ClientClamps =>
                     /\ ~(b /\ n = 0)                     \* RequestedNothing [R3]
                     /\ Mutation # "clampBlocking"
                          => ~(b /\ Len(U) - (IF Mutation = "refuseAckedBlocking"
                                              THEN 0 ELSE a) > 0)  \* RequestBlocking [R3]
        goOK    == a <= Len(U) /\ window /\ blockOK
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
\* Literally: "ServerMaySendIds of b, a and n is defined as: letting goOK be (a
\*   equals sAck, and a is less than or equal to the length of sU, and the
\*   length of sU minus a plus n is less than or equal to MaxUnacked): in the
\*   case Server equals "reference", a is less than or equal to the length of
\*   sU, and the length of sU minus a plus n is less than or equal to
\*   MaxUnacked plus (if V16 then 1, else 0), and StyleRules of b, a, n and sU;
\*   in the case Server equals "gouroboros", goOK; in the case Server equals
\*   "fixed", goOK and StyleRules of b, a, n and sU; in the case Server equals
\*   "rogue", TRUE."
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
\* Literally: "ServerAcceptsReply of b, a, n and k is defined as: if Server is
\*   a member of the set containing "gouroboros" and "fixed", then (k is less
\*   than or equal to n, and it is not the case that b is true and n is greater
\*   than 0 and k equals 0, and the length of Drop of sU and a plus k is less
\*   than or equal to MaxUnacked), else RefAcceptsReply of b, n and k."
ServerAcceptsReply(b, a, n, k) ==
    IF Server \in {"gouroboros", "fixed"}
       THEN /\ k <= n
            /\ ~(b /\ n > 0 /\ k = 0)
            /\ Len(Drop(sU, a)) + k <= MaxUnacked
       ELSE RefAcceptsReply(b, n, k)

\* In English: "The faults a request reveals: a client accepting what the
\* reference refuses, a client refusing what the reference accepts (and,
\* named on its own, refusing it only because it asks past the window),
\* and an honest server sending what the reference refuses."
\* Literally: "RequestFaults of accepted, legal and overWindow is defined as
\*   the union of: (if Client is a member of Honest and accepted is true and
\*   legal is not true, then the set containing "clientAcceptedIllegal", else
\*   the empty set); (if Client is a member of Honest and accepted is not true
\*   and legal is true, then the set containing "clientRefusedLegal", else the
\*   empty set); (if Client is a member of Honest and accepted is not true and
\*   legal is true and overWindow is true, then the set containing
\*   "clientRefusedOverWindow", else the empty set); and (if Server is a member
\*   of Honest and legal is not true, then the set containing
\*   "serverSentIllegal", else the empty set)."
RequestFaults(accepted, legal, overWindow) ==
    (IF Client \in Honest /\ accepted /\ ~legal
        THEN {"clientAcceptedIllegal"} ELSE {})
    \cup (IF Client \in Honest /\ ~accepted /\ legal
             THEN {"clientRefusedLegal"} ELSE {})
    \cup (IF Client \in Honest /\ ~accepted /\ legal /\ overWindow
             THEN {"clientRefusedOverWindow"} ELSE {})
    \cup (IF Server \in Honest /\ ~legal THEN {"serverSentIllegal"} ELSE {})

\* In English: "The faults a reply reveals: a server accepting what the
\* reference refuses, and an honest client sending it."
\* Literally: "ReplyFaults of accepted and legal is defined as the union of:
\*   (if Server is a member of Honest and accepted is true and legal is not
\*   true, then the set containing "serverAcceptedIllegal", else the empty
\*   set); and (if Client is a member of Honest and legal is not true, then the
\*   set containing "clientSentIllegal", else the empty set)."
ReplyFaults(accepted, legal) ==
    (IF Server \in Honest /\ accepted /\ ~legal
        THEN {"serverAcceptedIllegal"} ELSE {})
    \cup (IF Client \in Honest /\ ~legal THEN {"clientSentIllegal"} ELSE {})

-----------------------------------------------------------------------------
(* Steps. *)

\* In English: "The client opens the protocol with MsgInit [S2]."
\* Literally: "ClientInit is defined as: st equals "StInit", and st in the next
\*   state equals "StIdle", and the other seven variables are unchanged."
ClientInit ==
    /\ st = "StInit"
    /\ st' = "StIdle"
    /\ UNCHANGED <<cU, sU, sAck, pend, nextId, nReq, faults>>

\* In English: "The server asks for up to n ids, acknowledging a, blocking
\* or not. The client judges the request against its FIFO."
\* Literally: "ServerRequestIds is defined as: st equals "StIdle", and nReq is
\*   less than MaxRequests, and there exists a b in BOOLEAN, an a in 0 through
\*   MaxUnacked plus 1, and an n in 0 through MaxUnacked plus 1 such that
\*   ServerMaySendIds of b, a and n, and, letting accepted be ClientAcceptsIds
\*   of b, a, n and cU, legal be RefAcceptsIds of b, a, n and cU, and overWin
\*   be (the length of cU minus a plus n is greater than MaxUnacked): st in the
\*   next state equals (if accepted is not true then "StError", else if b then
\*   "StTxIdsBlocking", else "StTxIdsNonBlocking"), and pend in the next state
\*   equals the record whose field kind is "ids", field b is b, field a is a,
\*   and field n is n, and faults in the next state equals the union of faults
\*   and RequestFaults of accepted, legal and overWin; and nReq in the next
\*   state equals nReq plus 1, and cU, sU, sAck and nextId are unchanged."
ServerRequestIds ==
    /\ st = "StIdle" /\ nReq < MaxRequests
    /\ \E b \in BOOLEAN, a \in 0..MaxUnacked + 1, n \in 0..MaxUnacked + 1 :
         /\ ServerMaySendIds(b, a, n)
         /\ LET accepted == ClientAcceptsIds(b, a, n, cU)
                legal    == RefAcceptsIds(b, a, n, cU)
                overWin  == Len(cU) - a + n > MaxUnacked   \* asks past the client's window
            IN /\ st' = IF ~accepted THEN "StError"
                        ELSE IF b THEN "StTxIdsBlocking"
                        ELSE "StTxIdsNonBlocking"
               /\ pend' = [kind |-> "ids", b |-> b, a |-> a, n |-> n]
               /\ faults' = faults \cup RequestFaults(accepted, legal, overWin)
    /\ nReq' = nReq + 1
    /\ UNCHANGED <<cU, sU, sAck, nextId>>

\* In English: "The server asks for the bodies of `ids`; `dup` means the
\* list names one id twice. Every client checks this the same way [G2][R3]."
\* Literally: "ServerRequestTxs is defined as: st equals "StIdle", and nReq is
\*   less than MaxRequests, and there exists an ids in the set of subsets of 1
\*   through MaxIds, and a dup in BOOLEAN, such that (if dup, then ids does not
\*   equal the empty set), and (Server equals "rogue", or dup is not true and
\*   ids is a subset of Range of sU), and, letting ok be RefAcceptsTxs of ids,
\*   dup and cU: st in the next state equals (if ok then "StTxs", else
\*   "StError"), and pend in the next state equals the record whose field kind
\*   is "txs" and field ids is ids, and faults in the next state equals the
\*   union of faults and (if Server is a member of Honest and ok is not true,
\*   then the set containing "serverSentIllegal", else the empty set); and nReq
\*   in the next state equals nReq plus 1, and cU, sU, sAck and nextId are
\*   unchanged."
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
\* at least one to a blocking request when its bound hi is at least one
\* (gOuroboros refuses to send an empty one for a count of at least one
\* [G4]; with ClientClamps the count it checks is the clamped one, so a
\* blocking request clamped to zero gets an empty reply) and no more than it may (with ClientClamps,
\* the gOuroboros client too sends only what fits from V16 [R4]); a rogue
\* client sends up to one more than asked. Each side drops the acknowledged ids and
\* appends the new ones; the gOuroboros server then acknowledges this reply
\* next time [G3]."
\* Literally: "ClientReplyIds is defined as: st is a member of the set
\*   containing "StTxIdsBlocking" and "StTxIdsNonBlocking", and, letting b be
\*   pend's b, a be pend's a, n be pend's n, hi be (if Client equals "rogue"
\*   then n plus 1, else if Client equals "reference" or ClientClamps is true
\*   then RefRoom of a, n and cU, else n), and lo be (if Client does not equal
\*   "rogue" and b is true and hi is greater than 0 then 1, else 0): there
\*   exists a k in lo through Min of hi and (MaxIds plus 1 minus nextId) such
\*   that, letting reply be Fresh of nextId and k, accepted be
\*   ServerAcceptsReply of b, a, n and k, and legal be RefAcceptsReply of b, n
\*   and k: st in the next state equals (if accepted then "StIdle", else
\*   "StError"), and cU in the next state equals Drop of cU and a, concatenated
\*   with reply, and sU in the next state equals (if Mutation equals
\*   "serverKeepsAcked" then sU concatenated with reply, else Drop of sU and a,
\*   concatenated with reply), and sAck in the next state equals k, and nextId
\*   in the next state equals nextId plus k, and faults in the next state
\*   equals the union of faults and ReplyFaults of accepted and legal; and pend
\*   in the next state equals NoRequest, and nReq is unchanged."
ClientReplyIds ==
    /\ st \in {"StTxIdsBlocking", "StTxIdsNonBlocking"}
    /\ LET b  == pend.b
           a  == pend.a
           n  == pend.n
           hi == IF Client = "rogue" THEN n + 1
                 ELSE IF Client = "reference" \/ ClientClamps THEN RefRoom(a, n, cU)
                 ELSE n
           lo == IF Client # "rogue" /\ b /\ hi > 0 THEN 1 ELSE 0
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
\* Literally: "ClientDone is defined as: st is a member of the set containing
\*   "StTxIdsBlocking", "StTxIdsNonBlocking" and "StTxs", and (Client equals
\*   "rogue", or st equals "StTxIdsBlocking"), and st in the next state equals
\*   (if st equals "StTxIdsBlocking" then "StDone", else "StError"), and pend
\*   in the next state equals NoRequest, and cU, sU, sAck, nextId, nReq and
\*   faults are unchanged."
ClientDone ==
    /\ st \in {"StTxIdsBlocking", "StTxIdsNonBlocking", "StTxs"}
    /\ Client = "rogue" \/ st = "StTxIdsBlocking"
    /\ st' = IF st = "StTxIdsBlocking" THEN "StDone" ELSE "StError"
    /\ pend' = NoRequest
    /\ UNCHANGED <<cU, sU, sAck, nextId, nReq, faults>>

\* In English: "The client replies with bodies for some of the requested
\* ids; a rogue client may add one nobody asked for. Every server refuses
\* that [G3][R6]."
\* Literally: "ClientReplyTxs is defined as: st equals "StTxs", and there
\*   exists an extra in (if Client equals "rogue" then BOOLEAN, else the set
\*   containing FALSE) such that st in the next state equals (if extra then
\*   "StError", else "StIdle"); and pend in the next state equals NoRequest,
\*   and cU, sU, sAck, nextId, nReq and faults are unchanged."
ClientReplyTxs ==
    /\ st = "StTxs"
    /\ \E extra \in IF Client = "rogue" THEN BOOLEAN ELSE {FALSE} :
         /\ st' = IF extra THEN "StError" ELSE "StIdle"
    /\ pend' = NoRequest
    /\ UNCHANGED <<cU, sU, sAck, nextId, nReq, faults>>

\* In English: "The run is over: done, refused, or out of requests. Nothing
\* changes any more; this stutter step tells TLC that stopping here is not
\* a deadlock."
\* Literally: "Finished is defined as: (st is a member of the set containing
\*   "StDone" and "StError", or st equals "StIdle" and nReq equals
\*   MaxRequests), and vars is unchanged."
Finished ==
    /\ \/ st \in {"StDone", "StError"}
       \/ st = "StIdle" /\ nReq = MaxRequests
    /\ UNCHANGED vars

\* In English: "A step is any one client or server message, or staying
\* finished."
\* Literally: "Next is defined as: ClientInit, or ServerRequestIds, or
\*   ServerRequestTxs, or ClientReplyIds, or ClientDone, or ClientReplyTxs, or
\*   Finished."
Next ==
    \/ ClientInit
    \/ ServerRequestIds \/ ServerRequestTxs
    \/ ClientReplyIds \/ ClientDone \/ ClientReplyTxs
    \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "The client never answers a request the reference client
\* would refuse."
\* Literally: "ClientRefusesIllegal is defined as: "clientAcceptedIllegal" is
\*   not a member of faults."
ClientRefusesIllegal == "clientAcceptedIllegal" \notin faults

\* In English: "The client never refuses a request the reference client
\* would answer."
\* Literally: "ClientRefusesOnlyIllegal is defined as: "clientRefusedLegal" is
\*   not a member of faults."
ClientRefusesOnlyIllegal == "clientRefusedLegal" \notin faults

\* In English: "An honest server never sends a request the reference
\* client refuses."
\* Literally: "ServerSendsLegal is defined as: "serverSentIllegal" is not a
\*   member of faults."
ServerSendsLegal == "serverSentIllegal" \notin faults

\* In English: "The server never accepts a reply the reference server
\* would refuse."
\* Literally: "ServerRefusesIllegal is defined as: "serverAcceptedIllegal" is
\*   not a member of faults."
ServerRefusesIllegal == "serverAcceptedIllegal" \notin faults

\* In English: "An honest client never sends a reply the reference server
\* refuses."
\* Literally: "ClientSendsLegal is defined as: "clientSentIllegal" is not a
\*   member of faults."
ClientSendsLegal == "clientSentIllegal" \notin faults

\* In English: "Whenever a blocking request is being answered, nothing
\* remained unacknowledged after its acknowledgement; whenever a
\* non-blocking one is, something did [S3][S5]."
\* Literally: "BlockingRule is defined as: if st equals "StTxIdsBlocking", then
\*   the length of cU minus pend's a equals 0."
BlockingRule ==
    st = "StTxIdsBlocking" => Len(cU) - pend.a = 0
\* Literally: "NonBlockingRule is defined as: if st equals
\*   "StTxIdsNonBlocking", then the length of cU minus pend's a is greater than
\*   0."
NonBlockingRule ==
    st = "StTxIdsNonBlocking" => Len(cU) - pend.a > 0

\* In English: "The client never refuses a request only because it asks
\* for more ids than fit its window, when the reference would clamp it
\* (from V16 [S4][R4])."
\* Literally: "ClampsOverWindow is defined as: "clientRefusedOverWindow" is not
\*   a member of faults."
ClampsOverWindow == "clientRefusedOverWindow" \notin faults

\* In English: "The client's FIFO never holds more than the window."
\* Literally: "WindowBound is defined as: the length of cU is less than or
\*   equal to MaxUnacked."
WindowBound == Len(cU) <= MaxUnacked

\* In English: "Between messages, with both sides honest, the two FIFOs
\* are the same list of ids [S5]."
\* Literally: "ViewsAgree is defined as: if Server is a member of Honest and
\*   Client is a member of Honest and st equals "StIdle", then sU equals cU."
ViewsAgree ==
    (Server \in Honest /\ Client \in Honest /\ st = "StIdle") => sU = cU

\* In English: "Two honest sides never refuse each other."
\* Literally: "HonestNeverRefused is defined as: if Server is a member of
\*   Honest and Client is a member of Honest, then st does not equal
\*   "StError"."
HonestNeverRefused ==
    (Server \in Honest /\ Client \in Honest) => st /= "StError"

-----------------------------------------------------------------------------
(* Reachability probes, each EXPECTED to be violated, so that a passing     *)
(* invariant is not passing only because the model never got near the     *)
(* edge. Run each alone with TxSubmissionProbesBug.cfg (keep one line).  *)

\* In English: "Probes, each expected to be violated: no blocking request, no
\* non-blocking request, no MsgRequestTxs, no MsgDone, and a window that never
\* fills."
\* Literally: "ProbeNoBlocking is defined as: st does not equal
\*   "StTxIdsBlocking"."
ProbeNoBlocking    == st /= "StTxIdsBlocking"
\* Literally: "ProbeNoNonBlocking is defined as: st does not equal
\*   "StTxIdsNonBlocking"."
ProbeNoNonBlocking == st /= "StTxIdsNonBlocking"
\* Literally: "ProbeNoTxs is defined as: st does not equal "StTxs"."
ProbeNoTxs         == st /= "StTxs"
\* Literally: "ProbeNoDone is defined as: st does not equal "StDone"."
ProbeNoDone        == st /= "StDone"
\* Literally: "ProbeWindowNeverFull is defined as: the length of cU is less
\*   than MaxUnacked."
ProbeWindowNeverFull == Len(cU) < MaxUnacked
\* "No request ever both acknowledges and leaves ids outstanding."
\* Literally: "ProbeNoPartialAck is defined as: it is not the case that st
\*   equals "StTxIdsNonBlocking" and pend's a is greater than 0."
ProbeNoPartialAck ==
    ~(st = "StTxIdsNonBlocking" /\ pend.a > 0)
\* In English: "No non-blocking request asking for at least one id is ever
\* clamped to zero: run against a clamping config (V16, a full window)."
\* Literally: "ProbeNoZeroClamp is defined as: it is not the case that st
\*   equals "StTxIdsNonBlocking" and pend's n is greater than 0 and RefRoom of
\*   pend's a, pend's n and cU equals 0."
ProbeNoZeroClamp ==
    ~(st = "StTxIdsNonBlocking" /\ pend.n > 0 /\ RefRoom(pend.a, pend.n, cU) = 0)
=============================================================================
