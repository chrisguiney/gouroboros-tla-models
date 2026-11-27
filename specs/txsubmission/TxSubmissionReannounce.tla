------------------------ MODULE TxSubmissionReannounce ------------------------
(***************************************************************************)
(* tx-submission when the outbound's mempool removes a transaction and    *)
(* adds it back: what ids may a reference outbound announce, and what do  *)
(* the gOuroboros checks make of them. Also the byte limits the gOuroboros *)
(* Server applies to a reply of bodies.                                    *)
(*                                                                         *)
(* The reference outbound remembers the mempool index of the last id it    *)
(* announced and announces only entries after it [R1]. An index belongs to *)
(* an entry, not to a transaction: a transaction removed from the mempool  *)
(* and added back (a fork switch re-adds the transactions of the blocks    *)
(* rolled back) gets a new index, so the outbound announces it again, even *)
(* while its first announcement is still unacknowledged. The reference     *)
(* inbound expects this [R2]. A single reply is read from one mempool     *)
(* snapshot, in which a transaction appears once, so no reply names a      *)
(* transaction twice.                                                      *)
(*                                                                         *)
(* gOuroboros (reconcileTxIds [G1]) refuses a reply that names an id twice *)
(* and, on 7cd17437, also one that names an id still in the window. The    *)
(* Client applies it to its own application's reply [G2] and fails the     *)
(* connection when it refuses.                                             *)
(*                                                                         *)
(* Questions:                                                              *)
(*   HonestNeverRefused       nothing a reference outbound announces, and  *)
(*                            no reply of bodies an honest outbound sends, *)
(*                            is refused.                                  *)
(*   NoDuplicateWithinReply   no reply names one transaction twice (DRIFT  *)
(*                            N22: the extra gOuroboros check costs        *)
(*                            nothing against a reference peer).           *)
(*   ViewsAgree               between requests both sides hold the same    *)
(*                            window, repeats included: acknowledgement is *)
(*                            by count.                                    *)
(*   WindowBound              the window stays within MaxUnacked.          *)
(*                                                                         *)
(* Sources.                                                                *)
(*   [R1] ouroboros-network 4646039f05eb ouroboros-network/lib/Ouroboros/  *)
(*        Network/TxSubmission/Outbound.hs 116-175: the outbound appends   *)
(*        `mempoolTxIdsAfter lastIdx`, asserting only that the indices are *)
(*        fresh (124-125); one snapshot per reply (147-148, 170-171).      *)
(*   [R2] ouroboros-network 4646039f .../TxSubmission/Inbound/V1.hs        *)
(*        300-306 ("duplicate txids within the same window") and           *)
(*        .../Inbound/V2/State.hs 370-374 ("The same TxKey may            *)
(*        legitimately appear more than once in peerUnacknowledgedTxIds   *)
(*        (e.g. a fork switch on the sender re-adds a tx to the mempool   *)
(*        under a new idx").                                               *)
(*   [R3] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.  *)
(*        tex 1323-1418: the request rules; ids are acknowledged by count. *)
(*   [R4] ouroboros-network 4646039f .../TxSubmission/Inbound/V2/          *)
(*        Policy.hs: max_TX_SIZE 65540; the ingress limit is the window of *)
(*        maximum transactions and their announcements plus 10%.           *)
(*   gOuroboros 7cd17437, protocol/txsubmission/:                          *)
(*   [G1] validation.go reconcileTxIds (the "reply repeats outstanding     *)
(*        transaction ID" check), validateAndOrderTxBodies (each body      *)
(*        1..MaxTxSizeBytes, the running total within                      *)
(*        MaxPendingMessageBytes and MaxDecodedTxBytes).                   *)
(*   [G2] client.go handleRequestTxIds: the application's reply goes       *)
(*        through reconcileTxIds before it is sent; an error from the      *)
(*        handler fails the protocol.                                      *)
(*   [G3] server.go RequestTxIds: every request is blocking and            *)
(*        acknowledges the whole window, so the Server's window is empty   *)
(*        whenever a reply arrives and the repeat check cannot fire there. *)
(*   [G4] txsubmission.go MaxUnackedTxIds 10, MaxTxSizeBytes 65540,        *)
(*        TxIdReplyEntryBytes 44, MaxPendingMessageBytes = 10 * (44 +      *)
(*        65540) * 11 / 10, MaxDecodedTxBytes = 10 * 65540.                *)
(*                                                                         *)
(* One request is outstanding at a time; TxSubmissionPipelined.tla covers *)
(* pipelining, which does not change what the outbound announces.          *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,          \* the transactions (ids) that exist
    MaxIdx,       \* mempool indices available (each add uses one; keeps it finite)
    MaxUnacked,   \* the window (10)
    Size,         \* each transaction's body size in bytes
    MaxTx,        \* MaxTxSizeBytes
    RetainedLimit,\* MaxPendingMessageBytes
    DecodedLimit, \* MaxDecodedTxBytes
    Inbound,      \* "reference": any request the rules allow; "gouroboros": the Server [G3]
    Fixed         \* TRUE: reconcileTxIds no longer refuses an id still in the window

\* In English: "The ids a queue holds, as a set."
Range(s) == {s[i] : i \in 1..Len(s)}

\* In English: "The queue without its first a ids."
Drop(s, a) == SubSeq(s, a + 1, Len(s))

\* In English: "Some index is named twice in s."
HasDup(s) == \E i, j \in 1..Len(s) : i < j /\ s[i] = s[j]

\* In English: "The smaller of two numbers."
Min(a, b) == IF a < b THEN a ELSE b

\* In English: "The sum of the body sizes of a set of transactions."
RECURSIVE Bytes(_)
Bytes(S) == IF S = {} THEN 0
            ELSE LET t == CHOOSE x \in S : TRUE IN Size[t] + Bytes(S \ {t})

None == [kind |-> "none", ack |-> 0, req |-> 0, blocking |-> FALSE, ids |-> {}]

VARIABLES
    mempool,  \* the outbound's mempool: a sequence of [tx, idx], oldest first
    nextIdx,  \* the index the next added transaction gets
    lastIdx,  \* the index of the last entry the outbound announced
    outQ,     \* the outbound's window of announced transaction ids
    inQ,      \* the inbound's window
    pend,     \* the request being answered, or None
    refused,  \* "" or why a check refused (the connection then ends)
    dupReply  \* some reply named one transaction twice

vars == <<mempool, nextIdx, lastIdx, outQ, inQ, pend, refused, dupReply>>

\* In English: "An empty mempool, nothing announced."
Init ==
    /\ mempool = <<>> /\ nextIdx = 1 /\ lastIdx = 0
    /\ outQ = <<>> /\ inQ = <<>>
    /\ pend = None /\ refused = "" /\ dupReply = FALSE

\* In English: "The transactions in the mempool."
InPool == {mempool[i].tx : i \in 1..Len(mempool)}

-----------------------------------------------------------------------------
(* The outbound's mempool. *)

\* In English: "A transaction not in the mempool is added under the next
\* index; this is also how a removed transaction comes back."
Add ==
    /\ refused = ""
    /\ nextIdx <= MaxIdx
    /\ \E t \in Txs \ InPool :
        mempool' = Append(mempool, [tx |-> t, idx |-> nextIdx])
    /\ nextIdx' = nextIdx + 1
    /\ UNCHANGED <<lastIdx, outQ, inQ, pend, refused, dupReply>>

\* In English: "A transaction leaves the mempool (included in a block, or
\* rolled back and about to be re-added)."
Remove ==
    /\ refused = ""
    /\ \E i \in 1..Len(mempool) :
        mempool' = SubSeq(mempool, 1, i - 1) \o Drop(mempool, i)
    /\ UNCHANGED <<nextIdx, lastIdx, outQ, inQ, pend, refused, dupReply>>

-----------------------------------------------------------------------------
(* The inbound. *)

\* In English: "The inbound asks for ids with nothing outstanding. A
\* reference inbound sends any request the rules [R3] allow; the gOuroboros
\* Server always acknowledges its whole window with a blocking request
\* [G3]."
RequestIds ==
    /\ refused = "" /\ pend = None
    /\ \E b \in BOOLEAN, a \in 0..Len(inQ), n \in 0..MaxUnacked :
        /\ Inbound = "gouroboros" => b /\ a = Len(inQ)
        /\ n > 0 \/ (~b /\ a > 0)
        /\ b <=> Len(inQ) - a = 0
        /\ Len(inQ) - a + n <= MaxUnacked
        /\ pend' = [kind |-> "ids", ack |-> a, req |-> n, blocking |-> b, ids |-> {}]
        /\ inQ' = Drop(inQ, a)
    /\ UNCHANGED <<mempool, nextIdx, lastIdx, outQ, refused, dupReply>>

\* In English: "The inbound asks for the bodies of some distinct ids in its
\* window."
RequestBodies ==
    /\ refused = "" /\ pend = None
    /\ \E S \in SUBSET Range(inQ) :
        /\ S # {}
        /\ pend' = [kind |-> "bodies", ack |-> 0, req |-> 0, blocking |-> FALSE, ids |-> S]
    /\ UNCHANGED <<mempool, nextIdx, lastIdx, outQ, inQ, refused, dupReply>>

-----------------------------------------------------------------------------
(* The outbound: a reference mempool reader [R1] behind the gOuroboros     *)
(* Client's checks [G2].                                                    *)

\* In English: "The mempool entries after the last announced index, in
\* order: what the outbound may announce next."
After == SelectSeq(mempool, LAMBDA e : e.idx > lastIdx)

\* In English: "Why reconcileTxIds refuses a reply, or "" [G1]: an id twice
\* within the reply, or (unless Fixed) an id still in the window."
ReplyRefusal(remaining, reply) ==
    IF HasDup(reply) THEN "duplicateInReply"
    ELSE IF ~Fixed /\ Range(reply) \cap Range(remaining) # {}
         THEN "repeatsOutstanding"
    ELSE ""

\* In English: "The outbound answers a request for ids with the first
\* entries after lastIdx, as many as asked; a blocking request waits until
\* there is one. gOuroboros checks the reply before sending it."
ReplyIds ==
    /\ refused = "" /\ pend.kind = "ids"
    /\ pend.blocking => Len(After) > 0
    /\ LET k         == Min(pend.req, Len(After))
           entries   == SubSeq(After, 1, k)
           reply     == [i \in 1..k |-> entries[i].tx]
           remaining == Drop(outQ, pend.ack)
           why       == ReplyRefusal(remaining, reply)
       IN /\ dupReply' = (dupReply \/ HasDup(reply))
          /\ IF why = ""
             THEN /\ outQ' = remaining \o reply
                  /\ inQ' = inQ \o reply
                  /\ lastIdx' = IF k = 0 THEN lastIdx ELSE entries[k].idx
                  /\ refused' = ""
             ELSE /\ refused' = why
                  /\ UNCHANGED <<outQ, inQ, lastIdx>>
    /\ pend' = None
    /\ UNCHANGED <<mempool, nextIdx>>

\* In English: "The outbound answers a request for bodies with those still
\* in its mempool. The gOuroboros Server checks each body against
\* MaxTxSizeBytes and the running total against MaxPendingMessageBytes and
\* MaxDecodedTxBytes [G1]."
ReplyBodies ==
    /\ refused = "" /\ pend.kind = "bodies"
    /\ LET sent == pend.ids \cap InPool IN
        refused' = IF Inbound = "gouroboros" /\
                      (\/ \E t \in sent : Size[t] > MaxTx
                       \/ Bytes(sent) > RetainedLimit
                       \/ Bytes(sent) > DecodedLimit)
                   THEN "bytes" ELSE ""
    /\ pend' = None
    /\ UNCHANGED <<mempool, nextIdx, lastIdx, outQ, inQ, dupReply>>

\* In English: "The connection ended, or nothing more can happen."
Quiet ==
    /\ refused # "" \/ (nextIdx > MaxIdx /\ pend.kind = "ids" /\ pend.blocking /\ Len(After) = 0)
    /\ UNCHANGED vars

Next ==
    \/ Add \/ Remove
    \/ RequestIds \/ RequestBodies
    \/ ReplyIds \/ ReplyBodies
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Every variable holds a value of the expected kind."
TypeOK ==
    /\ nextIdx \in 1..MaxIdx + 1
    /\ lastIdx \in 0..MaxIdx
    /\ Range(outQ) \subseteq Txs /\ Range(inQ) \subseteq Txs
    /\ dupReply \in BOOLEAN

\* In English: "No check refused anything: the connection stays up."
HonestNeverRefused == refused = ""

\* In English: "No reply named one transaction twice."
NoDuplicateWithinReply == ~dupReply

\* In English: "With nothing outstanding, both sides hold the same window."
ViewsAgree == (refused = "" /\ pend = None) => inQ = outQ

\* In English: "The window stays within MaxUnacked."
WindowBound == Len(outQ) <= MaxUnacked

\* The body sizes the configs use: one transaction at MaxTx, one below it.
ScaledSize == [t \in Txs |-> IF t = "a" THEN 3 ELSE 2]

\* Probe (expected to be violated): "the window never holds a transaction
\* twice". Its violation shows the re-announcement is reachable.
ProbeNoRepeatInWindow == ~HasDup(outQ)
=============================================================================
