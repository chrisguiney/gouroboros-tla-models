----------------------- MODULE LocalMessageNotification -----------------------
(***************************************************************************)
(* Model 11, part 3: DMQ local message notification (node-to-client).     *)
(*                                                                         *)
(* A local client asks the node for new messages. A NON-BLOCKING request   *)
(* is answered at once, possibly with nothing. A BLOCKING request is       *)
(* answered only once there is at least one message, and the answer is    *)
(* never empty. MsgClientDone from StIdle ends the run.                    *)
(*                                                                         *)
(* The gOuroboros server (protocol/localmessagenotification/server.go)     *)
(* answers a blocking request inside its message handler                   *)
(* (handleBlockingRequest): it takes the lock, drains the queue, and if    *)
(* that gave nothing, releases the lock and waits in WaitForMessage for a  *)
(* signal on newMessageSignal, a channel with ONE slot. AddMessage puts a  *)
(* signal in the slot if it is empty. WaitForMessage is also exported, so  *)
(* the application can wait on the same channel. One signal wakes one      *)
(* waiter.                                                                 *)
(*                                                                         *)
(* The gOuroboros client (client.go) hands every reply to                  *)
(* ReplyMessagesFunc, including an empty blocking reply.                   *)
(*                                                                         *)
(* Questions:                                                              *)
(*   WakeupNotLost   a handler waiting for messages while messages are     *)
(*                   queued always has a signal coming. (If not, the       *)
(*                   client's blocking request is never answered.)         *)
(*   NoEmptyBlocking the client never accepts an empty blocking reply.     *)
(*                                                                         *)
(* Sources:                                                                *)
(*   CIP-0137 (cardano-foundation/CIPs 03387471), CIP-0137/README.md:      *)
(*   [C1] 652-721: states, agency, transitions; the blocking reply "is     *)
(*        guaranteed to contain at least one message"; CDDL               *)
(*        msgReplyMessagesBlocking = [2, [+ message]].                     *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e:           *)
(*   [S1] docs/network-spec/miniprotocols.tex 27-36: an unexpected message *)
(*        aborts the connection.                                           *)
(*   Reference, IntersectMBO/dmq-node a267003c:                            *)
(*   [R1] dmq-node/src/DMQ/Protocol/LocalMsgNotification/Type.hs 45-77:    *)
(*        MsgRequest, MsgReply (a BlockingReplyList: non-empty when        *)
(*        blocking), MsgClientDone; agency.                                *)
(*   [R2] dmq-node/src/DMQ/Protocol/LocalMsgNotification/Codec.hs 137-143: *)
(*        decoding an empty blocking reply fails.                          *)
(*   [R3] dmq-node/src/DMQ/NodeToClient/LocalMsgNotification.hs 69-91: the *)
(*        server blocks in STM until the mempool has a message (an STM     *)
(*        retry is woken by every change it read, so no wakeup is lost).   *)
(*   gOuroboros, blinklabs-io/gouroboros 61046085:                         *)
(*   [G1] protocol/localmessagenotification/server.go: AddMessage,         *)
(*        WaitForMessage, handleBlockingRequest,                           *)
(*        handleNonBlockingRequest, drainValidMessagesLocked.              *)
(*   [G2] protocol/localmessagenotification/client.go:                     *)
(*        handleReplyMessagesBlocking.                                     *)
(*                                                                         *)
(* Not modelled: message validation and the replay cache, hasMore (the     *)
(* gOuroboros server always sends FALSE and the whole queue), timeouts,    *)
(* Stop while a blocking request waits.                                    *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    MaxAdds,      \* how many messages AddMessage queues in total
    MaxRequests,  \* how many requests the client sends in total
    AppWaits,     \* TRUE: the application also calls WaitForMessage once
    \* FALSE in gOuroboros. TRUE: AddMessage wakes EVERY waiter (a
    \* broadcast), as an STM retry does in the reference [R3].
    Broadcast,
    \* Mutation, FALSE normally. TRUE: the signal channel has no slot, so a
    \* signal with no waiter ready is dropped.
    Unbuffered,
    \* TRUE: a rogue server may answer a blocking request with nothing.
    RogueServer,
    \* FALSE in gOuroboros. TRUE: the client refuses an empty blocking
    \* reply, as the reference codec does [R2].
    ClientRefusesEmpty

VARIABLES
    cs,       \* the protocol state: "Idle", "BusyBlocking",
              \* "BusyNonBlocking", "Done"
    sent,     \* requests the client has sent (model bound)
    q,        \* messages queued at the server
    adds,     \* AddMessage calls so far (model bound)
    signal,   \* TRUE while newMessageSignal's slot holds a signal
    hpc,      \* the server's handler: "idle", "check", "unlocked" (found
              \* nothing, released the lock), "wait" (in WaitForMessage)
    aw,       \* the application's WaitForMessage: "no", "wait", "done"
    reply,    \* the reply in flight: "none", or its size and kind
    emptyBlockingAccepted, \* TRUE once the client accepted one
    refused   \* TRUE once the client refused a reply [S1]

vars == <<cs, sent, q, adds, signal, hpc, aw, reply, emptyBlockingAccepted,
          refused>>

NoReply == [kind |-> "none", size |-> 0]

Init ==
    /\ cs = "Idle" /\ sent = 0
    /\ q = 0 /\ adds = 0 /\ signal = FALSE
    /\ hpc = "idle" /\ aw = "no"
    /\ reply = NoReply
    /\ emptyBlockingAccepted = FALSE /\ refused = FALSE

-----------------------------------------------------------------------------
(* The client.                                                             *)

\* In English: "In StIdle the client sends a blocking or non-blocking
\* request; the server's handler starts on it."
Request ==
    /\ cs = "Idle" /\ ~refused /\ sent < MaxRequests
    /\ \E blocking \in BOOLEAN :
        cs' = IF blocking THEN "BusyBlocking" ELSE "BusyNonBlocking"
    /\ hpc' = "check"
    /\ sent' = sent + 1
    /\ UNCHANGED <<q, adds, signal, aw, reply, emptyBlockingAccepted, refused>>

\* In English: "The client ends the run from StIdle."
ClientDone ==
    /\ cs = "Idle" /\ ~refused
    /\ cs' = "Done"
    /\ UNCHANGED <<sent, q, adds, signal, hpc, aw, reply,
                   emptyBlockingAccepted, refused>>

\* In English: "A reply arrives and the client is back in StIdle. An empty
\* blocking reply is accepted (gOuroboros) or refused [R2]."
Receive ==
    /\ reply /= NoReply
    /\ IF reply.kind = "blocking" /\ reply.size = 0
          THEN IF ClientRefusesEmpty
                  THEN /\ refused' = TRUE
                       /\ UNCHANGED emptyBlockingAccepted
                  ELSE /\ emptyBlockingAccepted' = TRUE
                       /\ UNCHANGED refused
          ELSE UNCHANGED <<emptyBlockingAccepted, refused>>
    /\ cs' = "Idle" /\ reply' = NoReply
    /\ UNCHANGED <<sent, q, adds, signal, hpc, aw>>

-----------------------------------------------------------------------------
(* The server's handler [G1].                                              *)

\* In English: "The handler takes the lock and drains the queue. A
\* non-blocking request is answered with whatever was there. A blocking
\* one is answered if that was something; otherwise the handler goes to
\* wait. A rogue server may answer a blocking request with nothing."
HandlerCheck ==
    /\ hpc = "check"
    /\ \/ /\ cs = "BusyNonBlocking"
          /\ reply' = [kind |-> "nonblocking", size |-> q]
          /\ q' = 0 /\ hpc' = "idle"
       \/ /\ cs = "BusyBlocking" /\ q > 0
          /\ reply' = [kind |-> "blocking", size |-> q]
          /\ q' = 0 /\ hpc' = "idle"
       \/ /\ cs = "BusyBlocking" /\ q = 0 /\ ~RogueServer
          /\ hpc' = "unlocked"
          /\ UNCHANGED <<reply, q>>
       \/ /\ cs = "BusyBlocking" /\ q = 0 /\ RogueServer
          /\ reply' = [kind |-> "blocking", size |-> 0]
          /\ hpc' = "idle"
          /\ UNCHANGED q
    /\ UNCHANGED <<cs, sent, adds, signal, aw, emptyBlockingAccepted, refused>>

\* In English: "Having released the lock, the handler calls WaitForMessage.
\* An AddMessage may run in between."
HandlerWait ==
    /\ hpc = "unlocked"
    /\ hpc' = "wait"
    /\ UNCHANGED <<cs, sent, q, adds, signal, aw, reply, emptyBlockingAccepted,
                   refused>>

\* In English: "The waiting handler takes the signal from the slot and
\* looks at the queue again."
HandlerWake ==
    /\ hpc = "wait" /\ signal
    /\ signal' = FALSE /\ hpc' = "check"
    /\ UNCHANGED <<cs, sent, q, adds, aw, reply, emptyBlockingAccepted,
                   refused>>

-----------------------------------------------------------------------------
(* The application.                                                        *)

\* In English: "The application calls WaitForMessage."
AppWait ==
    /\ AppWaits /\ aw = "no"
    /\ aw' = "wait"
    /\ UNCHANGED <<cs, sent, q, adds, signal, hpc, reply,
                   emptyBlockingAccepted, refused>>

\* In English: "The application's WaitForMessage takes the signal."
AppWake ==
    /\ aw = "wait" /\ signal
    /\ signal' = FALSE /\ aw' = "done"
    /\ UNCHANGED <<cs, sent, q, adds, hpc, reply, emptyBlockingAccepted,
                   refused>>

\* In English: "AddMessage queues a message, then signals. gOuroboros: put
\* a signal in the slot if it is empty. Broadcast: wake every waiter,
\* including a handler that has released the lock but not yet started to
\* wait (it took the channel to wait on under the lock).
\* Unbuffered (mutation): hand the signal to one ready waiter, or drop it."
AddMessage ==
    /\ adds < MaxAdds
    /\ q' = q + 1 /\ adds' = adds + 1
    /\ IF Broadcast
          \* The handler took the channel to wait on while it held the lock,
          \* so an add in the gap before it waits also wakes it.
          THEN /\ hpc' = IF hpc \in {"unlocked", "wait"} THEN "check" ELSE hpc
               /\ aw' = IF aw = "wait" THEN "done" ELSE aw
               /\ UNCHANGED signal
       ELSE IF Unbuffered
          THEN \/ /\ hpc = "wait" /\ hpc' = "check" /\ UNCHANGED aw
               \/ /\ aw = "wait" /\ aw' = "done" /\ UNCHANGED hpc
               \/ /\ hpc /= "wait" /\ aw /= "wait" /\ UNCHANGED <<hpc, aw>>
             /\ UNCHANGED signal
       ELSE /\ signal' = TRUE
            /\ UNCHANGED <<hpc, aw>>
    /\ UNCHANGED <<cs, sent, reply, emptyBlockingAccepted, refused>>

-----------------------------------------------------------------------------

\* In English: "Nothing more happens: the run ended or was refused, or the
\* client has sent its requests and no step is pending - including a
\* blocking request that waits for a message that will never be added."
Quiet ==
    /\ \/ cs = "Done" \/ refused
       \/ /\ sent = MaxRequests /\ cs = "Idle"
       \/ /\ cs = "BusyBlocking" /\ hpc = "wait" /\ q = 0 /\ adds = MaxAdds
    /\ aw /= "wait" \/ adds = MaxAdds
    /\ UNCHANGED vars

Next ==
    \/ Request \/ ClientDone \/ Receive
    \/ HandlerCheck \/ HandlerWait \/ HandlerWake
    \/ AppWait \/ AppWake \/ AddMessage
    \/ Quiet

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "A handler waiting while messages are queued always has a
\* signal in the slot to wake it."
WakeupNotLost == (hpc = "wait" /\ q > 0) => signal

\* In English: "The client never accepts an empty blocking reply [C1][R2]."
NoEmptyBlocking == ~emptyBlockingAccepted

\* Probes, each EXPECTED to be violated.
\* In English: "The handler never waits." Violated = it does.
ProbeNeverWaits == hpc /= "wait"
\* In English: "A blocking request is never answered after a wait."
\* Violated = the handler waits, wakes, and answers.
ProbeNeverWokenReply == ~(reply.kind = "blocking" /\ reply.size > 0 /\ sent = 1
                          /\ adds = MaxAdds)
\* In English: "The application's WaitForMessage never returns." Violated =
\* it does.
ProbeAppNeverWakes == aw /= "done"
=============================================================================
