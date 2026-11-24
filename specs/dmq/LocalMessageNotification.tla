----------------------- MODULE LocalMessageNotification -----------------------
(***************************************************************************)
(* Model `dmq`, part 3: DMQ local message notification (node-to-client).     *)
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
(*   AppWaitOutlivesRun an application WaitForMessage is never ended by    *)
(*                   the client ending a run: the server restarts and      *)
(*                   keeps its queue, so the wait still has a message to   *)
(*                   wait for. Only Stop (not modelled) ends it.           *)
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
(*        93-94: MsgClientDone ends only the run (mdone); the mempool the  *)
(*        server reads belongs to the node and outlives it.                *)
(*   [S2] docs/network-spec/connection-manager.tex 492-496: the server     *)
(*        side "should be restarted in its initial state".                 *)
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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
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
    ClientRefusesEmpty,
    \* FALSE: MsgClientDone ends the protocol for good (gOuroboros before
    \* the restart fix). TRUE: the server restarts in StIdle and the client
    \* may start a new run [S2].
    ServerRestarts,
    \* With ServerRestarts. TRUE: the restart closes the ended run's stop
    \* channel, which WaitForMessage also watched, so an application wait
    \* returns a shutdown error (the restart fix's first draft). FALSE:
    \* WaitForMessage watches only the server's own Stop and the
    \* connection, and survives the restart.
    RestartReleasesWaiters

VARIABLES
    cs,       \* the protocol state: "Idle", "BusyBlocking",
              \* "BusyNonBlocking", "Done"
    sent,     \* requests the client has sent (model bound)
    q,        \* messages queued at the server
    adds,     \* AddMessage calls so far (model bound)
    signal,   \* TRUE while newMessageSignal's slot holds a signal
    hpc,      \* the server's handler: "idle", "check", "unlocked" (found
              \* nothing, released the lock), "wait" (in WaitForMessage)
    aw,       \* the application's WaitForMessage: "no", "wait", "done",
              \* or "failed" (returned a shutdown error)
    reply,    \* the reply in flight: "none", or its size and kind
    emptyBlockingAccepted, \* TRUE once the client accepted one
    refused   \* TRUE once the client refused a reply [S1]

\* Literally: "vars is defined as the tuple of all ten variables."
vars == <<cs, sent, q, adds, signal, hpc, aw, reply, emptyBlockingAccepted,
          refused>>

\* In English: "No reply in flight: kind "none", size 0."
\* Literally: "NoReply is defined as the record whose field kind is "none" and
\*   whose field size is 0."
NoReply == [kind |-> "none", size |-> 0]

\* In English: "The client is in StIdle and has sent nothing, the queue is
\* empty, nothing has been added or signalled, the handler and the application
\* are idle, no reply is in flight, and nothing has been accepted or refused."
\* Literally: "Init is defined as: cs equals "Idle" and sent equals 0, and q
\*   equals 0 and adds equals 0 and signal equals FALSE, and hpc equals "idle"
\*   and aw equals "no", and reply equals NoReply, and emptyBlockingAccepted
\*   equals FALSE and refused equals FALSE."
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
\* Literally: "Request is defined as: cs equals "Idle" and refused is not true
\*   and sent is less than MaxRequests, and there exists a blocking in BOOLEAN
\*   such that cs in the next state equals (if blocking then "BusyBlocking",
\*   else "BusyNonBlocking"), and hpc in the next state equals "check", and
\*   sent in the next state equals sent plus 1, and q, adds, signal, aw, reply,
\*   emptyBlockingAccepted and refused are unchanged."
Request ==
    /\ cs = "Idle" /\ ~refused /\ sent < MaxRequests
    /\ \E blocking \in BOOLEAN :
        cs' = IF blocking THEN "BusyBlocking" ELSE "BusyNonBlocking"
    /\ hpc' = "check"
    /\ sent' = sent + 1
    /\ UNCHANGED <<q, adds, signal, aw, reply, emptyBlockingAccepted, refused>>

\* In English: "The client ends the run from StIdle. Without a restart the
\* protocol is done. With one, the server is back in StIdle for the next
\* run, with its queue as it was; an application wait is ended with an
\* error only if the restart closes a channel the wait watches."
\* Literally: "ClientDone is defined as: cs equals "Idle" and refused is not
\*   true, and cs in the next state equals (if ServerRestarts then "Idle",
\*   else "Done"), and aw in the next state equals (if ServerRestarts is true
\*   and RestartReleasesWaiters is true and aw equals "wait", then "failed",
\*   else aw), and sent, q, adds, signal, hpc, reply, emptyBlockingAccepted
\*   and refused are unchanged."
ClientDone ==
    /\ cs = "Idle" /\ ~refused
    /\ cs' = IF ServerRestarts THEN "Idle" ELSE "Done"
    /\ aw' = IF ServerRestarts /\ RestartReleasesWaiters /\ aw = "wait"
              THEN "failed" ELSE aw
    /\ UNCHANGED <<sent, q, adds, signal, hpc, reply,
                   emptyBlockingAccepted, refused>>

\* In English: "A reply arrives and the client is back in StIdle. An empty
\* blocking reply is accepted (gOuroboros) or refused [R2]."
\* Literally: "Receive is defined as: reply does not equal NoReply, and if
\*   reply's kind equals "blocking" and reply's size equals 0, then (if
\*   ClientRefusesEmpty is true, then refused in the next state equals TRUE and
\*   emptyBlockingAccepted is unchanged; else emptyBlockingAccepted in the next
\*   state equals TRUE and refused is unchanged); else emptyBlockingAccepted
\*   and refused are unchanged; and cs in the next state equals "Idle" and
\*   reply in the next state equals NoReply, and sent, q, adds, signal, hpc and
\*   aw are unchanged."
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
\* Literally: "HandlerCheck is defined as: hpc equals "check", and either (cs
\*   equals "BusyNonBlocking", and reply in the next state equals the record
\*   whose field kind is "nonblocking" and whose field size is q, and q in the
\*   next state equals 0 and hpc in the next state equals "idle"), or (cs
\*   equals "BusyBlocking" and q is greater than 0, and reply in the next state
\*   equals the record whose field kind is "blocking" and whose field size is
\*   q, and q in the next state equals 0 and hpc in the next state equals
\*   "idle"), or (cs equals "BusyBlocking" and q equals 0 and RogueServer is
\*   not true, and hpc in the next state equals "unlocked", and reply and q are
\*   unchanged), or (cs equals "BusyBlocking" and q equals 0 and RogueServer is
\*   true, and reply in the next state equals the record whose field kind is
\*   "blocking" and whose field size is 0, and hpc in the next state equals
\*   "idle", and q is unchanged); and cs, sent, adds, signal, aw,
\*   emptyBlockingAccepted and refused are unchanged."
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
\* Literally: "HandlerWait is defined as: hpc equals "unlocked", and hpc in the
\*   next state equals "wait", and cs, sent, q, adds, signal, aw, reply,
\*   emptyBlockingAccepted and refused are unchanged."
HandlerWait ==
    /\ hpc = "unlocked"
    /\ hpc' = "wait"
    /\ UNCHANGED <<cs, sent, q, adds, signal, aw, reply, emptyBlockingAccepted,
                   refused>>

\* In English: "The waiting handler takes the signal from the slot and
\* looks at the queue again."
\* Literally: "HandlerWake is defined as: hpc equals "wait" and signal is true,
\*   and signal in the next state equals FALSE and hpc in the next state equals
\*   "check", and cs, sent, q, adds, aw, reply, emptyBlockingAccepted and
\*   refused are unchanged."
HandlerWake ==
    /\ hpc = "wait" /\ signal
    /\ signal' = FALSE /\ hpc' = "check"
    /\ UNCHANGED <<cs, sent, q, adds, aw, reply, emptyBlockingAccepted,
                   refused>>

-----------------------------------------------------------------------------
(* The application.                                                        *)

\* In English: "The application calls WaitForMessage."
\* Literally: "AppWait is defined as: AppWaits is true and aw equals "no", and
\*   aw in the next state equals "wait", and cs, sent, q, adds, signal, hpc,
\*   reply, emptyBlockingAccepted and refused are unchanged."
AppWait ==
    /\ AppWaits /\ aw = "no"
    /\ aw' = "wait"
    /\ UNCHANGED <<cs, sent, q, adds, signal, hpc, reply,
                   emptyBlockingAccepted, refused>>

\* In English: "The application's WaitForMessage takes the signal."
\* Literally: "AppWake is defined as: aw equals "wait" and signal is true, and
\*   signal in the next state equals FALSE and aw in the next state equals
\*   "done", and cs, sent, q, adds, hpc, reply, emptyBlockingAccepted and
\*   refused are unchanged."
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
\* Literally: "AddMessage is defined as: adds is less than MaxAdds, and q in
\*   the next state equals q plus 1 and adds in the next state equals adds plus
\*   1, and if Broadcast is true, then hpc in the next state equals (if hpc is
\*   a member of the set containing "unlocked" and "wait" then "check", else
\*   hpc), and aw in the next state equals (if aw equals "wait" then "done",
\*   else aw), and signal is unchanged; else if Unbuffered is true, then
\*   (either (hpc equals "wait" and hpc in the next state equals "check" and aw
\*   is unchanged), or (aw equals "wait" and aw in the next state equals "done"
\*   and hpc is unchanged), or (hpc does not equal "wait" and aw does not equal
\*   "wait" and hpc and aw are unchanged)), and signal is unchanged; else
\*   signal in the next state equals TRUE, and hpc and aw are unchanged; and
\*   cs, sent, reply, emptyBlockingAccepted and refused are unchanged."
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
\* Literally: "Quiet is defined as: (cs equals "Done", or refused is true, or
\*   (sent equals MaxRequests and cs equals "Idle"), or (cs equals
\*   "BusyBlocking" and hpc equals "wait" and q equals 0 and adds equals
\*   MaxAdds)), and (aw does not equal "wait", or adds equals MaxAdds), and
\*   vars is unchanged."
Quiet ==
    /\ \/ cs = "Done" \/ refused
       \/ /\ sent = MaxRequests /\ cs = "Idle"
       \/ /\ cs = "BusyBlocking" /\ hpc = "wait" /\ q = 0 /\ adds = MaxAdds
    /\ aw /= "wait" \/ adds = MaxAdds
    /\ UNCHANGED vars

\* In English: "A step is a client step, a handler step, an application step,
\* an AddMessage, or, once nothing more happens, nothing."
\* Literally: "Next is defined as: Request, or ClientDone, or Receive, or
\*   HandlerCheck, or HandlerWait, or HandlerWake, or AppWait, or AppWake, or
\*   AddMessage, or Quiet."
Next ==
    \/ Request \/ ClientDone \/ Receive
    \/ HandlerCheck \/ HandlerWait \/ HandlerWake
    \/ AppWait \/ AppWake \/ AddMessage
    \/ Quiet

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "A handler waiting while messages are queued always has a
\* signal in the slot to wake it."
\* Literally: "WakeupNotLost is defined as: if hpc equals "wait" and q is
\*   greater than 0, then signal is true."
WakeupNotLost == (hpc = "wait" /\ q > 0) => signal

\* In English: "An application's WaitForMessage never returns a shutdown
\* error while the server is running: ending a run restarts the server
\* and keeps the queue it waits on [S2][R3]."
\* Literally: "AppWaitOutlivesRun is defined as: aw does not equal
\*   "failed"."
AppWaitOutlivesRun == aw /= "failed"

\* In English: "The client never accepts an empty blocking reply [C1][R2]."
\* Literally: "NoEmptyBlocking is defined as: emptyBlockingAccepted is not
\*   true."
NoEmptyBlocking == ~emptyBlockingAccepted

\* Probes, each EXPECTED to be violated.
\* In English: "The handler never waits." Violated = it does.
\* Literally: "ProbeNeverWaits is defined as: hpc does not equal "wait"."
ProbeNeverWaits == hpc /= "wait"
\* In English: "A blocking request is never answered after a wait."
\* Violated = the handler waits, wakes, and answers.
\* Literally: "ProbeNeverWokenReply is defined as: it is not the case that
\*   (reply's kind equals "blocking", and reply's size is greater than 0, and
\*   sent equals 1, and adds equals MaxAdds)."
ProbeNeverWokenReply == ~(reply.kind = "blocking" /\ reply.size > 0 /\ sent = 1
                          /\ adds = MaxAdds)
\* In English: "The application's WaitForMessage never returns." Violated =
\* it does.
\* Literally: "ProbeAppNeverWakes is defined as: aw does not equal "done"."
ProbeAppNeverWakes == aw /= "done"
=============================================================================
