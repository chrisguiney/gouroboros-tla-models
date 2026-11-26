---------------------- MODULE ConnectionShutdownAgency ----------------------
(***************************************************************************)
(* Model `connection`, part 4b: when the peer closes the connection, is    *)
(* that an error? ConnectionShutdown.tla checks how an error travels and   *)
(* the connection shuts down; this module checks which closes count as an  *)
(* error in the first place.                                               *)
(*                                                                         *)
(* gOuroboros (connection.go, protocol/protocol.go): the muxer reports a   *)
(* read of EOF as a ConnectionClosedError. The connection's muxer-error    *)
(* forwarder drops that error, closing quietly, when allProtocolsIdle()    *)
(* holds: every mini-protocol's Protocol.IsInTerminalOrIdleState() is      *)
(* true. That function is true when the protocol is stopped (doneChan is   *)
(* closed), when its current state has AgencyNone (Done), or when its      *)
(* current state is the initial one. recvLoop asks the same question of    *)
(* a zero-byte read.                                                       *)
(*                                                                         *)
(* The rule [S1][S2]: a close is normal only when no mini-protocol is      *)
(* running a transaction, that is when nobody owes a message. Each         *)
(* mini-protocol here is a requester (chain-sync, block-fetch, leios-*     *)
(* clients): Idle (requester's agency, the initial state) -> request ->    *)
(* Busy (peer's agency) -> reply -> Idle, and MsgDone from Idle -> Done.   *)
(* While a request is unanswered the peer owes its reply, and a close then *)
(* is an error.                                                            *)
(*                                                                         *)
(* Pipelining [S3]: in Busy the requester may send more requests. The      *)
(* engine writes such a request at once but defers its state transition    *)
(* (sendLoop's queuedStateTransitions) and counts it in                    *)
(* pendingPipelinedRequests until the transition is applied. When the      *)
(* first reply returns the protocol to Idle, the current state is Idle -   *)
(* the initial state - while the peer still owes the pipelined reply,     *)
(* until sendLoop flushes the deferred transition into Busy. A reply that  *)
(* arrives in that window is admitted and reserved                         *)
(* (pendingPipelinedReplies) and applied after the flush.                  *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Protos,       \* the mini-protocols on the connection, all requesters
    Depth,        \* how many requests may be unanswered at once
    MaxRequests,  \* how many requests each protocol sends in all
    Pipelining,   \* TRUE: requests may be pipelined in Busy
    Classifier    \* which IsInTerminalOrIdleState is modelled:
                  \*   "current"    gOuroboros at 7cd17437: stopped, Done, or
                  \*                the initial state
                  \*   "fixed"      "current", and no pipelined request is
                  \*                still without its reply
                  \*   "anyState"   mutation: every state is idle
                  \*   "doneIsBusy" mutation: Done is not idle

ASSUME Classifier \in {"current", "fixed", "anyState", "doneIsBusy"}

VARIABLES
    st,       \* st[p]: the current state gOuroboros holds: "Idle", "Busy", "Done"
    owed,     \* owed[p]: requests the peer has and has not answered (it owes these)
    inbox,    \* inbox[p]: replies read from the bearer, not yet admitted
    pend,     \* pend[p]: pendingPipelinedRequests
    rsv,      \* rsv[p]: pendingPipelinedReplies (admitted, held for the flush)
    sent,     \* sent[p]: requests sent so far
    stopped,  \* stopped[p]: TRUE once Stop closed the protocol's doneChan
    eof,      \* TRUE once the peer has closed the bearer
    verdict,  \* the forwarder's verdict on the close: "none", "clean", "error"
    restAtJudge \* TRUE if every protocol was at rest when the verdict was made

vars == <<st, owed, inbox, pend, rsv, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "Each protocol starts in its initial state Idle with nothing
\* sent, owed or pending; the bearer is open and nothing has been judged."
Init ==
    /\ st = [p \in Protos |-> "Idle"]          \* InitialState
    /\ owed = [p \in Protos |-> 0]
    /\ inbox = [p \in Protos |-> 0]
    /\ pend = [p \in Protos |-> 0]
    /\ rsv = [p \in Protos |-> 0]
    /\ sent = [p \in Protos |-> 0]
    /\ stopped = [p \in Protos |-> FALSE]
    /\ eof = FALSE
    /\ verdict = "none"
    /\ restAtJudge = FALSE

\* In English: "p is still running: not stopped, not Done."
Live(p) == ~stopped[p] /\ st[p] /= "Done"

\* In English: "p may send one more request: the bearer is open and both
\* limits allow it."
\* A request written after the peer closed never reaches it.
CanRequest(p) ==
    ~eof /\ sent[p] < MaxRequests /\ owed[p] + inbox[p] + rsv[p] < Depth

-----------------------------------------------------------------------------
(* The requester's steps (sendLoop and recvLoop). *)

\* In English: "In Idle with no deferred work, an ordinary request: its
\* transition is applied as it is written, so the state becomes Busy and the
\* peer owes one more reply." (sendLoop: transitionState, then the write.)
Request(p) ==
    /\ Live(p) /\ st[p] = "Idle" /\ pend[p] = 0 /\ rsv[p] = 0
    /\ CanRequest(p)
    /\ st' = [st EXCEPT ![p] = "Busy"]         \* Idle -> Busy
    /\ owed' = [owed EXCEPT ![p] = @ + 1]       \* the peer owes the reply
    /\ sent' = [sent EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<inbox, pend, rsv, stopped, eof, verdict, restAtJudge>>

\* In English: "In Busy, a pipelined request: written now, its transition
\* deferred, so the state stays Busy and pend counts it." [S3]
PipelineRequest(p) ==
    /\ Pipelining /\ Live(p) /\ st[p] = "Busy"
    /\ CanRequest(p)
    /\ owed' = [owed EXCEPT ![p] = @ + 1]       \* the peer owes the reply
    /\ pend' = [pend EXCEPT ![p] = @ + 1]       \* addPendingPipelinedRequest
    /\ sent' = [sent EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<st, inbox, rsv, stopped, eof, verdict, restAtJudge>>

\* In English: "The peer answers one request; the reply reaches our side
\* before the peer closes."
PeerReplies(p) ==
    /\ ~eof /\ owed[p] > 0
    /\ owed' = [owed EXCEPT ![p] = @ - 1]       \* the peer owes one fewer
    /\ inbox' = [inbox EXCEPT ![p] = @ + 1]     \* the bytes are ours
    /\ UNCHANGED <<st, pend, rsv, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "recvLoop applies a reply in Busy: back to Idle."
AdmitInBusy(p) ==
    /\ Live(p) /\ inbox[p] > 0 /\ st[p] = "Busy"
    /\ st' = [st EXCEPT ![p] = "Idle"]          \* Busy -> Idle
    /\ inbox' = [inbox EXCEPT ![p] = @ - 1]
    /\ UNCHANGED <<owed, pend, rsv, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "recvLoop admits a reply in Idle, while a pipelined request
\* has no reply reserved: it is reserved and held for the flush."
\* (reserveInboundAdmission, agencyLocal case.)
AdmitInIdle(p) ==
    /\ Live(p) /\ inbox[p] > 0 /\ st[p] = "Idle" /\ pend[p] > rsv[p]
    /\ rsv' = [rsv EXCEPT ![p] = @ + 1]         \* reservePipelinedReply
    /\ inbox' = [inbox EXCEPT ![p] = @ - 1]
    /\ UNCHANGED <<st, owed, pend, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "sendLoop, woken by agency in Idle, applies the oldest
\* deferred transition: Idle -> Busy, and pend loses it."
Flush(p) ==
    /\ Live(p) /\ st[p] = "Idle" /\ pend[p] > 0
    /\ st' = [st EXCEPT ![p] = "Busy"]          \* Idle -> Busy
    /\ pend' = [pend EXCEPT ![p] = @ - 1]       \* consumesPipelinedRequest
    /\ UNCHANGED <<owed, inbox, rsv, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "A held reply is applied once the flush reached Busy."
ApplyHeld(p) ==
    /\ Live(p) /\ st[p] = "Busy" /\ rsv[p] > 0
    /\ st' = [st EXCEPT ![p] = "Idle"]          \* Busy -> Idle
    /\ rsv' = [rsv EXCEPT ![p] = @ - 1]         \* consumesPipelinedReply
    /\ UNCHANGED <<owed, inbox, pend, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "In Idle with nothing deferred or unread, MsgDone: Done."
SendDone(p) ==
    /\ Live(p) /\ st[p] = "Idle"
    /\ pend[p] = 0 /\ rsv[p] = 0 /\ inbox[p] = 0
    /\ st' = [st EXCEPT ![p] = "Done"]          \* Idle -> Done
    /\ UNCHANGED <<owed, inbox, pend, rsv, sent, stopped, eof, verdict, restAtJudge>>

\* In English: "The application stops p: doneChan closes. Whatever the peer
\* still owes, we no longer want it."
Stop(p) ==
    /\ ~stopped[p] /\ ~eof
    /\ stopped' = [stopped EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<st, owed, inbox, pend, rsv, sent, eof, verdict, restAtJudge>>

-----------------------------------------------------------------------------
(* The peer closes; the forwarder judges. *)

\* In English: "The peer closes the bearer, at any moment."
PeerCloses ==
    /\ ~eof
    /\ eof' = TRUE
    /\ UNCHANGED <<st, owed, inbox, pend, rsv, sent, stopped, verdict, restAtJudge>>

\* In English: "What IsInTerminalOrIdleState returns for p now."
Idle(p) ==
    CASE Classifier = "current" ->
            stopped[p] \/ st[p] = "Done" \/ st[p] = "Idle"
      [] Classifier = "fixed" ->
            \/ stopped[p] \/ st[p] = "Done"
            \/ st[p] = "Idle" /\ pend[p] <= rsv[p]   \* no request unanswered
      [] Classifier = "anyState" -> TRUE
      [] Classifier = "doneIsBusy" -> stopped[p] \/ st[p] = "Idle"

\* In English: "p is at rest: Idle or Done, nothing owed, unread, held or
\* deferred."
AtRest(p) ==
    /\ st[p] \in {"Idle", "Done"}
    /\ owed[p] = 0 /\ inbox[p] = 0 /\ pend[p] = 0 /\ rsv[p] = 0

\* In English: "Once the bearer is closed, the muxer-error forwarder reads
\* allProtocolsIdle once: clean if every protocol is idle, else an error.
\* The protocols' own loops may still run around it."
Judge ==
    /\ eof /\ verdict = "none"
    /\ verdict' = IF \A p \in Protos : Idle(p) THEN "clean" ELSE "error"
    /\ restAtJudge' = \A p \in Protos : AtRest(p)  \* recorded for NoErrorAtRest
    /\ UNCHANGED <<st, owed, inbox, pend, rsv, sent, stopped, eof>>

\* In English: "Nothing more happens once the close is judged."
Finished ==
    /\ verdict /= "none"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Protos :
          \/ Request(p) \/ PipelineRequest(p) \/ PeerReplies(p)
          \/ AdmitInBusy(p) \/ AdmitInIdle(p) \/ Flush(p) \/ ApplyHeld(p)
          \/ SendDone(p) \/ Stop(p)
    \/ PeerCloses \/ Judge \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Nobody owes anything on p: it was stopped, or the peer has
\* answered every request it was sent."
NobodyOwes(p) == stopped[p] \/ owed[p] = 0

\* In English: "A close is let through as clean only when the peer owes
\* nothing on any running protocol." [S1][S2]
NoErrorOnlyWhenNobodyOwes ==
    verdict = "clean" => \A p \in Protos : NobodyOwes(p)

\* In English: "A close judged while every protocol was at rest is not an
\* error."
NoErrorAtRest ==
    verdict = "error" => ~restAtJudge

\* In English: "Reachability probe: a close is judged clean while the
\* current state of every protocol is Idle or Done and some pipelined
\* request is still unanswered. It holds under "fixed"; its Bug config
\* runs it under "current" to show the window exists."
NoCleanWithUnansweredPipelined ==
    verdict = "clean" =>
        \A p \in Protos : stopped[p] \/ pend[p] <= rsv[p]

\* In English: "Each counter stays within its bounds."
TypeOK ==
    /\ \A p \in Protos :
         /\ st[p] \in {"Idle", "Busy", "Done"}
         /\ owed[p] \in 0..Depth /\ inbox[p] \in 0..Depth
         /\ pend[p] \in 0..Depth /\ rsv[p] \in 0..Depth
    /\ verdict \in {"none", "clean", "error"}
=============================================================================
