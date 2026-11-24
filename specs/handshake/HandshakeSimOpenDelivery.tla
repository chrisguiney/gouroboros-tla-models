---------------------- MODULE HandshakeSimOpenDelivery ----------------------
(***************************************************************************)
(* Simultaneous open at goroutine and channel granularity: does each side *)
(* get the peer's proposal, and does each side end?                       *)
(*                                                                         *)
(* HandshakeSimOpen.tla treats a sent proposal as delivered. This module   *)
(* follows the proposal through the gOuroboros goroutines: Client.Start    *)
(* queues it (protocol.SendMessage), the protocol send loop takes it,      *)
(* moves the client to StConfirm and hands it to the muxer, and the        *)
(* muxer's per-protocol writer writes it to the connection. Client.Start   *)
(* returns at StConfirm, before the write, and the connection then lets    *)
(* the muxer read one segment (Muxer.StartOnce).                           *)
(*                                                                         *)
(* The connection is net.Pipe, a rendezvous: a write completes only when  *)
(* the peer's read loop takes it. Closing either end fails every pending  *)
(* and later read and write on both.                                       *)
(*                                                                         *)
(* When a side ends the handshake it stops its protocol, which            *)
(* unregisters it from the muxer; the muxer writer drops anything it has   *)
(* not started writing (muxer.go RegisterProtocol, "protocol              *)
(* unregistered"). PR #3127 at 8461ae3a ends a side as soon as it has      *)
(* handled the peer's proposal, so its own proposal can be dropped and the *)
(* peer never hears it. WaitForProposal = TRUE models the fix: the side    *)
(* first waits until its proposal is written.                              *)
(*                                                                         *)
(* The reference cannot drop it: the handshake runs on bearerAsChannel,   *)
(* whose send is a synchronous bearer write (network-mux                   *)
(* src/Network/Mux/Types.hs 327-330), and the client yields               *)
(* MsgProposeVersions before it awaits a reply (Client.hs 117-121).        *)
(*                                                                         *)
(* CloseOnRefuse = TRUE is a connection that closes on a handshake error, *)
(* as connection.go does; FALSE is the Go test harness, which leaves the   *)
(* muxer running after a side reports.                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Common           \* TRUE: the tables share a version, so both sides accept
CONSTANT WaitForProposal  \* TRUE: a side ends only once its proposal is written
CONSTANT CloseOnRefuse    \* TRUE: a refusing side closes the connection

Sides == {"L", "R"}

\* In English: "The other side."
\* Literally: "Peer of s is defined as: if s equals "L" then "R", else "L"."
Peer(s) == IF s = "L" THEN "R" ELSE "L"

\* In English: "What each side should end with: its own acceptance or
\* refusal, as the reference acceptOrRefuse decides it."
\* Literally: "Outcome is defined as: if Common then "accepted", else
\* "refused"."
Outcome == IF Common THEN "accepted" ELSE "refused"

VARIABLES
    st,       \* st[s]: protocol state, "Propose", "Confirm" or "Done"
    prop,     \* prop[s]: where side s's proposal is
    rd,       \* rd[s]: side s's muxer read loop: "held", "once" or "used"
    inbox,    \* inbox[s]: side s has read the peer's proposal
    hd,       \* hd[s]: side s's handler: "idle", "wait" or "done"
    stopped,  \* stopped[s]: side s's protocol is stopped
    closed,   \* the pipe is closed
    result    \* result[s]: what side s reported, "none" until it reports

vars == <<st, prop, rd, inbox, hd, stopped, closed, result>>

\* In English: "Every variable has a value of the right kind."
\* Literally: "TypeOK is defined as: st is a function from Sides to the
\*   three state names, and prop is a function from Sides to the proposal
\*   places, and rd is a function from Sides to the read-loop states, and
\*   inbox and stopped are functions from Sides to BOOLEAN, and hd is a
\*   function from Sides to the handler states, and closed is a member of
\*   BOOLEAN, and result is a function from Sides to the results."
TypeOK ==
    /\ st \in [Sides -> {"Propose", "Confirm", "Done"}]
    /\ prop \in [Sides -> {"none", "queued", "muxer", "writing", "written",
                           "dropped", "failed"}]
    /\ rd \in [Sides -> {"held", "once", "used"}]
    /\ inbox \in [Sides -> BOOLEAN]
    /\ hd \in [Sides -> {"idle", "wait", "done"}]
    /\ stopped \in [Sides -> BOOLEAN]
    /\ closed \in BOOLEAN
    /\ result \in [Sides -> {"none", "accepted", "refused", "eof"}]

\* In English: "Nothing has happened: no proposal queued, read loops held,
\* nothing reported."
\* Literally: "Init is defined as: st maps every side to "Propose", and
\*   prop maps every side to "none", and rd maps every side to "held", and
\*   inbox maps every side to FALSE, and hd maps every side to "idle", and
\*   stopped maps every side to FALSE, and closed equals FALSE, and result
\*   maps every side to "none"."
Init ==
    /\ st = [s \in Sides |-> "Propose"]
    /\ prop = [s \in Sides |-> "none"]
    /\ rd = [s \in Sides |-> "held"]
    /\ inbox = [s \in Sides |-> FALSE]
    /\ hd = [s \in Sides |-> "idle"]
    /\ stopped = [s \in Sides |-> FALSE]
    /\ closed = FALSE
    /\ result = [s \in Sides |-> "none"]

\* In English: "Client.Start queues side s's proposal."
\* Literally: "Queue of s is defined as: prop of s equals "none", and the
\*   next prop is prop with s mapped to "queued", and every other variable
\*   is unchanged."
Queue(s) ==
    /\ prop[s] = "none"
    /\ prop' = [prop EXCEPT ![s] = "queued"]
    /\ UNCHANGED <<st, rd, inbox, hd, stopped, closed, result>>

\* In English: "The send loop takes the proposal, moves the client to
\* StConfirm, and hands the proposal to the muxer writer; nothing is on the
\* wire yet."
\* Literally: "Dequeue of s is defined as: prop of s equals "queued", and
\*   not stopped of s, and the next prop is prop with s mapped to "muxer",
\*   and the next st is st with s mapped to "Confirm", and every other
\*   variable is unchanged."
Dequeue(s) ==
    /\ prop[s] = "queued"
    /\ ~stopped[s]
    /\ prop' = [prop EXCEPT ![s] = "muxer"]
    /\ st' = [st EXCEPT ![s] = "Confirm"]
    /\ UNCHANGED <<rd, inbox, hd, stopped, closed, result>>

\* In English: "Client.Start has returned at StConfirm, so the connection
\* lets side s's muxer read one segment (Muxer.StartOnce)."
\* Literally: "StartOnce of s is defined as: st of s is not "Propose", and
\*   rd of s equals "held", and the next rd is rd with s mapped to "once",
\*   and every other variable is unchanged."
StartOnce(s) ==
    /\ st[s] # "Propose"
    /\ rd[s] = "held"
    /\ rd' = [rd EXCEPT ![s] = "once"]
    /\ UNCHANGED <<st, prop, inbox, hd, stopped, closed, result>>

\* In English: "The muxer writer of a running protocol takes the proposal
\* and starts writing it to the pipe."
\* Literally: "StartWrite of s is defined as: prop of s equals "muxer", and
\*   not stopped of s, and the next prop is prop with s mapped to
\*   "writing", and every other variable is unchanged."
StartWrite(s) ==
    /\ prop[s] = "muxer"
    /\ ~stopped[s]
    /\ prop' = [prop EXCEPT ![s] = "writing"]
    /\ UNCHANGED <<st, rd, inbox, hd, stopped, closed, result>>

\* In English: "A stopped protocol is unregistered, and the muxer drops a
\* proposal it has not started writing."
\* Literally: "Drop of s is defined as: prop of s is a member of the set
\*   of "queued" and "muxer", and stopped of s, and the next prop is prop
\*   with s mapped to "dropped", and every other variable is unchanged."
Drop(s) ==
    /\ prop[s] \in {"queued", "muxer"}
    /\ stopped[s]
    /\ prop' = [prop EXCEPT ![s] = "dropped"]
    /\ UNCHANGED <<st, rd, inbox, hd, stopped, closed, result>>

\* In English: "The pipe rendezvous: side s's write completes as the
\* peer's read loop, allowed one segment, takes it."
\* Literally: "Deliver of s is defined as: prop of s equals "writing", and
\*   rd of Peer of s equals "once", and not closed, and the next prop is
\*   prop with s mapped to "written", and the next rd is rd with Peer of s
\*   mapped to "used", and the next inbox is inbox with Peer of s mapped to
\*   TRUE, and every other variable is unchanged."
Deliver(s) ==
    /\ prop[s] = "writing"
    /\ rd[Peer(s)] = "once"
    /\ ~closed
    /\ prop' = [prop EXCEPT ![s] = "written"]
    /\ rd' = [rd EXCEPT ![Peer(s)] = "used"]
    /\ inbox' = [inbox EXCEPT ![Peer(s)] = TRUE]
    /\ UNCHANGED <<st, hd, stopped, closed, result>>

\* In English: "Side s ends the handshake: it reports its decision, stops
\* its protocol, and, refusing on a connection that closes on refusal,
\* closes the pipe."
\* Literally: "Finish of s is defined as: the next result is result with s
\*   mapped to Outcome, and the next st is st with s mapped to "Done", and
\*   the next hd is hd with s mapped to "done", and the next stopped is
\*   stopped with s mapped to TRUE, and the next closed equals closed or
\*   (CloseOnRefuse and not Common)."
Finish(s) ==
    /\ result' = [result EXCEPT ![s] = Outcome]
    /\ st' = [st EXCEPT ![s] = "Done"]
    /\ hd' = [hd EXCEPT ![s] = "done"]
    /\ stopped' = [stopped EXCEPT ![s] = TRUE]
    /\ closed' = (closed \/ (CloseOnRefuse /\ ~Common))

\* In English: "Side s handles the peer's proposal in StConfirm. With the
\* fix it first waits for its own proposal to be written; without it, it
\* ends at once."
\* Literally: "Handle of s is defined as: inbox of s, and st of s equals
\*   "Confirm", and hd of s equals "idle", and result of s equals "none",
\*   and if WaitForProposal then the next hd is hd with s mapped to "wait"
\*   and every other variable is unchanged, else Finish of s and prop, rd
\*   and inbox are unchanged."
Handle(s) ==
    /\ inbox[s]
    /\ st[s] = "Confirm"
    /\ hd[s] = "idle"
    /\ result[s] = "none"
    /\ IF WaitForProposal
         THEN /\ hd' = [hd EXCEPT ![s] = "wait"]
              /\ UNCHANGED <<st, prop, rd, inbox, stopped, closed, result>>
         ELSE /\ Finish(s)
              /\ UNCHANGED <<prop, rd, inbox>>

\* In English: "A waiting side ends once its proposal is written."
\* Literally: "WaitDone of s is defined as: hd of s equals "wait", and prop
\*   of s equals "written", and Finish of s, and prop, rd and inbox are
\*   unchanged."
WaitDone(s) ==
    /\ hd[s] = "wait"
    /\ prop[s] = "written"
    /\ Finish(s)
    /\ UNCHANGED <<prop, rd, inbox>>

\* In English: "On a closed pipe, a pending read or write fails, the muxer
\* reports the error, and a side that has reported nothing yet reports it
\* (the result goroutine in the Go tests, the connection error in
\* connection.go)."
\* Literally: "PipeError of s is defined as: closed, and (rd of s equals
\*   "once" or prop of s equals "writing"), and the next rd is rd with s
\*   mapped to "used" if it was "once", and the next prop is prop with s
\*   mapped to "failed" if it was "writing", and the next result is result
\*   with s mapped to "eof" if result of s equals "none", and the next
\*   stopped is stopped with s mapped to TRUE, and st, inbox, hd and closed
\*   are unchanged."
PipeError(s) ==
    /\ closed
    /\ rd[s] = "once" \/ prop[s] = "writing"
    /\ rd' = [rd EXCEPT ![s] = IF @ = "once" THEN "used" ELSE @]
    /\ prop' = [prop EXCEPT ![s] = IF @ = "writing" THEN "failed" ELSE @]
    /\ result' = [result EXCEPT ![s] = IF @ = "none" THEN "eof" ELSE @]
    /\ stopped' = [stopped EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<st, inbox, hd, closed>>

\* In English: "Both sides have reported; nothing more happens."
\* Literally: "Ended is defined as: for all s in Sides, result of s is not
\*   "none", and every variable is unchanged."
Ended ==
    /\ \A s \in Sides : result[s] # "none"
    /\ UNCHANGED vars

\* In English: "Some side takes one step, or both have ended."
\* Literally: "Next is defined as: there exists an s in Sides such that
\*   Queue, Dequeue, StartOnce, StartWrite, Drop, Deliver, Handle, WaitDone
\*   or PipeError of s holds; or Ended holds."
Next ==
    \/ \E s \in Sides :
         \/ Queue(s) \/ Dequeue(s) \/ StartOnce(s) \/ StartWrite(s)
         \/ Drop(s) \/ Deliver(s) \/ Handle(s) \/ WaitDone(s)
         \/ PipeError(s)
    \/ Ended

\* In English: "Start from Init, take Next steps, and never stall while a
\* side's step stays possible."
\* Literally: "Spec is defined as: Init, and always Next or vars unchanged,
\*   and for each s in Sides, weak fairness of each of s's steps."
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A s \in Sides :
         /\ WF_vars(Queue(s)) /\ WF_vars(Dequeue(s)) /\ WF_vars(StartOnce(s))
         /\ WF_vars(StartWrite(s)) /\ WF_vars(Drop(s)) /\ WF_vars(Deliver(s))
         /\ WF_vars(Handle(s)) /\ WF_vars(WaitDone(s)) /\ WF_vars(PipeError(s))

\* In English: "A side that reports anything reports its own decision, as
\* the reference does: never a closed connection in its place."
\* Literally: "EndsWithOwnDecision is defined as: for all s in Sides,
\*   result of s is a member of the set of "none" and Outcome."
EndsWithOwnDecision == \A s \in Sides : result[s] \in {"none", Outcome}

\* In English: "Every proposal sent is heard: a side never drops its own
\* proposal."
\* Literally: "NoDroppedProposal is defined as: for all s in Sides, prop of
\*   s is not "dropped"."
NoDroppedProposal == \A s \in Sides : prop[s] # "dropped"

\* In English: "Eventually both sides have reported."
\* Literally: "BothSidesEnd is defined as: eventually, for all s in Sides,
\*   result of s is not "none"."
BothSidesEnd == <>(\A s \in Sides : result[s] # "none")

\* In English: "Reachability probe: it is not the case that both sides
\* have ended with their own decision. A passing config must break it."
\* Literally: "ProbeNotBothEnded is defined as: not, for all s in Sides,
\*   result of s equals Outcome."
ProbeNotBothEnded == ~(\A s \in Sides : result[s] = Outcome)

=============================================================================
