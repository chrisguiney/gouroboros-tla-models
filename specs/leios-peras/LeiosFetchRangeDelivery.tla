---------------------- MODULE LeiosFetchRangeDelivery ----------------------
(***************************************************************************)
(* The gOuroboros LeiosFetch client's range delivery, at the level of its  *)
(* goroutines (protocol/leiosfetch/client.go: requestSlot,                 *)
(* requestDelivery, BlockRangeRequest).                                    *)
(*                                                                         *)
(* A block-range request gets several replies; the last one is terminal.   *)
(* The receive loop hands each reply to the slot (deliverRange), which     *)
(* queues it on the request's delivery; the delivery's own goroutine       *)
(* (`run`) moves the queue, one reply at a time, into the caller's         *)
(* one-slot channel `w`. The caller reads `w` until the terminal reply, or *)
(* leaves early:                                                           *)
(*   - through its context: `abandon(w)` (the peer will still send the     *)
(*     rest of the range; the slot stays busy until the terminal reply);   *)
(*   - through the protocol ending: `release(w)` (nothing more arrives).   *)
(* Both only act while `w` is still the slot's live waiter.                *)
(*                                                                         *)
(* The terminal reply clears the waiter and frees the slot at once, while  *)
(* the caller may still have replies to read. On main a caller that then   *)
(* leaves matches nothing, so its delivery is never stopped and `run`      *)
(* blocks for ever on the full channel, holding the queued replies         *)
(* (hazard C8). The fix keeps a finished range's delivery, keyed by its    *)
(* waiter, until that caller's abandon or release stops it.                *)
(*                                                                         *)
(* Granularity: one step per locked block of the slot (s.mu), per channel  *)
(* operation of `run` and the caller, and per unlocked `d.enqueue`.        *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. Each goroutine is a program counter (`caller`, `run`); a step  *)
(*   is enabled only when the Go line it stands for could run.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Replies,    \* replies in a range, the last one terminal (the Go test uses 3)
    Fixed,      \* TRUE: abandon and release also stop the caller's finished range
    Second,     \* TRUE: a second request takes the slot once it is free
    Leaves      \* how a caller may leave early: a subset of {"abandon", "release"}

\* In English: "the requests: the first, and the second when there is one."
\* Literally: "Reqs is defined as: if Second then the set 1 through 2, else
\*   the set containing 1."
Reqs == IF Second THEN 1..2 ELSE {1}

VARIABLES
    waiter,     \* the slot's live waiter: a request number, or 0 for none
    busy,       \* the slot is taken (s.busy)
    abandoned,  \* the slot's request was abandoned (s.abandoned)
    finished,   \* requests whose terminal reply arrived and whose delivery the slot keeps (fix only)
    protoDone,  \* the protocol has ended: no more replies, no new requests
    onWire,     \* the request whose replies the peer is sending, 0 for none
    sent,       \* sent[r]: replies the receive loop has handed to the slot for r
    pendEnq,    \* pendEnq[r]: deliverRange left s.mu and has not yet called d.enqueue
    q,          \* q[r]: replies queued on r's delivery
    hold,       \* hold[r]: `run` took a reply off the queue and has not sent it
    taken,      \* taken[r]: replies `run` has taken off the queue
    buf,        \* buf[r]: replies in the caller's one-slot channel (0 or 1)
    stopped,    \* stopped[r]: r's delivery was stopped (d.stopped closed)
    run,        \* run[r]: "none", "running" or "ended"
    caller,     \* caller[r]: "idle", "waiting" or "gone"
    read        \* read[r]: replies r's caller has read

\* In English: "all the variables, for saying a step changes none of them."
\* Literally: "vars is defined as the tuple of all sixteen variables."
vars == <<waiter, busy, abandoned, finished, protoDone, onWire, sent, pendEnq,
          q, hold, taken, buf, stopped, run, caller, read>>

\* In English: "Request 1 has taken the slot, its delivery is running, and
\* its caller waits; a second request, if any, has not started."
\* Literally: "Init is defined as: waiter equals 1, busy is true, abandoned is
\*   false, finished is the empty set, protoDone is false, onWire equals 1,
\*   sent, q, taken, buf and read map every r to 0, pendEnq, hold and
\*   stopped map every r to false, run maps r to "running" if r is 1 else
\*   "none", and caller maps r to "waiting" if r is 1 else "idle"."
Init ==
    /\ waiter = 1
    /\ busy = TRUE
    /\ abandoned = FALSE
    /\ finished = {}
    /\ protoDone = FALSE
    /\ onWire = 1
    /\ sent = [r \in Reqs |-> 0]
    /\ pendEnq = [r \in Reqs |-> FALSE]
    /\ q = [r \in Reqs |-> 0]
    /\ hold = [r \in Reqs |-> FALSE]
    /\ taken = [r \in Reqs |-> 0]
    /\ buf = [r \in Reqs |-> 0]
    /\ stopped = [r \in Reqs |-> FALSE]
    /\ run = [r \in Reqs |-> IF r = 1 THEN "running" ELSE "none"]
    /\ caller = [r \in Reqs |-> IF r = 1 THEN "waiting" ELSE "idle"]
    /\ read = [r \in Reqs |-> 0]

-----------------------------------------------------------------------------
(* The receive loop: deliverRange, in two steps. *)

\* In English: "The receive loop takes the slot's lock for the next reply of
\* the request on the wire. If that request is the live waiter, the reply is
\* to be queued; a terminal one also clears the waiter and frees the slot,
\* and with the fix the slot keeps the request's delivery. If the request was
\* abandoned, the reply is dropped, and the terminal one frees the slot."
\* Literally: "DeliverRange of r is defined as: onWire equals r, and protoDone
\*   is false, and sent of r is less than Replies, and pendEnq of r is false,
\*   and there exists a t equal to (sent of r plus 1 equals Replies) such
\*   that: sent of r becomes sent of r plus 1; if waiter equals r then
\*   pendEnq of r becomes true, waiter becomes 0 if t else stays, busy becomes
\*   false if t else stays, finished gains r if t and Fixed, and abandoned is
\*   unchanged; otherwise pendEnq and finished are unchanged, and if t and
\*   abandoned then busy and abandoned become false, else they are unchanged."
DeliverRange(r) ==
    /\ onWire = r
    /\ ~protoDone                          \* nothing arrives once the protocol ended
    /\ sent[r] < Replies
    /\ ~pendEnq[r]
    /\ LET t == sent[r] + 1 = Replies IN    \* is this the terminal reply?
       /\ sent' = [sent EXCEPT ![r] = @ + 1]
       /\ IF waiter = r
            THEN /\ pendEnq' = [pendEnq EXCEPT ![r] = TRUE]   \* d.enqueue after unlock
                 /\ waiter' = IF t THEN 0 ELSE waiter         \* s.waiter = nil
                 /\ busy' = IF t THEN FALSE ELSE busy         \* s.freeLocked()
                 /\ finished' = IF t /\ Fixed THEN finished \cup {r} ELSE finished
                 /\ UNCHANGED abandoned
            ELSE /\ UNCHANGED <<pendEnq, finished, waiter>>   \* no waiter: dropped
                 /\ IF t /\ abandoned
                      THEN /\ busy' = FALSE                   \* the late terminal frees it
                           /\ abandoned' = FALSE
                      ELSE UNCHANGED <<busy, abandoned>>
    /\ UNCHANGED <<protoDone, onWire, q, hold, taken, buf, stopped, run, caller, read>>

\* In English: "Outside the lock, the receive loop queues the reply on the
\* delivery, unless the delivery was stopped in the meantime."
\* Literally: "Enqueue of r is defined as: pendEnq of r is true, and pendEnq
\*   of r becomes false, and q of r becomes q of r plus 1 if stopped of r is
\*   false, else is unchanged."
Enqueue(r) ==
    /\ pendEnq[r]
    /\ pendEnq' = [pendEnq EXCEPT ![r] = FALSE]
    /\ q' = IF stopped[r] THEN q ELSE [q EXCEPT ![r] = @ + 1]   \* enqueue checks d.stopped
    /\ UNCHANGED <<waiter, busy, abandoned, finished, protoDone, onWire, sent,
                   hold, taken, buf, stopped, run, caller, read>>

-----------------------------------------------------------------------------
(* The delivery goroutine: requestDelivery.run. *)

\* In English: "`run` takes the next reply off its queue."
\* Literally: "RunTake of r is defined as: run of r equals "running", and
\*   stopped of r is false, and hold of r is false, and q of r is greater
\*   than 0, and q of r decreases by 1, hold of r becomes true, and taken of
\*   r increases by 1."
RunTake(r) ==
    /\ run[r] = "running"
    /\ ~stopped[r]
    /\ ~hold[r]
    /\ q[r] > 0
    /\ q' = [q EXCEPT ![r] = @ - 1]
    /\ hold' = [hold EXCEPT ![r] = TRUE]
    /\ taken' = [taken EXCEPT ![r] = @ + 1]
    /\ UNCHANGED <<waiter, busy, abandoned, finished, protoDone, onWire, sent,
                   pendEnq, buf, stopped, run, caller, read>>

\* In English: "`run` puts the reply it holds into the caller's channel,
\* which it can only do while the channel is empty. After the terminal reply
\* it stops itself and ends."
\* Literally: "RunSend of r is defined as: run of r equals "running", hold of
\*   r is true, buf of r equals 0, buf of r becomes 1, hold of r becomes
\*   false, and if taken of r equals Replies then stopped of r becomes true
\*   and run of r becomes "ended", else both are unchanged."
RunSend(r) ==
    /\ run[r] = "running"
    /\ hold[r]
    /\ buf[r] = 0                                  \* d.out <- msg can proceed
    /\ buf' = [buf EXCEPT ![r] = 1]
    /\ hold' = [hold EXCEPT ![r] = FALSE]
    /\ IF taken[r] = Replies
         THEN /\ stopped' = [stopped EXCEPT ![r] = TRUE]  \* d.stop()
              /\ run' = [run EXCEPT ![r] = "ended"]
         ELSE UNCHANGED <<stopped, run>>
    /\ UNCHANGED <<waiter, busy, abandoned, finished, protoDone, onWire, sent,
                   pendEnq, q, taken, caller, read>>

\* In English: "`run` sees its delivery stopped, while it waits for a reply
\* to queue or to send, and ends."
\* Literally: "RunStopped of r is defined as: run of r equals "running", and
\*   stopped of r is true, and (hold of r is true or q of r equals 0), and
\*   run of r becomes "ended"."
RunStopped(r) ==
    /\ run[r] = "running"
    /\ stopped[r]
    /\ hold[r] \/ q[r] = 0                         \* both selects watch d.stopped
    /\ run' = [run EXCEPT ![r] = "ended"]
    /\ UNCHANGED <<waiter, busy, abandoned, finished, protoDone, onWire, sent,
                   pendEnq, q, hold, taken, buf, stopped, caller, read>>

-----------------------------------------------------------------------------
(* The caller: BlockRangeRequest, and the slot's abandon and release. *)

\* In English: "stop r's delivery: close d.stopped and drop its queue."
\* Literally: "StopDelivery of r is defined as: stopped of r becomes true and
\*   q of r becomes 0."
StopDelivery(r) ==
    /\ stopped' = [stopped EXCEPT ![r] = TRUE]
    /\ q' = [q EXCEPT ![r] = 0]

\* In English: "release(w): if r is still the live waiter, clear it, stop
\* its delivery and free the slot. Otherwise, with the fix, stop r's
\* finished range if the slot keeps one; on main do nothing."
\* Literally: "Release of r is defined as: if waiter equals r then waiter
\*   becomes 0, busy becomes false, r's delivery is stopped, and finished is
\*   unchanged; else if Fixed and r is in finished, r's delivery is stopped
\*   and finished loses r, with waiter and busy unchanged; else waiter, busy,
\*   finished, stopped and q are unchanged."
Release(r) ==
    IF waiter = r
      THEN /\ waiter' = 0 /\ busy' = FALSE /\ StopDelivery(r)
           /\ UNCHANGED finished
      ELSE IF Fixed /\ r \in finished
             THEN /\ StopDelivery(r) /\ finished' = finished \ {r}  \* stopFinishedRangeLocked
                  /\ UNCHANGED <<waiter, busy>>
             ELSE UNCHANGED <<waiter, busy, finished, stopped, q>>

\* In English: "The caller reads one reply. After the terminal one it calls
\* release and returns."
\* Literally: "Read of r is defined as: caller of r equals "waiting", buf of
\*   r equals 1, buf of r becomes 0, read of r increases by 1, and if read of
\*   r plus 1 equals Replies then Release of r and caller of r becomes
\*   "gone", else waiter, busy, finished, stopped, q and caller are
\*   unchanged."
Read(r) ==
    /\ caller[r] = "waiting"
    /\ buf[r] = 1
    /\ buf' = [buf EXCEPT ![r] = 0]
    /\ read' = [read EXCEPT ![r] = @ + 1]
    /\ IF read[r] + 1 = Replies
         THEN /\ Release(r)
              /\ caller' = [caller EXCEPT ![r] = "gone"]
         ELSE UNCHANGED <<waiter, busy, finished, stopped, q, caller>>
    /\ UNCHANGED <<abandoned, protoDone, onWire, sent, pendEnq, hold, taken, run>>

\* In English: "The caller's context ends: abandon(w). If r is still the
\* live waiter, clear it, stop its delivery and mark the slot abandoned
\* (it stays busy until the late terminal reply). Otherwise, with the fix,
\* stop r's finished range; on main do nothing. The caller returns."
\* Literally: "Abandon of r is defined as: "abandon" is in Leaves, and caller
\*   of r equals "waiting", and
\*   caller of r becomes "gone", and if waiter equals r then waiter becomes
\*   0, abandoned becomes true and r's delivery is stopped, with busy and
\*   finished unchanged; else if Fixed and r is in finished, r's delivery is
\*   stopped and finished loses r; else nothing else changes."
Abandon(r) ==
    /\ "abandon" \in Leaves
    /\ caller[r] = "waiting"
    /\ caller' = [caller EXCEPT ![r] = "gone"]
    /\ IF waiter = r
         THEN /\ waiter' = 0 /\ abandoned' = TRUE /\ StopDelivery(r)
              /\ UNCHANGED <<busy, finished>>
         ELSE /\ UNCHANGED abandoned
              /\ IF Fixed /\ r \in finished
                   THEN /\ StopDelivery(r) /\ finished' = finished \ {r}
                        /\ UNCHANGED <<waiter, busy>>
                   ELSE UNCHANGED <<waiter, busy, finished, stopped, q>>
    /\ UNCHANGED <<protoDone, onWire, sent, pendEnq, hold, taken, buf, run, read>>

\* In English: "The protocol ends (DoneChan closes): the caller calls
\* release and returns, and no further reply or request comes."
\* Literally: "ProtocolEnds of r is defined as: "release" is in Leaves, and
\*   caller of r equals
\*   "waiting", protoDone becomes true, Release of r, and caller of r
\*   becomes "gone"."
ProtocolEnds(r) ==
    /\ "release" \in Leaves
    /\ caller[r] = "waiting"
    /\ protoDone' = TRUE
    /\ Release(r)
    /\ caller' = [caller EXCEPT ![r] = "gone"]
    /\ UNCHANGED <<abandoned, onWire, sent, pendEnq, hold, taken, buf, run, read>>

\* In English: "The second request takes the free slot (acquire), once the
\* first range is off the wire, and the peer starts answering it."
\* Literally: "Acquire2 is defined as: Second, and caller of 2 equals
\*   "idle", and caller of 1 is not "idle", and busy is false, and protoDone
\*   is false, and sent of 1 equals Replies, and waiter becomes 2, busy
\*   becomes true, abandoned becomes false, onWire becomes 2, run of 2
\*   becomes "running", and caller of 2 becomes "waiting"."
Acquire2 ==
    /\ Second
    /\ caller[2] = "idle"
    /\ ~busy                                       \* acquire waits for a free slot
    /\ ~protoDone
    /\ sent[1] = Replies
    /\ waiter' = 2 /\ busy' = TRUE /\ abandoned' = FALSE
    /\ onWire' = 2
    /\ run' = [run EXCEPT ![2] = "running"]
    /\ caller' = [caller EXCEPT ![2] = "waiting"]
    /\ UNCHANGED <<finished, protoDone, sent, pendEnq, q, hold, taken, buf,
                   stopped, read>>

\* In English: "any step any goroutine can take."
\* Literally: "Progress is defined as: there exists an r in Reqs such that
\*   DeliverRange of r, or Enqueue of r, or RunTake of r, or RunSend of r,
\*   or RunStopped of r, or Read of r, or Abandon of r, or ProtocolEnds of
\*   r; or Acquire2."
Progress ==
    \/ \E r \in Reqs :
        \/ DeliverRange(r) \/ Enqueue(r)
        \/ RunTake(r) \/ RunSend(r) \/ RunStopped(r)
        \/ Read(r) \/ Abandon(r) \/ ProtocolEnds(r)
    \/ Acquire2

\* In English: "Every caller has returned or never started, every delivery
\* goroutine has ended, and nothing is half-delivered."
\* Literally: "AllEnded is defined as: for all r in Reqs, caller of r is not
\*   "waiting", and run of r is not "running", and pendEnq of r is false."
AllEnded == \A r \in Reqs : caller[r] # "waiting" /\ run[r] # "running" /\ ~pendEnq[r]

\* In English: "Once everything has ended, nothing changes: an expected
\* ending, not a deadlock."
\* Literally: "Finished is defined as: AllEnded, and vars is unchanged."
Finished == AllEnded /\ UNCHANGED vars

\* In English: "a step is a goroutine's step, or staying finished."
\* Literally: "Next is defined as: Progress or Finished."
Next == Progress \/ Finished

\* In English: "start in Init; every later step is a Next step."
\* Literally: "Spec is defined as: Init, and always every step is a Next
\*   step or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "no goroutine can take a step."
\* Literally: "Quiescent is defined as: Progress is not enabled."
Quiescent == ~ENABLED Progress

\* In English: "Once nothing can move, no delivery goroutine is still
\* running after its caller left: every leaked `run` is a goroutine goleak
\* finds, holding the replies it queued." The reference gives each request's
\* replies to the one thread that asked (ouroboros-consensus LeiosFetch
\* client), so nothing outlives the caller.
\* Literally: "DeliveryEndsWhenCallerLeaves is defined as: if Quiescent then
\*   for all r in Reqs, if caller of r equals "gone" then run of r is not
\*   "running"."
DeliveryEndsWhenCallerLeaves ==
    Quiescent => \A r \in Reqs : caller[r] = "gone" => run[r] # "running"

\* In English: "A caller's leaving never touches another request: a
\* delivery is stopped only by its own caller or after its own terminal
\* reply, and the live waiter's caller is always still waiting."
\* Literally: "OwnDeliveryOnly is defined as: for all r in Reqs, if stopped
\*   of r then caller of r equals "gone" or taken of r equals Replies; and
\*   if waiter is not 0 then caller of waiter equals "waiting"."
OwnDeliveryOnly ==
    /\ \A r \in Reqs : stopped[r] => caller[r] = "gone" \/ taken[r] = Replies
    /\ waiter # 0 => caller[waiter] = "waiting"

\* In English: "Each variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: waiter is in 0 through 2, busy,
\*   abandoned and protoDone are booleans, finished is a subset of Reqs, and
\*   for all r in Reqs, buf of r is in 0 through 1 and read of r is at most
\*   Replies."
TypeOK ==
    /\ waiter \in 0..2
    /\ busy \in BOOLEAN /\ abandoned \in BOOLEAN /\ protoDone \in BOOLEAN
    /\ finished \subseteq Reqs
    /\ \A r \in Reqs : buf[r] \in 0..1 /\ read[r] <= Replies
=============================================================================
