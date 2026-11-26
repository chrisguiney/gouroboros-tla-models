------------------------- MODULE BlockFetchAdmission -------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 8: the in-flight byte bound and the ingress   *)
(* allowance for pipelined RequestRange callers.                           *)
(*                                                                         *)
(* gOuroboros file: protocol/blockfetch/client.go (sendRequestRange,       *)
(* waitForInFlightCapacity, hasInFlightCapacityLocked,                     *)
(* updateIngressAllowanceLocked, removeLocked, releaseBytesLocked), at     *)
(* blinklabs-io/gouroboros 7cd17437.                                       *)
(*                                                                         *)
(* What the code does [G1]:                                                *)
(*   A caller first waits, without the send token, until the request fits: *)
(*   under queueMutex it checks the bound, and if the request does not fit *)
(*   it takes the current bytesFreed channel and waits for it to close.    *)
(*   It then takes the send token and checks again under queueMutex; if    *)
(*   another caller took the room meanwhile it hands the token back and    *)
(*   waits again. Otherwise, in the same queueMutex hold, it appends the   *)
(*   request, adds its expected bytes to inFlightBytes and recomputes the  *)
(*   protocol's ingress allowance, then sends and hands the token back.    *)
(*   A request fits when the queue is empty (so one larger than the whole  *)
(*   bound still goes), or when it fits in what is left of the bound.      *)
(*   Removing a request (an answer, a deadline, a drain) subtracts its     *)
(*   bytes, closes and replaces bytesFreed, and recomputes the allowance:  *)
(*   the sum of the estimated requests' ingress bytes plus one             *)
(*   maximum-size message, with backpressure on while any unestimated      *)
(*   request is queued.                                                    *)
(*                                                                         *)
(* Questions: is inFlightBytes always within the bound (except one lone    *)
(* oversize request) and equal to what is queued; can a parked caller miss *)
(* the wake-up for room that is free; does the allowance always match the  *)
(* queue?                                                                  *)
(*                                                                         *)
(* Sources: the bound and the allowance are gOuroboros's own; the          *)
(* reference's fetch decision logic bounds bytes in flight per peer        *)
(* (ouroboros-network 5f356486ab3e,                                        *)
(* ouroboros-network/lib/Ouroboros/Network/BlockFetch/Decision.hs,         *)
(* maxInFlightReqsPerPeer / inFlightBytesHighWatermark) but is not modelled *)
(* here. [G1] client.go 992-1001 (hasInFlightCapacityLocked), 1061-1089    *)
(* (updateIngressAllowanceLocked), 1094-1118 (waitForInFlightCapacity),    *)
(* 1145-1201 (the admission loop), 1369-1392 (removeLocked,                *)
(* releaseBytesLocked).                                                    *)
(*                                                                         *)
(* An ingress allowance is abstracted to the request's size (the code adds *)
(* a tenth); Max stands for StreamingMaxPendingMessageBytes.               *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `pc` is a program counter per caller.                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Estimated,   \* the callers that set ExpectedBytes
    Bound,       \* MaxInFlightBytes
    Max,         \* one maximum-size message
    \* Mutations, each FALSE in the code as it is:
    NoRecheck,   \* no capacity check under the send token
    NoWake,      \* removing a request does not close bytesFreed
    StaleAllowance \* removing a request does not recompute the allowance

\* The callers, and each one's expected bytes. With Bound = 4: caller 3 is
\* larger than the whole bound, and callers 1 and 2 do not fit together.
\* Literally: "Callers is the set 1 through 3; Size is the sequence 3, 2, 5."
Callers == 1..3
Size == <<3, 2, 5>>

VARIABLES
    pc,        \* pc[c]: "start", "parked", "token", "send", "sent", "done"
    parkGen,   \* parkGen[c]: the bytesFreed generation c waits on
    gen,       \* the current bytesFreed generation
    token,     \* who holds the send token: a caller, or 0
    queue,     \* the client queue: callers' requests, oldest first
    inFlight,  \* inFlightBytes
    allowance, \* the protocol's ingress allowance
    backp      \* the protocol's ingress backpressure

vars == <<pc, parkGen, gen, token, queue, inFlight, allowance, backp>>

RECURSIVE SumSizes(_)
\* In English: "The sum of the sizes of the requests in sequence s."
\* Literally: "SumSizes(s) is defined as: 0 if s is empty, else Size of the
\*   head of s plus SumSizes of the tail of s."
SumSizes(s) == IF s = <<>> THEN 0 ELSE Size[Head(s)] + SumSizes(Tail(s))

RECURSIVE SumIngress(_)
\* In English: "The sum of the ingress bytes of the estimated requests in s."
\* Literally: "SumIngress(s) is defined as: 0 if s is empty, else (Size of
\*   the head if it is estimated, else 0) plus SumIngress of the tail."
SumIngress(s) ==
    IF s = <<>> THEN 0
    ELSE (IF Head(s) \in Estimated THEN Size[Head(s)] ELSE 0)
         + SumIngress(Tail(s))

\* In English: "The allowance the code computes for queue s [G1 1061-1089]."
\* Literally: "AllowanceFor(s) is defined as: 0 if SumIngress(s) is 0, else
\*   SumIngress(s) plus Max."
AllowanceFor(s) == IF SumIngress(s) = 0 THEN 0 ELSE SumIngress(s) + Max

\* In English: "Some request in s is unestimated."
\* Literally: "BackpFor(s) is defined as: there is an i in 1 through the
\*   length of s whose element is not in Estimated."
BackpFor(s) == \E i \in 1..Len(s) : s[i] \notin Estimated

\* In English: "A request of e bytes fits [G1 992-1001]."
\* Literally: "Fits(e) is defined as: the queue is empty, or inFlight is at
\*   most Bound and e is at most Bound minus inFlight."
Fits(e) == queue = <<>> \/ (inFlight <= Bound /\ e <= Bound - inFlight)

\* In English: "Nobody has asked yet; the token is free."
\* Literally: "Init is defined as: every caller is at "start" waiting on
\*   generation 0, gen is 0, token is 0, queue is empty, and inFlight,
\*   allowance are 0 and backp is FALSE."
Init ==
    /\ pc = [c \in Callers |-> "start"]
    /\ parkGen = [c \in Callers |-> 0]
    /\ gen = 0 /\ token = 0 /\ queue = <<>> /\ inFlight = 0
    /\ allowance = 0 /\ backp = FALSE

-----------------------------------------------------------------------------

\* In English: "Under queueMutex, caller c checks for room: it goes on to
\* the token, or parks on the current bytesFreed."
\* Literally: "Check(c) is defined as: pc[c] equals "start", and if
\*   Fits(Size[c]) then pc' maps c to "token" and parkGen is unchanged, else
\*   pc' maps c to "parked" and parkGen' maps c to gen; and the other
\*   variables are unchanged."
Check(c) ==
    /\ pc[c] = "start"
    /\ IF Fits(Size[c])
          THEN /\ pc' = [pc EXCEPT ![c] = "token"] /\ UNCHANGED parkGen
          ELSE /\ pc' = [pc EXCEPT ![c] = "parked"]
               /\ parkGen' = [parkGen EXCEPT ![c] = gen]
    /\ UNCHANGED <<gen, token, queue, inFlight, allowance, backp>>

\* In English: "bytesFreed closed: the parked caller checks again."
\* Literally: "Wake(c) is defined as: pc[c] equals "parked", and gen is not
\*   parkGen[c], and pc' maps c to "start", and the other variables are
\*   unchanged."
Wake(c) ==
    /\ pc[c] = "parked" /\ gen /= parkGen[c]
    /\ pc' = [pc EXCEPT ![c] = "start"]
    /\ UNCHANGED <<parkGen, gen, token, queue, inFlight, allowance, backp>>

\* In English: "Caller c takes the send token and, under queueMutex, checks
\* again: if the request still fits it is appended, its bytes reserved and
\* the allowance recomputed; otherwise the token goes back and c starts
\* over."
\* Literally: "Admit(c) is defined as: pc[c] equals "token", and token
\*   equals 0, and if NoRecheck or Fits(Size[c]) then token' equals c, pc'
\*   maps c to "send", queue' is queue with c appended, inFlight' is
\*   inFlight plus Size[c], allowance' and backp' are those for queue'; else
\*   pc' maps c to "start" and the rest is unchanged; and parkGen and gen
\*   are unchanged."
Admit(c) ==
    /\ pc[c] = "token" /\ token = 0
    /\ IF NoRecheck \/ Fits(Size[c])
          THEN /\ token' = c
               /\ pc' = [pc EXCEPT ![c] = "send"]
               /\ queue' = Append(queue, c)
               /\ inFlight' = inFlight + Size[c]
               /\ allowance' = AllowanceFor(Append(queue, c))
               /\ backp' = BackpFor(Append(queue, c))
          ELSE /\ pc' = [pc EXCEPT ![c] = "start"]
               /\ UNCHANGED <<token, queue, inFlight, allowance, backp>>
    /\ UNCHANGED <<parkGen, gen>>

\* In English: "MsgRequestRange is queued on the protocol; the token goes
\* back."
\* Literally: "Send(c) is defined as: pc[c] equals "send", and pc' maps c to
\*   "sent", and token' equals 0, and the other variables are unchanged."
Send(c) ==
    /\ pc[c] = "send"
    /\ pc' = [pc EXCEPT ![c] = "sent"] /\ token' = 0
    /\ UNCHANGED <<parkGen, gen, queue, inFlight, allowance, backp>>

\* In English: "Request i of the queue is resolved and removed (an answer
\* takes the head; a deadline or drain may take any): its bytes are freed,
\* bytesFreed is closed and replaced, and the allowance recomputed."
\* Literally: "Remove(i) is defined as: i is in 1 through the length of
\*   queue, and pc of its caller is "sent", and queue' is queue without
\*   element i, and inFlight' is inFlight minus its size, and gen' is gen
\*   plus 1 unless NoWake, and allowance' and backp' are those for queue'
\*   unless StaleAllowance, and pc' maps its caller to "done", and parkGen
\*   and token are unchanged."
\* SubSeq(s, m, n) is elements m through n of s, and s \o t is s followed
\* by t (both from the standard Sequences module); `rest` is the queue
\* without element i.
Remove(i) ==
    LET c == queue[i]
        rest == SubSeq(queue, 1, i - 1) \o SubSeq(queue, i + 1, Len(queue))
    IN /\ pc[c] = "sent"
       /\ queue' = rest
       /\ inFlight' = inFlight - Size[c]
       /\ gen' = IF NoWake THEN gen ELSE gen + 1
       /\ IF StaleAllowance
             THEN UNCHANGED <<allowance, backp>>
             ELSE /\ allowance' = AllowanceFor(rest)
                  /\ backp' = BackpFor(rest)
       /\ pc' = [pc EXCEPT ![c] = "done"]
       /\ UNCHANGED <<parkGen, token>>

-----------------------------------------------------------------------------

\* In English: "Every caller's request has come and gone."
\* Literally: "Finished is defined as: every caller is "done", and the
\*   variables are unchanged."
Finished == (\A c \in Callers : pc[c] = "done") /\ UNCHANGED vars

\* Literally: "Next is defined as: some caller c takes Check(c), Wake(c),
\*   Admit(c) or Send(c), or some queue position i takes Remove(i), or
\*   Finished."
Next ==
    \/ \E c \in Callers : Check(c) \/ Wake(c) \/ Admit(c) \/ Send(c)
    \/ \E i \in 1..Len(queue) : Remove(i)
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Each variable holds a value of the right kind."
TypeOK ==
    /\ pc \in [Callers -> {"start", "parked", "token", "send", "sent",
                           "done"}]
    /\ token \in Callers \cup {0}
    /\ inFlight \in Nat /\ allowance \in Nat /\ backp \in BOOLEAN

\* In English: "inFlightBytes is within the bound, unless the queue holds a
\* single request (one larger than the bound, admitted to an empty queue)."
\* Literally: "InFlightWithinBound is defined as: inFlight is at most Bound,
\*   or the length of queue is 1."
InFlightWithinBound == inFlight <= Bound \/ Len(queue) = 1

\* In English: "inFlightBytes is exactly the reserved bytes of the queue."
\* Literally: "InFlightMatchesQueue is defined as: inFlight equals
\*   SumSizes(queue)."
InFlightMatchesQueue == inFlight = SumSizes(queue)

\* In English: "At most the token's holder is between append and send."
\* Literally: "TokenConserved is defined as: for every caller c, pc[c]
\*   equals "send" exactly when token equals c."
TokenConserved == \A c \in Callers : (pc[c] = "send") <=> (token = c)

\* In English: "A caller parked on the current bytesFreed really has no
\* room: room appears only by a removal, which closes that channel."
\* Literally: "NoLostWakeup is defined as: for every caller c parked on
\*   generation gen, Fits(Size[c]) is false."
NoLostWakeup ==
    \A c \in Callers : (pc[c] = "parked" /\ parkGen[c] = gen) =>
                           ~Fits(Size[c])

\* In English: "The allowance and backpressure always match the queue, so
\* every byte of every estimated request is covered from before its send."
\* Literally: "AllowanceMatchesQueue is defined as: allowance equals
\*   AllowanceFor(queue) and backp equals BackpFor(queue)."
AllowanceMatchesQueue ==
    allowance = AllowanceFor(queue) /\ backp = BackpFor(queue)

\* Probes, each EXPECTED to be violated (reachability).
\* In English: "Nobody ever parks." Violated = the bound makes a caller wait.
\* Literally: "ProbeNeverParks is defined as: no caller is "parked"."
ProbeNeverParks == \A c \in Callers : pc[c] /= "parked"
\* In English: "inFlight never exceeds the bound." Violated = a lone
\* oversize request is admitted.
\* Literally: "ProbeNeverOver is defined as: inFlight is at most Bound."
ProbeNeverOver == inFlight <= Bound
=============================================================================
