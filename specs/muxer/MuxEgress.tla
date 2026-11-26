------------------------------ MODULE MuxEgress ------------------------------
(***************************************************************************)
(* Who writes the next segment (muxer/egress.go: egress.acquire, release,  *)
(* EgressClassOf; muxer/muxer.go: Send and the per-role sender goroutine). *)
(*                                                                         *)
(* One segment is written at a time. A Send that finds the connection free *)
(* takes the turn at once; otherwise it queues, in the Praos queue or the  *)
(* Leios queue by its mini-protocol's class. On release the turn goes to   *)
(* the head of the Praos queue, unless a Leios segment waits and either no *)
(* Praos segment waits or praosBurst Praos turns in a row have passed it.  *)
(* Each mini-protocol role has one sender goroutine, so it has at most one *)
(* segment in Send at a time.                                              *)
(*                                                                         *)
(* The reference [R2] keeps one FIFO queue for every mini-protocol, each   *)
(* with at most one entry, and puts a mini-protocol back at the tail after *)
(* each SDU: round-robin, with no classes. gOuroboros keeps that inside    *)
(* each class (FIFO, one entry per mini-protocol) and adds a bounded       *)
(* Praos priority over Leios.                                              *)
(*                                                                         *)
(* Stop closes doneChan. A queued Send that sees it leaves the queue, or,  *)
(* if it was granted the turn at the same moment, hands the turn on; a     *)
(* Send granted the turn re-checks doneChan before writing.                *)
(*                                                                         *)
(* Granularity: Send's acquire is one step (egress.mu held); noticing the  *)
(* grant or doneChan is one step; the write together with release is one  *)
(* step (other Sends may queue before it, which is what fairness is        *)
(* about).                                                                 *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `pc[p]` is mini-protocol p's sender.                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Praos,      \* the Praos-class mini-protocols, e.g. {"cs", "bf"}
    Leios,      \* the Leios-class mini-protocols, e.g. {"lf", "lv"}
    Burst,      \* praosBurst
    WithStop,   \* Stop may happen
    \* Mutations, each FALSE for gOuroboros:
    NoBurst,    \* Leios goes only when no Praos waits
    LeiosFirst, \* Leios always goes before Praos
    Lifo,       \* the newest waiter of a class goes first
    NoDoneCheck,\* a granted Send writes without re-checking doneChan
    IgnoreBusy  \* the fast path takes the turn even when it is held

\* In English: "every mini-protocol, of either class."
Protocols == Praos \cup Leios

VARIABLES
    pc,         \* per protocol: "idle", "queued", "granted", "check", "write", "exited"
    busy,       \* egress.busy
    praosQ,     \* egress.praos, as a sequence of protocols
    leiosQ,     \* egress.leios
    praosRun,   \* egress.praosRun
    done,       \* doneChan is closed
    \* Ghost variables: they record history for the invariants and change
    \* nothing in the Go code's behaviour.
    streak,     \* Praos grants in a row while a Leios segment waits
    lstreak,    \* Leios grants in a row while a Praos segment waits
    overtook,   \* a grant went to a waiter that was not the head of its queue
    queuedAtStop \* the protocols whose Send was waiting when Stop came

\* In English: "all the variables."
vars == <<pc, busy, praosQ, leiosQ, praosRun, done,
          streak, lstreak, overtook, queuedAtStop>>

\* In English: "the set of elements of a sequence."
Elems(s) == {s[i] : i \in 1..Len(s)}

\* In English: "s without its i-th element."
Drop(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

\* In English: "the position in s the next grant takes: the head, or with
\* the Lifo mutation the tail."
Pick(s) == IF Lifo THEN Len(s) ELSE 1

\* In English: "the state just after New."
Init ==
    /\ pc = [p \in Protocols |-> "idle"]
    /\ busy = FALSE
    /\ praosQ = <<>> /\ leiosQ = <<>>
    /\ praosRun = 0
    /\ done = FALSE
    /\ streak = 0 /\ lstreak = 0 /\ overtook = FALSE
    /\ queuedAtStop = {}

\* In English: "release decides the next holder: Leios when one waits and
\* either no Praos waits or the Praos run has reached Burst; otherwise
\* Praos; nobody when no one waits. The chosen waiter's channel is closed
\* (its pc becomes "granted"), and the ghost counters are updated." [G1]
\* Literally: "Release(pc1) is defined as: if both queues are empty, busy
\*   becomes false and praosRun 0; else, with toLeios the choice above,
\*   the waiter at Pick of the chosen queue leaves it, its pc becomes
\*   "granted", praosRun becomes 0 for Leios or goes up by one when Leios
\*   waits, and streak, lstreak and overtook record the grant."
Release(pc1) ==
    IF praosQ = <<>> /\ leiosQ = <<>>
    THEN /\ busy' = FALSE /\ praosRun' = 0                   \* egress.go:145-148
         /\ pc' = pc1
         /\ UNCHANGED <<praosQ, leiosQ, streak, lstreak, overtook>>
    ELSE LET toLeios ==
                 leiosQ # <<>> /\
                 \/ praosQ = <<>>
                 \/ LeiosFirst
                 \/ ~NoBurst /\ praosRun >= Burst            \* egress.go:151-152
             q == IF toLeios THEN leiosQ ELSE praosQ
             i == Pick(q)
             w == q[i]
         IN /\ IF toLeios
                 THEN /\ leiosQ' = Drop(leiosQ, i) /\ UNCHANGED praosQ
                      /\ praosRun' = 0
                 ELSE /\ praosQ' = Drop(praosQ, i) /\ UNCHANGED leiosQ
                      \* praosRun is only compared with Burst, so it is
                      \* kept at most Burst here (the Go int keeps counting).
                      /\ praosRun' = IF leiosQ # <<>> /\ praosRun < Burst
                                       THEN praosRun + 1 ELSE praosRun
            /\ pc' = [pc1 EXCEPT ![w] = "granted"]            \* close(w)
            /\ UNCHANGED busy
            \* The ghost counters stop one past their bound, which is all
            \* the invariants need and keeps the state space finite.
            /\ streak' = IF ~toLeios /\ leiosQ # <<>>
                         THEN IF streak <= Burst THEN streak + 1 ELSE streak
                         ELSE 0
            /\ lstreak' = IF toLeios /\ praosQ # <<>>
                          THEN IF lstreak <= 1 THEN lstreak + 1 ELSE lstreak
                          ELSE 0
            /\ overtook' = (overtook \/ i # 1)

\* In English: "p's sender calls Send. After Stop, Send returns at once and
\* the sender goroutine ends. Otherwise acquire takes the free turn, or
\* queues p in its class's queue."
\* Literally: "Send(p) is defined as: pc[p] is "idle", and if done then
\*   pc[p] becomes "exited"; else if busy is false (or IgnoreBusy) busy
\*   becomes true and pc[p] "check"; else p is appended to its queue and
\*   pc[p] becomes "queued"."
Send(p) ==
    /\ pc[p] = "idle"
    /\ IF done
       THEN /\ pc' = [pc EXCEPT ![p] = "exited"]               \* muxer.go Send: doneChan check
            /\ UNCHANGED <<busy, praosQ, leiosQ>>
       ELSE IF ~busy \/ IgnoreBusy
       THEN /\ busy' = TRUE /\ pc' = [pc EXCEPT ![p] = "check"] \* egress.go:88-97
            /\ UNCHANGED <<praosQ, leiosQ>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "queued"]
            /\ IF p \in Leios
                 THEN leiosQ' = Append(leiosQ, p) /\ UNCHANGED praosQ
                 ELSE praosQ' = Append(praosQ, p) /\ UNCHANGED leiosQ
            /\ UNCHANGED busy
    /\ UNCHANGED <<praosRun, done, streak, lstreak, overtook, queuedAtStop>>

\* In English: "A queued Send sees doneChan before its grant: it removes
\* itself from its queue and returns."
\* Literally: "LeaveOnStop(p) is defined as: pc[p] is "queued" and done,
\*   p leaves its queue and pc[p] becomes "exited"."
LeaveOnStop(p) ==
    /\ pc[p] = "queued" /\ done
    /\ praosQ' = SelectSeq(praosQ, LAMBDA x : x # p)            \* egress.go:116-118
    /\ leiosQ' = SelectSeq(leiosQ, LAMBDA x : x # p)
    /\ pc' = [pc EXCEPT ![p] = "exited"]
    /\ UNCHANGED <<busy, praosRun, done, streak, lstreak, overtook, queuedAtStop>>

\* In English: "A granted Send notices its grant (either select branch; both
\* end with it holding the turn and checking doneChan)."
\* Literally: "Granted(p) is defined as: pc[p] is "granted" and becomes
\*   "check"."
Granted(p) ==
    /\ pc[p] = "granted"
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ UNCHANGED <<busy, praosQ, leiosQ, praosRun, done,
                   streak, lstreak, overtook, queuedAtStop>>

\* In English: "Holding the turn, Send re-checks doneChan: stopped, it hands
\* the turn on and returns; otherwise it goes on to write."
\* Literally: "Check(p) is defined as: pc[p] is "check", and if done and not
\*   NoDoneCheck then Release with pc[p] "exited", else pc[p] becomes
\*   "write"."
Check(p) ==
    /\ pc[p] = "check"
    /\ IF done /\ ~NoDoneCheck
       THEN Release([pc EXCEPT ![p] = "exited"])                \* egress.go:91-95, :107-111, :119-122
       ELSE /\ pc' = [pc EXCEPT ![p] = "write"]
            /\ UNCHANGED <<busy, praosQ, leiosQ, praosRun, streak, lstreak, overtook>>
    /\ UNCHANGED <<done, queuedAtStop>>

\* In English: "Send writes the segment and releases the turn; the sender
\* goroutine then takes the protocol's next segment."
\* Literally: "WriteRelease(p) is defined as: pc[p] is "write", and Release
\*   with pc[p] "idle"."
WriteRelease(p) ==
    /\ pc[p] = "write"
    /\ Release([pc EXCEPT ![p] = "idle"])                       \* muxer.go Send: deferred release
    /\ UNCHANGED <<done, queuedAtStop>>

\* In English: "Stop closes doneChan; the ghost records who was waiting."
\* Literally: "Stop is defined as: WithStop, done is false and becomes true,
\*   and queuedAtStop becomes the protocols queued or granted."
Stop ==
    /\ WithStop /\ ~done
    /\ done' = TRUE
    /\ queuedAtStop' = {p \in Protocols : pc[p] \in {"queued", "granted"}}
    /\ UNCHANGED <<pc, busy, praosQ, leiosQ, praosRun, streak, lstreak, overtook>>

\* In English: "any step of p's sender."
Step(p) == Send(p) \/ LeaveOnStop(p) \/ Granted(p) \/ Check(p) \/ WriteRelease(p)

\* In English: "any step."
Progress == Stop \/ \E p \in Protocols : Step(p)

\* In English: "once nothing can move, nothing changes."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is any step, or resting once none can move."
Next == Progress \/ Rest

\* In English: "start in Init, take Next steps, and every sender that can
\* keep moving eventually does (weak fairness, see the glossary)."
Spec == Init /\ [][Next]_vars /\ \A p \in Protocols : WF_vars(Step(p))

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "At most one Send holds the turn: granted, checking or
\* writing."
\* Literally: "OneHolder is defined as: the set of protocols whose pc is
\*   "granted", "check" or "write" has at most one member."
OneHolder ==
    Cardinality({p \in Protocols : pc[p] \in {"granted", "check", "write"}}) <= 1

\* In English: "A waiting Leios segment is passed by at most Burst Praos
\* turns in a row: Leios is not starved."
LeiosNotStarved == streak <= Burst

\* In English: "A waiting Praos segment is passed by at most one Leios turn
\* in a row: Praos is not starved, and keeps its priority."
PraosNotStarved == lstreak <= 1

\* In English: "Within a class, waiters are granted in the order they
\* queued. With one segment in Send per mini-protocol this is [R2]'s
\* round-robin inside the class."
WithinClassFIFO == ~overtook

\* In English: "A Send still waiting for its turn when Stop came never
\* writes."
NoWriteAfterStop == \A p \in queuedAtStop : pc[p] # "write"

\* In English: "Once stopped and nothing can move, every sender has ended
\* and the turn is free: no turn was lost and no Send hangs."
StopDrains ==
    (~ENABLED Progress /\ done) =>
        /\ \A p \in Protocols : pc[p] = "exited"
        /\ ~busy /\ praosQ = <<>> /\ leiosQ = <<>>

\* In English: "each variable holds the kind of value it should."
TypeOK ==
    /\ pc \in [Protocols -> {"idle", "queued", "granted", "check", "write", "exited"}]
    /\ busy \in BOOLEAN /\ done \in BOOLEAN /\ overtook \in BOOLEAN
    /\ praosRun \in Nat /\ streak \in Nat /\ lstreak \in Nat

-----------------------------------------------------------------------------
(* Liveness. *)

\* In English: "Every queued segment is eventually granted the turn, or its
\* Send ends because the muxer stopped."
EveryQueuedSegmentEventuallySent ==
    \A p \in Protocols : pc[p] = "queued" ~> pc[p] \in {"check", "exited"}
=============================================================================
