--------------------------- MODULE DmqReplayShared ---------------------------
(***************************************************************************)
(* Model `dmq`: the local message notification client's replay cache,      *)
(* shared by every connection built from one Config, and the notification  *)
(* server's expiration cleaner (gOuroboros 7cd17437,                       *)
(* protocol/localmessagenotification/client.go: validateAndReserve,        *)
(* pruneExpiredLocked, admitLocked; server.go: startExpirationCleaner,     *)
(* stopExpirationCleaner, Stop).                                           *)
(*                                                                         *)
(* Replay cache (C22). Two connections receive a reply carrying the same   *)
(* message, which expires at Expiry. Each takes the Config-wide replay     *)
(* lock and, while holding it, prunes expired ids, drops an id already     *)
(* accepted, checks the TTL, authenticates and commits, and records the    *)
(* id; it then releases the lock and hands what is left to                 *)
(* ReplyMessagesFunc. Holding the lock across the whole step is what makes *)
(* "check, authenticate, record" one step across connections; that a slow *)
(* stake lookup stalls the other connections is the price (by design).     *)
(*                                                                         *)
(* Time is whole seconds. A message is valid at t iff t <= Expiry          *)
(* (TTLValidator.ValidateMessageTTLAt: now.After(expiry) rejects); an id   *)
(* is pruned at t iff t > Expiry (pruneExpiredLocked: nowUnix > expiresAt).*)
(* The two bounds meet: an id is kept for as long as its message could be *)
(* admitted again.                                                         *)
(*                                                                         *)
(* Cleaner (C23). NewServer starts a goroutine that prunes acknowledged    *)
(* ids every minute and ends on Stop, the connection's done channel or the *)
(* muxer's. Stop closes the stop channel and waits for it.                 *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoDuplicateDelivery  the message reaches ReplyMessagesFunc at most    *)
(*                        once across the connections sharing the Config.  *)
(*   CleanerJoinedOnStop  once Stop has returned, the cleaner has ended.   *)
(*   CleanerEndsWithOwner the cleaner ends once Stop is called or the      *)
(*                        connection is done (liveness, weak fairness).    *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [R10] dmq-node a267003c, DMQ/NodeToClient/LocalMsgNotification.hs     *)
(*        45-95: the server replays its mempool on every request, so a     *)
(*        client sees the same message again on every connection.          *)
(*   [G3] gOuroboros 7cd17437, protocol/localmessagenotification/          *)
(*        client.go, server.go, as above.                                  *)
(*   [G5] gOuroboros 7cd17437, protocol/common/authentication.go           *)
(*        ValidateMessageTTLAt, and dmq.go IsValidAt.                      *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `pc[c]`, `cleaner` and `stopper` are program counters.         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Expiry,         \* the message's expiresAt, in whole seconds
    MaxTime,        \* the last second the model reaches
    OneLockStep,    \* TRUE: check and record under one hold of the lock
                    \*   (7cd17437); FALSE: a mutation that releases it between
    PruneStrict,    \* TRUE: prune at t > Expiry (7cd17437); FALSE: a mutation
                    \*   that prunes at t >= Expiry
    StopWaits       \* TRUE: Stop waits for the cleaner (7cd17437); FALSE: a
                    \*   mutation that does not

\* In English: "The two connections sharing the Config."
Conns == {1, 2}

VARIABLES
    t,              \* the clock, in whole seconds
    accepted,       \* the id is in the replay cache
    pc,             \* pc[c]: "idle", "checked" (mutation only), "deliver",
                    \*   "done" or "refused"
    delivered,      \* times the message reached ReplyMessagesFunc
    cleaner,        \* the cleaner goroutine: "running" or "ended"
    stopSignal,     \* Stop has closed the cleaner's stop channel
    connDone,       \* the connection's (or muxer's) done channel is closed
    stopper         \* Server.Stop: "idle", "waiting" or "returned"

vars == <<t, accepted, pc, delivered, cleaner, stopSignal, connDone,
          stopper>>
\* The replay lock is held only inside one step (Check, Record), so it
\* needs no variable: a step is atomic.
replayVars == <<t, accepted, pc, delivered>>
cleanerVars == <<cleaner, stopSignal, connDone, stopper>>

\* In English: "At second 0, nothing is cached or delivered; the cleaner
\* runs."
Init ==
    /\ t = 0
    /\ accepted = FALSE
    /\ pc = [c \in Conns |-> "idle"]
    /\ delivered = 0
    /\ cleaner = "running"
    /\ stopSignal = FALSE
    /\ connDone = FALSE
    /\ stopper = "idle"

\* In English: "The message is valid at second t [G5]."
Valid(at) == at <= Expiry
\* In English: "The cached id is dropped at second t [G3]."
Pruned(at) == IF PruneStrict THEN at > Expiry ELSE at >= Expiry

-----------------------------------------------------------------------------
(* The replay cache. *)

\* In English: "A second passes."
Tick ==
    /\ t < MaxTime
    /\ t' = t + 1
    /\ UNCHANGED <<accepted, pc, delivered>> /\ UNCHANGED cleanerVars

\* In English: "Connection c's reply arrives: it takes the lock, prunes,
\* and drops the id if cached. Otherwise, holding the lock, it checks the
\* TTL, authenticates and records the id (one step at 7cd17437), and goes
\* on to deliver after releasing the lock. In the mutation it releases the
\* lock after the check and records later."
Check(c) ==
    /\ pc[c] = "idle"
    /\ LET cached == accepted /\ ~Pruned(t)
       IN  IF cached \/ ~Valid(t)
              THEN /\ pc' = [pc EXCEPT ![c] = "refused"]
                   /\ accepted' = cached
              ELSE IF OneLockStep
                      THEN /\ accepted' = TRUE
                           /\ pc' = [pc EXCEPT ![c] = "deliver"]
                      ELSE /\ accepted' = cached
                           /\ pc' = [pc EXCEPT ![c] = "checked"]
    /\ UNCHANGED <<t, delivered>> /\ UNCHANGED cleanerVars

\* In English: "The mutation's second hold of the lock: record the id."
Record(c) ==
    /\ pc[c] = "checked"
    /\ accepted' = TRUE
    /\ pc' = [pc EXCEPT ![c] = "deliver"]
    /\ UNCHANGED <<t, delivered>> /\ UNCHANGED cleanerVars

\* In English: "Outside the lock, ReplyMessagesFunc gets the message."
Deliver(c) ==
    /\ pc[c] = "deliver"
    /\ delivered' = delivered + 1
    /\ pc' = [pc EXCEPT ![c] = "done"]
    /\ UNCHANGED <<t, accepted>> /\ UNCHANGED cleanerVars

-----------------------------------------------------------------------------
(* The server's cleaner and Stop. *)

\* In English: "Stop closes the cleaner's stop channel."
StopCalls ==
    /\ stopper = "idle"
    /\ stopSignal' = TRUE
    /\ stopper' = "waiting"
    /\ UNCHANGED <<cleaner, connDone>> /\ UNCHANGED replayVars

\* In English: "Stop returns once the cleaner has ended, or at once in the
\* mutation."
StopReturns ==
    /\ stopper = "waiting"
    /\ StopWaits => cleaner = "ended"                  \* <-s.expirationDoneChan
    /\ stopper' = "returned"
    /\ UNCHANGED <<cleaner, stopSignal, connDone>> /\ UNCHANGED replayVars

\* In English: "The connection, or the muxer, is done."
ConnDone ==
    /\ ~connDone
    /\ connDone' = TRUE
    /\ UNCHANGED <<cleaner, stopSignal, stopper>> /\ UNCHANGED replayVars

\* In English: "The cleaner sees its stop channel or the connection done,
\* and ends."
CleanerExits ==
    /\ cleaner = "running" /\ (stopSignal \/ connDone)
    /\ cleaner' = "ended"
    /\ UNCHANGED <<stopSignal, connDone, stopper>> /\ UNCHANGED replayVars

\* In English: "Nothing more can happen."
Finished ==
    /\ \A c \in Conns : pc[c] \in {"done", "refused"}
    /\ t = MaxTime
    /\ stopper \in {"idle", "returned"}

Next ==
    \/ Tick
    \/ \E c \in Conns : Check(c) \/ Record(c) \/ Deliver(c)
    \/ StopCalls \/ StopReturns \/ ConnDone \/ CleanerExits
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(CleanerExits)

-----------------------------------------------------------------------------

TypeOK ==
    /\ t \in 0..MaxTime
    /\ accepted \in BOOLEAN
    /\ pc \in [Conns -> {"idle", "checked", "deliver", "done", "refused"}]
    /\ delivered \in 0..2
    /\ cleaner \in {"running", "ended"}
    /\ stopper \in {"idle", "waiting", "returned"}

\* In English: "The message reaches ReplyMessagesFunc at most once."
NoDuplicateDelivery == delivered <= 1

\* In English: "Once Stop has returned, the cleaner has ended."
CleanerJoinedOnStop == stopper = "returned" => cleaner = "ended"

\* In English: "Once Stop is called or the connection is done, the cleaner
\* eventually ends." (~> is "leads to": whenever the left side holds, the
\* right side holds then or later.)
CleanerEndsWithOwner == (stopSignal \/ connDone) ~> (cleaner = "ended")

\* Probe, EXPECTED to be violated: "The message is never delivered at the
\* last second it is valid."
ProbeNoDeliveryAtExpiry == ~(delivered > 0 /\ t = Expiry /\ \E c \in Conns : pc[c] = "idle")
=============================================================================
