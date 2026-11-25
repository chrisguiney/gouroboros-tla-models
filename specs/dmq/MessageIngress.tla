---------------------------- MODULE MessageIngress ----------------------------
(***************************************************************************)
(* Model `dmq`, part 6: what a node does with the DMQ messages it         *)
(* receives.                                                               *)
(*                                                                         *)
(* A peer replies to a body request with up to two messages. The node     *)
(* drops a message it already holds, then validates the rest one at a     *)
(* time. Each validation either accepts the message, drops it quietly     *)
(* (expired, or its pool is not registered), or fails fatally, which      *)
(* disconnects the peer once the whole reply has been handled. The       *)
(* reference also refuses, fatally, a second message from one pool within *)
(* a minimum delay of the last one it accepted.                            *)
(*                                                                         *)
(* gOuroboros also re-verifies messages it already accepted (relaying     *)
(* them with AddMessage, or a local notification replay), and runs local  *)
(* submissions from two connections at once through PrepareMessages and   *)
(* its commit function.                                                    *)
(*                                                                         *)
(* Questions:                                                              *)
(*   OutcomeAsReference  each reply ends as the reference's would: the    *)
(*                same messages accepted, the same last-accepted time,    *)
(*                and a disconnect exactly when the reference disconnects. *)
(*   ReverifyAccepted  re-verifying an accepted message never fails.      *)
(*   DelayHeld    no two accepted messages of a pool are closer than the  *)
(*                minimum delay.                                           *)
(*   DuplicateNotFatal  a local submission that lost a race to the same   *)
(*                message is not refused.                                  *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Reference, IntersectMBO/dmq-node a267003c14e9, dmq-node/:             *)
(*   [R1] src/DMQ/Protocol/SigSubmission/Validate.hs 115-212: check order *)
(*        expired, too far ahead, too frequent, id, KES window, pool,      *)
(*        counter, opcert and KES signatures; a refused message changes    *)
(*        no state (96-100).                                               *)
(*   [R2] Validate.hs 124-145: SigTooFrequent when less than vcMinSigDelay *)
(*        has passed since the pool's last accepted message; the time is   *)
(*        recorded only on acceptance.                                     *)
(*   [R3] src/DMQ/Policy.hs 52-55: minSigDelay = 60 s.                     *)
(*   [R4] app/Main.hs 199-221: for node-to-node, SigDuplicate, SigExpired, *)
(*        NotInitialized, PoolNotEligible and UnrecognizedPool are only    *)
(*        traced; any other error is thrown, closing the connection.       *)
(*   [R5] ouroboros-network 4646039f, ouroboros-network/lib/Ouroboros/    *)
(*        Network/TxSubmission/Mempool/Simple.hs 183-245: one timestamp    *)
(*        per batch; messages already in the mempool are SigDuplicate and  *)
(*        not validated; the valid ones are added before the invalid ones  *)
(*        are handled.                                                     *)
(*   gOuroboros, blinklabs-io/gouroboros ebc63eab:                         *)
(*   [G1] protocol/messagesubmission/server.go handleReplyMessages: any   *)
(*        TTL or authentication error refuses the whole reply and closes   *)
(*        the connection.                                                  *)
(*   [G2] protocol/common/authentication.go verifyMessageInternal: order  *)
(*        id, stake, opcert, KES (window and signature), counter; no rate  *)
(*        limit.                                                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Ids,        \* the messages, all from one pool
    FailSets,   \* the sets of failures a message may carry
    Delay,      \* the minimum delay between a pool's messages, in ticks
    MaxTicks,   \* the clock stops here
    Workers,    \* connections that may hold a prepared local submission
    Mutation    \* "none", or which gOuroboros behaviour to model

\* In English: "The reference's check order, with "toofrequent" in the
\* place it is checked [R1]."
\* Literally: "RefOrder is defined as the sequence "expired", "toofar",
\*   "toofrequent", "kesWindow", "unregistered", "counter", "badsig"."
RefOrder == <<"expired", "toofar", "toofrequent", "kesWindow",
              "unregistered", "counter", "badsig">>

\* In English: "gOuroboros's order: the reference's, or main's, which checks
\* the pool before the KES window and the signatures before the counter."
\* Literally: "GoOrder is defined as: if Mutation equals "MainOrder", then
\*   the sequence "expired", "toofar", "toofrequent", "unregistered",
\*   "badsig", "kesWindow", "counter"; otherwise RefOrder."
GoOrder == IF Mutation = "MainOrder"
           THEN <<"expired", "toofar", "toofrequent", "unregistered",
                  "badsig", "kesWindow", "counter">>
           ELSE RefOrder

\* In English: "The outcomes the reference only traces, for node-to-node
\* [R4]; every other failure disconnects."
\* Literally: "Tolerated is defined as the set containing "expired" and
\*   "unregistered"."
Tolerated == {"expired", "unregistered"}

\* In English: "The node has never accepted a message from the pool."
\* Literally: "Never is defined as minus Delay." (So that 0 - Never >= Delay.)
Never == -Delay

\* In English: "A worker with no prepared submission."
\* Literally: "Idle is defined as the record whose field kind is "idle"."
Idle == [kind |-> "idle"]

VARIABLES
    now,       \* the clock, in ticks
    fails,     \* id -> the failures that message carries (fixed at start)
    accepted,  \* ids the node holds (the reference's mempool)
    lastT,     \* time the pool's last message was accepted, or Never
    history,   \* the times of every acceptance, in order
    pending,   \* worker -> prepared local submission, or Idle
    out        \* the last decision, for the invariants

\* Literally: "vars is defined as the tuple of all seven variables."
vars == <<now, fails, accepted, lastT, history, pending, out>>

\* In English: "The first failure of message id, in order ord, given the
\* last-accepted time t, or "ok"." Too frequent applies only when the rate
\* limit is in force ("NoRateLimit" is main today).
\* Literally: "FirstFail of id, ord, t and rate is defined as: letting fs be
\*   fails of id, together with "toofrequent" if rate and now minus t is less
\*   than Delay; if there exists an i in 1 to the length of ord such that
\*   ord of i is a member of fs, then ord of the least such i; otherwise
\*   "ok"."
FirstFail(id, ord, t, rate) ==
    LET fs == fails[id] \cup
              (IF rate /\ now - t < Delay THEN {"toofrequent"} ELSE {})
        hits == {i \in 1..Len(ord) : ord[i] \in fs}
    IN IF hits = {} THEN "ok"
       ELSE ord[CHOOSE i \in hits : \A j \in hits : i <= j]

\* In English: "Handle one message of a reply, given the running result r:
\* a held one is dropped unvalidated; otherwise the first failure decides."
\* Literally: "Step of r, id, ord and rate is defined as: if id is a member
\*   of r.acc, then r; otherwise, letting f be FirstFail of id, ord, r.t and
\*   rate: if f equals "ok", then r with id added to acc, t set to now and
\*   now appended to hist; otherwise r with fatal set to (r.fatal or f is
\*   not a member of Tolerated)."
Step(r, id, ord, rate) ==
    IF id \in r.acc THEN r
    ELSE LET f == FirstFail(id, ord, r.t, rate) IN
         IF f = "ok"
         THEN [r EXCEPT !.acc = @ \cup {id}, !.t = now,
                        !.hist = Append(@, now)]
         ELSE [r EXCEPT !.fatal = @ \/ f \notin Tolerated]

\* In English: "Handle a reply b (one or two ids) from the current state."
\* Literally: "Run of b, ord and rate is defined as: letting r0 be the
\*   record of accepted, lastT, history and fatal FALSE, and r1 be Step of
\*   r0 and b of 1: if the length of b is 1 then r1, otherwise Step of r1 and
\*   b of 2."
Run(b, ord, rate) ==
    LET r0 == [acc |-> accepted, t |-> lastT, hist |-> history,
               fatal |-> FALSE]
        r1 == Step(r0, b[1], ord, rate)
    IN IF Len(b) = 1 THEN r1 ELSE Step(r1, b[2], ord, rate)

\* In English: "The reference's result for reply b [R1]-[R5]."
\* Literally: "RefRun of b is defined as Run of b, RefOrder and TRUE."
RefRun(b) == Run(b, RefOrder, TRUE)

\* In English: "gOuroboros's result for reply b. "AllOrNothing" is main:
\* any failure (other than a held id) refuses the whole reply and
\* disconnects [G1]."
\* Literally: "GoRun of b is defined as: letting r be Run of b, GoOrder and
\*   (Mutation is not "NoRateLimit"), and bad be whether there exists an i in
\*   the domain of b such that b of i is not in accepted and FirstFail of b of
\*   i, GoOrder, lastT and (Mutation is not "NoRateLimit") is not "ok": if
\*   Mutation equals "AllOrNothing" and bad, then the record of accepted,
\*   lastT, history and fatal TRUE; otherwise r."
GoRun(b) ==
    LET rate == Mutation # "NoRateLimit"
        r == Run(b, GoOrder, rate)
        bad == \E i \in DOMAIN b :
                  b[i] \notin accepted /\ FirstFail(b[i], GoOrder, lastT, rate) # "ok"
    IN IF Mutation = "AllOrNothing" /\ bad
       THEN [acc |-> accepted, t |-> lastT, hist |-> history, fatal |-> TRUE]
       ELSE r

\* In English: "Every reply: one id, or two different ids."
\* Literally: "Replies is defined as the set of sequences <<i>> for i in
\*   Ids, together with <<i, j>> for i and j in Ids with i not equal to j."
Replies == {<<i>> : i \in Ids} \cup
           ({<<i, j>> : i, j \in Ids} \ {<<i, i>> : i \in Ids})

\* In English: "Start: clock 0, any failures per message, nothing held."
\* Literally: "Init is defined as: now equals 0, fails is a member of the
\*   set of functions from Ids to FailSets, accepted is empty, lastT equals
\*   Never, history is empty, every worker is Idle, out has kind "none"."
Init ==
    /\ now = 0
    /\ fails \in [Ids -> FailSets]
    /\ accepted = {}
    /\ lastT = Never
    /\ history = <<>>
    /\ pending = [w \in Workers |-> Idle]
    /\ out = [kind |-> "none"]

\* Literally: "Tick is defined as: now is less than MaxTicks, now in the
\*   next state is now plus 1, and everything else is unchanged."
Tick ==
    /\ now < MaxTicks
    /\ now' = now + 1
    /\ UNCHANGED <<fails, accepted, lastT, history, pending, out>>

\* In English: "A peer's reply b arrives; gOuroboros handles it, and the
\* reference's result is kept beside it for comparison."
\* Literally: "Reply of b is defined as: letting g be GoRun of b and r be
\*   RefRun of b: accepted, lastT and history in the next state are g's, and
\*   out in the next state is the record of kind "reply", g, r, and the ids
\*   in g.acc but not in accepted; and now, fails and pending are
\*   unchanged."
Reply(b) ==
    LET g == GoRun(b)
        r == RefRun(b)
    IN /\ accepted' = g.acc
       /\ lastT' = g.t
       /\ history' = g.hist
       /\ out' = [kind |-> "reply", go |-> g, ref |-> r,
                  fresh |-> g.acc \ accepted]
       /\ UNCHANGED <<now, fails, pending>>

\* In English: "gOuroboros re-verifies a message it already holds (relay
\* or replay). It is exempt from the rate limit as a duplicate, unless
\* "RateOnDuplicate"."
\* Literally: "Reverify of id is defined as: id is a member of accepted,
\*   and out in the next state is the record of kind "reverify" and ok,
\*   where ok is whether FirstFail of id, GoOrder, lastT and (Mutation equals
\*   "RateOnDuplicate") equals "ok"; everything else unchanged."
Reverify(id) ==
    /\ id \in accepted
    /\ out' = [kind |-> "reverify",
               ok |-> FirstFail(id, GoOrder, lastT,
                                Mutation = "RateOnDuplicate") = "ok"]
    /\ UNCHANGED <<now, fails, accepted, lastT, history, pending>>

\* In English: "A local submission of id is prepared on worker w against
\* the current state, without changing it."
\* Literally: "Prepare of w and id is defined as: pending of w is Idle, and
\*   pending of w in the next state is the record of kind "prepared", id,
\*   now, whether id is a member of accepted, and ok (FirstFail of id,
\*   GoOrder, lastT and TRUE equals "ok"); everything else unchanged."
Prepare(w, id) ==
    /\ pending[w] = Idle
    /\ pending' = [pending EXCEPT ![w] =
          [kind |-> "prepared", id |-> id, at |-> now,
           dup |-> id \in accepted,
           ok |-> id \in accepted \/ FirstFail(id, GoOrder, lastT, TRUE) = "ok"]]
    /\ UNCHANGED <<now, fails, accepted, lastT, history, out>>

\* In English: "Worker w commits: a message held by now (another
\* connection won the race) succeeds without recording anything ("DupRaceFatal":
\* it is refused); otherwise the rate limit is re-checked against the
\* latest acceptance ("NoRateRecheck" skips it) and the acceptance is
\* recorded."
\* Literally: "Commit of w is defined as: pending of w is not Idle; letting
\*   q be pending of w, held be whether q.id is a member of accepted, and
\*   ok be q.ok and (if held then Mutation is not "DupRaceFatal" otherwise
\*   (Mutation is "NoRateRecheck" or q.at minus lastT is at least Delay)):
\*   if ok and not held, accepted gains q.id, lastT becomes q.at and q.at is
\*   appended to history, otherwise they are unchanged; pending of w becomes
\*   Idle; out becomes the record of kind "commit", held and ok."
Commit(w) ==
    /\ pending[w] # Idle
    /\ LET q == pending[w]
           held == q.id \in accepted
           ok == q.ok /\ IF held THEN Mutation # "DupRaceFatal"
                         ELSE Mutation = "NoRateRecheck" \/ q.at - lastT >= Delay
       IN /\ IF ok /\ ~held
               THEN /\ accepted' = accepted \cup {q.id}
                    /\ lastT' = q.at
                    /\ history' = Append(history, q.at)
               ELSE UNCHANGED <<accepted, lastT, history>>
          /\ pending' = [pending EXCEPT ![w] = Idle]
          /\ out' = [kind |-> "commit", dup |-> held,
                     valid |-> q.ok, ok |-> ok]
    /\ UNCHANGED <<now, fails>>

\* Literally: "Next is defined as: Tick, or a Reply of some b in Replies, or
\*   a Reverify of some id in Ids, or a Prepare of some w and id, or a Commit
\*   of some w."
Next ==
    \/ Tick
    \/ \E b \in Replies : Reply(b)
    \/ \E id \in Ids : Reverify(id)
    \/ \E w \in Workers, id \in Ids : Prepare(w, id)
    \/ \E w \in Workers : Commit(w)

\* Literally: "Spec is defined as: Init and always (Next or vars unchanged)."
Spec == Init /\ [][Next]_vars

\* In English: "A reply ends as the reference's would."
\* Literally: "OutcomeAsReference is defined as: if out.kind is "reply",
\*   then out.go equals out.ref."
OutcomeAsReference == out.kind = "reply" => out.go = out.ref

\* In English: "Re-verifying a held message never fails."
\* Literally: "ReverifyAccepted is defined as: if out.kind is "reverify",
\*   then out.ok."
ReverifyAccepted == out.kind = "reverify" => out.ok

\* In English: "Acceptances are at least Delay apart."
\* Literally: "DelayHeld is defined as: for every i and j in the domain of
\*   history with i less than j, history of j minus history of i is at
\*   least Delay."
DelayHeld ==
    \A i, j \in DOMAIN history : i < j => history[j] - history[i] >= Delay

\* In English: "A valid local submission that lost a race to the same
\* message is not refused."
\* Literally: "DuplicateNotFatal is defined as: if out.kind is "commit" and
\*   out.dup and out.valid, then out.ok."
DuplicateNotFatal ==
    (out.kind = "commit" /\ out.dup /\ out.valid) => out.ok

\* In English: "No reply both accepts a message and disconnects." Violated:
\* as in the reference, the valid messages of a reply are kept even when
\* another one in it is fatal.
\* Literally: "ProbeNoAcceptAndDisconnect is defined as: it is not the case
\*   that out.kind is "reply" and out.go.fatal and out.fresh is not empty."
ProbeNoAcceptAndDisconnect ==
    ~(out.kind = "reply" /\ out.go.fatal /\ out.fresh # {})

\* In English: "No message is refused as too frequent." Violated: the rate
\* limit refuses one.
\* Literally: "ProbeNeverTooFrequent is defined as: it is not the case that
\*   out.kind is "reply", out.go.fatal, and some id fails no other check."
ProbeNeverTooFrequent ==
    ~(out.kind = "reply" /\ out.go.fatal /\ \A id \in Ids : fails[id] = {})
=============================================================================
