---------------------------- MODULE LmsReplayTokens ----------------------------
(***************************************************************************)
(* Model `dmq`: the local message submission server's replay cache, shared *)
(* by every connection built from one Config (gOuroboros 7cd17437,         *)
(* protocol/localmessagesubmission/server.go: submissionReplayState        *)
(* reserve and release, handleSubmitMessage; localmessagesubmission.go:    *)
(* replayStateForConfig, normalizeConfig).                                 *)
(*                                                                         *)
(* Two connections submit the same message, which expires at Expiry. Each  *)
(* one, under the Config-wide replay lock and in one step, prunes expired  *)
(* ids, refuses an id already reserved (AlreadyReceived), commits the      *)
(* authentication and reserves the id with a fresh token. It then runs     *)
(* SubmitMessageFunc without the lock. If the callback accepts, the        *)
(* reservation stays until the message expires; if it rejects, the        *)
(* connection releases the reservation, but only if it still holds that   *)
(* token: once its entry has expired and been pruned, another connection   *)
(* may hold the id under a newer token, and that one must survive. A       *)
(* rejected connection may submit again.                                   *)
(*                                                                         *)
(* Time is whole seconds. With the TTL validator on, a message is admitted *)
(* only at t <= Expiry; with NewNoOpTTLValidator it is admitted at any t.  *)
(* An entry is pruned at t > Expiry.                                       *)
(*                                                                         *)
(* Questions:                                                              *)
(*   AcceptedAtMostOnce    while the message is valid it is accepted once  *)
(*                         at most, across the connections.                *)
(*   ReleaseOnlyOwn        a release never removes another connection's    *)
(*                         reservation.                                    *)
(*   RejectedResubmittable a rejected submission leaves no reservation of  *)
(*                         its own behind.                                 *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [R8] dmq-node a267003c, DMQ/NodeToClient.hs 155-185: local            *)
(*        submission is LocalTxSubmission; a rejected message may be       *)
(*        submitted again.                                                 *)
(*   [G2] gOuroboros 7cd17437, protocol/localmessagesubmission/server.go,  *)
(*        as above.                                                        *)
(*   [G5] gOuroboros 7cd17437, protocol/common/authentication.go           *)
(*        ValidateMessageTTLAt, NewNoOpTTLValidator.                       *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `pc[c]` is a program counter.                                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Expiry,         \* the message's expiresAt, in whole seconds
    MaxTime,        \* the last second the model reaches
    TTLEnforced,    \* TRUE: the TTL validator is on; FALSE: NewNoOpTTLValidator
    TokenRelease,   \* TRUE: release checks the token (7cd17437); FALSE: a
                    \*   mutation that removes the id whoever holds it
    ReleaseOnReject \* TRUE: a rejection releases the id (7cd17437); FALSE: a
                    \*   mutation that keeps it

\* In English: "The two connections sharing the Config."
Conns == {1, 2}

VARIABLES
    t,              \* the clock, in whole seconds
    entry,          \* the cached reservation's token, 0 for none
    nextToken,      \* the last token handed out
    tok,            \* tok[c]: the token connection c holds, 0 for none
    at,             \* at[c]: the second connection c reserved at
    pc,             \* pc[c]: "idle", "callback", "accepted", "rejected" or
                    \*   "refused"
    tries,          \* tries[c]: submissions connection c has made
    acceptedValid,  \* acceptances made while the message was valid
    stolen          \* a release removed another connection's reservation

vars == <<t, entry, nextToken, tok, at, pc, tries, acceptedValid,
          stolen>>

Init ==
    /\ t = 0
    /\ entry = 0
    /\ nextToken = 0
    /\ tok = [c \in Conns |-> 0]
    /\ at = [c \in Conns |-> 0]
    /\ pc = [c \in Conns |-> "idle"]
    /\ tries = [c \in Conns |-> 0]
    /\ acceptedValid = 0
    /\ stolen = FALSE

\* In English: "The message passes the TTL check at second s [G5]."
Admissible(s) == ~TTLEnforced \/ s <= Expiry

\* In English: "A second passes."
Tick ==
    /\ t < MaxTime
    /\ t' = t + 1
    /\ UNCHANGED <<entry, nextToken, tok, at, pc, tries,
                   acceptedValid, stolen>>

\* In English: "Connection c submits (at most twice). Under the replay lock,
\* in one step: an expired entry is pruned; an id still reserved is refused;
\* otherwise the id is reserved under a fresh token and c runs
\* SubmitMessageFunc. A message the TTL check refuses never gets here."
Reserve(c) ==
    /\ pc[c] \in {"idle", "rejected"} /\ tries[c] < 2
    /\ Admissible(t)
    /\ tries' = [tries EXCEPT ![c] = @ + 1]
    /\ LET live == entry # 0 /\ ~(t > Expiry)       \* pruneExpired
       IN  IF live
              THEN /\ pc' = [pc EXCEPT ![c] = "refused"]
                   /\ UNCHANGED <<entry, nextToken, tok, at>>
              ELSE /\ nextToken' = nextToken + 1
                   /\ entry' = nextToken + 1
                   /\ tok' = [tok EXCEPT ![c] = nextToken + 1]
                   /\ at' = [at EXCEPT ![c] = t]
                   /\ pc' = [pc EXCEPT ![c] = "callback"]
    /\ UNCHANGED <<t, acceptedValid, stolen>>

\* In English: "SubmitMessageFunc accepts: the reservation stays."
Accept(c) ==
    /\ pc[c] = "callback"
    /\ pc' = [pc EXCEPT ![c] = "accepted"]
    /\ acceptedValid' = IF at[c] <= Expiry THEN acceptedValid + 1
                                            ELSE acceptedValid
    /\ UNCHANGED <<t, entry, nextToken, tok, at, tries, stolen>>

\* In English: "SubmitMessageFunc rejects: c releases the id, under the
\* lock, if the entry still carries its token (or, in the mutation, in any
\* case); then it may submit again."
Reject(c) ==
    /\ pc[c] = "callback"
    /\ pc' = [pc EXCEPT ![c] = "rejected"]
    /\ LET mine == entry = tok[c]
           drop == ReleaseOnReject /\ entry # 0 /\ (mine \/ ~TokenRelease)
       IN  /\ entry' = IF drop THEN 0 ELSE entry
           /\ stolen' = (stolen \/ (drop /\ ~mine))
    /\ UNCHANGED <<t, nextToken, tok, at, tries, acceptedValid>>

\* In English: "Nothing more can happen."
Finished ==
    /\ t = MaxTime
    /\ \A c \in Conns : pc[c] \in {"accepted", "refused"}
                        \/ (pc[c] \in {"idle", "rejected"}
                            /\ (tries[c] = 2 \/ ~Admissible(t)))

Next ==
    \/ Tick
    \/ \E c \in Conns : Reserve(c) \/ Accept(c) \/ Reject(c)
    \/ Finished /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
    /\ t \in 0..MaxTime
    /\ entry \in 0..4
    /\ pc \in [Conns -> {"idle", "callback", "accepted", "rejected", "refused"}]
    /\ tries \in [Conns -> 0..2]
    /\ acceptedValid \in 0..4
    /\ stolen \in BOOLEAN

\* In English: "While the message is valid it is accepted at most once."
AcceptedAtMostOnce == acceptedValid <= 1

\* In English: "No release has removed another connection's reservation."
ReleaseOnlyOwn == ~stolen

\* In English: "A connection whose submission was rejected holds no
\* reservation: the cache does not carry its token."
RejectedResubmittable ==
    \A c \in Conns : pc[c] = "rejected" => entry # tok[c]

\* Probe, EXPECTED to be violated: "No connection ever reserves the id after
\* another's reservation expired while that other is still in its callback."
ProbeReserveOverExpired ==
    ~(\E c, d \in Conns : c # d /\ pc[c] = "callback" /\ pc[d] = "callback")
=============================================================================
