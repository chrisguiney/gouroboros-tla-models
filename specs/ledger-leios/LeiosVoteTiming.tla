-------------------------- MODULE LeiosVoteTiming --------------------------
(***************************************************************************)
(* When a node keeps a Leios vote, when it forgets it, and how many        *)
(* announcements of one election it accepts.                               *)
(*                                                                         *)
(* Each election slot s has a vote deadline, the end of its diffusion      *)
(* period; here Deadline(s) = s + W. A vote arriving after its deadline is *)
(* dropped. A vote is kept only for an announcement the node accepted, and *)
(* the node accepts at most two announcements per election (the second is  *)
(* the equivocation proof; a third is refused). The node verifies a vote's *)
(* signature between two steps, so it may prune in between: pruning at     *)
(* time t forgets every election whose deadline is before t, and a vote   *)
(* whose deadline is before the last pruning is refused when it is        *)
(* recorded, so no vote of a seat in an election is ever recorded twice.   *)
(* The votes for an announcement are aggregated into its certificate when  *)
(* every seat has voted for it (the quorum here), and the certificate is   *)
(* kept until the immutable tip passes its election slot.                  *)
(*                                                                         *)
(* gOuroboros has none of this: votes, announcements and certificates are  *)
(* the caller's. The model states the caller's obligations.                *)
(*                                                                         *)
(* Sources (README.md has quotes):                                         *)
(*   [R1] ouroboros-consensus ec239d57f618, ouroboros-consensus/src/       *)
(*        ouroboros-consensus/Ouroboros/Consensus/Leios/VoteState.hs:      *)
(*        224-301 addVote (late, not announced, seen, then verify; record  *)
(*        in a later transaction), 348-399 recordVote (refuses a vote      *)
(*        whose deadline is before votesPrunedAt), 405-431 pruneVotes,     *)
(*        458-464 pruneCertificates (keeps those not before the immutable  *)
(*        tip's slot), 280-288 recordCertificate.                          *)
(*   [R2] the same, Leios/AnnounceState.hs 94-151: at most two             *)
(*        announcements per election, none of an election before the      *)
(*        immutable tip; MiniProtocol/LeiosNotify/Client/State.hs 432-446  *)
(*        leiosVoteWindow: the deadline is 3 L_hdr + L_vote + L_diff after *)
(*        the election slot began.                                         *)
(*   [C1] CIP-0164 at CIPs db48da14bff1, CIP-0164/README.md 1083-1092:     *)
(*        votes are relayed for a bounded time; at most one vote per       *)
(*        member per slot is forwarded.                                    *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Slots,     \* the election slots, natural numbers
    Seats,     \* the committee seats
    Hashes,    \* the announcing blocks an election may have
    VoteHashes, \* the announcing blocks votes are cast for (bounds the run)
    W,         \* time from an election slot to its vote deadline
    MaxTime,   \* the last instant explored
    MaxPending, \* the most votes being verified at once (bounds the run)
    Mutation   \* "none", or one deliberate break (see README)

VARIABLES
    now,        \* the current time
    announced,  \* per election slot, the announcements accepted
    pending,    \* votes received and being verified: <<slot, seat, hash, t>>
    votes,      \* the votes kept: <<slot, seat, hash, t>>, t when received
    prunedAt,   \* when the votes were last pruned
    immTip,     \* the immutable tip's slot
    records,    \* per <<slot, seat>>, how many times a vote was recorded
    certs,      \* the certificates kept: <<slot, hash>>
    formed,     \* every certificate ever formed: <<slot, hash>>
    outcomes    \* what happened to arriving votes so far (for probes)

\* In English: "All the variables, for stuttering steps."
\* Literally: "vars is defined as the tuple of now, announced, pending, votes,
\*   prunedAt, immTip, records, certs, formed and outcomes."
vars == <<now, announced, pending, votes, prunedAt, immTip, records, certs,
          formed, outcomes>>

\* In English: "The vote deadline of election slot s [R2]."
\* Literally: "Deadline of s is defined as s plus W."
Deadline(s) == s + W

\* In English: "Whether seat k already has a kept vote in election s."
\* Literally: "Seen of s and k is defined as: there exists a v in votes such
\*   that v[1] equals s and v[2] equals k."
Seen(s, k) == \E v \in votes : v[1] = s /\ v[2] = k

\* In English: "The most announcements of an election the node accepts.
\* The ThirdAnnouncement mutation accepts three."
\* Literally: "MaxAnnouncements is defined as: if Mutation equals
\*   "ThirdAnnouncement" then 3, else 2."
MaxAnnouncements == IF Mutation = "ThirdAnnouncement" THEN 3 ELSE 2

\* In English: "Nothing announced, voted or pruned at time 0."
\* Literally: "Init is defined as: now equals 0, and announced equals the
\*   function that maps every s in Slots to the empty set, and pending,
\*   votes, certs and formed equal the empty set, and prunedAt and immTip
\*   equal 0, and records equals the function that maps every p in the
\*   Cartesian product of Slots and Seats to 0, and outcomes equals the
\*   empty set."
Init ==
    /\ now = 0
    /\ announced = [s \in Slots |-> {}]
    /\ pending = {}
    /\ votes = {}
    /\ prunedAt = 0
    /\ immTip = 0
    /\ records = [p \in Slots \X Seats |-> 0]
    /\ certs = {}
    /\ formed = {}
    /\ outcomes = {}

\* In English: "Time passes."
\* Literally: "Tick is defined as: now is less than MaxTime, and now in the
\*   next state equals now plus 1, and every other variable is unchanged."
Tick ==
    /\ now < MaxTime
    /\ now' = now + 1
    /\ UNCHANGED <<announced, pending, votes, prunedAt, immTip, records,
                   certs, formed, outcomes>>

\* In English: "An announcement of election s arrives. The node accepts it
\* if the election is not before the immutable tip, it is new, and fewer
\* than the maximum are accepted already [R2]."
\* Literally: "Announce of s and h is defined as: s is greater than or equal
\*   to immTip, and h is not a member of announced of s, and the number of
\*   members of announced of s is less than MaxAnnouncements, and announced
\*   in the next state equals announced except that its s entry is the union
\*   of the old entry and the set containing h, and every other variable is
\*   unchanged."
Announce(s, h) ==
    /\ s >= immTip
    /\ h \notin announced[s]
    /\ Cardinality(announced[s]) < MaxAnnouncements
    /\ announced' = [announced EXCEPT ![s] = @ \cup {h}]
    /\ UNCHANGED <<now, pending, votes, prunedAt, records, immTip, certs,
                   formed, outcomes>>

\* In English: "Seat k's vote for announcement h of election s arrives. It
\* is dropped if it is past its deadline, if the node did not accept that
\* announcement, or if the seat already has a vote in the election;
\* otherwise its signature is being verified [R1 addVote]. The NoDeadline
\* and NoAnnounceCheck mutations skip a check."
\* Literally: "Arrive of s, k and h is defined as: the number of members of
\*   pending is less than MaxPending, and letting late be (now is
\*   greater than Deadline of s and Mutation does not equal "NoDeadline"),
\*   and unannounced be (h is not a member of announced of s and Mutation
\*   does not equal "NoAnnounceCheck"): if late then outcomes in the next
\*   state is the union of outcomes and the set containing "Late", else if
\*   unannounced then the same with "NotAnnounced", else if Seen of s and k
\*   then the same with "AlreadyKnown", else pending in the next state is
\*   the union of pending and the set containing the tuple of s, k, h and
\*   now; and every other variable is unchanged. Only while fewer than
\*   MaxPending votes are being verified."
Arrive(s, k, h) ==
    /\ Cardinality(pending) < MaxPending
    /\ LET late == now > Deadline(s) /\ Mutation # "NoDeadline"
        unannounced == h \notin announced[s] /\ Mutation # "NoAnnounceCheck"
       IN /\ IF late
             THEN /\ outcomes' = outcomes \cup {"Late"}
                  /\ UNCHANGED pending
             ELSE IF unannounced
             THEN /\ outcomes' = outcomes \cup {"NotAnnounced"}
                  /\ UNCHANGED pending
             ELSE IF Seen(s, k)
             THEN /\ outcomes' = outcomes \cup {"AlreadyKnown"}
                  /\ UNCHANGED pending
             ELSE /\ pending' = pending \cup {<<s, k, h, now>>}
                  /\ UNCHANGED outcomes
          /\ UNCHANGED <<now, announced, votes, prunedAt, immTip, records,
                         certs, formed>>

\* In English: "The verified vote p is recorded, unless the node pruned past
\* its deadline meanwhile or holds a vote of its seat in its election by
\* now [R1 recordVote]. Once every seat voted for its announcement, the
\* votes are aggregated into a certificate, if the election is not before
\* the last certificate pruning. The NoPrunedCheck mutation skips the
\* pruning check."
\* Literally: "Record of p is defined as: p is a member of pending, and
\*   pending in the next state is pending without the members of the set
\*   containing p, and letting s be p[1], k be p[2] and h be p[3]: if
\*   Deadline of s is less than prunedAt and Mutation does not equal
\*   "NoPrunedCheck", then outcomes in the next state is the union of
\*   outcomes and the set containing "PrunedMeanwhile" and votes, records,
\*   certs and formed are unchanged; else if Seen of s and k, then outcomes
\*   in the next state is the union of outcomes and the set containing
\*   "AlreadyKnown" and the same are unchanged; else votes in the next state
\*   is the union of votes and the set containing p, and records in the next
\*   state is records except that its <<s, k>> entry is the old entry plus 1,
\*   and, letting full be (for all j in Seats, j equals k or there exists a
\*   v in votes such that v[1] equals s and v[2] equals j and v[3] equals
\*   h): if full and s is greater than or equal to immTip and the tuple of s
\*   and h is not a member of certs, then certs and formed in the next state
\*   each gain the tuple of s and h, else they are unchanged; and outcomes is
\*   unchanged; and now, announced, prunedAt and immTip are unchanged."
Record(p) ==
    /\ p \in pending
    /\ pending' = pending \ {p}
    /\ LET s == p[1]
           k == p[2]
           h == p[3]
       IN IF Deadline(s) < prunedAt /\ Mutation # "NoPrunedCheck"
          THEN /\ outcomes' = outcomes \cup {"PrunedMeanwhile"}
               /\ UNCHANGED <<votes, records, certs, formed>>
          ELSE IF Seen(s, k)
          THEN /\ outcomes' = outcomes \cup {"AlreadyKnown"}
               /\ UNCHANGED <<votes, records, certs, formed>>
          ELSE LET full == \A j \in Seats :
                               j = k \/ \E v \in votes :
                                   v[1] = s /\ v[2] = j /\ v[3] = h
               IN /\ votes' = votes \cup {p}
                  /\ records' = [records EXCEPT ![<<s, k>>] = @ + 1]
                  /\ IF full /\ s >= immTip /\ <<s, h>> \notin certs
                     THEN /\ certs' = certs \cup {<<s, h>>}
                          /\ formed' = formed \cup {<<s, h>>}
                     ELSE UNCHANGED <<certs, formed>>
                  /\ UNCHANGED outcomes
    /\ UNCHANGED <<now, announced, prunedAt, immTip>>

\* In English: "The node prunes the votes now: it forgets every election
\* whose deadline is before now [R1 pruneVotes]. The PruneEarly mutation
\* also forgets the elections whose deadline is now."
\* Literally: "PruneVotes is defined as: now is greater than prunedAt, and
\*   prunedAt in the next state equals now, and votes in the next state is
\*   the set of every v in votes such that (if Mutation equals "PruneEarly"
\*   then now is less than Deadline of v[1], else now is less than or equal
\*   to Deadline of v[1]), and every other variable is unchanged."
PruneVotes ==
    /\ now > prunedAt
    /\ prunedAt' = now
    /\ votes' = {v \in votes :
                    IF Mutation = "PruneEarly" THEN now < Deadline(v[1])
                    ELSE now <= Deadline(v[1])}
    /\ UNCHANGED <<now, announced, pending, immTip, records, certs, formed,
                   outcomes>>

\* In English: "The immutable tip moves on one slot; the node forgets the
\* announcements and certificates of elections before it [R1
\* pruneCertificates][R2]. The PruneCertsEarly mutation also forgets those
\* of the tip's own slot."
\* Literally: "AdvanceImmutable is defined as: immTip is less than or equal
\*   to the largest member of Slots, and immTip in the next state equals
\*   immTip plus 1, and announced in the next state is the function that
\*   maps every s in Slots to (if s is less than immTip plus 1 then the
\*   empty set, else announced of s), and certs in the next state is the set
\*   of every c in certs such that (if Mutation equals "PruneCertsEarly"
\*   then c[1] is greater than immTip plus 1, else c[1] is greater than or
\*   equal to immTip plus 1), and every other variable is unchanged."
AdvanceImmutable ==
    /\ immTip <= CHOOSE m \in Slots : \A s \in Slots : s <= m
    /\ immTip' = immTip + 1
    /\ announced' = [s \in Slots |-> IF s < immTip + 1 THEN {} ELSE announced[s]]
    /\ certs' = {c \in certs :
                    IF Mutation = "PruneCertsEarly" THEN c[1] > immTip + 1
                    ELSE c[1] >= immTip + 1}
    /\ UNCHANGED <<now, pending, votes, prunedAt, records, formed, outcomes>>

\* In English: "Some step happens."
\* Literally: "Next is defined as: Tick, or there exists an s in Slots and h
\*   in Hashes such that Announce of s and h, or there exists an s in Slots,
\*   k in Seats and h in VoteHashes such that Arrive of s, k and h, or there
\*   exists a p in pending such that Record of p, or PruneVotes, or
\*   AdvanceImmutable."
Next ==
    \/ Tick
    \/ \E s \in Slots, h \in Hashes : Announce(s, h)
    \/ \E s \in Slots, k \in Seats, h \in VoteHashes : Arrive(s, k, h)
    \/ \E p \in pending : Record(p)
    \/ PruneVotes
    \/ AdvanceImmutable

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

\* In English: "Every variable has the expected shape."
\* Literally: "TypeOK is defined as: now is a member of 0 through MaxTime,
\*   and announced is a member of the set of functions from Slots to the set
\*   of subsets of Hashes, and records is a member of the set of functions
\*   from the Cartesian product of Slots and Seats to Nat."
TypeOK ==
    /\ now \in 0..MaxTime
    /\ announced \in [Slots -> SUBSET Hashes]
    /\ records \in [Slots \X Seats -> Nat]

\* In English: "At most two announcements per election [R2]."
\* Literally: "AtMostTwoAnnouncements is defined as: for all s in Slots, the
\*   number of members of announced of s is less than or equal to 2."
AtMostTwoAnnouncements == \A s \in Slots : Cardinality(announced[s]) <= 2

\* In English: "Every kept vote arrived by its deadline [R1][R2]."
\* Literally: "NoLateVote is defined as: for all v in votes, v[4] is less
\*   than or equal to Deadline of v[1]."
NoLateVote == \A v \in votes : v[4] <= Deadline(v[1])

\* In English: "Every kept vote is for an announcement the node accepted,
\* while that election's announcements are kept [R1 hasAnnouncement]."
\* Literally: "OnlyAnnouncedVotes is defined as: for all v in votes, v[3] is
\*   a member of announced of v[1], or v[1] is less than immTip."
OnlyAnnouncedVotes ==
    \A v \in votes : v[3] \in announced[v[1]] \/ v[1] < immTip

\* In English: "No vote of a seat in an election is recorded twice, even
\* after its election was pruned [R1; reference test prop_keepsUnexpired]."
\* Literally: "NeverRecordedTwice is defined as: for all p in the Cartesian
\*   product of Slots and Seats, records of p is less than or equal to 1."
NeverRecordedTwice == \A p \in Slots \X Seats : records[p] <= 1

\* In English: "The node still holds every recorded vote whose deadline
\* has not passed at the last pruning."
\* Literally: "KeepsUnexpired is defined as: for all p in the Cartesian
\*   product of Slots and Seats, if records of p is greater than 0 and
\*   prunedAt is less than or equal to Deadline of p[1], then there exists a
\*   v in votes such that v[1] equals p[1] and v[2] equals p[2]."
KeepsUnexpired ==
    \A p \in Slots \X Seats :
        records[p] > 0 /\ prunedAt <= Deadline(p[1]) =>
            \E v \in votes : v[1] = p[1] /\ v[2] = p[2]

\* In English: "A certificate is kept until the immutable tip passes its
\* election slot [R1 pruneCertificates]."
\* Literally: "CertsKeptUntilImmutable is defined as: for all c in formed,
\*   if c[1] is greater than or equal to immTip, then c is a member of
\*   certs."
CertsKeptUntilImmutable == \A c \in formed : c[1] >= immTip => c \in certs

\* In English: "Probe: no vote is dropped as late."
\* Literally: "ProbeNoLate is defined as: "Late" is not a member of outcomes."
ProbeNoLate == "Late" \notin outcomes

\* In English: "Probe: no verified vote is dropped because pruning passed
\* its deadline meanwhile."
\* Literally: "ProbeNoPrunedRace is defined as: "PrunedMeanwhile" is not a
\*   member of outcomes."
ProbeNoPrunedRace == "PrunedMeanwhile" \notin outcomes

\* In English: "Probe: no vote for an unaccepted announcement is dropped."
\* Literally: "ProbeNoUnannounced is defined as: "NotAnnounced" is not a
\*   member of outcomes."
ProbeNoUnannounced == "NotAnnounced" \notin outcomes

\* In English: "Probe: no election gets two announcements."
\* Literally: "ProbeNoSecondAnnouncement is defined as: for all s in Slots,
\*   the number of members of announced of s is less than 2."
ProbeNoSecondAnnouncement == \A s \in Slots : Cardinality(announced[s]) < 2

\* In English: "Probe: no certificate is formed."
\* Literally: "ProbeNoCert is defined as: formed equals the empty set."
ProbeNoCert == formed = {}

\* In English: "Probe: no certificate is ever forgotten."
\* Literally: "ProbeNoCertPruned is defined as: formed is a subset of
\*   certs."
ProbeNoCertPruned == formed \subseteq certs
=============================================================================
