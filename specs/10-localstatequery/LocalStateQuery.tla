-------------------------- MODULE LocalStateQuery --------------------------
(***************************************************************************)
(* The local-state-query mini-protocol (node-to-client protocol 7): states,*)
(* agency, the three acquire targets, re-acquiring, failures, and runs     *)
(* that end with MsgDone and restart on the same connection.               *)
(*                                                                         *)
(* A client asks the node to "acquire" a ledger state (a snapshot at a     *)
(* point, the volatile tip, or the immutable tip), sends queries against   *)
(* it, then releases it or moves to another one (MsgReAcquire).            *)
(*                                                                         *)
(* Every rule follows the specification; where it is silent, the model     *)
(* follows the reference implementation and says so.                      *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e;            *)
(* specs/10-localstatequery/README.md has links.                           *)
(*   Specification (docs/network-spec/miniprotocols.tex):                  *)
(*   [S1] 27-36: one side has agency at a time; an unexpected message      *)
(*        aborts the connection.                                           *)
(*   [S2] 1915-1948: the state machine figure and the agency table.        *)
(*   [S3] 1950-2008: the messages; Target is ImmutableTip, VolatileTip or  *)
(*        SpecificPoint; "failure to re-acquire is equivalent to           *)
(*        MsgRelease"; the transition table.                               *)
(*   Reference implementation                                              *)
(*   (ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/          *)
(*   LocalStateQuery/):                                                    *)
(*   [R1] Type.hs 44-70, 139-200: states, messages, agency; StDone is      *)
(*        NobodyAgency.                                                    *)
(*   [R2] Type.hs 114-130: VolatileTip and ImmutableTip "cannot fail to be *)
(*        acquired"; only a SpecificPoint can fail.                        *)
(*   [R3] Codec.hs 80-191: the wire keys 0-11, decoded against the         *)
(*        reader's state; any other key in an active state fails.          *)
(*   [R4] InboundGovernor.hs 440-476 and Diffusion.hs 402-419: the         *)
(*        node-to-client server runs under the inbound governor, which     *)
(*        restarts a responder that terminated cleanly.                    *)
(*                                                                         *)
(* The gOuroboros code it is compared with is                              *)
(* protocol/localstatequery/localstatequery.go (StateMap), server.go       *)
(* (handleDone), and the receive checks in protocol/protocol.go.           *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxAcquires,    \* how many MsgAcquire/MsgReAcquire a run may send (keeps it finite)
    MaxQueries,     \* how many MsgQuery a run may send
    MaxRuns,        \* how many runs the client may start on one connection
    ServerRestarts, \* TRUE: the server restarts after MsgDone [R4]. FALSE: gOuroboros
                    \* today, which leaves the next run's messages unread
    FailureToIdle   \* TRUE: MsgFailure moves to StIdle [S3]. FALSE: a mutation
                    \* where the client keeps its old state after a failed re-acquire

Roles   == {"Client", "Server"}
States  == {"StIdle", "StAcquiring", "StAcquired", "StQuerying", "StDone"}
Targets == {"SpecificPoint", "VolatileTip", "ImmutableTip"}   \* [S3]
None    == "none"

\* In English: "A message is a type and, for MsgAcquire and MsgReAcquire, a
\* target; other messages carry None."
Msg(t, tg) == [type |-> t, target |-> tg]

\* In English: "Who may send in each state." [S2] agency table; [R1] for
\* StDone.
Agency(s) == CASE s = "StIdle"      -> "Client"
             []   s = "StAcquiring" -> "Server"
             []   s = "StAcquired"  -> "Client"
             []   s = "StQuerying"  -> "Server"
             []   s = "StDone"      -> "Nobody"

\* The transition table [S3] (lines 1999-2008), [R1] (Type.hs 139-193), as
\* <<from-state, message type, to-state>>. In English:
\*   "In StIdle, MsgAcquire moves to StAcquiring and MsgDone to StDone.
\*    In StAcquiring, MsgAcquired moves to StAcquired, MsgFailure to StIdle.
\*    In StAcquired, MsgQuery moves to StQuerying, MsgReAcquire to
\*    StAcquiring, MsgRelease to StIdle.
\*    In StQuerying, MsgResult moves back to StAcquired."
Transitions ==
    { <<"StIdle",      "MsgAcquire",   "StAcquiring">>,
      <<"StIdle",      "MsgDone",      "StDone">>,
      <<"StAcquiring", "MsgAcquired",  "StAcquired">>,
      <<"StAcquiring", "MsgFailure",   "StIdle">>,
      <<"StAcquired",  "MsgQuery",     "StQuerying">>,
      <<"StAcquired",  "MsgReAcquire", "StAcquiring">>,
      <<"StAcquired",  "MsgRelease",   "StIdle">>,
      <<"StQuerying",  "MsgResult",    "StAcquired">> }

\* In English: "Message type t is legal in state s if a row starts with s, t."
IsLegal(s, t) == \E tr \in Transitions : tr[1] = s /\ tr[2] = t

\* In English: "The state that sending t in s moves to."
After(s, t) == (CHOOSE tr \in Transitions : tr[1] = s /\ tr[2] = t)[3]

Peer(r) == IF r = "Client" THEN "Server" ELSE "Client"

\* In English: "Side r is waiting for its peer in state s."
Awaiting(r, s) == s /= "StDone" /\ Agency(s) = Peer(r)

\* In English: "What side r does with message m in state s: an illegal
\* message aborts the connection [S1][R3]; otherwise follow the table. With
\* the FailureToIdle mutation off, a client that re-acquired (wasReAcquire)
\* treats MsgFailure as keeping its old state."
Judge(r, s, m, wasReAcquire) ==
    IF ~IsLegal(s, m.type) THEN "Violation"                 \* not legal here: hang up
    ELSE IF r = "Client" /\ m.type = "MsgFailure" /\ wasReAcquire /\ ~FailureToIdle
         THEN "StAcquired"                                  \* the mutation
    ELSE After(s, m.type)                                   \* otherwise: next state

\* In English: "A server whose run ended starts a new one in StIdle [R4]."
RunState(s) == IF s = "StDone" THEN "StIdle" ELSE s

(***************************************************************************)
(* THE RECEIVE TABLE, printed by LocalStateQueryTable.tla. Kinds are the   *)
(* twelve wire keys of [R3]; three keys each for MsgAcquire and            *)
(* MsgReAcquire, one per target.                                           *)
(*   "Waits": r holds agency, so it does not read yet.                     *)
(*   "Held":  the client's run is over; nothing reads it until a new run.  *)
(***************************************************************************)
Kinds == {"MsgAcquire", "MsgAcquired", "MsgFailure", "MsgQuery", "MsgResult",
          "MsgRelease", "MsgReAcquire", "MsgDone", "MsgAcquireVolatileTip",
          "MsgReAcquireVolatileTip", "MsgAcquireImmutableTip",
          "MsgReAcquireImmutableTip"}

\* In English: "The protocol message each wire kind stands for." [R3]
KindMsg(k) ==
    CASE k = "MsgAcquire"               -> Msg("MsgAcquire", "SpecificPoint")
    []   k = "MsgAcquireVolatileTip"    -> Msg("MsgAcquire", "VolatileTip")
    []   k = "MsgAcquireImmutableTip"   -> Msg("MsgAcquire", "ImmutableTip")
    []   k = "MsgReAcquire"             -> Msg("MsgReAcquire", "SpecificPoint")
    []   k = "MsgReAcquireVolatileTip"  -> Msg("MsgReAcquire", "VolatileTip")
    []   k = "MsgReAcquireImmutableTip" -> Msg("MsgReAcquire", "ImmutableTip")
    []   OTHER                          -> Msg(k, None)

\* In English: "If the run is over, a restarting server judges the message
\* as the first of a new run; a client, or a server that does not restart
\* (gOuroboros today), leaves it Held. If r holds agency, the message
\* Waits. Otherwise judge it."
ReceiveTable(r, s, k) ==
    IF s = "StDone"
        THEN IF r = "Server" /\ ServerRestarts
                 THEN Judge(r, "StIdle", KindMsg(k), FALSE)
                 ELSE "Held"
    ELSE IF Agency(s) = r THEN "Waits"
    ELSE Judge(r, s, KindMsg(k), FALSE)

-----------------------------------------------------------------------------

VARIABLES
    view,       \* view[r]: the state side r believes the protocol is in
    inbox,      \* inbox[r]: messages sent to r that r has not read yet
    target,     \* the target of the last MsgAcquire/MsgReAcquire the server read
    reacq,      \* TRUE while the client waits on a MsgReAcquire (not MsgAcquire)
    acquires,   \* MsgAcquire/MsgReAcquire sent in this run
    queries,    \* MsgQuery sent in this run
    runs,       \* client runs started on this connection
    seen        \* ghost: the transitions taken so far, for the reachability probes

vars == <<view, inbox, target, reacq, acquires, queries, runs, seen>>

\* In English: "Both sides start in StIdle with nothing in flight." [S2]
Init ==
    /\ view = [r \in Roles |-> "StIdle"]
    /\ inbox = [r \in Roles |-> <<>>]
    /\ target = None
    /\ reacq = FALSE
    /\ acquires = 0 /\ queries = 0
    /\ runs = 1
    /\ seen = {}

\* In English: "The connection is over when someone hung up, or both are
\* done and no more runs may start."
Ended ==
    \/ \E r \in Roles : view[r] = "Violation"
    \/ /\ \A r \in Roles : view[r] = "StDone"
       /\ runs = MaxRuns

\* In English: "Side r, holding agency in its state, sends m: it moves to
\* the state the table gives, and m goes into its peer's inbox."
Send(r, m) ==
    /\ view[r] /= "Violation"
    /\ Agency(view[r]) = r                                  \* r may send [S1]
    /\ IsLegal(view[r], m.type)                             \* an honest sender sends only legal messages
    /\ view' = [view EXCEPT ![r] = After(view[r], m.type)]  \* next, r believes the new state
    /\ inbox' = [inbox EXCEPT ![Peer(r)] = Append(@, m)]    \* next, m is in the peer's inbox
    /\ seen' = seen \cup {m.type}

\* --- The client: any program the reference client type allows [R1]. ----

\* In English: "In StIdle the client may acquire any target, while it has
\* acquires left." Remembers that this is not a re-acquire.
ClientAcquire(tg) ==
    /\ acquires < MaxAcquires
    /\ Send("Client", Msg("MsgAcquire", tg))
    /\ acquires' = acquires + 1 /\ reacq' = FALSE
    /\ UNCHANGED <<target, queries, runs>>

\* In English: "In StAcquired the client may move to another target."
ClientReAcquire(tg) ==
    /\ acquires < MaxAcquires
    /\ Send("Client", Msg("MsgReAcquire", tg))
    /\ acquires' = acquires + 1 /\ reacq' = TRUE
    /\ UNCHANGED <<target, queries, runs>>

\* In English: "In StAcquired the client may query, while it has queries left."
ClientQuery ==
    /\ queries < MaxQueries
    /\ Send("Client", Msg("MsgQuery", None))
    /\ queries' = queries + 1
    /\ UNCHANGED <<target, reacq, acquires, runs>>

\* In English: "In StAcquired the client may release; in StIdle it may end
\* the run."
ClientRelease ==
    /\ Send("Client", Msg("MsgRelease", None))
    /\ UNCHANGED <<target, reacq, acquires, queries, runs>>

ClientDone ==
    /\ Send("Client", Msg("MsgDone", None))
    /\ UNCHANGED <<target, reacq, acquires, queries, runs>>

\* --- The server. --------------------------------------------------------

\* In English: "In StAcquiring the server confirms; or, for a SpecificPoint
\* only, reports a failure (point too old or not on chain) [R2]."
ServerAcquired ==
    /\ Send("Server", Msg("MsgAcquired", None))
    /\ UNCHANGED <<target, reacq, acquires, queries, runs>>

ServerFailure ==
    /\ target = "SpecificPoint"                             \* only a point can fail [R2]
    /\ Send("Server", Msg("MsgFailure", None))
    /\ UNCHANGED <<target, reacq, acquires, queries, runs>>

\* In English: "In StQuerying the server answers."
ServerResult ==
    /\ Send("Server", Msg("MsgResult", None))
    /\ UNCHANGED <<target, reacq, acquires, queries, runs>>

\* --- Reading. -----------------------------------------------------------

\* In English: "Side r reads the oldest message in its inbox when it is
\* waiting for its peer, or when it is a restarting server whose run is
\* over. A server that does not restart never reads again, so a new run's
\* first message waits forever: TLC reports that as a deadlock. It judges the message and moves to the result. The server
\* remembers an acquire's target."
Recv(r) ==
    /\ inbox[r] /= <<>>
    /\ \/ Awaiting(r, view[r])
       \/ r = "Server" /\ view[r] = "StDone" /\ ServerRestarts
    /\ LET m == Head(inbox[r]) IN
         /\ view' = [view EXCEPT ![r] = Judge(r, RunState(view[r]), m, reacq)]
         /\ target' = IF r = "Server" /\ m.type \in {"MsgAcquire", "MsgReAcquire"}
                          THEN m.target ELSE target
         /\ seen' = seen \cup
                IF r = "Client" /\ m.type = "MsgFailure" /\ reacq
                    THEN {"FailedReAcquire"} ELSE {}
    /\ inbox' = [inbox EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<reacq, acquires, queries, runs>>

\* In English: "When the client's run is over and it may start another, it
\* starts in StIdle with fresh allowances."
ClientRestart ==
    /\ view["Client"] = "StDone"
    /\ runs < MaxRuns
    /\ view' = [view EXCEPT !["Client"] = "StIdle"]
    /\ runs' = runs + 1
    /\ acquires' = 0 /\ queries' = 0
    /\ seen' = seen \cup {"Restart"}
    /\ UNCHANGED <<inbox, target, reacq>>

Next ==
    \/ \E tg \in Targets : ClientAcquire(tg) \/ ClientReAcquire(tg)
    \/ ClientQuery \/ ClientRelease \/ ClientDone
    \/ ServerAcquired \/ ServerFailure \/ ServerResult
    \/ \E r \in Roles : Recv(r)
    \/ ClientRestart
    \/ Ended /\ UNCHANGED vars                               \* the terminal stutter

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "No side ever receives a message its state does not allow."
NoViolations == \A r \in Roles : view[r] /= "Violation"

\* In English: "The two sides never both believe they may send." [S1]
NeverBothHaveAgency ==
    ~(Agency(view["Client"]) = "Client" /\ Agency(view["Server"]) = "Server")

\* In English: "When nothing is in flight, both sides agree on the state.
\* (A restarting server's StDone counts as StIdle.)"
ViewsAgreeWhenQuiet ==
    (\A r \in Roles : inbox[r] = <<>> /\ view[r] /= "Violation") =>
        \/ view["Client"] = view["Server"]
        \/ ServerRestarts /\ view["Server"] = "StDone" /\ view["Client"] = "StIdle"

\* In English: "Whenever the server is answering a query, the client is in
\* StQuerying or the answer is on its way: queries happen only on an
\* acquired state."
QueriesOnlyWhenAcquired ==
    view["Server"] = "StQuerying" =>
        view["Client"] \in {"StQuerying", "Violation"}

\* Reachability probes, EXPECTED to be violated (each shows a path exists).
ProbeNoFailedReAcquire == "FailedReAcquire" \notin seen
ProbeNoQuery            == "MsgQuery" \notin seen
ProbeNoSecondRun        == "Restart" \notin seen
ProbeNoImmutable        == target /= "ImmutableTip"
=============================================================================
