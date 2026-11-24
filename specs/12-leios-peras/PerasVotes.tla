------------------------------ MODULE PerasVotes ------------------------------
(***************************************************************************)
(* Model 12, PerasVotes: Peras vote diffusion over the ObjectDiffusion     *)
(* mini-protocol, the gOuroboros client's Sync loop, and a server that is  *)
(* either gOuroboros' or the reference's.                                  *)
(*                                                                         *)
(* The pinned network specification lists NodeToNodeV_17 as "support      *)
(* Peras mini-protocols" and nothing more. The reference is ObjectDiffusion*)
(* in ouroboros-network at the same commit; CIP-0140 only asks for a vote  *)
(* diffusion protocol. README.md says how authoritative each is.           *)
(*                                                                         *)
(* The gOuroboros client (protocol/perasvotes/client.go) Sync loop:        *)
(* acknowledge every identifier of the last round and make a blocking      *)
(* request for up to the window, request every identifier it got, hand    *)
(* the votes to VoteFunc, repeat. Done sends MsgDone from Idle. The        *)
(* gOuroboros server (server.go) answers a blocking request with whatever *)
(* ObjectIDsFunc returns, and fails the connection if that is empty.       *)
(*                                                                         *)
(* The reference added two messages on 2026-11-11: in a blocking request's *)
(* state the server may send MsgAwaitReply (no identifiers now), and must  *)
(* then send identifiers or MsgServerIdle, which returns agency. gOuroboros*)
(* has neither.                                                            *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoClientViolation  does the client refuse a message the reference    *)
(*                      server may send?                                   *)
(*   NoServerFailure    does the server fail the connection because it has *)
(*                      no vote to offer yet?                              *)
(*   WindowBound        do unacknowledged identifiers stay within the      *)
(*                      window?                                            *)
(*   Deadlock           TLC checks it.                                     *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [R1] ouroboros-network 5f356486ab3e, .../ObjectDiffusion/Type.hs      *)
(*        263-393: Init(client) -MsgInit-> Idle(client); Idle              *)
(*        -MsgRequestObjectIds-> ObjectIds blocking or non-blocking;       *)
(*        a blocking request only with nothing left unacknowledged, its    *)
(*        reply non-empty; MsgAwaitReply CanAwait -> MustReply;            *)
(*        MsgServerIdle MustReply -> Idle; MsgRequestObjects -> Objects    *)
(*        -MsgReplyObjects-> Idle; MsgDone from Idle.                      *)
(*   [R2] .../ObjectDiffusion/Codec.hs 60-92: CanAwait and the other       *)
(*        reply states wait shortWait (10 s), MustReply longWait (60 s).   *)
(*   [G1] gOuroboros 61046085, protocol/perasvotes/perasvotes.go           *)
(*        (StateMap, match functions), client.go (Sync, Done),             *)
(*        server.go (handleRequestObjectIDs).                              *)
(*                                                                         *)
(* Not modelled: non-blocking requests (the Sync loop sends none), vote    *)
(* content, timeouts.                                                      *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Window,            \* MaxObjectsUnacknowledged
    MaxRounds,         \* rounds of the Sync loop (keeps it finite)
    ReferenceServer,   \* TRUE: the server may send MsgAwaitReply and MsgServerIdle [R1]
    ServerMayBeEmpty,  \* TRUE: at some request the server has no new vote yet
    ClientKnowsAwait   \* FALSE today; TRUE: a client with the reference's MustReply state

VARIABLES
    pc,         \* the client: "init", "ids", "waitIds", "objs", "waitObjs", "done"
    cst,        \* the client's protocol state
    sst,        \* the server's protocol state
    c2s,        \* client messages in flight
    s2c,        \* server messages in flight
    unacked,    \* identifiers the server has announced and the client not acknowledged
    lastIds,    \* identifiers the last reply carried
    rounds,     \* Sync rounds started
    cviol,      \* the client refused a server message
    sfail       \* the server failed the connection

vars == <<pc, cst, sst, c2s, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "A message: its kind and a number (identifiers acknowledged,
\* requested, or carried)."
M(k, n) == [k |-> k, n |-> n]

Init ==
    /\ pc = "init" /\ cst = "Init" /\ sst = "Init"
    /\ c2s = <<>> /\ s2c = <<>> /\ unacked = 0 /\ lastIds = 0 /\ rounds = 0
    /\ cviol = FALSE /\ sfail = FALSE

\* In English: "The client sends one message and moves its own state."
ClientSend(m, next, newPc) ==
    /\ c2s' = Append(c2s, m) /\ cst' = next /\ pc' = newPc

\* --- The client's Sync loop [G1]. ----------------------------------------

SendInit ==
    /\ pc = "init"
    /\ ClientSend(M("Init", 0), "Idle", "ids")
    /\ UNCHANGED <<sst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "Acknowledge the last round's identifiers, which leaves
\* none, so the request is blocking [R1], for up to the window."
SendBlocking ==
    /\ pc = "ids" /\ rounds < MaxRounds
    /\ ClientSend(M("ReqIdsBlocking", lastIds), "Blocking", "waitIds")
    /\ unacked' = unacked - lastIds
    /\ rounds' = rounds + 1
    /\ UNCHANGED <<sst, s2c, lastIds, cviol, sfail>>

SendObjects ==
    /\ pc = "objs"
    /\ ClientSend(M("ReqObjects", lastIds), "Objects", "waitObjs")
    /\ UNCHANGED <<sst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "Done, from Idle, once the loop has stopped."
SendDone ==
    /\ pc = "ids" /\ rounds = MaxRounds
    /\ ClientSend(M("Done", 0), "Done", "done")
    /\ UNCHANGED <<sst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "The client judges the oldest server message against its
\* state map [G1]. A client that knows MsgAwaitReply moves to MustReply and
\* treats MsgServerIdle as a cue to ask again."
ClientRecv ==
    /\ s2c /= <<>> /\ ~cviol
    /\ LET m == Head(s2c) IN
       CASE m.k = "ReplyIds" /\ cst \in {"Blocking", "MustReply"} /\ m.n >= 1 ->
              /\ cst' = "Idle" /\ pc' = "objs"
              /\ unacked' = unacked + m.n /\ lastIds' = m.n
              /\ UNCHANGED cviol
         [] m.k = "AwaitReply" /\ cst = "Blocking" /\ ClientKnowsAwait ->
              /\ cst' = "MustReply"
              /\ UNCHANGED <<pc, unacked, lastIds, cviol>>
         [] m.k = "ServerIdle" /\ cst = "MustReply" /\ ClientKnowsAwait ->
              /\ cst' = "Idle" /\ pc' = "ids" /\ lastIds' = 0
              /\ UNCHANGED <<unacked, cviol>>
         [] m.k = "ReplyObjects" /\ cst = "Objects" ->
              /\ cst' = "Idle" /\ pc' = "ids"
              /\ UNCHANGED <<unacked, lastIds, cviol>>
         [] OTHER ->
              /\ cviol' = TRUE
              /\ UNCHANGED <<cst, pc, unacked, lastIds>>
    /\ s2c' = Tail(s2c)
    /\ UNCHANGED <<sst, c2s, rounds, sfail>>

\* --- The server. ---------------------------------------------------------

\* In English: "The server reads the oldest client message and moves to
\* the state it names [R1]."
ServerRead ==
    /\ c2s /= <<>> /\ sst \in {"Init", "Idle"} /\ ~sfail
    /\ LET m == Head(c2s) IN
       sst' = CASE m.k = "Init"           -> "Idle"
                [] m.k = "ReqIdsBlocking" -> "Blocking"
                [] m.k = "ReqObjects"     -> "Objects"
                [] m.k = "Done"           -> "Done"
    /\ c2s' = Tail(c2s)
    /\ UNCHANGED <<pc, cst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "In a blocking request's state the server answers one to
\* the window's worth of identifiers, if it has any."
ServerReplyIds(n) ==
    /\ sst \in {"Blocking", "MustReply"} /\ n \in 1..Window
    /\ s2c' = Append(s2c, M("ReplyIds", n)) /\ sst' = "Idle"
    /\ UNCHANGED <<pc, cst, c2s, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "A server with no vote yet: the reference sends MsgAwaitReply
\* and later MsgServerIdle [R1]; gOuroboros' server fails the connection
\* when ObjectIDsFunc returns nothing [G1]."
ServerNothing ==
    /\ ServerMayBeEmpty /\ sst = "Blocking"
    /\ IF ReferenceServer
       THEN s2c' = Append(s2c, M("AwaitReply", 0)) /\ sst' = "MustReply"
            /\ UNCHANGED sfail
       ELSE sfail' = TRUE /\ UNCHANGED <<s2c, sst>>
    /\ UNCHANGED <<pc, cst, c2s, unacked, lastIds, rounds, cviol>>

ServerIdle ==
    /\ ReferenceServer /\ ServerMayBeEmpty /\ sst = "MustReply"
    /\ s2c' = Append(s2c, M("ServerIdle", 0)) /\ sst' = "Idle"
    /\ UNCHANGED <<pc, cst, c2s, unacked, lastIds, rounds, cviol, sfail>>

ServerObjects ==
    /\ sst = "Objects"
    /\ s2c' = Append(s2c, M("ReplyObjects", 0)) /\ sst' = "Idle"
    /\ UNCHANGED <<pc, cst, c2s, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "Over: both sides done, or one hung up."
Ended == (pc = "done" /\ sst = "Done") \/ cviol \/ sfail

Next ==
    \/ SendInit \/ SendBlocking \/ SendObjects \/ SendDone \/ ClientRecv
    \/ ServerRead \/ \E n \in 1..Window : ServerReplyIds(n)
    \/ ServerNothing \/ ServerIdle \/ ServerObjects
    \/ Ended /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "The client never refused a server message."
NoClientViolation == ~cviol

\* In English: "The server never failed the connection."
NoServerFailure == ~sfail

\* In English: "Unacknowledged identifiers stay within the window [R1]."
WindowBound == unacked <= Window

\* Probe, EXPECTED to be violated: "No Sync round ever completes."
ProbeNoRound == ~(rounds >= 1 /\ pc = "ids")
=============================================================================
