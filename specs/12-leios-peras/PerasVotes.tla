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
(* 61046085 has neither. Branch fix/perasvotes-await-reply (f7ebba9b)      *)
(* adds both: its client moves to MustReply and asks again after           *)
(* MsgServerIdle; its server, with no vote, sends MsgAwaitReply, then the  *)
(* identifiers that arrive or MsgServerIdle, as the reference server does. *)
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
(*   [G2] gOuroboros f7ebba9b on fix/perasvotes-await-reply: StateMap's    *)
(*        ObjectIDsBlockingMustReply, client.go (Sync asks again after     *)
(*        MsgServerIdle), server.go (awaitObjectIDs).                      *)
(*                                                                         *)
(* After MsgDone the client may start a new run on the same connection    *)
(* (MaxRuns). The reference runs the outbound side (this server) as a      *)
(* responder [R3], and the inbound governor restarts a responder that      *)
(* ended cleanly [S5][R4]. gOuroboros main d8f5bc2a ignores MsgDone and    *)
(* stays in Done; branch fix/perasvotes-server-restart restarts it.        *)
(*   [S5] ouroboros-network 5f356486ab3e, docs/network-spec/               *)
(*        connection-manager.tex 492-496: "should be restarted in its      *)
(*        initial state".                                                  *)
(*   [R3] ouroboros-consensus ec239d57f618, ouroboros-consensus-diffusion/ *)
(*        .../Network/NodeToNode.hs 522-536: the vote diffusion client is  *)
(*        the inbound (initiator), the server the outbound (responder).    *)
(*   [R4] ouroboros-network 5f356486ab3e, .../InboundGovernor.hs 455-470:  *)
(*        TrResponderRestarted.                                            *)
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
    ReferenceServer,   \* TRUE: the server may send MsgAwaitReply and MsgServerIdle [R1]:
                       \* the reference server, or gOuroboros' with the fix [G2]
    ServerMayBeEmpty,  \* TRUE: at some request the server has no new vote yet
    ClientKnowsAwait,  \* FALSE today; TRUE: a client with the reference's MustReply
                       \* state, as gOuroboros' is with the fix [G2]
    MaxRuns,           \* how many runs the client may start on one connection
    ServerRestarts     \* TRUE: the server restarts after MsgDone [S5][R4]
                       \* FALSE: gOuroboros main d8f5bc2a, which stays in Done

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
    sfail,      \* the server failed the connection
    runs        \* client runs started so far on this connection

\* Literally: "vars is defined as the tuple of all eleven variables."
vars == <<pc, cst, sst, c2s, s2c, unacked, lastIds, rounds, cviol, sfail, runs>>

\* In English: "A message: its kind and a number (identifiers acknowledged,
\* requested, or carried)."
\* Literally: "M of k and n is defined as the record whose field k is k and
\*   whose field n is n."
M(k, n) == [k |-> k, n |-> n]

\* In English: "Both sides are in Init, nothing is in flight or unacknowledged,
\* no round has started, nothing has failed, and this is run 1."
\* Literally: "Init is defined as: pc equals "init" and cst equals "Init" and
\*   sst equals "Init", and c2s equals the empty sequence and s2c equals the
\*   empty sequence and unacked equals 0 and lastIds equals 0 and rounds equals
\*   0, and cviol equals FALSE and sfail equals FALSE and runs equals 1."
Init ==
    /\ pc = "init" /\ cst = "Init" /\ sst = "Init"
    /\ c2s = <<>> /\ s2c = <<>> /\ unacked = 0 /\ lastIds = 0 /\ rounds = 0
    /\ cviol = FALSE /\ sfail = FALSE /\ runs = 1

\* In English: "The client sends one message and moves its own state."
\* Literally: "ClientSend of m, next and newPc is defined as: c2s in the next
\*   state equals c2s with m appended, and cst in the next state equals next,
\*   and pc in the next state equals newPc."
ClientSend(m, next, newPc) ==
    /\ c2s' = Append(c2s, m) /\ cst' = next /\ pc' = newPc

\* --- The client's Sync loop [G1]. ----------------------------------------

\* In English: "The client sends MsgInit and moves to Idle, ready to ask for
\* identifiers."
\* Literally: "SendInit is defined as: pc equals "init", and ClientSend of M of
\*   "Init" and 0, "Idle", and "ids", and runs, sst, s2c, unacked, lastIds,
\*   rounds, cviol and sfail are unchanged."
SendInit ==
    /\ pc = "init"
    /\ ClientSend(M("Init", 0), "Idle", "ids")
    /\ UNCHANGED <<runs, sst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "Acknowledge the last round's identifiers, which leaves
\* none, so the request is blocking [R1], for up to the window."
\* Literally: "SendBlocking is defined as: pc equals "ids" and rounds is less
\*   than MaxRounds, and ClientSend of M of "ReqIdsBlocking" and lastIds,
\*   "Blocking", and "waitIds", and unacked in the next state equals unacked
\*   minus lastIds, and rounds in the next state equals rounds plus 1, and
\*   runs, sst, s2c, lastIds, cviol and sfail are unchanged."
SendBlocking ==
    /\ pc = "ids" /\ rounds < MaxRounds
    /\ ClientSend(M("ReqIdsBlocking", lastIds), "Blocking", "waitIds")
    /\ unacked' = unacked - lastIds
    /\ rounds' = rounds + 1
    /\ UNCHANGED <<runs, sst, s2c, lastIds, cviol, sfail>>

\* In English: "The client asks for the votes the last reply announced."
\* Literally: "SendObjects is defined as: pc equals "objs", and ClientSend of M
\*   of "ReqObjects" and lastIds, "Objects", and "waitObjs", and runs, sst,
\*   s2c, unacked, lastIds, rounds, cviol and sfail are unchanged."
SendObjects ==
    /\ pc = "objs"
    /\ ClientSend(M("ReqObjects", lastIds), "Objects", "waitObjs")
    /\ UNCHANGED <<runs, sst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "Done, from Idle, once the loop has stopped."
\* Literally: "SendDone is defined as: pc equals "ids" and rounds equals
\*   MaxRounds, and ClientSend of M of "Done" and 0, "Done", and "done", and
\*   runs, sst, s2c, unacked, lastIds, rounds, cviol and sfail are unchanged."
SendDone ==
    /\ pc = "ids" /\ rounds = MaxRounds
    /\ ClientSend(M("Done", 0), "Done", "done")
    /\ UNCHANGED <<runs, sst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "The client judges the oldest server message against its
\* state map [G1]. A client that knows MsgAwaitReply moves to MustReply and
\* treats MsgServerIdle as a cue to ask again."
\* Literally: "ClientRecv is defined as: s2c does not equal the empty sequence
\*   and cviol is not true, and, letting m be the head of s2c: in the case m's
\*   k equals "ReplyIds" and cst is a member of the set containing "Blocking"
\*   and "MustReply" and m's n is greater than or equal to 1, cst in the next
\*   state equals "Idle" and pc in the next state equals "objs", and unacked in
\*   the next state equals unacked plus m's n and lastIds in the next state
\*   equals m's n, and cviol is unchanged; in the case m's k equals
\*   "AwaitReply" and cst equals "Blocking" and ClientKnowsAwait is true, cst
\*   in the next state equals "MustReply", and runs, pc, unacked, lastIds and
\*   cviol are unchanged; in the case m's k equals "ServerIdle" and cst equals
\*   "MustReply" and ClientKnowsAwait is true, cst in the next state equals
\*   "Idle" and pc in the next state equals "ids" and lastIds in the next state
\*   equals 0, and runs, unacked and cviol are unchanged; in the case m's k
\*   equals "ReplyObjects" and cst equals "Objects", cst in the next state
\*   equals "Idle" and pc in the next state equals "ids", and runs, unacked,
\*   lastIds and cviol are unchanged; in every other case, cviol in the next
\*   state equals TRUE, and runs, cst, pc, unacked and lastIds are unchanged;
\*   and s2c in the next state equals the tail of s2c, and runs, sst, c2s,
\*   rounds and sfail are unchanged."
ClientRecv ==
    /\ s2c /= <<>> /\ ~cviol
    /\ LET m == Head(s2c) IN
       CASE m.k = "ReplyIds" /\ cst \in {"Blocking", "MustReply"} /\ m.n >= 1 ->
              /\ cst' = "Idle" /\ pc' = "objs"
              /\ unacked' = unacked + m.n /\ lastIds' = m.n
              /\ UNCHANGED cviol
         [] m.k = "AwaitReply" /\ cst = "Blocking" /\ ClientKnowsAwait ->
              /\ cst' = "MustReply"
              /\ UNCHANGED <<runs, pc, unacked, lastIds, cviol>>
         [] m.k = "ServerIdle" /\ cst = "MustReply" /\ ClientKnowsAwait ->
              /\ cst' = "Idle" /\ pc' = "ids" /\ lastIds' = 0
              /\ UNCHANGED <<runs, unacked, cviol>>
         [] m.k = "ReplyObjects" /\ cst = "Objects" ->
              /\ cst' = "Idle" /\ pc' = "ids"
              /\ UNCHANGED <<runs, unacked, lastIds, cviol>>
         [] OTHER ->
              /\ cviol' = TRUE
              /\ UNCHANGED <<runs, cst, pc, unacked, lastIds>>
    /\ s2c' = Tail(s2c)
    /\ UNCHANGED <<runs, sst, c2s, rounds, sfail>>

\* --- The server. ---------------------------------------------------------

\* In English: "The server reads the oldest client message and moves to
\* the state it names [R1]. A server that restarts also reads once its run
\* is over, as the first message of a new run [S5][R4]."
\* Literally: "ServerRead is defined as: c2s does not equal the empty sequence
\*   and sfail is not true, and (sst is a member of the set containing "Init"
\*   and "Idle", or sst equals "Done" and ServerRestarts is true), and, letting
\*   m be the head of c2s: sst in the next state equals: in the case m's k
\*   equals "Init", "Idle"; in the case m's k equals "ReqIdsBlocking",
\*   "Blocking"; in the case m's k equals "ReqObjects", "Objects"; in the case
\*   m's k equals "Done", "Done"; and c2s in the next state equals the tail of
\*   c2s, and runs, pc, cst, s2c, unacked, lastIds, rounds, cviol and sfail are
\*   unchanged."
ServerRead ==
    /\ c2s /= <<>> /\ ~sfail
    /\ \/ sst \in {"Init", "Idle"}
       \/ sst = "Done" /\ ServerRestarts
    /\ LET m == Head(c2s) IN
       sst' = CASE m.k = "Init"           -> "Idle"
                [] m.k = "ReqIdsBlocking" -> "Blocking"
                [] m.k = "ReqObjects"     -> "Objects"
                [] m.k = "Done"           -> "Done"
    /\ c2s' = Tail(c2s)
    /\ UNCHANGED <<runs, pc, cst, s2c, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "In a blocking request's state the server answers one to
\* the window's worth of identifiers, if it has any."
\* Literally: "ServerReplyIds of n is defined as: sst is a member of the set
\*   containing "Blocking" and "MustReply" and n is a member of 1 through
\*   Window, and s2c in the next state equals s2c with M of "ReplyIds" and n
\*   appended and sst in the next state equals "Idle", and runs, pc, cst, c2s,
\*   unacked, lastIds, rounds, cviol and sfail are unchanged."
ServerReplyIds(n) ==
    /\ sst \in {"Blocking", "MustReply"} /\ n \in 1..Window
    /\ s2c' = Append(s2c, M("ReplyIds", n)) /\ sst' = "Idle"
    /\ UNCHANGED <<runs, pc, cst, c2s, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "A server with no vote yet: the reference sends MsgAwaitReply
\* and later MsgServerIdle [R1]; gOuroboros' server fails the connection
\* when ObjectIDsFunc returns nothing [G1]."
\* Literally: "ServerNothing is defined as: ServerMayBeEmpty is true and sst
\*   equals "Blocking", and if ReferenceServer is true, then s2c in the next
\*   state equals s2c with M of "AwaitReply" and 0 appended and sst in the next
\*   state equals "MustReply", and sfail is unchanged; else sfail in the next
\*   state equals TRUE, and runs, s2c and sst are unchanged; and runs, pc, cst,
\*   c2s, unacked, lastIds, rounds and cviol are unchanged."
ServerNothing ==
    /\ ServerMayBeEmpty /\ sst = "Blocking"
    /\ IF ReferenceServer
       THEN s2c' = Append(s2c, M("AwaitReply", 0)) /\ sst' = "MustReply"
            /\ UNCHANGED sfail
       ELSE sfail' = TRUE /\ UNCHANGED <<runs, s2c, sst>>
    /\ UNCHANGED <<runs, pc, cst, c2s, unacked, lastIds, rounds, cviol>>

\* In English: "A reference server that has made the client wait sends
\* MsgServerIdle and returns agency."
\* Literally: "ServerIdle is defined as: ReferenceServer is true and
\*   ServerMayBeEmpty is true and sst equals "MustReply", and s2c in the next
\*   state equals s2c with M of "ServerIdle" and 0 appended and sst in the next
\*   state equals "Idle", and runs, pc, cst, c2s, unacked, lastIds, rounds,
\*   cviol and sfail are unchanged."
ServerIdle ==
    /\ ReferenceServer /\ ServerMayBeEmpty /\ sst = "MustReply"
    /\ s2c' = Append(s2c, M("ServerIdle", 0)) /\ sst' = "Idle"
    /\ UNCHANGED <<runs, pc, cst, c2s, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "The server answers a request for votes."
\* Literally: "ServerObjects is defined as: sst equals "Objects", and s2c in
\*   the next state equals s2c with M of "ReplyObjects" and 0 appended and sst
\*   in the next state equals "Idle", and runs, pc, cst, c2s, unacked, lastIds,
\*   rounds, cviol and sfail are unchanged."
ServerObjects ==
    /\ sst = "Objects"
    /\ s2c' = Append(s2c, M("ReplyObjects", 0)) /\ sst' = "Idle"
    /\ UNCHANGED <<runs, pc, cst, c2s, unacked, lastIds, rounds, cviol, sfail>>

\* In English: "Once its run is over, the client may start another on the
\* same connection, with a fresh window, up to MaxRuns."
\* Literally: "ClientRestart is defined as: pc equals "done" and runs is less
\*   than MaxRuns, and pc in the next state equals "init" and cst in the next
\*   state equals "Init", and unacked in the next state equals 0 and lastIds in
\*   the next state equals 0 and rounds in the next state equals 0, and runs in
\*   the next state equals runs plus 1, and sst, c2s, s2c, cviol and sfail are
\*   unchanged."
ClientRestart ==
    /\ pc = "done" /\ runs < MaxRuns
    /\ pc' = "init" /\ cst' = "Init"
    /\ unacked' = 0 /\ lastIds' = 0 /\ rounds' = 0
    /\ runs' = runs + 1
    /\ UNCHANGED <<sst, c2s, s2c, cviol, sfail>>

\* In English: "Over: every run done on both sides, or one hung up."
\* Literally: "Ended is defined as: (pc equals "done" and runs equals MaxRuns
\*   and sst equals "Done" and c2s equals the empty sequence), or cviol is
\*   true, or sfail is true."
Ended == (pc = "done" /\ runs = MaxRuns /\ sst = "Done" /\ c2s = <<>>)
         \/ cviol \/ sfail

\* In English: "A step is a client send, the client reading, a server step, a
\* client restart, or, once over, nothing."
\* Literally: "Next is defined as: SendInit, or SendBlocking, or SendObjects,
\*   or SendDone, or ClientRecv, or ServerRead, or there exists an n in 1
\*   through Window such that ServerReplyIds of n, or ServerNothing, or
\*   ServerIdle, or ServerObjects, or ClientRestart, or Ended is true and vars
\*   is unchanged."
Next ==
    \/ SendInit \/ SendBlocking \/ SendObjects \/ SendDone \/ ClientRecv
    \/ ServerRead \/ \E n \in 1..Window : ServerReplyIds(n)
    \/ ServerNothing \/ ServerIdle \/ ServerObjects \/ ClientRestart
    \/ Ended /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "The client never refused a server message."
\* Literally: "NoClientViolation is defined as: cviol is not true."
NoClientViolation == ~cviol

\* In English: "The server never failed the connection."
\* Literally: "NoServerFailure is defined as: sfail is not true."
NoServerFailure == ~sfail

\* In English: "Unacknowledged identifiers stay within the window [R1]."
\* Literally: "WindowBound is defined as: unacked is less than or equal to
\*   Window."
WindowBound == unacked <= Window

\* In English: "A message waiting for the server can be read: the server
\* is never left holding a client message it will not read." It fails when
\* a client starts a second run and the server stayed in Done.
\* Literally: "NewRunServed is defined as: if c2s does not equal the empty
\*   sequence and cviol is not true and sfail is not true, then ServerRead is
\*   enabled."
NewRunServed == (c2s /= <<>> /\ ~cviol /\ ~sfail) => ENABLED ServerRead

\* Probe, EXPECTED to be violated: "The client never starts a second run."
\* Literally: "ProbeNoSecondRun is defined as: runs equals 1."
ProbeNoSecondRun == runs = 1

\* Probe, EXPECTED to be violated: "No Sync round ever completes."
\* Literally: "ProbeNoRound is defined as: it is not the case that (rounds is
\*   greater than or equal to 1 and pc equals "ids")."
ProbeNoRound == ~(rounds >= 1 /\ pc = "ids")

\* Probe, EXPECTED to be violated under the fix: "The client never gets
\* agency back through MsgServerIdle." After MsgServerIdle the client is
\* ready for its next request with no identifiers from the last one, which
\* no completed round leaves (a reply carries at least one).
\* Literally: "ProbeNoIdle is defined as: it is not the case that (rounds is
\*   greater than or equal to 1, and pc equals "ids", and lastIds equals 0)."
ProbeNoIdle == ~(rounds >= 1 /\ pc = "ids" /\ lastIds = 0)
=============================================================================
