---------------------------- MODULE LimitsTables ----------------------------
(***************************************************************************)
(* Model `limits-timeouts`: the per-state tables of six mini-protocol      *)
(* sides, as gOuroboros 7cd17437 builds them and as the reference sets     *)
(* them. StateLimits.tla runs one side against an abstract peer.           *)
(*                                                                         *)
(* A side is one role of one protocol: its effective state map is what     *)
(* that role's constructor installs (a copy of StateMap with its own       *)
(* timeouts and byte limits). Agency is from that side's view: "local"     *)
(* when it holds agency, "peer" when it waits, "none" in Done.             *)
(*                                                                         *)
(* Encoding:                                                               *)
(*   GoTimeout   seconds the engine arms when it times the state; 0 = no  *)
(*               timer.                                                    *)
(*   RefTimeout  the reference's limit for the side that waits: seconds,  *)
(*               0 = waitForever, -1 = no reference for this state.        *)
(*   GoLimit     the state's PendingMessageByteLimit; 0 = none.            *)
(*   RefLimit    the reference's byte limit; -1 = none or no reference.    *)
(*                                                                         *)
(* Sources (README has links and line numbers):                            *)
(*   [R1] ouroboros-consensus ec239d57f618 MiniProtocol/LeiosFetch/Type.hs *)
(*        byteLimitsLeiosFetch, timeLimitsLeiosFetch; Leios/Types.hs        *)
(*        maxEndorserBlockBytesSize = 600 * 1000.                          *)
(*   [R2] same commit, MiniProtocol/LeiosNotify/Type.hs                    *)
(*        maxLeiosNotifyReplyBytes, byteLimitsLeiosNotify,                 *)
(*        timeLimitsLeiosNotify.                                           *)
(*   [R3] ouroboros-network 5f356486ab3e ObjectDiffusion/Codec.hs          *)
(*        timeLimitsObjectDiffusion; ouroboros-network d5fc44653f8b (the   *)
(*        release ouroboros-consensus 136122cc builds against)            *)
(*        byteLimitsObjectDiffusion; api/.../Protocol/Limits.hs:          *)
(*        smallByteLimit 65535, largeByteLimit 2500000, shortWait 10,     *)
(*        longWait 60.                                                    *)
(*   [R4] dmq-node 67a1a1e5a579 DMQ/Protocol/SigSubmission/Codec.hs        *)
(*        timeLimitsSigSubmission (V1) and SigSubmissionV2/Codec.hs        *)
(*        timeLimitsSigSubmissionV2 (V2, blocking `Just 20`).              *)
(*   [C1] CIP-0164 (LeiosVotes): no limits or timeouts. UNSOURCED for      *)
(*        LeiosVotes and for LeiosFetch Votes and BlockRange, which are    *)
(*        gOuroboros additions: RefTimeout and RefLimit are -1.           *)
(*   [G]  gOuroboros 7cd17437: protocol/leiosfetch/leiosfetch.go,          *)
(*        client.go NewClient; protocol/leiosnotify/leiosnotify.go         *)
(*        protocolConfig; protocol/leiosvotes/client.go clientStateMap;    *)
(*        protocol/perasvotes/client.go clientStateMap (the server uses   *)
(*        it too); protocol/messagesubmission/messagesubmission.go         *)
(*        stateMapV1, stateMapV2, client.go NewClient, server.go          *)
(*        initProtocol.                                                    *)
(*                                                                         *)
(* Fixes selects which local fix branches are applied:                     *)
(*   "LeiosFetchBlockLimit"  MaxBlockMessageBytes = 600,000 + 10 as [R1]   *)
(*                           (7cd17437: 600,000 + 60,000).                 *)
(*   "ServerOptions"         the messagesubmission Server builds its map  *)
(*                           from the Config timeouts (7cd17437: the      *)
(*                           package constants, whatever the Config).     *)
(*   "NonBlockingTimed"      MessageIdsNonblockingTimeout 10 s as [R4]     *)
(*                           (7cd17437: 0, untimed).                       *)
(*   "V1BlockingUntimed"     V1 blocking id request untimed as [R4]       *)
(*                           (7cd17437: 30 s).                             *)
(* OptionValue is what a caller passed to every messagesubmission         *)
(* With...Timeout option, in seconds; 0 = none passed (defaults).          *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS Side, Fixes, OptionValue

Sides == {"LeiosFetchClient", "LeiosFetchServer", "LeiosNotifyClient",
          "LeiosVotesClient", "PerasVotesClient", "PerasVotesServer",
          "MsgSubV1Server", "MsgSubV1Client", "MsgSubV2Server",
          "MsgSubV2Client"}

-----------------------------------------------------------------------------
(* LeiosFetch [G] leiosfetch.go StateMap, client.go NewClient; [R1].        *)

FetchStates == {"Idle", "Block", "BlockTxs", "Votes", "BlockRange", "Done"}

\* In English: "Each request leads to its own server-agency state; each reply
\* returns to Idle, except a range reply that is not the last; MsgDone ends."
FetchNext(s) ==
    CASE s = "Idle"       -> {"Block", "BlockTxs", "Votes", "BlockRange",
                              "Done"}
      [] s = "BlockRange" -> {"BlockRange", "Idle"}
      [] s = "Done"       -> {}
      [] OTHER            -> {"Idle"}

\* In English: "The block reply's byte limit: the reference's endorser block
\* plus ten bytes with the fix, plus a tenth at 7cd17437."
FetchBlockLimit ==
    IF "LeiosFetchBlockLimit" \in Fixes THEN 600010 ELSE 660000

\* In English: "The client's effective table, per state: (agency, Go timeout,
\* reference timeout, Go limit, reference limit)."
FetchClient(s) ==
    CASE s = "Idle"       -> <<"local", 0, 0, 65535, 65535>>
      [] s = "Block"      -> <<"peer", 0, 60, FetchBlockLimit, 600010>>
      [] s = "BlockTxs"   -> <<"peer", 0, 60, 550000, 550000>>
      [] s = "Votes"      -> <<"peer", 5, -1, 0, -1>>
      [] s = "BlockRange" -> <<"peer", 5, -1, 67108864, -1>>
      [] s = "Done"       -> <<"none", 0, -1, 0, -1>>

\* In English: "The server installs StateMap unchanged: it waits only in Idle,
\* untimed, as the reference."
FetchServer(s) ==
    CASE s = "Idle"       -> <<"peer", 0, 0, 65535, 65535>>
      [] s = "Block"      -> <<"local", 0, -1, FetchBlockLimit, -1>>
      [] s = "BlockTxs"   -> <<"local", 0, -1, 550000, -1>>
      [] s = "Done"       -> <<"none", 0, -1, 0, -1>>
      [] OTHER            -> <<"local", 0, -1, 0, -1>>

-----------------------------------------------------------------------------
(* LeiosNotify [G] leiosnotify.go protocolConfig (every state gets the     *)
(* default budget, 10 x 65,535 bytes; Quit gets Config.Timeout, 60 s); [R2]. *)

NotifyStates == {"Idle", "Busy", "Quit", "Done"}

NotifyNext(s) ==
    CASE s = "Idle" -> {"Busy", "Quit"}
      [] s = "Busy" -> {"Idle"}
      [] s = "Quit" -> {"Done"}
      [] s = "Done" -> {}

NotifyClient(s) ==
    CASE s = "Idle" -> <<"local", 0, -1, 655350, -1>>
      [] s = "Busy" -> <<"peer", 0, 0, 655350, 1536>>
      [] s = "Quit" -> <<"peer", 60, 60, 655350, 65535>>
      [] s = "Done" -> <<"none", 0, -1, 655350, -1>>

-----------------------------------------------------------------------------
(* LeiosVotes [G] leiosvotes.go StateMap, client.go clientStateMap; [C1].   *)

VotesStates == {"Idle", "Busy", "Done"}

VotesNext(s) ==
    CASE s = "Idle" -> {"Busy", "Done"}
      [] s = "Busy" -> {"Busy", "Idle"}
      [] s = "Done" -> {}

VotesClient(s) ==
    CASE s = "Idle" -> <<"local", 0, -1, 0, -1>>
      [] s = "Busy" -> <<"peer", 60, -1, 1111, -1>>
      [] s = "Done" -> <<"none", 0, -1, 0, -1>>

-----------------------------------------------------------------------------
(* Peras votes (ObjectDiffusion) [G] perasvotes.go StateMap, client.go     *)
(* clientStateMap: limit 50 x 1,100 + 256 = 55,256 bytes in every active   *)
(* state at the default window; [R3].                                      *)

PerasStates == {"Init", "Idle", "Blocking", "MustReply", "NonBlocking",
                "Objects", "Done"}

PerasNext(s) ==
    CASE s = "Init"        -> {"Idle"}
      [] s = "Idle"        -> {"Blocking", "NonBlocking", "Objects", "Done"}
      [] s = "Blocking"    -> {"Idle", "MustReply"}
      [] s = "MustReply"   -> {"Idle"}
      [] s = "Done"        -> {}
      [] OTHER             -> {"Idle"}

PerasClient(s) ==
    CASE s = "Init"        -> <<"local", 0, -1, 55256, -1>>
      [] s = "Idle"        -> <<"local", 0, -1, 55256, -1>>
      [] s = "Blocking"    -> <<"peer", 10, 10, 55256, 2500000>>
      [] s = "MustReply"   -> <<"peer", 60, 60, 55256, 2500000>>
      [] s = "NonBlocking" -> <<"peer", 10, 10, 55256, 2500000>>
      [] s = "Objects"     -> <<"peer", 10, 10, 55256, 2500000>>
      [] s = "Done"        -> <<"none", 0, -1, 0, -1>>

PerasServer(s) ==
    CASE s = "Init"        -> <<"peer", 0, 0, 55256, 65535>>
      [] s = "Idle"        -> <<"peer", 0, 0, 55256, 65535>>
      [] s = "Done"        -> <<"none", 0, -1, 0, -1>>
      [] OTHER             -> <<"local", 0, -1, 55256, -1>>

-----------------------------------------------------------------------------
(* Message submission [G] messagesubmission.go, client.go, server.go;     *)
(* [R4]. No state has a PendingMessageByteLimit, so GoLimit is 0 and the   *)
(* byte limits are not compared here (a recorded drift).                   *)

MsgSubV1States == {"Init", "Idle", "Blocking", "NonBlocking", "Messages",
                   "Done"}
MsgSubV2States == {"Idle", "Blocking", "NonBlocking", "Messages", "Done"}

\* In English: "V1 starts with MsgInit; the blocking state may also end with
\* the Client's MsgDone. V2 has no Init and ends with MsgDone from Idle."
MsgSubV1Next(s) ==
    CASE s = "Init"     -> {"Idle"}
      [] s = "Idle"     -> {"Blocking", "NonBlocking", "Messages"}
      [] s = "Blocking" -> {"Idle", "Done"}
      [] s = "Done"     -> {}
      [] OTHER          -> {"Idle"}

MsgSubV2Next(s) ==
    CASE s = "Idle" -> {"Blocking", "NonBlocking", "Messages", "Done"}
      [] s = "Done" -> {}
      [] OTHER      -> {"Idle"}

\* In English: "The package constant for each state's timeout, in seconds."
MsgSubBase(v, s) ==
    CASE s = "Init"        -> 30
      [] s = "Idle"        -> 300
      [] s = "Blocking"    -> IF v = 1 /\ "V1BlockingUntimed" \in Fixes
                                THEN 0 ELSE 30
      [] s = "NonBlocking" -> IF "NonBlockingTimed" \in Fixes THEN 10 ELSE 0
      [] s = "Messages"    -> 30
      [] OTHER             -> 0

\* In English: "The states whose With...Timeout option the fixed Server
\* applies. A V1 blocking request is left out: it stays untimed, as [R4].
\* Init is left out too: it is the initial state, which the engine never
\* times (InitialStateTimeout is unset), so WithInitTimeout bounds nothing on
\* either side, and the reference waits forever there."
MsgSubOptionStates(v) ==
    IF v = 1 THEN {"Idle", "NonBlocking", "Messages"}
             ELSE {"Idle", "Blocking", "NonBlocking", "Messages"}

\* In English: "The timeout the Client installs: the caller's option where
\* one names the state (7cd17437 applies every option, V1 blocking too)."
MsgSubClientTimeout(v, s) ==
    IF OptionValue > 0 /\ s \in {"Init", "Idle", "Blocking", "NonBlocking",
                                  "Messages"}
       THEN OptionValue ELSE MsgSubBase(v, s)

\* In English: "The timeout the Server installs: the package constants at
\* 7cd17437; with the fix, the caller's option where it names the state."
MsgSubServerTimeout(v, s) ==
    IF "ServerOptions" \in Fixes /\ OptionValue > 0
       /\ s \in MsgSubOptionStates(v)
       THEN OptionValue ELSE MsgSubBase(v, s)

\* The reference's limit per state, [R4]: V1 Init, Idle, blocking forever,
\* non-blocking and bodies shortWait; V2 Idle forever, blocking 20 s.
MsgSubRef(v, s) ==
    CASE s = "Init"        -> 0
      [] s = "Idle"        -> 0
      [] s = "Blocking"    -> IF v = 1 THEN 0 ELSE 20
      [] s = "NonBlocking" -> 10
      [] s = "Messages"    -> 10
      [] OTHER             -> -1

\* In English: "In V1 the Client (the side with the messages) is the
\* initiator: it holds Init and every reply state; the Server holds Idle.
\* In V2 the Server is the initiator and holds Idle; the Client the rest."
MsgSubAgency(v, side, s) ==
    IF s = "Done" THEN "none"
    ELSE IF (side = "server") = (s \in {"Idle"}) THEN "local" ELSE "peer"

MsgSubV1Server(s) ==
    <<MsgSubAgency(1, "server", s), MsgSubServerTimeout(1, s),
      MsgSubRef(1, s), 0, -1>>
MsgSubV1Client(s) ==
    <<MsgSubAgency(1, "client", s), MsgSubClientTimeout(1, s),
      MsgSubRef(1, s), 0, -1>>
MsgSubV2Server(s) ==
    <<MsgSubAgency(2, "server", s), MsgSubServerTimeout(2, s),
      MsgSubRef(2, s), 0, -1>>
MsgSubV2Client(s) ==
    <<MsgSubAgency(2, "client", s), MsgSubClientTimeout(2, s),
      MsgSubRef(2, s), 0, -1>>

-----------------------------------------------------------------------------
(* The selected side.                                                      *)

States ==
    CASE Side \in {"LeiosFetchClient", "LeiosFetchServer"} -> FetchStates
      [] Side = "LeiosNotifyClient"  -> NotifyStates
      [] Side = "LeiosVotesClient"   -> VotesStates
      [] Side \in {"PerasVotesClient", "PerasVotesServer"} -> PerasStates
      [] Side \in {"MsgSubV1Server", "MsgSubV1Client"} -> MsgSubV1States
      [] OTHER -> MsgSubV2States

InitState ==
    CASE Side \in {"PerasVotesClient", "PerasVotesServer",
                   "MsgSubV1Server", "MsgSubV1Client"} -> "Init"
      [] OTHER -> "Idle"

NextStates(s) ==
    CASE Side \in {"LeiosFetchClient", "LeiosFetchServer"} -> FetchNext(s)
      [] Side = "LeiosNotifyClient"  -> NotifyNext(s)
      [] Side = "LeiosVotesClient"   -> VotesNext(s)
      [] Side \in {"PerasVotesClient", "PerasVotesServer"} -> PerasNext(s)
      [] Side \in {"MsgSubV1Server", "MsgSubV1Client"} -> MsgSubV1Next(s)
      [] OTHER -> MsgSubV2Next(s)

Row(s) ==
    CASE Side = "LeiosFetchClient"  -> FetchClient(s)
      [] Side = "LeiosFetchServer"  -> FetchServer(s)
      [] Side = "LeiosNotifyClient" -> NotifyClient(s)
      [] Side = "LeiosVotesClient"  -> VotesClient(s)
      [] Side = "PerasVotesClient"  -> PerasClient(s)
      [] Side = "PerasVotesServer"  -> PerasServer(s)
      [] Side = "MsgSubV1Server"    -> MsgSubV1Server(s)
      [] Side = "MsgSubV1Client"    -> MsgSubV1Client(s)
      [] Side = "MsgSubV2Server"    -> MsgSubV2Server(s)
      [] Side = "MsgSubV2Client"    -> MsgSubV2Client(s)

Agency(s)     == Row(s)[1]
GoTimeout(s)  == Row(s)[2]
RefTimeout(s) == Row(s)[3]
GoLimit(s)    == Row(s)[4]
RefLimit(s)   == Row(s)[5]

\* In English: "LeiosFetch Block and BlockTxs have no state timer: the
\* caller's context bounds each request, and a later request on a
\* desynchronised exchange fails the protocol ([G] client.go acquireSlot)."
CtxBound(s) == Side = "LeiosFetchClient" /\ s \in {"Block", "BlockTxs"}

\* In English: "The states a caller expects its options to bound, whatever
\* the code does: the waits each option names on the side that waits."
OptionIntent ==
    CASE Side = "MsgSubV1Server" -> MsgSubOptionStates(1) \ {"Idle"}
      [] Side = "MsgSubV2Server" -> MsgSubOptionStates(2) \ {"Idle"}
      [] Side \in {"MsgSubV1Client", "MsgSubV2Client"} -> {"Idle"}
      [] OTHER -> {}
=============================================================================
