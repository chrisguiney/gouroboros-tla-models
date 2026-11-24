--------------------------- MODULE ChainSyncQueries ---------------------------
(***************************************************************************)
(* Model 04, slice 3: one-shot MsgFindIntersect exchanges, and whether     *)
(* each answer reaches the call that asked.                                *)
(*                                                                         *)
(* Two client calls send MsgFindIntersect and wait for an answer           *)
(* (protocol/chainsync/client.go):                                         *)
(*   GetCurrentTip  sends MsgFindIntersect with no points (the server      *)
(*                  answers MsgIntersectNotFound with its tip). It         *)
(*                  registers on wantCurrentTipChan and returns on the     *)
(*                  first tip ANY handler delivers.                        *)
(*   Jump           sends MsgFindIntersect with points, registers on       *)
(*                  wantIntersectFoundChan, and returns the first          *)
(*                  intersect result a handler delivers.                   *)
(* Both hold busyMutex while they wait, so they never overlap. Neither     *)
(* tags its request: the handler gives a reply to whichever call is        *)
(* registered when it looks.                                               *)
(*                                                                         *)
(* The handler for MsgIntersectNotFound does two things, in order          *)
(* (handleIntersectNotFound): it delivers the tip (sendCurrentTip), then   *)
(* takes the registered intersect request, if any, and fails it with       *)
(* ErrIntersectNotFound. Between the two, GetCurrentTip may already have   *)
(* returned and released busyMutex.                                        *)
(*                                                                         *)
(* Questions: does Jump always get the answer to its own MsgFindIntersect? *)
(* Does any answer arrive with no request registered (the handler then     *)
(* returns "received IntersectFound without a pending FindIntersect        *)
(* request", a protocol error)?                                            *)
(*                                                                         *)
(* Sources:                                                                *)
(*   Specification, IntersectMBO/ouroboros-network 5f356486ab3e,           *)
(*   docs/network-spec/miniprotocols.tex:                                  *)
(*   [C1] 893-908: StIntersect is answered by exactly one                  *)
(*        MsgIntersectFound or MsgIntersectNotFound.                       *)
(*   [P1] 2180-2208: replies come back in request order.                   *)
(*   Reference, same commit:                                               *)
(*   [R2] ChainSync/ClientPipelined.hs 257-273: the answer to              *)
(*        MsgFindIntersect goes to the continuation that sent it (Yield    *)
(*        then Await); there is no shared registry to mismatch.            *)
(*   gOuroboros, blinklabs-io/gouroboros 61046085,                         *)
(*   protocol/chainsync/client.go:                                         *)
(*   [G1] GetCurrentTip, Jump, findIntersect, wantCurrentTip,              *)
(*        wantIntersectFound, sendCurrentTip, handleIntersectFound,        *)
(*        handleIntersectNotFound.                                         *)
(*                                                                         *)
(* Not modelled: a running sync beyond one roll delivering a tip,         *)
(* GetAvailableBlockRange, Reintersect, and several concurrent             *)
(* GetCurrentTip callers (waitingForCurrentTipChan).                       *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    \* FALSE in gOuroboros. TRUE: handleIntersectNotFound takes the
    \* registered intersect request BEFORE it delivers the tip, as
    \* handleIntersectFound already does.
    PopBeforeTip,
    \* TRUE: a sync was running, so a roll (the reply to a MsgRequestNext
    \* sent before GetCurrentTip's MsgFindIntersect) may deliver a tip while
    \* GetCurrentTip waits. Rolls call sendCurrentTip too.
    RollTips,
    \* FALSE in gOuroboros. TRUE: GetCurrentTip returns only once the
    \* answer to its own MsgFindIntersect has been handled.
    TipWaitsOwnAnswer

None == "none"

\* In English: "no answer", as a record so it compares with real answers.
NoAnswer == [kind |-> "none", for |-> "none"]

VARIABLES
    busy,       \* who holds busyMutex: None, "tip" (GetCurrentTip) or "jump"
    gpc,        \* GetCurrentTip's next step
    jpc,        \* Jump's next step
    wantTip,    \* wantCurrentTipChan's single slot: None or "tip"
    wantIF,     \* wantIntersectFoundChan's single slot: None or "jump"
    jres,       \* what Jump received: NoAnswer, or [kind, for] where for names
                \* the call whose MsgFindIntersect the answer was to
    toServer,   \* MsgFindIntersect in flight, tagged with the call that sent it
    toClient,   \* answers in flight: [kind |-> "Found"/"NotFound", for |-> call]
    hpc,        \* the handler: "idle", or its next step for msg
    msg,        \* the answer the handler is working on
    orphan,     \* an answer arrived with no request registered
    rolled,     \* TRUE once a roll has delivered a tip (at most one)
    tipAnswered \* TRUE once the handler has finished GetCurrentTip's answer

vars == <<busy, gpc, jpc, wantTip, wantIF, jres, toServer, toClient, hpc,
          msg, orphan, rolled, tipAnswered>>

\* In English: "Both calls are about to start; nothing is in flight."
Init ==
    /\ busy = None /\ gpc = "lock" /\ jpc = "lock"
    /\ wantTip = None /\ wantIF = None /\ jres = NoAnswer
    /\ toServer = <<>> /\ toClient = <<>>
    /\ hpc = "idle" /\ msg = NoAnswer /\ orphan = FALSE
    /\ rolled = FALSE /\ tipAnswered = FALSE

-----------------------------------------------------------------------------
(* GetCurrentTip [G1]. *)

TipLock ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ gpc = "lock" /\ busy = None
    /\ busy' = "tip" /\ gpc' = "send"
    /\ UNCHANGED <<jpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

\* In English: "Register for the next tip, and send MsgFindIntersect with no
\* points."
TipSend ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ gpc = "send" /\ wantTip = None
    /\ wantTip' = "tip"
    /\ toServer' = Append(toServer, "tip")
    /\ gpc' = "wait"
    /\ UNCHANGED <<busy, jpc, wantIF, jres, toClient, hpc, msg, orphan>>

\* In English: "Once a tip has been delivered (the slot is empty again),
\* return it and release busyMutex."
TipDone ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ gpc = "wait" /\ wantTip = None
    /\ TipWaitsOwnAnswer => tipAnswered
    /\ busy' = None /\ gpc' = "done"
    /\ UNCHANGED <<jpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

-----------------------------------------------------------------------------
(* Jump [G1]. *)

JumpLock ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ jpc = "lock" /\ busy = None
    /\ busy' = "jump" /\ jpc' = "send"
    /\ UNCHANGED <<gpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

\* In English: "Register for the next intersect result, and send
\* MsgFindIntersect with points."
JumpSend ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ jpc = "send" /\ wantIF = None
    /\ wantIF' = "jump"
    /\ toServer' = Append(toServer, "jump")
    /\ jpc' = "wait"
    /\ UNCHANGED <<busy, gpc, wantTip, jres, toClient, hpc, msg, orphan>>

\* In English: "Once a result has been delivered, return it and release
\* busyMutex."
JumpDone ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ jpc = "wait" /\ jres /= NoAnswer
    /\ busy' = None /\ jpc' = "done"
    /\ UNCHANGED <<gpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

-----------------------------------------------------------------------------
(* The server [C1][P1]: answers each MsgFindIntersect in order. No points  *)
(* (GetCurrentTip) always gets MsgIntersectNotFound; Jump's points may get *)
(* either answer.                                                          *)

ServerAnswer ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ toServer /= <<>>
    /\ \E k \in IF Head(toServer) = "tip" THEN {"NotFound"}
                ELSE {"Found", "NotFound"} :
          toClient' = Append(toClient, [kind |-> k, for |-> Head(toServer)])
    /\ toServer' = Tail(toServer)
    /\ UNCHANGED <<busy, gpc, jpc, wantTip, wantIF, jres, hpc, msg, orphan>>

-----------------------------------------------------------------------------
(* The handler [G1]: one answer at a time, in steps.                       *)

\* In English: "Take the next answer. MsgIntersectFound first takes the
\* registered request; MsgIntersectNotFound first delivers the tip, unless
\* PopBeforeTip."
HandleTake ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ hpc = "idle" /\ toClient /= <<>>
    /\ msg' = Head(toClient)
    /\ toClient' = Tail(toClient)
    /\ hpc' = IF Head(toClient).kind = "Found" \/ PopBeforeTip
                 THEN "pop" ELSE "tip"
    /\ UNCHANGED <<busy, gpc, jpc, wantTip, wantIF, jres, toServer, orphan>>

\* sendCurrentTip. In English: "Give the tip to whoever is registered for
\* one, if anyone."
HandleTip ==
    /\ UNCHANGED rolled
    /\ hpc = "tip"
    /\ wantTip' = None
    /\ hpc' = IF msg.kind = "NotFound" /\ ~PopBeforeTip THEN "pop" ELSE "idle"
    \* "If this was the last step for GetCurrentTip's answer, it is handled."
    /\ tipAnswered' = (tipAnswered \/ (hpc' = "idle" /\ msg.for = "tip"))
    /\ UNCHANGED <<busy, gpc, jpc, wantIF, jres, toServer, toClient, msg,
                   orphan>>

\* In English: "Take the registered intersect request and give it this
\* answer. MsgIntersectFound with nobody registered is an error;
\* MsgIntersectNotFound with nobody registered is ignored."
HandlePop ==
    /\ hpc = "pop"
    /\ IF wantIF = None
          THEN /\ orphan' = (orphan \/ msg.kind = "Found")
               /\ UNCHANGED <<wantIF, jres>>
          ELSE /\ jres' = msg
               /\ wantIF' = None
               /\ UNCHANGED orphan
    /\ hpc' = IF msg.kind = "Found" \/ PopBeforeTip THEN "tip" ELSE "idle"
    \* "If this was the last step for GetCurrentTip's answer, it is handled."
    /\ tipAnswered' = (tipAnswered \/ (hpc' = "idle" /\ msg.for = "tip"))
    /\ UNCHANGED <<busy, gpc, jpc, wantTip, toServer, toClient, msg, rolled>>

\* In English: "With a sync running, the reply to its earlier MsgRequestNext
\* arrives first and its handler delivers a tip to GetCurrentTip, before
\* GetCurrentTip's own answer. The roll's other effects are not modelled."
HandleRoll ==
    /\ RollTips /\ ~rolled /\ hpc = "idle" /\ gpc = "wait"
    /\ wantTip' = None /\ rolled' = TRUE
    /\ UNCHANGED <<busy, gpc, jpc, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan, tipAnswered>>

-----------------------------------------------------------------------------

\* In English: "Both calls returned and nothing is in flight."
Finished ==
    /\ gpc = "done" /\ jpc = "done"
    /\ toServer = <<>> /\ toClient = <<>> /\ hpc = "idle"
    /\ UNCHANGED vars

Next ==
    \/ TipLock \/ TipSend \/ TipDone
    \/ JumpLock \/ JumpSend \/ JumpDone
    \/ ServerAnswer
    \/ HandleTake \/ HandleTip \/ HandlePop \/ HandleRoll
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Whatever Jump receives is the answer to its own
\* MsgFindIntersect."
JumpGetsOwnAnswer == jres /= NoAnswer => jres.for = "jump"

\* In English: "No MsgIntersectFound ever arrives with nobody registered for
\* it."
NoOrphanAnswer == ~orphan

\* Probe, EXPECTED to be violated: "Jump never runs after GetCurrentTip."
\* Violated = the order in which the race can happen is reachable.
ProbeJumpNeverAfterTip == ~(gpc = "done" /\ jpc = "wait")
=============================================================================
