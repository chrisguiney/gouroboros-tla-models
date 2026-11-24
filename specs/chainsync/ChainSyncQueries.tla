--------------------------- MODULE ChainSyncQueries ---------------------------
(***************************************************************************)
(* Model `chainsync`, slice 3: one-shot MsgFindIntersect exchanges, and whether     *)
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
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.     *)
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

\* In English: "The value of busyMutex, or of a channel slot, when it is
\* empty."
\* Literally: "None is defined as "none"."
None == "none"

\* In English: "no answer", as a record so it compares with real answers.
\* Literally: "NoAnswer is defined as the record whose field kind is "none" and
\*   field for is "none"."
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

\* Literally: "vars is defined as the tuple of all thirteen variables."
vars == <<busy, gpc, jpc, wantTip, wantIF, jres, toServer, toClient, hpc,
          msg, orphan, rolled, tipAnswered>>

\* In English: "Both calls are about to start; nothing is in flight."
\* Literally: "Init is defined as: busy equals None, and gpc equals "lock", and
\*   jpc equals "lock", and wantTip equals None, and wantIF equals None, and
\*   jres equals NoAnswer, and toServer equals the empty sequence, and toClient
\*   equals the empty sequence, and hpc equals "idle", and msg equals NoAnswer,
\*   and orphan equals FALSE, and rolled equals FALSE, and tipAnswered equals
\*   FALSE."
Init ==
    /\ busy = None /\ gpc = "lock" /\ jpc = "lock"
    /\ wantTip = None /\ wantIF = None /\ jres = NoAnswer
    /\ toServer = <<>> /\ toClient = <<>>
    /\ hpc = "idle" /\ msg = NoAnswer /\ orphan = FALSE
    /\ rolled = FALSE /\ tipAnswered = FALSE

-----------------------------------------------------------------------------
(* GetCurrentTip [G1]. *)

\* In English: "GetCurrentTip takes busyMutex when it is free."
\* Literally: "TipLock is defined as: rolled and tipAnswered are unchanged, and
\*   gpc equals "lock", and busy equals None, and busy in the next state equals
\*   "tip", and gpc in the next state equals "send", and jpc, wantTip, wantIF,
\*   jres, toServer, toClient, hpc, msg and orphan are unchanged."
TipLock ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ gpc = "lock" /\ busy = None
    /\ busy' = "tip" /\ gpc' = "send"
    /\ UNCHANGED <<jpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

\* In English: "Register for the next tip, and send MsgFindIntersect with no
\* points."
\* Literally: "TipSend is defined as: rolled and tipAnswered are unchanged, and
\*   gpc equals "send", and wantTip equals None, and wantTip in the next state
\*   equals "tip", and toServer in the next state equals toServer with "tip"
\*   appended, and gpc in the next state equals "wait", and busy, jpc, wantIF,
\*   jres, toClient, hpc, msg and orphan are unchanged."
TipSend ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ gpc = "send" /\ wantTip = None
    /\ wantTip' = "tip"
    /\ toServer' = Append(toServer, "tip")
    /\ gpc' = "wait"
    /\ UNCHANGED <<busy, jpc, wantIF, jres, toClient, hpc, msg, orphan>>

\* In English: "Once a tip has been delivered (the slot is empty again),
\* return it and release busyMutex."
\* Literally: "TipDone is defined as: rolled and tipAnswered are unchanged, and
\*   gpc equals "wait", and wantTip equals None, and if TipWaitsOwnAnswer, then
\*   tipAnswered; and busy in the next state equals None, and gpc in the next
\*   state equals "done", and jpc, wantTip, wantIF, jres, toServer, toClient,
\*   hpc, msg and orphan are unchanged."
TipDone ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ gpc = "wait" /\ wantTip = None
    /\ TipWaitsOwnAnswer => tipAnswered
    /\ busy' = None /\ gpc' = "done"
    /\ UNCHANGED <<jpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

-----------------------------------------------------------------------------
(* Jump [G1]. *)

\* In English: "Jump takes busyMutex when it is free."
\* Literally: "JumpLock is defined as: rolled and tipAnswered are unchanged,
\*   and jpc equals "lock", and busy equals None, and busy in the next state
\*   equals "jump", and jpc in the next state equals "send", and gpc, wantTip,
\*   wantIF, jres, toServer, toClient, hpc, msg and orphan are unchanged."
JumpLock ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ jpc = "lock" /\ busy = None
    /\ busy' = "jump" /\ jpc' = "send"
    /\ UNCHANGED <<gpc, wantTip, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan>>

\* In English: "Register for the next intersect result, and send
\* MsgFindIntersect with points."
\* Literally: "JumpSend is defined as: rolled and tipAnswered are unchanged,
\*   and jpc equals "send", and wantIF equals None, and wantIF in the next
\*   state equals "jump", and toServer in the next state equals toServer with
\*   "jump" appended, and jpc in the next state equals "wait", and busy, gpc,
\*   wantTip, jres, toClient, hpc, msg and orphan are unchanged."
JumpSend ==
    /\ UNCHANGED <<rolled, tipAnswered>>
    /\ jpc = "send" /\ wantIF = None
    /\ wantIF' = "jump"
    /\ toServer' = Append(toServer, "jump")
    /\ jpc' = "wait"
    /\ UNCHANGED <<busy, gpc, wantTip, jres, toClient, hpc, msg, orphan>>

\* In English: "Once a result has been delivered, return it and release
\* busyMutex."
\* Literally: "JumpDone is defined as: rolled and tipAnswered are unchanged,
\*   and jpc equals "wait", and jres does not equal NoAnswer, and busy in the
\*   next state equals None, and jpc in the next state equals "done", and gpc,
\*   wantTip, wantIF, jres, toServer, toClient, hpc, msg and orphan are
\*   unchanged."
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

\* In English: "The server answers the oldest MsgFindIntersect for the call
\* that sent it: GetCurrentTip's (no points) is always not found; Jump's may be
\* found or not."
\* Literally: "ServerAnswer is defined as: rolled and tipAnswered are
\*   unchanged, and toServer does not equal the empty sequence, and there
\*   exists a k in (if the head of toServer equals "tip" then the set
\*   containing "NotFound", else the set containing "Found" and "NotFound")
\*   such that toClient in the next state equals toClient with the record whose
\*   field kind is k and field for is the head of toServer appended; and
\*   toServer in the next state equals the tail of toServer, and busy, gpc,
\*   jpc, wantTip, wantIF, jres, hpc, msg and orphan are unchanged."
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
\* Literally: "HandleTake is defined as: rolled and tipAnswered are unchanged,
\*   and hpc equals "idle", and toClient does not equal the empty sequence, and
\*   msg in the next state equals the head of toClient, and toClient in the
\*   next state equals the tail of toClient, and hpc in the next state equals
\*   (if the head of toClient's kind equals "Found" or PopBeforeTip is true,
\*   then "pop", else "tip"), and busy, gpc, jpc, wantTip, wantIF, jres,
\*   toServer and orphan are unchanged."
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
\* Literally: "HandleTip is defined as: rolled is unchanged, and hpc equals
\*   "tip", and wantTip in the next state equals None, and hpc in the next
\*   state equals (if msg's kind equals "NotFound" and PopBeforeTip is not
\*   true, then "pop", else "idle"), and tipAnswered in the next state equals
\*   (tipAnswered is true, or hpc in the next state equals "idle" and msg's for
\*   equals "tip"), and busy, gpc, jpc, wantIF, jres, toServer, toClient, msg
\*   and orphan are unchanged."
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
\* Literally: "HandlePop is defined as: hpc equals "pop", and if wantIF equals
\*   None, then (orphan in the next state equals (orphan is true or msg's kind
\*   equals "Found"), and wantIF and jres are unchanged), else (jres in the
\*   next state equals msg, and wantIF in the next state equals None, and
\*   orphan is unchanged); and hpc in the next state equals (if msg's kind
\*   equals "Found" or PopBeforeTip is true, then "tip", else "idle"), and
\*   tipAnswered in the next state equals (tipAnswered is true, or hpc in the
\*   next state equals "idle" and msg's for equals "tip"), and busy, gpc, jpc,
\*   wantTip, toServer, toClient, msg and rolled are unchanged."
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
\* Literally: "HandleRoll is defined as: RollTips is true, and rolled is not
\*   true, and hpc equals "idle", and gpc equals "wait", and wantTip in the
\*   next state equals None, and rolled in the next state equals TRUE, and the
\*   other eleven variables are unchanged."
HandleRoll ==
    /\ RollTips /\ ~rolled /\ hpc = "idle" /\ gpc = "wait"
    /\ wantTip' = None /\ rolled' = TRUE
    /\ UNCHANGED <<busy, gpc, jpc, wantIF, jres, toServer, toClient, hpc, msg,
                   orphan, tipAnswered>>

-----------------------------------------------------------------------------

\* In English: "Both calls returned and nothing is in flight."
\* Literally: "Finished is defined as: gpc equals "done", and jpc equals
\*   "done", and toServer equals the empty sequence, and toClient equals the
\*   empty sequence, and hpc equals "idle", and vars is unchanged."
Finished ==
    /\ gpc = "done" /\ jpc = "done"
    /\ toServer = <<>> /\ toClient = <<>> /\ hpc = "idle"
    /\ UNCHANGED vars

\* In English: "A step is any one step of GetCurrentTip, Jump, the server or
\* the handler, or staying finished."
\* Literally: "Next is defined as: TipLock, or TipSend, or TipDone, or
\*   JumpLock, or JumpSend, or JumpDone, or ServerAnswer, or HandleTake, or
\*   HandleTip, or HandlePop, or HandleRoll, or Finished."
Next ==
    \/ TipLock \/ TipSend \/ TipDone
    \/ JumpLock \/ JumpSend \/ JumpDone
    \/ ServerAnswer
    \/ HandleTake \/ HandleTip \/ HandlePop \/ HandleRoll
    \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Whatever Jump receives is the answer to its own
\* MsgFindIntersect."
\* Literally: "JumpGetsOwnAnswer is defined as: if jres does not equal
\*   NoAnswer, then jres's for equals "jump"."
JumpGetsOwnAnswer == jres /= NoAnswer => jres.for = "jump"

\* In English: "No MsgIntersectFound ever arrives with nobody registered for
\* it."
\* Literally: "NoOrphanAnswer is defined as: orphan is not true."
NoOrphanAnswer == ~orphan

\* Probe, EXPECTED to be violated: "Jump never runs after GetCurrentTip."
\* Violated = the order in which the race can happen is reachable.
\* Literally: "ProbeJumpNeverAfterTip is defined as: it is not the case that
\*   gpc equals "done" and jpc equals "wait"."
ProbeJumpNeverAfterTip == ~(gpc = "done" /\ jpc = "wait")
=============================================================================
