--------------------- MODULE LocalStateQueryClientLimits ---------------------
(***************************************************************************)
(* Three things the gOuroboros local-state-query client adds to the        *)
(* protocol, each a place an answer could go stale or a caller could be    *)
(* left waiting:                                                           *)
(*   - the cached current era (`currentEra`), which era-specific queries   *)
(*     read instead of asking the node every time;                         *)
(*   - the opt-in state timeouts (AcquireTimeout on StAcquiring,           *)
(*     QueryTimeout on StQuerying), each a deadline that belongs to the    *)
(*     state it was armed in;                                              *)
(*   - the read-buffer limit (MaxReadBufferSize): a result larger than it  *)
(*     is refused, which ends the protocol.                                *)
(*                                                                         *)
(* LocalStateQueryClient.tla checks the calls and their answers; this      *)
(* module abstracts those to one caller and adds the era the node is in.   *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] ouroboros-network 5f356486ab3e docs/network-spec/miniprotocols.tex*)
(*        1950-2020: MsgAcquire/MsgReAcquire, MsgAcquired, MsgFailure      *)
(*        ("failure to re-acquire is equivalent to MsgRelease", 1990),     *)
(*        MsgQuery/MsgResult, MsgRelease; "No timeouts" and "No size       *)
(*        limits" (2020).                                                  *)
(*   [R1] ouroboros-consensus ec239d57f618 .../Ledger/Query.hs: the        *)
(*        current era is a property of the acquired ledger state, so two   *)
(*        acquired states may answer it differently.                       *)
(*   UNSOURCED (library additions): the cache, the opt-in timeouts and the *)
(*   read-buffer limit.                                                    *)
(*                                                                         *)
(* gOuroboros at 7cd17437:                                                 *)
(*   [G1] protocol/localstatequery/client.go handleAcquired and            *)
(*        handleFailure clear currentEra before waking the caller;         *)
(*        release() clears it; getCurrentEra fills it from a               *)
(*        QueryTypeHardForkCurrentEra result.                              *)
(*   [G2] runQueryMaxItems with nothing acquired acquires the volatile tip *)
(*        for the call; endCall releases it, clearing the cache.           *)
(*   [G3] protocol/protocol.go stateLoop: setState stops and drains the    *)
(*        previous state's timer before anything else, and arms a timer    *)
(*        only in a state where the peer holds agency.                     *)
(*   [G4] protocol/protocol.go appendSegment: a message larger than        *)
(*        MaxReadBufferSize is a SendError, which stops the protocol.      *)
(*   [G5] client.go Start: once DoneChan closes, a goroutine closes        *)
(*        queryResultChan and acquireResultChan, so a waiting call returns *)
(*        ErrProtocolShuttingDown.                                         *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see the legend at the top of                   *)
(* specs/keepalive/KeepAlive.tla and the "Reading a formula literally"     *)
(* table in the top-level README.                                          *)
(***************************************************************************)
EXTENDS Integers   \* numbers, including -1 for "none"

CONSTANTS
    MaxEra,               \* the node's era goes from 0 up to MaxEra
    MaxCalls,             \* how many public calls the caller makes (keeps the model finite)
    Timeouts,             \* TRUE: AcquireTimeout and QueryTimeout are set; FALSE: the default, none
    Oversize,             \* TRUE: the node may send a result larger than MaxReadBufferSize
    InvalidateOnAcquired, \* TRUE: MsgAcquired clears the cached era [G1]; FALSE: a mutation
    InvalidateOnFailure,  \* TRUE: MsgFailure clears it [G1]; FALSE: a mutation
    InvalidateOnRelease,  \* TRUE: release() clears it [G1][G2]; FALSE: a mutation
    DisarmOnTransition,   \* TRUE: every transition stops the previous timer [G3];
                          \* FALSE: a mutation, entering a client-agency state keeps it
    CloseOnDone           \* TRUE: the result channels close once the protocol is done [G5];
                          \* FALSE: a mutation

\* Literally: "None is defined as -1 (no era cached or held)."
None == -1

\* In English: "The states where the node holds agency, the only ones a
\* timer is armed in [G3]."
\* Literally: "PeerAgency is defined as the set containing "StAcquiring" and
\*   "StQuerying"."
PeerAgency == {"StAcquiring", "StQuerying"}

VARIABLES
    chainEra,  \* the era of the node's tip
    pstate,    \* the client protocol's state, or "Failed" once it stopped on an error
    heldEra,   \* the era of the acquired ledger state, or None
    cache,     \* currentEra: the cached era, or None
    call,      \* the call in progress: "none", "acquire", "era" (an era query),
               \* or "implicit" (an era query that acquired the tip itself [G2])
    timer,     \* the state the armed timer belongs to, or "none"
    stale,     \* TRUE once a timer fired in a state it does not belong to
    wrongEra,  \* TRUE once a GetCurrentEra call returned an era other than the held state's
    calls      \* calls made so far

\* Literally: "vars is defined as the tuple of all nine variables."
vars == <<chainEra, pstate, heldEra, cache, call, timer, stale, wrongEra, calls>>

\* In English: "The timer after entering state s: the previous one is
\* stopped (or kept, in the mutation, when s gives the client agency), and
\* with Timeouts a new one is armed if the node holds agency in s [G3]."
\* Literally: "TimerFor of s is defined as: if s is in PeerAgency, then s if
\*   Timeouts and "none" otherwise; else "none" if DisarmOnTransition, else
\*   timer."
TimerFor(s) ==
    IF s \in PeerAgency THEN (IF Timeouts THEN s ELSE "none")
    ELSE IF DisarmOnTransition THEN "none" ELSE timer

\* In English: "At the start the node is in era 0, the client is idle with
\* nothing held, cached or armed."
Init ==
    /\ chainEra = 0
    /\ pstate = "StIdle"
    /\ heldEra = None
    /\ cache = None
    /\ call = "none"
    /\ timer = "none"
    /\ stale = FALSE
    /\ wrongEra = FALSE
    /\ calls = 0

\* In English: "The node moves into the next era."
\* Literally: "EraAdvance is defined as: chainEra is less than MaxEra, and
\*   chainEra goes up by one, and the rest is unchanged."
EraAdvance ==
    /\ chainEra < MaxEra
    /\ chainEra' = chainEra + 1
    /\ UNCHANGED <<pstate, heldEra, cache, call, timer, stale, wrongEra, calls>>

\* In English: "The caller acquires (MsgAcquire from StIdle, MsgReAcquire
\* from StAcquired) and waits."
\* Literally: "CallAcquire is defined as: call is "none", calls is less than
\*   MaxCalls, pstate is "StIdle" or "StAcquired", and pstate becomes
\*   "StAcquiring", timer becomes TimerFor of "StAcquiring", call becomes
\*   "acquire", calls goes up by one, the rest unchanged."
CallAcquire ==
    /\ call = "none" /\ calls < MaxCalls
    /\ pstate \in {"StIdle", "StAcquired"}
    /\ pstate' = "StAcquiring"
    /\ timer' = TimerFor("StAcquiring")
    /\ call' = "acquire"
    /\ calls' = calls + 1
    /\ UNCHANGED <<chainEra, heldEra, cache, stale, wrongEra>>

\* In English: "The caller releases the acquired state; release() clears
\* the cached era [G1]."
CallRelease ==
    /\ call = "none" /\ calls < MaxCalls
    /\ pstate = "StAcquired"
    /\ pstate' = "StIdle"
    /\ heldEra' = None
    /\ cache' = IF InvalidateOnRelease THEN None ELSE cache
    /\ timer' = TimerFor("StIdle")
    /\ calls' = calls + 1
    /\ UNCHANGED <<chainEra, call, stale, wrongEra>>

\* In English: "GetCurrentEra: a cached era is returned at once (and
\* checked against the held state's era); with a state acquired the client
\* asks the node; with none it acquires the tip first [G1][G2]."
\* Literally: "CallEra is defined as: call is "none", calls is less than
\*   MaxCalls, pstate is "StIdle" or "StAcquired", calls goes up by one, and
\*   either the cache holds an era (it is returned: wrongEra becomes
\*   wrongEra or cache differs from heldEra), or pstate is "StAcquired" (the
\*   query is sent: pstate becomes "StQuerying" and call "era"), or pstate is
\*   "StIdle" (MsgAcquire is sent: pstate becomes "StAcquiring" and call
\*   "implicit"); the timer follows the new state."
CallEra ==
    /\ call = "none" /\ calls < MaxCalls
    /\ pstate \in {"StIdle", "StAcquired"}
    /\ calls' = calls + 1
    /\ \/ /\ cache /= None
          /\ wrongEra' = (wrongEra \/ cache /= heldEra)
          /\ UNCHANGED <<pstate, call, timer>>
       \/ /\ cache = None /\ pstate = "StAcquired"
          /\ pstate' = "StQuerying"
          /\ timer' = TimerFor("StQuerying")
          /\ call' = "era"
          /\ UNCHANGED wrongEra
       \/ /\ cache = None /\ pstate = "StIdle"
          /\ pstate' = "StAcquiring"
          /\ timer' = TimerFor("StAcquiring")
          /\ call' = "implicit"
          /\ UNCHANGED wrongEra
    /\ UNCHANGED <<chainEra, heldEra, cache, stale>>

\* In English: "The node acquires its tip: the client now holds a state of
\* the node's current era, and its handler clears the cache before waking
\* the caller [G1]. An acquire call returns; an implicit era query sends its
\* query."
\* Literally: "ServerAcquired is defined as: pstate is "StAcquiring", heldEra
\*   becomes chainEra, cache becomes None if InvalidateOnAcquired and stays
\*   otherwise, and if call is "implicit" pstate becomes "StQuerying" with
\*   its timer, otherwise pstate becomes "StAcquired" with its timer and call
\*   becomes "none"."
ServerAcquired ==
    /\ pstate = "StAcquiring"
    /\ heldEra' = chainEra
    /\ cache' = IF InvalidateOnAcquired THEN None ELSE cache
    /\ IF call = "implicit"
          THEN /\ pstate' = "StQuerying"
               /\ timer' = TimerFor("StQuerying")
               /\ UNCHANGED call
          ELSE /\ pstate' = "StAcquired"
               /\ timer' = TimerFor("StAcquired")
               /\ call' = "none"
    /\ UNCHANGED <<chainEra, stale, wrongEra, calls>>

\* In English: "The node cannot acquire: the client is idle again, holding
\* nothing, and the handler clears the cache [S1 1990][G1]."
ServerFailure ==
    /\ pstate = "StAcquiring"
    /\ pstate' = "StIdle"
    /\ heldEra' = None
    /\ cache' = IF InvalidateOnFailure THEN None ELSE cache
    /\ timer' = TimerFor("StIdle")
    /\ call' = "none"
    /\ UNCHANGED <<chainEra, stale, wrongEra, calls>>

\* In English: "The node answers the era query with the held state's era,
\* which the client caches and returns. An implicit call then releases the
\* state it acquired, clearing the cache [G2]."
ServerResult ==
    /\ pstate = "StQuerying"
    /\ wrongEra' = wrongEra            \* the node answers from the held state
    /\ call' = "none"
    /\ IF call = "implicit"
          THEN /\ pstate' = "StIdle"
               /\ heldEra' = None
               /\ cache' = IF InvalidateOnRelease THEN None ELSE heldEra
               /\ timer' = TimerFor("StIdle")
          ELSE /\ pstate' = "StAcquired"
               /\ cache' = heldEra
               /\ timer' = TimerFor("StAcquired")
               /\ UNCHANGED heldEra
    /\ UNCHANGED <<chainEra, stale, calls>>

\* In English: "The node sends a result larger than MaxReadBufferSize. The
\* read loop refuses it and stops the protocol [G4]; nothing is delivered."
OversizedResult ==
    /\ Oversize
    /\ pstate = "StQuerying"
    /\ pstate' = "Failed"
    /\ timer' = "none"
    /\ UNCHANGED <<chainEra, heldEra, cache, call, stale, wrongEra, calls>>

\* In English: "The armed timer fires: the protocol stops with a timeout.
\* If the timer belongs to a state the protocol has left, that is a stale
\* timeout."
TimerFires ==
    /\ timer /= "none"
    /\ pstate /= "Failed"
    /\ stale' = (stale \/ timer /= pstate)
    /\ pstate' = "Failed"
    /\ timer' = "none"
    /\ UNCHANGED <<chainEra, heldEra, cache, call, wrongEra, calls>>

\* In English: "Once the protocol has stopped, the result channels close and
\* a waiting call returns ErrProtocolShuttingDown [G5]."
CallSeesDone ==
    /\ CloseOnDone
    /\ pstate = "Failed"
    /\ call /= "none"
    /\ call' = "none"
    /\ UNCHANGED <<chainEra, pstate, heldEra, cache, timer, stale, wrongEra, calls>>

\* In English: "With no call in progress and no more calls to make, or the
\* protocol stopped, the behaviour may end. A call left waiting is a
\* deadlock."
Finished ==
    /\ call = "none"
    /\ calls = MaxCalls \/ pstate = "Failed"
    /\ UNCHANGED vars

Next ==
    \/ EraAdvance
    \/ CallAcquire \/ CallRelease \/ CallEra
    \/ ServerAcquired \/ ServerFailure \/ ServerResult \/ OversizedResult
    \/ TimerFires
    \/ CallSeesDone
    \/ Finished

Spec == Init /\ [][Next]_vars

\* ---- Invariants ---------------------------------------------------------

TypeOK ==
    /\ chainEra \in 0..MaxEra
    /\ pstate \in {"StIdle", "StAcquiring", "StAcquired", "StQuerying", "Failed"}
    /\ heldEra \in {None} \cup (0..MaxEra)
    /\ cache \in {None} \cup (0..MaxEra)
    /\ call \in {"none", "acquire", "era", "implicit"}
    /\ timer \in {"none"} \cup PeerAgency
    /\ stale \in BOOLEAN /\ wrongEra \in BOOLEAN
    /\ calls \in 0..MaxCalls

\* In English: "A cached era is the era of the state the client holds now,
\* never one from before a release, a re-acquire or a failed re-acquire
\* [R1]."
\* Literally: "CachedEraIsHeldEra is defined as: if cache is not None, then
\*   heldEra is not None and cache equals heldEra."
CachedEraIsHeldEra == cache /= None => (heldEra /= None /\ cache = heldEra)

\* In English: "GetCurrentEra never returned another state's era."
\* Literally: "ErasReturnedFresh is defined as: wrongEra is false."
ErasReturnedFresh == ~wrongEra

\* In English: "A timeout only ever fires in the state it was armed for,
\* one where the node holds agency [G3]: the deadlines are ordered by the
\* transitions."
\* Literally: "NoStaleTimeout is defined as: stale is false, and if timer is
\*   not "none" then timer equals pstate."
NoStaleTimeout == ~stale /\ (timer /= "none" => timer = pstate)

\* In English: "With no timeouts and no oversized result, the protocol
\* never stops on an error, as the specification has neither [S1 2020]."
\* Literally: "NoFailures is defined as: pstate does not equal "Failed"."
NoFailures == pstate /= "Failed"

\* ---- Reachability probes (each must fail on the passing config) ---------

\* "The cache is never filled while the node's era has moved on."
ProbeNoCacheBehindChain == ~(cache /= None /\ cache < chainEra)
\* "An oversized result never stops a waiting call's protocol."
ProbeNoOversizeWhileWaiting == ~(pstate = "Failed" /\ call /= "none" /\ timer = "none" /\ ~stale)
=============================================================================
