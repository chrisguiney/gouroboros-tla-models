----------------------- MODULE BlockFetchClientReader -----------------------
(***************************************************************************)
(* A block-fetch client's one-at-a-time fetch while Start replaces the     *)
(* stopped client's protocol instance (protocol/blockfetch/client.go:       *)
(* GetBlockRange, GetBlock, sendRequestRange, Start/initProtocol,          *)
(* ProtocolInstance).                                                      *)
(*                                                                         *)
(* A fetch logs through the instance, reads the instance's done channel,   *)
(* and sends its request through sendRequestRange, which reads the         *)
(* instance under protocolMu. It then waits for the batch to start, or for *)
(* the done channel it read.                                               *)
(*   main:  the log and the done channel come from the embedded field      *)
(*          `c.Protocol`, read with no lock, before the request is sent.   *)
(*          A read during Start's write is a data race (hazard B4), and a  *)
(*          read before a restart watches the old instance while the       *)
(*          request goes out on the new one.                               *)
(*   fix:   the log reads ProtocolInstance() under protocolMu, and the     *)
(*          fetch watches `req.protocol.DoneChan()`, the instance its      *)
(*          request went out on.                                           *)
(*                                                                         *)
(* As in the Go test, the client has been started and stopped once, and    *)
(* Start installs a second instance while the fetch runs; the test then    *)
(* stops the client again.                                                 *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `fetch` and `start` are program counters.                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Fixed       \* TRUE: fix/blockfetch-client-protocol-race; FALSE: main

\* The instances: the first (started and stopped), and the one Start installs.
\* Literally: "Instances is defined as the set 1 through 2."
Instances == 1..2

VARIABLES
    current,    \* the instance c.Protocol points at
    start,      \* Start: "idle", "installing" (holds protocolMu), "done"
    stopped,    \* the set of stopped instances
    fetch,      \* "log", "readDone", "send", "wait", "ok", "err"
    watched,    \* the instance whose done channel the fetch waits on, 0 for none
    sentOn,     \* the instance the request went out on, 0 for none
    racedRead   \* the fetch read c.Protocol while Start was writing it

\* In English: "all the variables."
\* Literally: "vars is defined as the tuple of all seven variables."
vars == <<current, start, stopped, fetch, watched, sentOn, racedRead>>

\* In English: "Instance 1 was started and stopped; the fetch is about to
\* log its call."
\* Literally: "Init is defined as: current equals 1, start equals "idle",
\*   stopped equals the set containing 1, fetch equals "log", watched and
\*   sentOn equal 0, and racedRead is false."
Init ==
    /\ current = 1
    /\ start = "idle"
    /\ stopped = {1}
    /\ fetch = "log"
    /\ watched = 0
    /\ sentOn = 0
    /\ racedRead = FALSE

\* In English: "Start takes protocolMu and installs instance 2."
\* Literally: "StartInstall is defined as: start equals "idle", start
\*   becomes "installing", and current becomes 2."
StartInstall ==
    /\ start = "idle"
    /\ start' = "installing"
    /\ current' = 2                               \* initProtocol: c.Protocol = p
    /\ UNCHANGED <<stopped, fetch, watched, sentOn, racedRead>>

\* In English: "Start releases protocolMu; instance 2 runs."
\* Literally: "StartUnlock is defined as: start equals "installing", and
\*   start becomes "done"."
StartUnlock ==
    /\ start = "installing"
    /\ start' = "done"
    /\ UNCHANGED <<current, stopped, fetch, watched, sentOn, racedRead>>

\* In English: "The test stops the client again once Start is done."
\* Literally: "StopAgain is defined as: start equals "done", 2 is not in
\*   stopped, and stopped gains 2."
StopAgain ==
    /\ start = "done" /\ 2 \notin stopped
    /\ stopped' = stopped \cup {2}
    /\ UNCHANGED <<current, start, fetch, watched, sentOn, racedRead>>

\* In English: "The fetch logs its call through the instance: on main the
\* field, unlocked; with the fix ProtocolInstance(), which waits for
\* protocolMu."
\* Literally: "Log is defined as: fetch equals "log", and (not Fixed or start
\*   is not "installing"), and fetch becomes "readDone" on main or "send"
\*   with the fix, and racedRead becomes (not Fixed and start equals
\*   "installing")."
Log ==
    /\ fetch = "log"
    /\ ~Fixed \/ start # "installing"
    /\ fetch' = IF Fixed THEN "send" ELSE "readDone"
    /\ racedRead' = (racedRead \/ (~Fixed /\ start = "installing"))
    /\ UNCHANGED <<current, start, stopped, watched, sentOn>>

\* In English: "Main only: the fetch reads c.DoneChan() through the
\* unlocked field, before sending."
\* Literally: "ReadDone is defined as: fetch equals "readDone", fetch
\*   becomes "send", watched becomes current, and racedRead becomes true if
\*   start equals "installing"."
ReadDone ==
    /\ fetch = "readDone"
    /\ fetch' = "send"
    /\ watched' = current
    /\ racedRead' = (racedRead \/ start = "installing")
    /\ UNCHANGED <<current, start, stopped, sentOn>>

\* In English: "sendRequestRange reads the instance under protocolMu and
\* sends on it; on a stopped instance it fails. With the fix the fetch then
\* watches that instance's done channel."
\* Literally: "Send is defined as: fetch equals "send", start is not
\*   "installing", and if current is in stopped then fetch becomes "err"
\*   with sentOn and watched unchanged, else sentOn becomes current, fetch
\*   becomes "wait", and watched becomes current with the fix and is
\*   unchanged on main."
Send ==
    /\ fetch = "send"
    /\ start # "installing"                       \* protocolAndGoroutines takes protocolMu
    /\ IF current \in stopped
         THEN /\ fetch' = "err" /\ UNCHANGED <<sentOn, watched>>
         ELSE /\ sentOn' = current
              /\ fetch' = "wait"
              /\ watched' = IF Fixed THEN current ELSE watched  \* req.protocol.DoneChan()
    /\ UNCHANGED <<current, start, stopped, racedRead>>

\* In English: "The wait ends when the watched instance is done: the fetch
\* returns ErrProtocolShuttingDown. (The peer in the test never starts a
\* batch.)"
\* Literally: "WaitEnds is defined as: fetch equals "wait", watched is in
\*   stopped, and fetch becomes "err"."
WaitEnds ==
    /\ fetch = "wait" /\ watched \in stopped
    /\ fetch' = "err"
    /\ UNCHANGED <<current, start, stopped, watched, sentOn, racedRead>>

\* In English: "any step."
\* Literally: "Progress is defined as: StartInstall, or StartUnlock, or
\*   StopAgain, or Log, or ReadDone, or Send, or WaitEnds."
Progress ==
    \/ StartInstall \/ StartUnlock \/ StopAgain
    \/ Log \/ ReadDone \/ Send \/ WaitEnds

\* In English: "Once nothing can move, nothing changes."
\* Literally: "Rest is defined as: Progress is not enabled, and vars is
\*   unchanged."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is any step, or resting once none can move."
\* Literally: "Next is defined as: Progress or Rest."
Next == Progress \/ Rest

\* In English: "start in Init; every later step is a Next step."
\* Literally: "Spec is defined as: Init, and always every step is a Next
\*   step or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "The fetch never reads c.Protocol while Start writes it."
\* Literally: "NoRacingRead is defined as: racedRead is false."
NoRacingRead == ~racedRead

\* In English: "A waiting fetch watches the instance its request went out
\* on: it ends exactly when that request can no longer be answered." The
\* reference ties each request to the one protocol run that carries it
\* (ouroboros-network BlockFetch client: one peer, one protocol thread).
\* Literally: "WatchesOwnInstance is defined as: if fetch equals "wait" then
\*   watched equals sentOn."
WatchesOwnInstance == fetch = "wait" => watched = sentOn

\* In English: "Once nothing can move, the fetch has returned." A fetch
\* waiting on an instance that is never stopped would hang.
\* Literally: "FetchReturns is defined as: if Progress is not enabled then
\*   fetch is "ok" or "err"."
FetchReturns == ~ENABLED Progress => fetch \in {"ok", "err"}

\* In English: "Each variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: current is in Instances, watched and
\*   sentOn are in 0 through 2, stopped is a subset of Instances, and
\*   racedRead is a boolean."
TypeOK ==
    /\ current \in Instances
    /\ watched \in 0..2 /\ sentOn \in 0..2
    /\ stopped \subseteq Instances
    /\ racedRead \in BOOLEAN
=============================================================================
