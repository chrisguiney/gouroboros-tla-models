------------------------- MODULE BlockFetchRangeCheck -------------------------
(***************************************************************************)
(* Model `blockfetch`, slice 7: what the client accepts as the blocks of   *)
(* one requested range, and how a refused block retires the range while a  *)
(* range deadline races it.                                                *)
(*                                                                         *)
(* gOuroboros file: protocol/blockfetch/client.go (handleBlock,            *)
(* recordBlock, pointInRange, failRequest, handleBatchDone,                *)
(* watchRangeDeadline), at blinklabs-io/gouroboros 7cd17437.               *)
(*                                                                         *)
(* What the code does [G1]:                                                *)
(*   handleBlock takes queueMutex, checks the block belongs to the queue's *)
(*   head, takes the head's deliveryMu and releases queueMutex. It then    *)
(*   decodes the block and, under queueMutex again, recordBlock checks it: *)
(*   its slot is within the requested slots; the end point was not already *)
(*   received; the first block is the start point; a later block is not a  *)
(*   repeat of the previous one, not in an earlier slot, and names the     *)
(*   previous block as its parent. A refused block, or one that arrives    *)
(*   once the protocol is stopping, goes to failRequest, which retires the *)
(*   request only if it is still the head - still under deliveryMu - and   *)
(*   returns the error, which stops the protocol. An accepted block goes   *)
(*   to BlockFunc under deliveryMu. MsgBatchDone completes the range only  *)
(*   if the last block was the end point.                                 *)
(*   A range deadline takes the request out of the queue, stops the        *)
(*   protocol, and resolves the request under its deliveryMu.              *)
(*                                                                         *)
(* Questions: is what BlockFunc sees always a hash chain from the start    *)
(* point, within the range, ending no later than the end point, and is a   *)
(* range completed only once the end point arrived? Is the range resolved  *)
(* once, never while a block of it is being delivered, and never before a  *)
(* block of it is delivered?                                               *)
(*                                                                         *)
(* Sources (IntersectMBO/ouroboros-network 5f356486ab3e; README links):    *)
(*   [B1] docs/network-spec/miniprotocols.tex 1139-1204: a range is        *)
(*        inclusive, from a start point to an end point.                   *)
(*   [R4] ouroboros-network/lib/Ouroboros/Network/BlockFetch/Client.hs     *)
(*        295-299: too few or too many blocks abort the fetch; the         *)
(*        reference also checks each block against the header it expects, *)
(*        which gOuroboros does not have (see the README).                 *)
(*   gOuroboros 7cd17437:                                                  *)
(*   [G1] protocol/blockfetch/client.go: handleBlock 1621-1819,            *)
(*        pointInRange 1826-1834, recordBlock 1846-1906, failRequest       *)
(*        1911-1924, handleBatchDone 1927-1989, watchRangeDeadline         *)
(*        1295-1340.                                                       *)
(*                                                                         *)
(* The blocks: a chain a <- b <- c <- d, where b and c share a slot (a     *)
(* Byron epoch boundary block and the first block of the epoch), and a     *)
(* fork block x whose parent is a, in b's slot. The request is a..b, so c *)
(* follows the end point in the end point's own slot: only the "end point *)
(* already received" check refuses it.                                    *)
(* Hashes are the block names.                                             *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `hpc` and `dpc` are program counters.                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxBlocks,           \* MsgBlock the peer sends at most
    WithDeadline,        \* TRUE: the range deadline may fire
    \* Mutations, each FALSE in the code as it is:
    NoParentCheck,       \* recordBlock skips the previous-hash check
    NoBeyondEndCheck,    \* recordBlock accepts a block after the end point
    NoEndCheckAtDone,    \* MsgBatchDone completes the range whatever came
    DeadlineNoDeliveryMu \* the deadline resolves without taking deliveryMu

Blocks == {"a", "b", "c", "d", "x"}
\* Literally: "Slot is the function giving 1 to a, 2 to b, c and x, and 3
\*   to d."
Slot == [k \in Blocks |-> CASE k = "a" -> 1 [] k = "d" -> 3 [] OTHER -> 2]
\* Literally: "Parent is the function giving "g" (the block before a) to a,
\*   a to b and x, b to c, and c to d."
Parent == [k \in Blocks |->
             CASE k = "a" -> "g" [] k = "b" -> "a" [] k = "x" -> "a"
               [] k = "c" -> "b" [] OTHER -> "c"]
Start == "a"
End == "b"

VARIABLES
    queued,    \* the request is still in the client queue
    last,      \* recordBlock's lastPoint: a block, or "none"
    delivered, \* the blocks BlockFunc was given, in order
    sentN,     \* MsgBlock the peer has sent
    hpc,       \* the handler: "idle", "claimed" (holds deliveryMu, block
               \* in cur), "cb" (in BlockFunc), "failing", "exited"
    cur,       \* the block the handler is on
    dpc,       \* the deadline watcher: "armed", "wantMu", "done"
    dmu,       \* who holds the request's deliveryMu: "none", "h", "d"
    stopped,   \* the protocol is stopping
    outcome,   \* the request's resolution: "open", "ok", "err", "deadline"
    resolves,  \* how many times the request was resolved
    badOrder   \* TRUE once a resolve ran during, or a delivery after, the
               \* other

vars == <<queued, last, delivered, sentN, hpc, cur, dpc, dmu, stopped,
          outcome, resolves, badOrder>>

\* In English: "The range a..c is queued and has started; nothing arrived."
\* Literally: "Init is defined as: queued is TRUE, last is "none",
\*   delivered is empty, sentN is 0, hpc is "idle", cur is "none", dpc is
\*   "armed", dmu is "none", stopped is FALSE, outcome is "open", resolves
\*   is 0, and badOrder is FALSE."
Init ==
    /\ queued = TRUE /\ last = "none" /\ delivered = <<>> /\ sentN = 0
    /\ hpc = "idle" /\ cur = "none"
    /\ dpc = IF WithDeadline THEN "armed" ELSE "done"
    /\ dmu = "none" /\ stopped = FALSE
    /\ outcome = "open" /\ resolves = 0 /\ badOrder = FALSE

\* In English: "recordBlock accepts block k after last [G1 1846-1906]."
\* Literally: "Accepts(k) is defined as: Slot[k] is between Slot[Start] and
\*   Slot[End]; and last is not End (unless NoBeyondEndCheck); and if last
\*   is "none" then k equals Start, else k is not last, and Slot[k] is not
\*   less than Slot[last], and (NoParentCheck or Parent[k] equals last)."
Accepts(k) ==
    /\ Slot[Start] <= Slot[k] /\ Slot[k] <= Slot[End]
    /\ NoBeyondEndCheck \/ last /= End
    /\ IF last = "none"
          THEN k = Start
          ELSE /\ k /= last
               /\ Slot[k] >= Slot[last]
               /\ NoParentCheck \/ Parent[k] = last

\* In English: "Resolve the request with o, noting a resolve while its
\* block is being delivered."
\* Literally: "Resolve(o) is defined as: outcome' equals o, resolves' equals
\*   resolves plus 1, and badOrder' equals badOrder or hpc equals "cb"."
Resolve(o) ==
    /\ outcome' = o
    /\ resolves' = resolves + 1
    /\ badOrder' = (badOrder \/ hpc = "cb")

-----------------------------------------------------------------------------
(* The receive loop [G1 handleBlock, failRequest, handleBatchDone].        *)

\* In English: "MsgBlock k for the queued head: the handler takes its
\* deliveryMu (under queueMutex)."
\* Literally: "HClaim(k) is defined as: hpc equals "idle", stopped is false,
\*   sentN is less than MaxBlocks, queued is true, dmu equals "none", and
\*   hpc' equals "claimed", cur' equals k, dmu' equals "h", sentN' equals
\*   sentN plus 1, and the other variables are unchanged."
HClaim(k) ==
    /\ hpc = "idle" /\ ~stopped /\ sentN < MaxBlocks /\ queued
    /\ dmu = "none"
    /\ hpc' = "claimed" /\ cur' = k /\ dmu' = "h" /\ sentN' = sentN + 1
    /\ UNCHANGED <<queued, last, delivered, dpc, stopped, outcome, resolves,
                   badOrder>>

\* In English: "Under queueMutex, recordBlock checks the block; then the
\* StopChan check. Accepted on a live protocol, it goes to BlockFunc;
\* otherwise to failRequest."
\* Literally: "HCheck is defined as: hpc equals "claimed", and if
\*   Accepts(cur) then last' equals cur, and if stopped then hpc' equals
\*   "failing" and delivered is unchanged, else hpc' equals "cb" and
\*   delivered' is delivered with cur appended and badOrder' notes a
\*   delivery after a resolve; else hpc' equals "failing" and last is
\*   unchanged; and the other variables are unchanged."
HCheck ==
    /\ hpc = "claimed"
    /\ IF Accepts(cur)
          THEN /\ last' = cur
               /\ IF stopped
                     THEN /\ hpc' = "failing"
                          /\ UNCHANGED <<delivered, badOrder>>
                     ELSE /\ hpc' = "cb"
                          /\ delivered' = Append(delivered, cur)
                          /\ badOrder' = (badOrder \/ resolves > 0)
          ELSE /\ hpc' = "failing"
               /\ UNCHANGED <<last, delivered, badOrder>>
    /\ UNCHANGED <<queued, sentN, cur, dpc, dmu, stopped, outcome, resolves>>

\* In English: "BlockFunc returns; the handler releases deliveryMu."
\* Literally: "HCbEnd is defined as: hpc equals "cb", and hpc' equals
\*   "idle", and dmu' equals "none", and the other variables are unchanged."
HCbEnd ==
    /\ hpc = "cb"
    /\ hpc' = "idle" /\ dmu' = "none"
    /\ UNCHANGED <<queued, last, delivered, sentN, cur, dpc, stopped,
                   outcome, resolves, badOrder>>

\* In English: "failRequest, still under deliveryMu: if the request is
\* still the head, it is removed and resolved with the error. The handler's
\* error stops the protocol and the receive loop exits."
\* Literally: "HFail is defined as: hpc equals "failing", and if queued then
\*   queued' is FALSE and Resolve("err"), else queued, outcome, resolves and
\*   badOrder are unchanged; and hpc' equals "exited", dmu' equals "none",
\*   stopped' is TRUE, and the other variables are unchanged."
HFail ==
    /\ hpc = "failing"
    /\ IF queued
          THEN /\ queued' = FALSE
               /\ Resolve("err")
          ELSE UNCHANGED <<queued, outcome, resolves, badOrder>>
    /\ hpc' = "exited" /\ dmu' = "none" /\ stopped' = TRUE
    /\ UNCHANGED <<last, delivered, sentN, cur, dpc>>

\* In English: "MsgBatchDone for the queued head: complete if the last block
\* was the end point, otherwise failRequest. Either way the handler is done
\* with this range."
\* Literally: "HBatchDone is defined as: hpc equals "idle", stopped is
\*   false, queued is true, and queued' is FALSE, and if NoEndCheckAtDone or
\*   last equals End then Resolve("ok") and stopped is unchanged, else
\*   Resolve("err") and stopped' is TRUE; and hpc' equals "exited", and the
\*   other variables are unchanged."
HBatchDone ==
    /\ hpc = "idle" /\ ~stopped /\ queued
    /\ queued' = FALSE
    /\ IF NoEndCheckAtDone \/ last = End
          THEN /\ Resolve("ok") /\ UNCHANGED stopped
          ELSE /\ Resolve("err") /\ stopped' = TRUE
    /\ hpc' = "exited"
    /\ UNCHANGED <<last, delivered, sentN, cur, dpc, dmu>>

-----------------------------------------------------------------------------
(* The range deadline [G1 watchRangeDeadline].                             *)

\* In English: "The timer fires while the request is queued: under
\* queueMutex the watcher removes it, then stops the protocol."
\* Literally: "DFire is defined as: dpc equals "armed", queued is true, and
\*   queued' is FALSE, stopped' is TRUE, dpc' equals "wantMu", and the other
\*   variables are unchanged."
DFire ==
    /\ dpc = "armed" /\ queued
    /\ queued' = FALSE /\ stopped' = TRUE /\ dpc' = "wantMu"
    /\ UNCHANGED <<last, delivered, sentN, hpc, cur, dmu, outcome, resolves,
                   badOrder>>

\* In English: "The watcher takes deliveryMu (or, with the mutation, does
\* not), resolves the request with the deadline error, and releases it."
\* Literally: "DResolve is defined as: dpc equals "wantMu", and
\*   (DeadlineNoDeliveryMu or dmu equals "none"), and Resolve("deadline"),
\*   and dpc' equals "done", and the other variables are unchanged."
DResolve ==
    /\ dpc = "wantMu"
    /\ DeadlineNoDeliveryMu \/ dmu = "none"
    /\ Resolve("deadline")
    /\ dpc' = "done"
    /\ UNCHANGED <<queued, last, delivered, sentN, hpc, cur, dmu, stopped>>

\* In English: "The timer is stopped without firing: the request left the
\* queue some other way."
\* Literally: "DQuiet is defined as: dpc equals "armed", queued is false,
\*   dpc' equals "done", and the other variables are unchanged."
DQuiet ==
    /\ dpc = "armed" /\ ~queued
    /\ dpc' = "done"
    /\ UNCHANGED <<queued, last, delivered, sentN, hpc, cur, dmu, stopped,
                   outcome, resolves, badOrder>>

-----------------------------------------------------------------------------

\* In English: "Nothing left to do: the request is resolved, the handler is
\* not holding deliveryMu, and the watcher is done; or the peer sent all it
\* may and stays silent (a real deadline would end that)."
\* Literally: "Finished is defined as: dpc equals "done", and hpc is
\*   "idle" or "exited", and (outcome is not "open" or sentN equals
\*   MaxBlocks or stopped); and the variables are unchanged."
Finished ==
    /\ dpc = "done" /\ hpc \in {"idle", "exited"}
    /\ outcome /= "open" \/ sentN = MaxBlocks \/ stopped
    /\ UNCHANGED vars

\* Literally: "Next is defined as: some block k takes HClaim(k), or HCheck,
\*   HCbEnd, HFail, HBatchDone, DFire, DResolve or DQuiet is a step, or
\*   Finished."
Next ==
    \/ \E k \in Blocks : HClaim(k)
    \/ HCheck \/ HCbEnd \/ HFail \/ HBatchDone
    \/ DFire \/ DResolve \/ DQuiet
    \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "Each variable holds a value of the right kind."
TypeOK ==
    /\ queued \in BOOLEAN /\ last \in Blocks \cup {"none"}
    /\ hpc \in {"idle", "claimed", "cb", "failing", "exited"}
    /\ dpc \in {"armed", "wantMu", "done"} /\ dmu \in {"none", "h", "d"}
    /\ outcome \in {"open", "ok", "err", "deadline"}
    /\ resolves \in Nat

\* In English: "BlockFunc sees a hash chain that begins at the start point:
\* the first block is the start, each later one names the one before as its
\* parent."
\* Literally: "DeliveredIsChainFromStart is defined as: delivered is empty,
\*   or its first element is Start and, for every i in 2 through its length,
\*   Parent of element i equals element i minus 1."
DeliveredIsChainFromStart ==
    delivered = <<>> \/
    /\ delivered[1] = Start
    /\ \A i \in 2..Len(delivered) : Parent[delivered[i]] = delivered[i - 1]

\* In English: "Every block BlockFunc sees is within the requested slots,
\* and nothing comes after the end point."
\* Literally: "DeliveredWithinRange is defined as: for every i in 1 through
\*   the length of delivered, its slot is between Slot[Start] and
\*   Slot[End], and if it equals End then i is the length of delivered."
DeliveredWithinRange ==
    \A i \in 1..Len(delivered) :
        /\ Slot[Start] <= Slot[delivered[i]]
        /\ Slot[delivered[i]] <= Slot[End]
        /\ delivered[i] = End => i = Len(delivered)

\* In English: "A range completes only once the end point was delivered."
\* Literally: "CompleteOnlyAtEnd is defined as: if outcome equals "ok" then
\*   delivered is not empty and its last element is End."
CompleteOnlyAtEnd ==
    outcome = "ok" => delivered /= <<>> /\ delivered[Len(delivered)] = End

\* In English: "The range is resolved at most once."
\* Literally: "ResolvedOnce is defined as: resolves is at most 1."
ResolvedOnce == resolves <= 1

\* In English: "The range is never resolved while one of its blocks is in
\* BlockFunc, and no block of it is delivered after it was resolved."
\* Literally: "NoResolveDuringDelivery is defined as: badOrder is false."
NoResolveDuringDelivery == ~badOrder

\* Probes, each EXPECTED to be violated (reachability).
\* In English: "The whole range is never delivered." Violated = a range
\* completes.
\* Literally: "ProbeNeverComplete is defined as: outcome is not "ok"."
ProbeNeverComplete == outcome /= "ok"
\* In English: "failRequest never resolves." Violated = a refused block
\* retires the range.
\* Literally: "ProbeNeverFailed is defined as: not (outcome equals "err",
\*   and sentN is greater than 0, and hpc equals "exited")."
ProbeNeverFailed == ~(outcome = "err" /\ sentN > 0 /\ hpc = "exited")
\* In English: "The fork block is never delivered." Violated = it is (a
\* chain from the start the reference would refuse against its headers;
\* the range still fails at MsgBatchDone).
\* Literally: "ProbeForkNeverDelivered is defined as: x is not among the
\*   elements of delivered."
ProbeForkNeverDelivered == "x" \notin {delivered[i] : i \in 1..Len(delivered)}
=============================================================================
