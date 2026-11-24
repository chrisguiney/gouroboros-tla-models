----------------------------- MODULE PBFTWindow -----------------------------
(***************************************************************************)
(* Byron PBFT's signature window: each regular block charges its genesis  *)
(* issuer, the state keeps the issuers of the last k blocks, and a block  *)
(* is refused when its issuer would then appear more than T times.        *)
(*                                                                         *)
(* gOuroboros keeps this window as an immutable value backed by a shared, *)
(* append-only log with a cached per-issuer count, so that extending the  *)
(* newest state costs the same at any k. Rollback extends an older state, *)
(* which must copy instead. The model asks whether that sharing ever      *)
(* changes a state already handed out, or the answer it gives, compared   *)
(* with the reference's plain window.                                     *)
(*                                                                         *)
(* Sources (README.md has links). ouroboros-consensus commit ec239d57.    *)
(*   [P1] ouroboros-consensus/.../Protocol/PBFT.hs 378-388: look up the   *)
(*        genesis key, append (slot, key), refuse if it now exceeds the   *)
(*        threshold. 428-444: window size k; threshold                    *)
(*        floor(signatureThreshold * k). 449-460: refused when the count  *)
(*        is GREATER than the threshold.                                  *)
(*   [P2] ouroboros-consensus/.../Protocol/PBFT/State.hs 212-233: append  *)
(*        to the right, then drop the oldest when the window was already  *)
(*        k long.                                                         *)
(*                                                                         *)
(* gOuroboros: consensus/byron/pbft.go (PBFTState, Transition, Observe,   *)
(* nextIssuerCountLocked, advanceLocked, advance, newPBFTLog).            *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/01-keepalive/KeepAlive.tla, and     *)
(* specs/13-consensus/ChainSelection.tla for \o, SubSeq and Cardinality.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    K,            \* the security parameter: the window holds k issuers [P1]
    T,            \* the threshold count, floor(threshold * k) [P1]
    Issuers,      \* the genesis issuers
    MaxSteps,     \* how many transitions the model takes (keeps it finite)
    AllowObserve, \* TRUE: Observe (append without the check) is used too
    Mutation      \* "none", or one changed line of pbft.go

Max2(a, b) == IF a >= b THEN a ELSE b

\* In English: how many times issuer i appears in list w.
Occ(w, i) == Cardinality({j \in 1..Len(w) : w[j] = i})

\* In English: every issuer's count in list w.
Hist(w) == [i \in Issuers |-> Occ(w, i)]

\* In English: the window that follows w when x is appended: drop the
\* oldest if w is already k long, then add x on the right [P2].
RefNext(w, x) == (IF Len(w) >= K THEN Tail(w) ELSE w) \o <<x>>

\* In English: the last min(len, k) entries of log e: the window of the
\* state that ends at the end of the log.
NewestWindow(e) == SubSeq(e, Max2(1, Len(e) - K + 1), Len(e))

VARIABLES
    logs,      \* log id -> [entries, hasCounts, counts, cap]: the shared logs
    nLogs,     \* how many logs exist
    handed,    \* every state handed out: [log, start, end, win], win the reference window
    lastAgree, \* did gOuroboros accept or refuse the last step as the reference does?
    steps      \* transitions taken

vars == <<logs, nLogs, handed, lastAgree, steps>>

LogIds == 1..nLogs

\* In English: a log holds entries, an optional cached count per issuer, and
\* a capacity; reaching it forces the next extension to copy.
NewLog(window) ==
    [entries |-> window, hasCounts |-> FALSE,
     counts |-> [i \in Issuers |-> 0], cap |-> Max2(Len(window), 2 * K)]

TypeOK ==
    /\ nLogs \in Nat
    /\ \A l \in LogIds : logs[l].entries \in Seq(Issuers)
    /\ \A s \in handed : s.log \in LogIds /\ s.start <= s.end
    /\ lastAgree \in BOOLEAN
    /\ steps \in 0..MaxSteps

\* In English: NewPBFTState(nil, k): one empty log and the empty state.
Init ==
    /\ logs = [l \in {1} |-> NewLog(<<>>)]
    /\ nLogs = 1
    /\ handed = {[log |-> 1, start |-> 0, end |-> 0, win |-> <<>>]}
    /\ lastAgree = TRUE
    /\ steps = 0

\* In English: append x to state s, checking the threshold when check is
\* TRUE (Transition) and not when FALSE (Observe). This follows pbft.go line
\* by line: count the issuer (nextIssuerCountLocked), then extend in place
\* when s is the log's newest state and the log has room (advanceLocked),
\* or copy its window into a new log (advance).
Step(s, x, check) ==
    LET L        == logs[s.log]
        win      == SubSeq(L.entries, s.start + 1, s.end)
        full     == s.end - s.start >= K
        extends  == s.end = Len(L.entries)                 \* extendsLog
        cached   == IF L.hasCounts THEN L.counts ELSE Hist(win)  \* countsLocked
        dropped  == full /\ win[1] = x
        others   == IF extends
                    THEN cached[x] - (IF dropped THEN 1 ELSE 0)
                    ELSE Occ(IF full THEN Tail(win) ELSE win, x)
        count    == others + (IF Mutation = "NoPlusOne" THEN 0 ELSE 1)
        ok       == ~check \/ count <= T                   \* refused when count > T
        refWin   == RefNext(s.win, x)
        refOk    == ~check \/ Occ(refWin, x) <= T
        \* countsLocked caches the counts as a side effect, even on refusal.
        L1       == IF check /\ extends /\ ~L.hasCounts
                    THEN [L EXCEPT !.hasCounts = TRUE, !.counts = Hist(win)]
                    ELSE L
        inPlace  == /\ extends \/ Mutation = "AlwaysInPlace"
                    /\ Len(L1.entries) < L1.cap
        counts2  == [i \in Issuers |->
                        L1.counts[i]
                        - (IF full /\ win[1] = i /\ Mutation # "NoDecrement" THEN 1 ELSE 0)
                        + (IF i = x THEN 1 ELSE 0)]
        L2       == [L1 EXCEPT !.entries = Append(L1.entries, x),
                               !.counts  = IF L1.hasCounts THEN counts2 ELSE L1.counts]
        trimmed  == IF full THEN Tail(win) ELSE win
        fresh    == NewLog(trimmed)
        copied   == [fresh EXCEPT !.entries = Append(trimmed, x)]
    IN  /\ steps < MaxSteps
        /\ steps' = steps + 1
        /\ lastAgree' = (ok = refOk)
        /\ IF ~ok
           THEN /\ logs' = [logs EXCEPT ![s.log] = L1]       \* refused: only the cache
                /\ UNCHANGED <<nLogs, handed>>
           ELSE IF inPlace
           THEN /\ logs' = [logs EXCEPT ![s.log] = L2]       \* extend in place
                /\ handed' = handed \cup
                     {[log |-> s.log, start |-> s.start + (IF full THEN 1 ELSE 0),
                       end |-> s.end + 1, win |-> refWin]}
                /\ UNCHANGED nLogs
           ELSE /\ nLogs' = nLogs + 1                        \* copy into a new log
                /\ logs' = [l \in 1..(nLogs + 1) |->
                              IF l = nLogs + 1 THEN copied
                              ELSE IF l = s.log THEN L1 ELSE logs[l]]
                /\ handed' = handed \cup
                     {[log |-> nLogs + 1, start |-> 0,
                       end |-> Len(copied.entries), win |-> refWin]}

\* In English: any state handed out so far is extended by any issuer, as
\* block application (the newest state) or a rollback (an older one) does.
Next ==
    \/ \E s \in handed, x \in Issuers : Step(s, x, TRUE)
    \/ AllowObserve /\ \E s \in handed, x \in Issuers : Step(s, x, FALSE)
    \/ steps = MaxSteps /\ UNCHANGED vars   \* done: an explicit end, not a deadlock

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* What must always be true.                                               *)
(***************************************************************************)

\* In English: every state's window still reads as the reference window it
\* was handed out with: no later step changed it.
WindowsMatch ==
    \A s \in handed : SubSeq(logs[s.log].entries, s.start + 1, s.end) = s.win

\* In English: a cached count is the count of the log's newest window.
CountsCacheCorrect ==
    \A l \in LogIds :
        logs[l].hasCounts => logs[l].counts = Hist(NewestWindow(logs[l].entries))

\* In English: gOuroboros accepts and refuses exactly what the reference does.
AgreesWithReference == lastAgree

\* In English: with Transition only, no window ever holds an issuer more
\* than T times [P1].
ThresholdHolds == \A s \in handed, i \in Issuers : Occ(s.win, i) <= T

\* In English: windows never exceed k [P2].
WindowBounded == \A s \in handed : Len(s.win) <= K

(***************************************************************************)
(* Reachability probes (expected to be violated).                          *)
(***************************************************************************)

\* Probe: no state is ever extended by copying into a new log.
NeverCopies == nLogs = 1

\* Probe: no window ever reaches the threshold exactly.
NeverAtThreshold == \A s \in handed, i \in Issuers : Occ(s.win, i) < T

\* Probe: no log ever fills to its capacity, so the next in-place
\* extension would have to copy.
NeverAtCapacity == \A l \in LogIds : Len(logs[l].entries) < logs[l].cap

\* Probe: no window ever fills to k, so the oldest entry never drops.
NeverFull == \A s \in handed : Len(s.win) < K
=============================================================================
