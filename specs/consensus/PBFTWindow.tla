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
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla, and     *)
(* specs/consensus/ChainSelection.tla for \o, SubSeq and Cardinality.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    K,            \* the security parameter: the window holds k issuers [P1]
    T,            \* the threshold count, floor(threshold * k) [P1]
    Issuers,      \* the genesis issuers
    MaxSteps,     \* how many transitions the model takes (keeps it finite)
    AllowObserve, \* TRUE: Observe (append without the check) is used too
    Mutation      \* "none", or one changed line of pbft.go

\* In English: the larger of a and b.
\* Literally: "Max2 of a and b is defined as: if a is greater than or equal to b
\*   then a, else b."
Max2(a, b) == IF a >= b THEN a ELSE b

\* In English: how many times issuer i appears in list w.
\* Literally: "Occ of w and i is defined as the number of members of the set of
\*   every j in 1 through the length of w such that element j of w equals i."
Occ(w, i) == Cardinality({j \in 1..Len(w) : w[j] = i})

\* In English: every issuer's count in list w.
\* Literally: "Hist of w is defined as the function that maps every i in Issuers
\*   to Occ of w and i."
Hist(w) == [i \in Issuers |-> Occ(w, i)]

\* In English: the window that follows w when x is appended: drop the
\* oldest if w is already k long, then add x on the right [P2].
\* Literally: "RefNext of w and x is defined as: (if the length of w is greater
\*   than or equal to K then the tail of w, else w) followed by the tuple of x."
RefNext(w, x) == (IF Len(w) >= K THEN Tail(w) ELSE w) \o <<x>>

\* In English: the last min(len, k) entries of log e: the window of the
\* state that ends at the end of the log.
\* Literally: "NewestWindow of e is defined as the subsequence of e from Max2 of
\*   1 and (the length of e minus K plus 1) through the length of e."
NewestWindow(e) == SubSeq(e, Max2(1, Len(e) - K + 1), Len(e))

VARIABLES
    logs,      \* log id -> [entries, hasCounts, counts, cap]: the shared logs
    nLogs,     \* how many logs exist
    handed,    \* every state handed out: [log, start, end, win], win the reference window
    lastAgree, \* did gOuroboros accept or refuse the last step as the reference does?
    steps      \* transitions taken

\* Literally: "vars is defined as the tuple of logs, nLogs, handed, lastAgree
\*   and steps."
vars == <<logs, nLogs, handed, lastAgree, steps>>

\* In English: the ids of the logs that exist.
\* Literally: "LogIds is defined as 1 through nLogs."
LogIds == 1..nLogs

\* In English: a log holds entries, an optional cached count per issuer, and
\* a capacity; reaching it forces the next extension to copy.
\* Literally: "NewLog of window is defined as the record whose field entries is
\*   window, whose field hasCounts is FALSE, whose field counts is the function
\*   that maps every i in Issuers to 0, and whose field cap is Max2 of the
\*   length of window and 2 times K."
NewLog(window) ==
    [entries |-> window, hasCounts |-> FALSE,
     counts |-> [i \in Issuers |-> 0], cap |-> Max2(Len(window), 2 * K)]

\* In English: every variable holds a value of the expected kind.
\* Literally: "TypeOK is defined as: nLogs is a member of Nat, and for all l in
\*   LogIds, logs of l's entries is a member of the set of sequences of members
\*   of Issuers, and for all s in handed, s's log is a member of LogIds and s's
\*   start is less than or equal to s's end, and lastAgree is a member of
\*   BOOLEAN, and steps is a member of 0 through MaxSteps."
TypeOK ==
    /\ nLogs \in Nat
    /\ \A l \in LogIds : logs[l].entries \in Seq(Issuers)
    /\ \A s \in handed : s.log \in LogIds /\ s.start <= s.end
    /\ lastAgree \in BOOLEAN
    /\ steps \in 0..MaxSteps

\* In English: NewPBFTState(nil, k): one empty log and the empty state.
\* Literally: "Init is defined as: logs equals the function that maps every l in
\*   the set containing 1 to NewLog of the empty sequence, and nLogs equals 1,
\*   and handed equals the set containing the record whose field log is 1, field
\*   start is 0, field end is 0 and field win is the empty sequence, and
\*   lastAgree equals TRUE, and steps equals 0."
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
\* Literally: "Step of s, x and check is defined as: letting L be logs of s's
\*   log; win be the subsequence of L's entries from s's start plus 1 through
\*   s's end; full be s's end minus s's start is greater than or equal to K;
\*   extends be s's end equals the length of L's entries; cached be: if L's
\*   hasCounts then L's counts, else Hist of win; dropped be full and element 1
\*   of win equals x; others be: if extends then cached of x minus (if dropped
\*   then 1, else 0), else Occ of (if full then the tail of win, else win) and
\*   x; count be others plus (if Mutation equals "NoPlusOne" then 0, else 1); ok
\*   be check is not true or count is less than or equal to T; refWin be RefNext
\*   of s's win and x; refOk be check is not true or Occ of refWin and x is less
\*   than or equal to T; L1 be: if check and extends and L's hasCounts is not
\*   true then L except that its hasCounts is TRUE and its counts is Hist of
\*   win, else L; inPlace be (extends or Mutation equals "AlwaysInPlace") and
\*   the length of L1's entries is less than L1's cap; counts2 be the function
\*   that maps every i in Issuers to L1's counts of i minus (if full and element
\*   1 of win equals i and Mutation does not equal "NoDecrement" then 1, else 0)
\*   plus (if i equals x then 1, else 0); L2 be L1 except that its entries is
\*   L1's entries with x appended and its counts is: if L1's hasCounts then
\*   counts2, else L1's counts; trimmed be: if full then the tail of win, else
\*   win; fresh be NewLog of trimmed; copied be fresh except that its entries is
\*   trimmed with x appended: steps is less than MaxSteps, and steps in the next
\*   state equals steps plus 1, and lastAgree in the next state equals (ok
\*   equals refOk), and if ok is not true then (logs in the next state equals
\*   logs except that its s's log entry is L1, and nLogs and handed are
\*   unchanged), else if inPlace then (logs in the next state equals logs except
\*   that its s's log entry is L2, and handed in the next state equals the union
\*   of handed and the set containing the record whose field log is s's log,
\*   field start is s's start plus (if full then 1, else 0), field end is s's
\*   end plus 1, and field win is refWin, and nLogs is unchanged), else (nLogs
\*   in the next state equals nLogs plus 1, and logs in the next state equals
\*   the function that maps every l in 1 through (nLogs plus 1) to: if l equals
\*   nLogs plus 1 then copied, else if l equals s's log then L1, else logs of l;
\*   and handed in the next state equals the union of handed and the set
\*   containing the record whose field log is nLogs plus 1, field start is 0,
\*   field end is the length of copied's entries, and field win is refWin)."
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
\* Literally: "Next is defined as: there exists an s in handed and an x in
\*   Issuers such that Step of s, x and TRUE; or AllowObserve and there exists
\*   an s in handed and an x in Issuers such that Step of s, x and FALSE; or
\*   steps equals MaxSteps and vars is unchanged."
Next ==
    \/ \E s \in handed, x \in Issuers : Step(s, x, TRUE)
    \/ AllowObserve /\ \E s \in handed, x \in Issuers : Step(s, x, FALSE)
    \/ steps = MaxSteps /\ UNCHANGED vars   \* done: an explicit end, not a deadlock

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* What must always be true.                                               *)
(***************************************************************************)

\* In English: every state's window still reads as the reference window it
\* was handed out with: no later step changed it.
\* Literally: "WindowsMatch is defined as: for all s in handed, the subsequence
\*   of logs of s's log's entries from s's start plus 1 through s's end equals
\*   s's win."
WindowsMatch ==
    \A s \in handed : SubSeq(logs[s.log].entries, s.start + 1, s.end) = s.win

\* In English: a cached count is the count of the log's newest window.
\* Literally: "CountsCacheCorrect is defined as: for all l in LogIds, if logs of
\*   l's hasCounts, then logs of l's counts equals Hist of NewestWindow of logs
\*   of l's entries."
CountsCacheCorrect ==
    \A l \in LogIds :
        logs[l].hasCounts => logs[l].counts = Hist(NewestWindow(logs[l].entries))

\* In English: gOuroboros accepts and refuses exactly what the reference does.
\* Literally: "AgreesWithReference is defined as lastAgree."
AgreesWithReference == lastAgree

\* In English: with Transition only, no window ever holds an issuer more
\* than T times [P1].
\* Literally: "ThresholdHolds is defined as: for all s in handed and all i in
\*   Issuers, Occ of s's win and i is less than or equal to T."
ThresholdHolds == \A s \in handed, i \in Issuers : Occ(s.win, i) <= T

\* In English: windows never exceed k [P2].
\* Literally: "WindowBounded is defined as: for all s in handed, the length of
\*   s's win is less than or equal to K."
WindowBounded == \A s \in handed : Len(s.win) <= K

(***************************************************************************)
(* Reachability probes (expected to be violated).                          *)
(***************************************************************************)

\* Probe: no state is ever extended by copying into a new log.
\* Literally: "NeverCopies is defined as: nLogs equals 1."
NeverCopies == nLogs = 1

\* Probe: no window ever reaches the threshold exactly.
\* Literally: "NeverAtThreshold is defined as: for all s in handed and all i in
\*   Issuers, Occ of s's win and i is less than T."
NeverAtThreshold == \A s \in handed, i \in Issuers : Occ(s.win, i) < T

\* Probe: no log ever fills to its capacity, so the next in-place
\* extension would have to copy.
\* Literally: "NeverAtCapacity is defined as: for all l in LogIds, the length of
\*   logs of l's entries is less than logs of l's cap."
NeverAtCapacity == \A l \in LogIds : Len(logs[l].entries) < logs[l].cap

\* Probe: no window ever fills to k, so the oldest entry never drops.
\* Literally: "NeverFull is defined as: for all s in handed, the length of s's
\*   win is less than K."
NeverFull == \A s \in handed : Len(s.win) < K
=============================================================================
