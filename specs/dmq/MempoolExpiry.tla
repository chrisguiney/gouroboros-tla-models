---------------------------- MODULE MempoolExpiry ----------------------------
(***************************************************************************)
(* When a held DMQ message expires. dmq-node's mempool worker drops a     *)
(* message once expiresAt <= now, with now at the clock's full precision. *)
(* gOuroboros prunes its local notification queue with                    *)
(* DmqMessage.IsValidAt, which must keep a message exactly while the      *)
(* reference's mempool does.                                               *)
(*                                                                         *)
(* Sources.                                                                *)
(*   Reference: dmq-node a267003c14e9                                     *)
(*   [R1] src/DMQ/NodeKernel.hs 313-330: the mempool worker removes every *)
(*        message with expiresAt <= now; now is a POSIXTime, sub-second.  *)
(*   [R2] src/DMQ/Protocol/SigSubmission/Validate.hs 115-122: admission   *)
(*        refuses only now > expiresAt, so a message arriving exactly at  *)
(*        its expiry is admitted and then dropped by [R1].                *)
(*   gOuroboros:                                                           *)
(*   [G1] protocol/common/dmq.go DmqMessage.IsValidAt: main keeps a       *)
(*        message while uint32(t.Unix()) <= expiresAt, so t is truncated  *)
(*        to whole seconds and the expiry instant itself still counts.    *)
(*   [G2] protocol/localmessagenotification/server.go 327: messages for  *)
(*        which IsValidAt(now) is false are pruned.                       *)
(*                                                                         *)
(* Time is counted in half-second ticks so that now can fall between two  *)
(* whole seconds. Expiry times are whole seconds.                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Exps,      \* expiry times, in whole seconds
    MaxTicks,  \* the last tick the clock reaches (keeps the model finite)
    Mutation   \* "none" (the fixed IsValidAt), or how gOuroboros differs:
               \*  "Main": main today, truncated and inclusive [G1];
               \*  "Truncate": truncated, strict (an equivalent mutant:
               \*    with whole-second expiries it holds exactly what the
               \*    reference holds, so it has no Bug configuration);
               \*  "Inclusive": full precision, inclusive

VARIABLES
    now,   \* the clock, in half-second ticks
    held   \* expiry times of the messages gOuroboros still holds

vars == <<now, held>>

\* In English: the reference holds a message expiring at e (whole seconds)
\* while now is strictly before it [R1].
\* Literally: "RefHeld of t and e is defined as: t is less than 2 times e."
RefHeld(t, e) == t < 2 * e

\* In English: IsValidAt in gOuroboros, by Mutation [G1].
\* Literally: "GoHeld of t and e is defined as: letting secs be 2 times (t
\*   divided by 2, rounded down): in the case Mutation equals "Main", secs is
\*   at most 2 times e; in the case "Truncate", secs is less than 2 times e;
\*   in the case "Inclusive", t is at most 2 times e; otherwise t is less than
\*   2 times e."
GoHeld(t, e) ==
    LET secs == 2 * (t \div 2)
    IN CASE Mutation = "Main"      -> secs <= 2 * e
         [] Mutation = "Truncate"  -> secs < 2 * e
         [] Mutation = "Inclusive" -> t <= 2 * e
         [] OTHER                  -> t < 2 * e

\* In English: admission [R2] accepts a message that has not passed its
\* expiry, the expiry instant included.
\* Literally: "Admitted of t and e is defined as: t is at most 2 times e."
Admitted(t, e) == t <= 2 * e

\* In English: every message is admitted at 0 and pruned at once if
\* IsValidAt no longer keeps it.
\* Literally: "Init is defined as: now equals 0 and held is the set of every
\*   e in Exps admitted at 0 for which GoHeld of 0 and e."
Init ==
    /\ now = 0
    /\ held = {e \in Exps : Admitted(0, e) /\ GoHeld(0, e)}

\* In English: the clock moves on half a second and gOuroboros prunes what
\* IsValidAt no longer keeps [G2].
\* Literally: "Tick is defined as: now is less than MaxTicks; now in the next
\*   state is now plus 1; and held in the next state is the set of every e in
\*   held for which GoHeld of now plus 1 and e."
Tick ==
    /\ now < MaxTicks
    /\ now' = now + 1
    /\ held' = {e \in held : GoHeld(now + 1, e)}

\* Literally: "Done is defined as: now equals MaxTicks and nothing changes."
Done == now = MaxTicks /\ UNCHANGED vars

Next == Tick \/ Done

Spec == Init /\ [][Next]_vars

\* In English: gOuroboros holds exactly the messages the reference's mempool
\* holds.
\* Literally: "HeldAsReference is defined as: held equals the set of every e
\*   in Exps admitted at 0 for which RefHeld of now and e."
HeldAsReference == held = {e \in Exps : Admitted(0, e) /\ RefHeld(now, e)}

\* Probe, expected to be violated: a message expires while the clock is
\* between two whole seconds.
\* Literally: "ProbeHalfSecond is defined as: no e in Exps has 2 times e
\*   less than now and now odd."
ProbeHalfSecond == ~\E e \in Exps : 2 * e < now /\ now % 2 = 1
=============================================================================
