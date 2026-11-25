------------------------- MODULE EngineIngressOwner -------------------------
(***************************************************************************)
(* Who may change the muxer's ingress settings for a protocol role once    *)
(* the instance that registered it has stopped (protocol/protocol.go:       *)
(* ensureRegistered, stop, applyIngressLimitLocked; protocol/blockfetch/    *)
(* client.go: Stop, takeOutstandingForProtocol, updateIngressAllowanceLocked).*)
(*                                                                         *)
(* The muxer keys a role's ingress limit, budget extension and             *)
(* backpressure by (protocol ID, role), not by instance. A block-fetch     *)
(* client's Stop releases its lifecycle lock before it resolves the old    *)
(* instance's requests, so a Start can register a successor for the same   *)
(* key and raise its allowance first. Resolving the old requests then      *)
(* recomputes the old instance's allowance, which is zero.                 *)
(*   before: the old instance stays `registered` after it stops, so its    *)
(*           update writes the shared key and resets the successor's       *)
(*           allowance and backpressure.                                   *)
(*   fix:    stop clears `registered` under ingressMu, so a stopped        *)
(*           instance's ingress updates no longer reach the muxer.         *)
(*                                                                         *)
(* Granularity: each action is one locked step. Unregistering the old      *)
(* role and the successor's registration both reset the key to its base   *)
(* limit; raising the allowance is one step.                               *)
(*                                                                         *)
(* SOURCES                                                                 *)
(*   UNSOURCED: ownership of a role's ingress settings is gOuroboros's own  *)
(*   rule. The reference mux sizes each mini-protocol's ingress queue once  *)
(*   (ouroboros-network `Network.Mux` `MiniProtocolLimits`) and has no      *)
(*   setting an instance changes at run time.                              *)
(*                                                                         *)
(* HOW TO READ IT                                                          *)
(*   Symbols are read as in the README's "Reading a formula literally"     *)
(*   table. `old` and `next` are program counters.                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Fixed       \* TRUE: stop clears registered; FALSE: before the fix

VARIABLES
    old,        \* old instance: "running", "stopped", "cleaned"
    oldReg,     \* the old instance's registered flag
    next,       \* successor: "none", "registered", "soliciting"
    limit       \* the muxer's setting for the key: "base" or "raised"

\* In English: "all the variables."
\* Literally: "vars is defined as the tuple of the four variables."
vars == <<old, oldReg, next, limit>>

\* In English: "The old instance is registered, has raised its allowance
\* for a range it requested, and no successor exists yet."
\* Literally: "Init is defined as: old equals "running", oldReg is true,
\*   next equals "none", and limit equals "raised"."
Init ==
    /\ old = "running"
    /\ oldReg = TRUE
    /\ next = "none"
    /\ limit = "raised"

\* In English: "Stop stops the old instance and unregisters its role, which
\* drops the key's settings. With the fix it also clears registered."
\* Literally: "OldStop is defined as: old equals "running", old becomes
\*   "stopped", oldReg becomes (not Fixed), and limit becomes "base"."
OldStop ==
    /\ old = "running"
    /\ old' = "stopped"
    /\ oldReg' = ~Fixed                         \* fix: registered = false
    /\ limit' = "base"                          \* UnregisterProtocol
    /\ UNCHANGED next

\* In English: "Once Stop has released the lifecycle lock, Start registers a
\* successor for the same key, at the base limit."
\* Literally: "NextRegister is defined as: old is not "running", next
\*   equals "none", next becomes "registered", and limit becomes "base"."
NextRegister ==
    /\ old # "running" /\ next = "none"
    /\ next' = "registered"
    /\ limit' = "base"                          \* ensureRegistered
    /\ UNCHANGED <<old, oldReg>>

\* In English: "The successor requests a range and raises its allowance."
\* Literally: "NextSolicit is defined as: next equals "registered", next
\*   becomes "soliciting", and limit becomes "raised"."
NextSolicit ==
    /\ next = "registered"
    /\ next' = "soliciting"
    /\ limit' = "raised"                        \* SetIngressAllowance
    /\ UNCHANGED <<old, oldReg>>

\* In English: "Stop resolves the old instance's requests and recomputes
\* its allowance, zero now. The update reaches the muxer only if the old
\* instance still counts itself registered."
\* Literally: "OldCleanup is defined as: old equals "stopped", old becomes
\*   "cleaned", and limit becomes "base" if oldReg else is unchanged."
OldCleanup ==
    /\ old = "stopped"
    /\ old' = "cleaned"
    /\ limit' = IF oldReg THEN "base" ELSE limit \* applyIngressLimitLocked
    /\ UNCHANGED <<oldReg, next>>

\* In English: "any step."
\* Literally: "Progress is defined as: OldStop, or NextRegister, or
\*   NextSolicit, or OldCleanup."
Progress == OldStop \/ NextRegister \/ NextSolicit \/ OldCleanup

\* In English: "Once nothing can move, nothing changes."
\* Literally: "Rest is defined as: Progress is not enabled, and vars is
\*   unchanged."
Rest == ~ENABLED Progress /\ UNCHANGED vars

\* In English: "a step is any step, or resting once none can move."
\* Literally: "Next is defined as: Progress or Rest."
Next == Progress \/ Rest

\* In English: "start in Init; every later step is a Next step."
\* Literally: "Spec is defined as: Init, and always every step is a Next step
\*   or leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants. *)

\* In English: "While the successor has a range outstanding, the muxer
\* holds the allowance it raised for it."
\* Literally: "SuccessorKeepsAllowance is defined as: if next equals
\*   "soliciting", then limit equals "raised"."
SuccessorKeepsAllowance == next = "soliciting" => limit = "raised"

\* In English: "Each variable holds the kind of value it should."
\* Literally: "TypeOK is defined as: old is "running", "stopped" or
\*   "cleaned", oldReg is a boolean, next is "none", "registered" or
\*   "soliciting", and limit is "base" or "raised"."
TypeOK ==
    /\ old \in {"running", "stopped", "cleaned"}
    /\ oldReg \in BOOLEAN
    /\ next \in {"none", "registered", "soliciting"}
    /\ limit \in {"base", "raised"}
=============================================================================
