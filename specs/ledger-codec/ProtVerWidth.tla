---------------------------- MODULE ProtVerWidth ----------------------------
(***************************************************************************)
(* The proposed protocol version in a classic (Shelley to Babbage)         *)
(* parameter update: which (major, minor) pairs decode, and which of them  *)
(* the update rule then lets follow the current version.                   *)
(*                                                                         *)
(* Sources. IntersectMBO/cardano-ledger commit 1210d37fe6bd.               *)
(*   [S1] libs/cardano-ledger-core/src/Cardano/Ledger/BaseTypes.hs 212:    *)
(*        ProtVer { pvMajor :: Version, pvMinor :: Word32 }.               *)
(*   [S2] BaseTypes.hs 254-264 (decodeProtVer): the major may be at most   *)
(*        succVersion (ProtVerHigh era).                                   *)
(*   [S3] libs/cardano-ledger-core/internal/Cardano/Ledger/Internal/       *)
(*        Definition/Era.hs 92-125: ProtVerLow/High are Shelley 2-2,       *)
(*        Allegra 3-3, Mary 4-4, Alonzo 5-6, Babbage 7-8.                  *)
(*   [S4] eras/shelley/impl/src/Cardano/Ledger/Shelley/PParams.hs 338-340  *)
(*        (pvCanFollow): (major + 1, 0), or (major, minor + 1) computed in *)
(*        Word32; 344-349 (hasLegalProtVerUpdate); Shelley/Rules/Ppup.hs   *)
(*        170-175 (PVCannotFollowPPUP).                                    *)
(*   The Shelley formal specification (update.tex, pvCanFollow) states the *)
(*   same following rule and is silent on the field widths.                *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ledger/common/               *)
(* pparam_update_validation.go (ValidateProtocolParameterUpdateDomains,    *)
(* field 14) and ledger/common/rules.go (protocolVersionCanFollow); from   *)
(* 5efc10c0 the next minor is computed in 32 bits there and in             *)
(* ledger/conway/rules.go (protocolVersionCanFollow, hard forks).          *)
(*                                                                         *)
(* Widths are scaled so TLC's integers suffice: W16 stands for 65,535 and  *)
(* W32 for 4,294,967,295. Every era's major bound stays far below W16, as  *)
(* in the real numbers. Symbols are read as in specs/keepalive/            *)
(* KeepAlive.tla.                                                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule,       \* "main": before the fix; "fixed": 7bd145e3; "wrapped": 5efc10c0
    CurMinors   \* the current minor versions a run may start from

\* Literally: "Rules is defined as the set containing "main", "fixed" and
\*   "wrapped"."
\* In English: the three gOuroboros behaviours a configuration can pick.
Rules == {"main", "fixed", "wrapped"}
ASSUME Rule \in Rules

\* Literally: "W16 is defined as 12."
\* In English: the largest 16-bit value, scaled down.
W16 == 12
\* Literally: "W32 is defined as 20."
\* In English: the largest 32-bit value (Word32's maxBound), scaled down.
W32 == 20

ASSUME CurMinors \subseteq 0..W32

\* Literally: "Eras is defined as the set containing "Shelley", "Allegra",
\*   "Mary", "Alonzo" and "Babbage"."
\* In English: the eras whose updates carry a classic protocol version.
Eras == {"Shelley", "Allegra", "Mary", "Alonzo", "Babbage"}

\* Literally: "Low of e is defined as: case e equals "Shelley" gives 2,
\*   "Allegra" gives 3, "Mary" gives 4, "Alonzo" gives 5, "Babbage" gives 7."
\* In English: the era's lowest protocol major version [S3].
Low(e) == CASE e = "Shelley" -> 2 [] e = "Allegra" -> 3 [] e = "Mary" -> 4
            [] e = "Alonzo" -> 5 [] e = "Babbage" -> 7
\* Literally: "High of e is defined as: case e equals "Alonzo" gives 6,
\*   e equals "Babbage" gives 8, otherwise Low of e."
\* In English: the era's highest protocol major version [S3].
High(e) == CASE e = "Alonzo" -> 6 [] e = "Babbage" -> 8 [] OTHER -> Low(e)

VARIABLES era, cur, prop
vars == <<era, cur, prop>>

\* Literally: "RefDecodes of e and p is defined as: element 1 of p is at most
\*   High of e plus 1, and element 2 of p is at most W32."
\* In English: the reference decodes the proposal when its major is at most
\* one above the era's highest [S2] and its minor fits in a Word32 [S1].
RefDecodes(e, p) == p[1] <= High(e) + 1 /\ p[2] <= W32

\* Literally: "RefFollows of c and p is defined as: element 1 of p equals
\*   element 1 of c plus 1 and element 2 of p equals 0, or element 1 of p
\*   equals element 1 of c and element 2 of p equals element 2 of c plus 1
\*   modulo W32 plus 1."
\* In English: pvCanFollow [S4]. The minor's successor is computed in
\* Word32, so it wraps from maxBound to 0.
RefFollows(c, p) == \/ p[1] = c[1] + 1 /\ p[2] = 0
                    \/ p[1] = c[1] /\ p[2] = (c[2] + 1) % (W32 + 1)

\* Literally: "RefAccepts of e, c and p is defined as RefDecodes of e and p
\*   and RefFollows of c and p."
\* In English: the reference accepts the proposed version.
RefAccepts(e, c, p) == RefDecodes(e, p) /\ RefFollows(c, p)

\* Literally: "GoMinorMax is defined as: if Rule equals "main" then W16 else
\*   W32."
\* In English: the widest minor gOuroboros decodes: 16 bits on main, 32
\* bits on the fix.
GoMinorMax == IF Rule = "main" THEN W16 ELSE W32

\* Literally: "GoDecodes of p is defined as: element 1 of p is at most W16,
\*   and element 2 of p is at most GoMinorMax."
\* In English: ValidateProtocolParameterUpdateDomains accepts field 14: the
\* major fits in 16 bits whatever the era, and the minor in GoMinorMax.
GoDecodes(p) == p[1] <= W16 /\ p[2] <= GoMinorMax

\* Literally: "GoNextMinor of n is defined as: if Rule equals "wrapped"
\*   then n plus 1 modulo W32 plus 1, else n plus 1."
\* In English: the minor protocolVersionCanFollow expects next: computed in
\* Go's uint before 5efc10c0, which does not wrap, and in 32 bits from it.
GoNextMinor(n) == IF Rule = "wrapped" THEN (n + 1) % (W32 + 1) ELSE n + 1

\* Literally: "GoFollows of c and p is defined as: element 1 of p equals
\*   element 1 of c plus 1 and element 2 of p equals 0, or element 1 of p
\*   equals element 1 of c and element 2 of p equals GoNextMinor of
\*   element 2 of c."
\* In English: protocolVersionCanFollow.
GoFollows(c, p) == \/ p[1] = c[1] + 1 /\ p[2] = 0
                   \/ p[1] = c[1] /\ p[2] = GoNextMinor(c[2])

\* Literally: "GoAccepts of c and p is defined as GoDecodes of p and
\*   GoFollows of c and p."
\* In English: gOuroboros accepts the proposed version.
GoAccepts(c, p) == GoDecodes(p) /\ GoFollows(c, p)

\* Literally: "Minors is defined as the set containing 0, 1, W16, W16 plus
\*   1, W32 and W32 plus 1."
\* In English: the proposed minors worth trying: small, and either side of
\* each width.
Minors == {0, 1, W16, W16 + 1, W32, W32 + 1}

\* Literally: "Init is defined as: era is a member of Eras, cur is a member
\*   of the set of pairs m, n for m in Low of era to High of era and n in
\*   CurMinors, and prop is a member of the pairs from 0 to W16 plus 1 and
\*   Minors."
\* In English: pick an era, a current version of that era, and a proposal.
Init == /\ era \in Eras
        /\ cur \in {<<m, n>> : m \in Low(era)..High(era), n \in CurMinors}
        /\ prop \in (0..(W16 + 1)) \X Minors

\* Literally: "Next is defined as: vars is unchanged."
\* In English: nothing happens after the choice; each state is one cell of
\* the table.
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always Next or vars unchanged."
Spec == Init /\ [][Next]_vars

\* Literally: "MinorWidthAsReference is defined as: if element 1 of prop is
\*   at most High of era plus 1, then GoDecodes of prop if and only if
\*   RefDecodes of era and prop."
\* In English: for a major the reference decodes, gOuroboros decodes exactly
\* the minors the reference does: every Word32 [S1].
MinorWidthAsReference ==
    prop[1] <= High(era) + 1 => (GoDecodes(prop) <=> RefDecodes(era, prop))

\* Literally: "OutcomeAsReference is defined as GoAccepts of cur and prop if
\*   and only if RefAccepts of era, cur and prop."
\* In English: gOuroboros accepts exactly the proposals the reference does,
\* whatever check refuses them.
OutcomeAsReference == GoAccepts(cur, prop) <=> RefAccepts(era, cur, prop)

\* Literally: "MajorWidthAsReference is defined as GoDecodes of prop if and
\*   only if RefDecodes of era and prop."
\* In English: gOuroboros refuses at decoding every major the reference
\* refuses there [S2]. gOuroboros bounds the major at 16 bits only, so this
\* fails by design: such a proposal is refused later, by the follow rule.
MajorWidthAsReference == GoDecodes(prop) <=> RefDecodes(era, prop)
=============================================================================
