--------------------------- MODULE LeiosVoteShape ---------------------------
(***************************************************************************)
(* The wire shape of a Leios vote: which encodings a LeiosVotes MsgVote or *)
(* a LeiosFetch votes reply decodes as a vote.                             *)
(*                                                                         *)
(* Sources.                                                                *)
(*   [S1] cardano-foundation/CIPs db48da14bff1, CIP-0164/README.md         *)
(*        3397-3410: leios_vote = [announcing_rb_hash, voter_id,           *)
(*        vote_signature]; 1541-1542: LeiosVotes' MsgLeiosVote carries it. *)
(*   [S2] IntersectMBO/ouroboros-consensus ec239d57f618, ouroboros-        *)
(*        consensus/src/ouroboros-consensus/Ouroboros/Consensus/Leios/     *)
(*        Types.hs 254-278 (decodeLeiosVote): a three-element array, the   *)
(*        voter id decoded as a Word16.                                    *)
(*   The rc-2026w41 prototype node's captured vote has the same shape.     *)
(*                                                                         *)
(* The gOuroboros code it is compared with is ledger/common/leios.go       *)
(* (LeiosVote; LeiosLegacyVote on the fix branch), carried by              *)
(* protocol/leiosvotes/messages.go (MsgVote) and checked in                *)
(* protocol/leiosfetch/validate.go (validateVotes). LeiosNotify vote       *)
(* offers, a gOuroboros extension, keep the earlier shape and are not      *)
(* modelled. Symbols are read as in specs/keepalive/KeepAlive.tla.         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Rule    \* "main": gOuroboros before the fix; "fixed": the branch

\* Literally: "Rules is defined as the set containing "main" and "fixed"."
\* In English: the two gOuroboros behaviours a configuration can pick.
Rules == {"main", "fixed"}
ASSUME Rule \in Rules

\* Literally: "W16 is defined as 3."
\* In English: the largest Word16, 65,535, scaled down.
W16 == 3

\* Literally: "Shapes is defined as the set containing "cip" and "legacy"."
\* In English: [announcing_rb_hash, voter_id, signature], or an earlier
\* draft's [slot, eb_hash, voter_id, signature].
Shapes == {"cip", "legacy"}
\* Literally: "Carriers is defined as the set containing "LeiosVotes" and
\*   "LeiosFetch"."
\* In English: the two messages whose votes decode through LeiosVote.
Carriers == {"LeiosVotes", "LeiosFetch"}

VARIABLES carrier, shape, voter
vars == <<carrier, shape, voter>>

\* Literally: "RefDecodes is defined as: shape equals "cip" and voter is at
\*   most W16."
\* In English: the reference decodes a three-element vote whose voter id
\* fits in 16 bits [S1, S2], and nothing else.
RefDecodes == shape = "cip" /\ voter <= W16

\* Literally: "GoDecodes is defined as: if Rule equals "main" then shape
\*   equals "legacy", else shape equals "cip" and voter is at most W16."
\* In English: main's LeiosVote is the four-element draft, with a 64-bit
\* voter id, so a reference vote fails ("cannot decode CBOR array to struct
\* with different number of elements"); the fix decodes the CIP shape
\* with a uint16 voter id.
GoDecodes == IF Rule = "main" THEN shape = "legacy"
                              ELSE shape = "cip" /\ voter <= W16

\* Literally: "Init is defined as: carrier is a member of Carriers, shape is
\*   a member of Shapes, and voter is a member of 0 to W16 plus 1."
\* In English: pick a message, a vote shape and a voter id, one past 16
\* bits included.
Init == /\ carrier \in Carriers
        /\ shape \in Shapes
        /\ voter \in 0..(W16 + 1)

\* Literally: "Next is defined as: vars is unchanged."
\* In English: each state is one cell of the table.
Next == UNCHANGED vars

\* Literally: "Spec is defined as Init and always Next or vars unchanged."
Spec == Init /\ [][Next]_vars

\* Literally: "VoteShapeAsReference is defined as GoDecodes if and only if
\*   RefDecodes."
\* In English: gOuroboros decodes exactly the votes decodeLeiosVote does.
VoteShapeAsReference == GoDecodes <=> RefDecodes
=============================================================================
