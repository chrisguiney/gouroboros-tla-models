------------------------------ MODULE GovVoterNil ------------------------------
(***************************************************************************)
(* What each Conway rule that reads a transaction's voters does with a nil *)
(* voter key, as a table over (rule, voter).                               *)
(*                                                                         *)
(* A nil voter is not a reference rule: the reference's Voter type cannot  *)
(* be absent, and no decoded transaction carries one. Only a transaction   *)
(* built by hand in Go can. The rule checked here is the one gOuroboros's  *)
(* own voting rules state by example: a rule skips a nil voter, or refuses *)
(* the transaction, and never dereferences it (a panic takes down the      *)
(* caller, a node or a wallet, instead of refusing one transaction).       *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [R1] cardano-ledger 1210d37fe6bd eras/conway/impl/src/Cardano/       *)
(*        Ledger/Conway/Governance/Procedures.hs ~351-355 data Voter:      *)
(*        CommitteeVoter, DRepVoter, StakePoolVoter, all strict; there is  *)
(*        no absent voter. Spec silent (DRIFT L3).                         *)
(*                                                                         *)
(* gOuroboros ledger/conway/rules.go and ledger/common/rules.go:           *)
(*   [G1] main before #3155 (0fd483b3^): UtxoValidateUnknownVoters,        *)
(*        UtxoValidateVotingOnExpiredGovAction,                            *)
(*        UtxoValidateBootstrapVotingRestrictions,                         *)
(*        UtxoValidateStakePoolVotingRestrictions and                      *)
(*        UtxoValidateUnelectedCommitteeVoters skip a nil voter;           *)
(*        common.voterCredential refuses it (MalformedAuthorizationError); *)
(*        UtxoValidateCCVotingRestrictions (4663-4666) reads voter.Type    *)
(*        first and panics.                                                *)
(*   [G2] #3155 (0fd483b3, 4664-4669): UtxoValidateCCVotingRestrictions    *)
(*        skips a nil voter too.                                           *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    GoRule  \* "main" [G1] or "fix" [G2]

VARIABLE input  \* the one input this behaviour checks: [rule, voter]

\* In English: "Every gOuroboros rule that reads the voters of a
\*   transaction's voting procedures."
\* Literally: "Rules is defined as the set containing "UnknownVoters",
\*   "VotingOnExpired", "BootstrapVoting", "StakePoolVoting", "CCVoting",
\*   "UnelectedCommittee" and "VoterCredential"."
Rules == {"UnknownVoters", "VotingOnExpired", "BootstrapVoting",
          "StakePoolVoting", "CCVoting", "UnelectedCommittee",
          "VoterCredential"}

\* In English: "A voter key: absent, or one of the reference's three kinds."
\* Literally: "Voters is defined as the set containing "nil", "committee",
\*   "drep" and "pool"."
Voters == {"nil", "committee", "drep", "pool"}

\* In English: "Every rule with every voter."
\* Literally: "Inputs is defined as the set of records whose rule is a
\*   member of Rules and whose voter is a member of Voters."
Inputs == [rule : Rules, voter : Voters]

\* In English: "What a rule does with a nil voter: VoterCredential refuses
\*   it; CCVoting panics on main [G1] and skips it with the fix [G2]; every
\*   other rule skips it."
\* Literally: "OnNil of r is defined as: if r equals "VoterCredential" then
\*   "refuse"; else if r equals "CCVoting" and GoRule equals "main" then
\*   "panic"; else "skip"."
OnNil(r) ==
    IF r = "VoterCredential" THEN "refuse"
    ELSE IF r = "CCVoting" /\ GoRule = "main" THEN "panic"
    ELSE "skip"

\* In English: "A rule's outcome: OnNil for a nil voter, otherwise it
\*   checks the voter (what it checks is modelled in GovLifecycle)."
\* Literally: "GoOutcome of i is defined as: if the voter of i equals "nil"
\*   then OnNil of the rule of i, else "check"."
GoOutcome(i) == IF i.voter = "nil" THEN OnNil(i.rule) ELSE "check"

\* In English: "Pick any one input; nothing changes after that."
\* Literally: "Init is defined as: input is a member of Inputs."
Init == input \in Inputs

\* In English: "A table has no steps: the input stays as it is."
\* Literally: "Next is defined as: input is unchanged."
Next == UNCHANGED input

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or input
\*   stays the same."
Spec == Init /\ [][Next]_input

\* In English: "No rule panics on any voter: a voter the reference cannot
\*   represent [R1] is skipped or refused, as the sibling rules do."
\* Literally: "NilVoterSkippedAsSiblings is defined as: GoOutcome of input
\*   does not equal "panic"."
NilVoterSkippedAsSiblings == GoOutcome(input) # "panic"
=============================================================================
