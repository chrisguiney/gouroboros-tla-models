---------------------------- MODULE Hello ----------------------------
(***************************************************************************)
(* A toy version of the keep-alive mini-protocol, small enough to read in  *)
(* one sitting. docs/02-first-model.md walks through it line by line.      *)
(*                                                                         *)
(* The client sends "ping", the server answers "pong", and they repeat.    *)
(* At any point when it is the client's turn, it may say "done" instead.   *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS                                                 *)
(*   ==          "is defined as"                                           *)
(*   /\          "and"   (a list of /\ lines: all of them are true)        *)
(*   \/          "or"    (a list of \/ lines: at least one is true)        *)
(*   ~           "not"                                                     *)
(*   =           "equals" (a comparison, never an assignment)              *)
(*   x'          "x in the next state"                                     *)
(*   \in         "is one of"                                               *)
(*   a..b        "the numbers a to b"                                      *)
(*   =>          "implies" (if the left is true, the right must be too)    *)
(*   <=>         "if and only if" (both true, or both false)               *)
(*   []          "always"                                                  *)
(*   \*          a comment until the end of the line                       *)
(***************************************************************************)
EXTENDS Naturals    \* use ordinary numbers: 0, 1, 2, +, -, <, ..

\* MaxPings is defined as 3.
\* Real clients ping forever; a limit keeps the number of states finite.
\* Literally: "MaxPings is defined as 3."
MaxPings == 3

\* The variables: everything that can change. A "state" is one value for each.
VARIABLES
    state,  \* whose turn it is: "Client", "Server", or "Done"
    pings,  \* how many pings the client has sent
    pongs   \* how many pongs the server has sent

\* vars is the list of all three variables, so we can say "none changed".
\* Literally: "vars is defined as the tuple of state, pings and pongs."
vars == <<state, pings, pongs>>

\* In English: "At the start, it is the client's turn, and nothing has been
\* sent yet."
\* Literally: "Init is defined as: state equals "Client", and pings equals 0,
\*   and pongs equals 0."
Init ==
    /\ state = "Client"     \* it is the client's turn
    /\ pings = 0            \* and no pings have been sent
    /\ pongs = 0            \* and no pongs have been sent

\* Each action is one possible step. Lines without a prime (') are
\* conditions that must be true NOW for the step to happen. Lines with a
\* prime say what the NEXT state looks like.

\* In English: "The client can send a ping when it is the client's turn and
\* it has pings left. Afterwards it is the server's turn, one more ping has
\* been sent, and the pong count is unchanged."
\* Literally: "SendPing is defined as: state equals "Client", and pings is less
\*   than MaxPings, and state in the next state equals "Server", and pings in
\*   the next state equals pings plus 1, and pongs is unchanged."
SendPing ==
    /\ state = "Client"         \* it is the client's turn
    /\ pings < MaxPings         \* and it has pings left
    /\ state' = "Server"        \* next, it is the server's turn
    /\ pings' = pings + 1       \* next, one more ping has been sent
    /\ UNCHANGED pongs          \* and the pong count stays the same

\* In English: "The server can send a pong when it is the server's turn.
\* Afterwards it is the client's turn and one more pong has been sent."
\* Literally: "SendPong is defined as: state equals "Server", and state in the
\*   next state equals "Client", and pongs in the next state equals pongs plus
\*   1, and pings is unchanged."
SendPong ==
    /\ state = "Server"         \* it is the server's turn
    /\ state' = "Client"        \* next, it is the client's turn
    /\ pongs' = pongs + 1       \* next, one more pong has been sent
    /\ UNCHANGED pings          \* and the ping count stays the same

\* In English: "The client can say done when it is the client's turn.
\* Afterwards the conversation is over and the counts are unchanged."
\* Literally: "SendDone is defined as: state equals "Client", and state in the
\*   next state equals "Done", and the tuple of pings and pongs is unchanged."
SendDone ==
    /\ state = "Client"                 \* it is the client's turn
    /\ state' = "Done"                  \* next, the conversation is over
    /\ UNCHANGED <<pings, pongs>>       \* and both counts stay the same

\* In English: "Once done, nothing changes any more." This step lets TLC
\* know that sitting in "Done" is the expected ending, not a crash.
\* Literally: "Finished is defined as: state equals "Done", and vars is
\*   unchanged."
Finished ==
    /\ state = "Done"           \* the conversation is over
    /\ UNCHANGED vars           \* and nothing changes

\* In English: "A step is a ping, or a pong, or done, or staying finished."
\* Literally: "Next is defined as: SendPing, or SendPong, or SendDone, or
\*   Finished."
Next == SendPing \/ SendPong \/ SendDone \/ Finished

\* In English: "Start in Init, and from then on every step is a Next step."
\* You will write this line, unchanged, at the bottom of almost every model.
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants: rules that must hold in EVERY reachable state. TLC checks
\* them after every step of every possible run.

\* In English: "state is one of the three turns, and both counts are
\* between 0 and MaxPings."
\* Literally: "TypeOK is defined as: state is a member of the set containing
\*   "Client", "Server" and "Done", and pings is a member of 0 through
\*   MaxPings, and pongs is a member of 0 through MaxPings."
TypeOK ==
    /\ state \in {"Client", "Server", "Done"}   \* state is one of these three
    /\ pings \in 0..MaxPings                    \* pings is between 0 and 3
    /\ pongs \in 0..MaxPings                    \* pongs is between 0 and 3

\* In English: "The server never sends more pongs than there were pings,
\* and at most one ping is ever waiting for an answer."
\* Literally: "PongsMatchPings is defined as: pongs is less than or equal to
\*   pings, and pings minus pongs is less than or equal to 1."
PongsMatchPings ==
    /\ pongs <= pings           \* never more pongs than pings
    /\ pings - pongs <= 1       \* at most one ping unanswered

\* In English: "It is the server's turn exactly when one ping is waiting."
\* This is "agency" from the Ouroboros spec: whoever has agency talks next.
\* Literally: "AgencyMatchesOutstandingPing is defined as: state equals
\*   "Server" if and only if pings minus pongs equals 1."
AgencyMatchesOutstandingPing ==
    (state = "Server") <=> (pings - pongs = 1)

\* DELIBERATELY WRONG, used by HelloBug.cfg. In English: "The client never
\* says done after getting a pong." TLC will find a counterexample.
\* Literally: "NeverDoneAfterPong is defined as: it is not the case that state
\*   equals "Done" and pongs is greater than 0."
NeverDoneAfterPong ==
    ~(state = "Done" /\ pongs > 0)  \* NOT (done AND at least one pong)
=============================================================================
