---------------------------- MODULE Hello ----------------------------
(***************************************************************************)
(* A toy version of the keep-alive mini-protocol, small enough to read in  *)
(* one sitting. docs/02-first-model.md walks through it line by line.      *)
(*                                                                         *)
(* The client sends "ping", the server answers "pong", and they repeat.    *)
(* At any point when it is the client's turn, it may say "done" instead.   *)
(***************************************************************************)
EXTENDS Naturals

\* How many pings the client may send before the model stops exploring.
\* Real clients ping forever; a limit keeps the number of states finite.
MaxPings == 3

\* The variables: everything that can change. A "state" is one value for each.
VARIABLES
    state,  \* whose turn it is: "Client", "Server", or "Done"
    pings,  \* how many pings the client has sent
    pongs   \* how many pongs the server has sent

vars == <<state, pings, pongs>>

\* What every behavior starts with.
Init ==
    /\ state = "Client"
    /\ pings = 0
    /\ pongs = 0

\* Each action is one possible step. A primed variable (state') means
\* "the value in the next state". An action can only happen when its
\* unprimed conditions are true.
SendPing ==
    /\ state = "Client"
    /\ pings < MaxPings
    /\ state' = "Server"
    /\ pings' = pings + 1
    /\ UNCHANGED pongs

SendPong ==
    /\ state = "Server"
    /\ state' = "Client"
    /\ pongs' = pongs + 1
    /\ UNCHANGED pings

SendDone ==
    /\ state = "Client"
    /\ state' = "Done"
    /\ UNCHANGED <<pings, pongs>>

\* Finished conversations stay finished; this step lets TLC know that
\* sitting in "Done" is the expected ending, not a crash.
Finished ==
    /\ state = "Done"
    /\ UNCHANGED vars

Next == SendPing \/ SendPong \/ SendDone \/ Finished

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants: rules that must hold in EVERY reachable state.

TypeOK ==
    /\ state \in {"Client", "Server", "Done"}
    /\ pings \in 0..MaxPings
    /\ pongs \in 0..MaxPings

\* The server never answers a ping that was not sent, and at most one ping
\* is ever waiting for an answer.
PongsMatchPings ==
    /\ pongs <= pings
    /\ pings - pongs <= 1

\* A ping is waiting for an answer exactly when it is the server's turn.
\* This is "agency" from the Ouroboros spec: whoever has agency talks next.
AgencyMatchesOutstandingPing ==
    (state = "Server") <=> (pings - pongs = 1)

\* DELIBERATELY WRONG, used by HelloBug.cfg: claims the client never says
\* "done" after the server's last pong. TLC will find a counterexample.
NeverDoneAfterPong ==
    ~(state = "Done" /\ pongs > 0)
=============================================================================
