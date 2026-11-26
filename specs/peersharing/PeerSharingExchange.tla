------------------------- MODULE PeerSharingExchange -------------------------
(***************************************************************************)
(* The peer-sharing exchange in gOuroboros: concurrent GetPeers callers,   *)
(* their exchangeLock and recorded amount, the receive handler, Stop or    *)
(* the Busy timeout against a caller in flight, and the NoPeerSharing      *)
(* gate on both the client and the server. PeerSharing.tla checks the      *)
(* wire protocol; this module checks the code around it.                   *)
(*                                                                         *)
(* gOuroboros code: protocol/peersharing/client.go (GetPeers,              *)
(* handleSharePeers), server.go (handleShareRequest), peersharing.go       *)
(* (Config.LocalDisabled, Config.RemoteDisabled), and connection.go, which *)
(* sets LocalDisabled when this node advertised NoPeerSharing and          *)
(* RemoteDisabled when the negotiated version data says NoPeerSharing.     *)
(*                                                                         *)
(* Sources. IntersectMBO/ouroboros-network commit 5f356486ab3e:            *)
(*   [S2] docs/network-spec/miniprotocols.tex 1702: a reply longer than   *)
(*        the request is a protocol error; 1770-1771: a peer with peer    *)
(*        sharing off "won't even have the Peer-Sharing miniprotocol      *)
(*        server running".                                                 *)
(*   [R5] cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs *)
(*        146: the negotiated mode is local <> remote, off when either     *)
(*        side is off; cardano-diffusion/lib/Cardano/Network/NodeToNode.hs *)
(*        371-381: the mini-protocol is registered only when it is on.     *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    Callers,          \* goroutines that may call GetPeers
    Amounts,          \* amounts they may ask for
    RogueRequests,    \* MsgShareRequests a misbehaving peer may send us
    ClientGate,       \* TRUE: GetPeers refuses when either flag is set (code)
    ServerGate,       \* "local": handleShareRequest checks LocalDisabled only
                      \*          (gOuroboros at 7cd17437)
                      \* "either": it checks LocalDisabled or RemoteDisabled
                      \* "none": mutation, it checks neither
    UseExchangeLock   \* TRUE: GetPeers holds exchangeLock (code)

ASSUME ServerGate \in {"local", "either", "none"}

\* In English: "None (no number) is -1; Nobody (no lock holder) is a name
\* that is not a caller."
None == -1
Nobody == "nobody"

VARIABLES
    localOff,    \* LocalDisabled: this node advertised NoPeerSharing
    remoteOff,   \* RemoteDisabled: the negotiated mode is NoPeerSharing
    pc,          \* pc[c]: "idle", "lock", "send", "wait", "got", "done"
    amt,         \* amt[c]: the amount caller c asks for
    got,         \* got[c]: how many peers c was given, or None
    lock,        \* exchangeLock's holder, or Nobody
    requested,   \* requestedAmount
    cst,         \* the client protocol's state: "Idle", "Busy"
    sendQ,       \* requests SendMessage queued, not yet written (a sequence)
    reqWire,     \* the amount of our request in flight, or None
    repWire,     \* the length of the peer's reply in flight, or None
    stopped,     \* TRUE once the client protocol stopped (Stop, timeout, error)
    sentReq,     \* TRUE once the client sent any MsgShareRequest
    rogueLeft,   \* rogue requests the peer may still send
    served       \* TRUE once the server called ShareRequestFunc

vars == <<localOff, remoteOff, pc, amt, got, lock, requested, cst, sendQ,
          reqWire, repWire, stopped, sentReq, rogueLeft, served>>

\* In English: "The handshake chose the two flags (any combination); every
\* caller is idle with some amount in mind; nothing is in flight."
Init ==
    /\ localOff \in BOOLEAN /\ remoteOff \in BOOLEAN
    \* RemoteDisabled is the negotiated mode, so it is set whenever
    \* LocalDisabled is [R5].
    /\ localOff => remoteOff
    /\ pc = [c \in Callers |-> "idle"]
    /\ amt \in [Callers -> Amounts]
    /\ got = [c \in Callers |-> None]
    /\ lock = Nobody /\ requested = 0
    /\ cst = "Idle" /\ sendQ = <<>> /\ reqWire = None /\ repWire = None
    /\ stopped = FALSE /\ sentReq = FALSE
    /\ rogueLeft = RogueRequests /\ served = FALSE

-----------------------------------------------------------------------------
(* GetPeers, one line at a time. *)

\* In English: "c calls GetPeers. With the client gate, a set flag refuses
\* at once; otherwise c goes for the lock."
Call(c) ==
    /\ pc[c] = "idle"
    /\ pc' = [pc EXCEPT ![c] =
                IF ClientGate /\ (localOff \/ remoteOff) THEN "done" ELSE "lock"]
    /\ UNCHANGED <<sendQ, localOff, remoteOff, amt, got, lock, requested, cst,
                   reqWire, repWire, stopped, sentReq, rogueLeft, served>>

\* In English: "c takes exchangeLock (or, without it, just goes on) and
\* records its amount as requestedAmount."
TakeLock(c) ==
    /\ pc[c] = "lock"
    /\ UseExchangeLock => lock = Nobody
    /\ lock' = IF UseExchangeLock THEN c ELSE lock
    /\ requested' = amt[c]                           \* requestedAmount = amount
    /\ pc' = [pc EXCEPT ![c] = "send"]
    /\ UNCHANGED <<sendQ, localOff, remoteOff, amt, got, cst, reqWire, repWire,
                   stopped, sentReq, rogueLeft, served>>

\* In English: "c calls SendMessage: a stopped protocol refuses and GetPeers
\* returns the error; otherwise the request is queued and c goes on to wait
\* on sharePeersChan." (SendMessage does not wait for the write.)
Send(c) ==
    /\ pc[c] = "send"
    /\ \/ /\ ~stopped
          /\ sendQ' = Append(sendQ, amt[c])
          /\ pc' = [pc EXCEPT ![c] = "wait"]
          /\ UNCHANGED lock
       \/ /\ stopped
          /\ pc' = [pc EXCEPT ![c] = "done"]
          /\ lock' = IF lock = c THEN Nobody ELSE lock  \* deferred Unlock
          /\ UNCHANGED sendQ
    /\ UNCHANGED <<localOff, remoteOff, amt, got, requested, cst, reqWire,
                   repWire, stopped, sentReq, rogueLeft, served>>

\* In English: "sendLoop writes the oldest queued request once the protocol
\* is in Idle: Idle -> Busy."
Write ==
    /\ ~stopped /\ cst = "Idle" /\ sendQ /= <<>>
    /\ cst' = "Busy" /\ reqWire' = Head(sendQ) /\ sendQ' = Tail(sendQ)
    /\ sentReq' = TRUE
    /\ UNCHANGED <<localOff, remoteOff, pc, amt, got, lock, requested, repWire,
                   stopped, rogueLeft, served>>

\* In English: "c receives from sharePeersChan, or sees DoneChan closed,
\* and returns, releasing the lock."
Return(c) ==
    /\ \/ pc[c] = "got"
       \/ pc[c] = "wait" /\ stopped
    /\ pc' = [pc EXCEPT ![c] = "done"]
    /\ lock' = IF lock = c THEN Nobody ELSE lock       \* deferred Unlock
    /\ UNCHANGED <<sendQ, localOff, remoteOff, amt, got, requested, cst, reqWire,
                   repWire, stopped, sentReq, rogueLeft, served>>

-----------------------------------------------------------------------------
(* The peer and our receive handler. *)

\* In English: "The (honest) peer answers our request with at most as many
\* peers as were asked for." [S2]
PeerReplies ==
    /\ reqWire /= None /\ ~stopped
    /\ \E n \in 0..reqWire : repWire' = n
    /\ reqWire' = None
    /\ UNCHANGED <<sendQ, localOff, remoteOff, pc, amt, got, lock, requested, cst,
                   stopped, sentReq, rogueLeft, served>>

\* In English: "handleSharePeers: a reply longer than requestedAmount is a
\* protocol error that stops the protocol; otherwise it is handed through
\* sharePeersChan to a caller waiting there, and the protocol is Idle."
Handle ==
    /\ repWire /= None /\ ~stopped
    /\ IF repWire > requested
         THEN /\ stopped' = TRUE                     \* ErrTooManyPeersShared
              /\ UNCHANGED <<pc, got, cst>>
         ELSE \E c \in Callers :
                /\ pc[c] = "wait"
                /\ got' = [got EXCEPT ![c] = repWire]
                /\ pc' = [pc EXCEPT ![c] = "got"]
                /\ cst' = "Idle"
                /\ UNCHANGED stopped
    /\ repWire' = None
    /\ UNCHANGED <<sendQ, localOff, remoteOff, amt, lock, requested, reqWire, sentReq,
                   rogueLeft, served>>

\* In English: "The client protocol stops: Stop, the Busy timeout, or the
\* connection closing."
StopClient ==
    /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED <<sendQ, localOff, remoteOff, pc, amt, got, lock, requested, cst,
                   reqWire, repWire, sentReq, rogueLeft, served>>

\* In English: "A misbehaving peer sends our server a MsgShareRequest
\* whatever was negotiated. handleShareRequest answers empty when its gate
\* holds, else it asks ShareRequestFunc for peers."
RogueRequest ==
    /\ rogueLeft > 0
    /\ rogueLeft' = rogueLeft - 1
    /\ LET gated == CASE ServerGate = "local"  -> localOff
                      [] ServerGate = "either" -> localOff \/ remoteOff
                      [] ServerGate = "none"   -> FALSE
       IN served' = (served \/ ~gated)
    /\ UNCHANGED <<sendQ, localOff, remoteOff, pc, amt, got, lock, requested, cst,
                   reqWire, repWire, stopped, sentReq>>

\* In English: "Every caller has returned and the peer is done."
Finished ==
    /\ \A c \in Callers : pc[c] = "done"
    /\ rogueLeft = 0
    /\ UNCHANGED vars

Next ==
    \/ \E c \in Callers : Call(c) \/ TakeLock(c) \/ Send(c) \/ Return(c)
    \/ Write \/ PeerReplies \/ Handle \/ StopClient \/ RogueRequest
    \/ Finished

\* Weak fairness: a step that stays possible eventually happens. The peer
\* answers, the handler runs, callers make progress; StopClient is the Busy
\* timeout or connection close, so it too eventually happens.
Fairness ==
    /\ \A c \in Callers : WF_vars(Call(c) \/ TakeLock(c) \/ Send(c) \/ Return(c))
    /\ WF_vars(Write) /\ WF_vars(PeerReplies) /\ WF_vars(Handle) /\ WF_vars(RogueRequest)
    /\ WF_vars(StopClient)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

\* In English: "Peer sharing negotiated off: either side advertised
\* NoPeerSharing." [R5]
NegotiatedOff == localOff \/ remoteOff

\* In English: "A node whose connection negotiated NoPeerSharing never sends
\* a MsgShareRequest." [S2][R5]
NeverRequestsWhenOff == NegotiatedOff => ~sentReq

\* In English: "... and never serves one: ShareRequestFunc is never asked
\* for peers to give that peer." [S2][R5]
NeverServesWhenOff == NegotiatedOff => ~served

\* In English: "No caller is ever given more peers than it asked for." [S2]
NeverGivenMoreThanAsked ==
    \A c \in Callers : got[c] /= None => got[c] <= amt[c]

\* In English: "Every caller of GetPeers returns."
EveryCallerReturns == \A c \in Callers : <>(pc[c] = "done")

TypeOK ==
    /\ pc \in [Callers -> {"idle", "lock", "send", "wait", "got", "done"}]
    /\ lock \in Callers \cup {Nobody}
    /\ cst \in {"Idle", "Busy"}
=============================================================================
