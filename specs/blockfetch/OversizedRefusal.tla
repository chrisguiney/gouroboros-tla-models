--------------------------- MODULE OversizedRefusal ---------------------------
(***************************************************************************)
(* Who refuses a block-fetch message one segment over the limit?           *)
(*                                                                         *)
(* The peer sends one message of Limit+1 segments. Two components can      *)
(* refuse it, and either ends the connection:                              *)
(*   - the muxer, when the segments queued for block-fetch and not yet     *)
(*     taken by the protocol's reader pass the ingress limit, which        *)
(*     gOuroboros derives from the largest per-state size limit, so it     *)
(*     equals the message limit here;                                      *)
(*   - the protocol's reader, once it has taken enough of the message to   *)
(*     judge it: the first segment when the message type alone is refused  *)
(*     (no agency), or more than Limit segments when only its size is.     *)
(*                                                                         *)
(* The muxer reports on its own error channel, the reader on the           *)
(* protocol's. A test harness that watches only the protocol's channel     *)
(* sees nothing when the muxer wins, which it can whenever the reader      *)
(* lags the demuxer by a whole message: a busy scheduler, or a server      *)
(* restarting after MsgClientDone, whose new reader is not yet running.    *)
(*                                                                         *)
(* gOuroboros code (read, not guessed):                                    *)
(*   muxer/muxer.go segmentChannel.enqueue - payload past the ingress      *)
(*     limit stops the muxer with ErrIngressOverflow; pendingBytes counts  *)
(*     every segment the reader has not taken.                             *)
(*   protocol/protocol.go ProtocolConfig.ingressLimit - the largest        *)
(*     PendingMessageByteLimit of any state.                               *)
(*   protocol/protocol.go readLoop - refuses a message without agency once *)
(*     its type is known, an oversized one once the buffer passes the      *)
(*     state's limit; returns without an error once the muxer is done.     *)
(*   protocol/blockfetch/server.go handleClientDone - the restart.         *)
(*   connection.go - reads the muxer's error channel and closes the        *)
(*     connection with it.                                                 *)
(*                                                                         *)
(* Symbols are explained in specs/keepalive/KeepAlive.tla's header.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Limit,          \* segments the ingress queue and the state's size limit allow
    TypeRefused,    \* TRUE: the reader refuses on the first segment (no agency)
    ReaderStarts    \* TRUE: the reader is not yet running (a restart in progress)

VARIABLES
    wire,       \* segments of the message the demuxer has not read yet
    pending,    \* segments queued by the muxer, not yet taken by the reader
    got,        \* segments the reader has taken
    readerUp,   \* TRUE once the reader is running
    muxErr,     \* TRUE when the muxer refused (ErrIngressOverflow)
    readerErr   \* TRUE when the reader refused (protocol error channel)

vars == <<wire, pending, got, readerUp, muxErr, readerErr>>

\* In English: "The connection has ended: one of the two refused."
\* Literally: "Ended is defined as muxErr or readerErr."
Ended == muxErr \/ readerErr

Init ==
    /\ wire = Limit + 1
    /\ pending = 0
    /\ got = 0
    /\ readerUp = ~ReaderStarts
    /\ muxErr = FALSE
    /\ readerErr = FALSE

\* The demuxer reads one segment. If it does not fit, the muxer stops.
Demux ==
    /\ ~Ended
    /\ wire > 0
    /\ wire' = wire - 1
    /\ IF pending + 1 > Limit
          THEN /\ muxErr' = TRUE
               /\ UNCHANGED pending
          ELSE /\ pending' = pending + 1
               /\ UNCHANGED muxErr
    /\ UNCHANGED <<got, readerUp, readerErr>>

\* The new protocol instance starts reading.
StartReader ==
    /\ ~Ended
    /\ ~readerUp
    /\ readerUp' = TRUE
    /\ UNCHANGED <<wire, pending, got, muxErr, readerErr>>

\* The reader takes one queued segment.
Take ==
    /\ ~Ended
    /\ readerUp
    /\ pending > 0
    /\ pending' = pending - 1
    /\ got' = got + 1
    /\ UNCHANGED <<wire, readerUp, muxErr, readerErr>>

\* The reader has seen enough to refuse the message.
\* Literally: "Judge is enabled when the connection has not ended, the reader
\*   is up, and got is at least 1 if TypeRefused, else greater than Limit."
Judge ==
    /\ ~Ended
    /\ readerUp
    /\ IF TypeRefused THEN got >= 1 ELSE got > Limit
    /\ readerErr' = TRUE
    /\ UNCHANGED <<wire, pending, got, readerUp, muxErr>>

Next == Demux \/ StartReader \/ Take \/ Judge \/ (Ended /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Demux) /\ WF_vars(StartReader) /\ WF_vars(Take) /\ WF_vars(Judge)

TypeOK ==
    /\ wire \in 0..(Limit + 1)
    /\ pending \in 0..Limit
    /\ got \in 0..(Limit + 1)
    /\ readerUp \in BOOLEAN
    /\ muxErr \in BOOLEAN
    /\ readerErr \in BOOLEAN

\* In English: "The muxer never holds more than the limit for the reader."
QueueWithinLimit == pending <= Limit

\* In English: "The message is always refused: the connection ends."
Refused == <>Ended

\* In English: "The protocol's own error channel always reports the refusal."
\* This is what a harness watching only that channel assumes.
ReaderReports == <>readerErr
=============================================================================
