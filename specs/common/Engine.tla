------------------------------- MODULE Engine -------------------------------
(***************************************************************************)
(* The protocol engine as the connection sees it: the interface every     *)
(* mini-protocol model refines, and the only part of an engine a          *)
(* connection-level model reads or writes. One instance of                *)
(* protocol.Protocol (gOuroboros protocol/protocol.go at 0c00b799).       *)
(*                                                                         *)
(* The interface's objects, named as in GoConcurrency.tla:                 *)
(*   started     Start ran its body and started the loops (:457-525)       *)
(*   sendQ       sendQueueChan, a channel of capacity QCap (80 in Go,      *)
(*               :346); SendMessage blocks while it is full (:1131-1139)   *)
(*   stopChan    closed by stop (:598), the signal every loop and every    *)
(*               blocked SendMessage observes                              *)
(*   handler     a MessageHandlerFunc is running on recvLoop (:2524)       *)
(*   doneChan    DoneChan (:717), closed once recvLoop and sendLoop have   *)
(*               exited (:508-512) or, if never started, by stop (:600)    *)
(*   loopsDone   loopsDoneChan (:687-696): shutdown has begun and every    *)
(*               loop counted by addLoop has returned; Stop(ctx) and the   *)
(*               connection's Close wait for it                            *)
(*   reg         the muxer registration: "none", "registered", then        *)
(*               "released" (unregistered, or suspended for a restart)     *)
(*   connClosed  the muxer's doneChan, which the engine observes           *)
(*                                                                         *)
(* The spec is a set of rules, one per object, that every step of an      *)
(* engine obeys; a detailed engine model refines it when every one of its *)
(* steps, seen through a refinement mapping, obeys all of them (Specifying *)
(* Systems, chapter 5, "refinement mapping"; docs/glossary.md).            *)
(* DoneAfterJoin is the contract under test: TRUE says a completed join   *)
(* implies DoneChan is closed, which is what Stop's doc promises ("waits   *)
(* until every goroutine of this instance has returned", :520-527) once   *)
(* the done watcher (:508) counts as one of them.                          *)
(*                                                                         *)
(* No specification source: protocol.Protocol is gOuroboros's own API.     *)
(* The nearest reference is ouroboros-network's mini-protocol job          *)
(* (network-mux/src/Network/Mux.hs:319-381, runMiniProtocol), which the    *)
(* job pool joins as a thread; see specs/connection/README.md part 8.      *)
(*                                                                         *)
(* How to read the symbols: see specs/keepalive/KeepAlive.tla's header.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, GoConcurrency

CONSTANTS
    QCap,          \* sendQueueChan's capacity, a small stand-in for 80
    DoneAfterJoin  \* TRUE: the join implies DoneChan is closed

VARIABLES started, stopChan, sendQ, handler, doneChan, loopsDone, reg,
          connClosed

\* In English: "The interface's variables."
evars == <<started, stopChan, sendQ, handler, doneChan, loopsDone, reg,
           connClosed>>

\* In English: "Every variable has the type the header gives it."
TypeOK ==
    /\ started \in BOOLEAN /\ stopChan \in BOOLEAN /\ handler \in BOOLEAN
    /\ doneChan \in BOOLEAN /\ loopsDone \in BOOLEAN /\ connClosed \in BOOLEAN
    /\ ChanLen(sendQ) <= QCap /\ sendQ.cap = QCap
    /\ reg \in {"none", "registered", "released"}

\* In English: "A new engine: nothing started, nothing closed, an empty
\* send queue, not registered."
Init ==
    /\ started = FALSE /\ stopChan = FALSE /\ handler = FALSE
    /\ doneChan = FALSE /\ loopsDone = FALSE /\ connClosed = FALSE
    /\ sendQ = Chan(QCap)
    /\ reg = "none"

\* In English: "A closed channel never reopens, and a started engine stays
\* started."
Monotone ==
    /\ started => started'
    /\ stopChan => stopChan'
    /\ doneChan => doneChan'
    /\ loopsDone => loopsDone'
    /\ connClosed => connClosed'
    /\ reg = "released" => reg' = "released"

\* In English: "Start starts the loops only before stop (the stopped check
\* under lifecycleMu, :459-463), and registers with the muxer as it does."
StartRule ==
    (~started /\ started') =>
        /\ ~stopChan /\ ~loopsDone
        /\ reg' = "registered"

\* In English: "The registration is made only by Start, and released only
\* once stop has closed stopChan (:602-622)."
RegRule ==
    /\ (reg = "none" /\ reg' = "registered") => started'
    /\ (reg /= "released" /\ reg' = "released") => stopChan'

\* In English: "The send queue is never closed (only sendLoop's muxer
\* channel is). A value leaves it only while the loops have not been
\* joined, because sendLoop, which takes it, is one of them. A send may
\* still land after stopChan closes: the enqueue select (:1131-1139) picks
\* any ready case, and a queued message nobody will take is dropped with
\* the instance."
QueueRule ==
    /\ ~sendQ'.closed /\ sendQ'.cap = QCap
    /\ ChanLen(sendQ') < ChanLen(sendQ) => started /\ ~loopsDone'

\* In English: "A handler starts only on a running engine whose DoneChan is
\* open and whose loops have not been joined."
HandlerRule ==
    (~handler /\ handler') => started /\ ~doneChan /\ ~loopsDone

\* In English: "DoneChan closes only when no handler runs (the DoneChan
\* doc: a handler never sees it close). On an engine that never started,
\* only stop or a Start refused by a closing connection closes it
\* (:465-470, :500-505)."
DoneRule ==
    (~doneChan /\ doneChan') =>
        ~handler' /\ (started \/ stopChan' \/ connClosed')

\* In English: "The join completes only after stop, with no handler
\* running; under DoneAfterJoin, DoneChan is closed by then."
JoinRule ==
    (~loopsDone /\ loopsDone') =>
        /\ stopChan' /\ ~handler'
        /\ DoneAfterJoin => doneChan'

\* In English: "A step of the engine: every rule holds, and something
\* changes."
Next ==
    /\ Monotone /\ StartRule /\ RegRule /\ QueueRule /\ HandlerRule
    /\ DoneRule /\ JoinRule
    /\ evars' /= evars

Spec == Init /\ [][Next]_evars

\* In English: "Promises a composed model may rely on: no handler runs once
\* DoneChan is closed or the loops are joined."
NoHandlerAfterDone == doneChan => ~handler
NoHandlerAfterJoin == loopsDone => ~handler
=============================================================================
