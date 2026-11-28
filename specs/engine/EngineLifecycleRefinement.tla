------------------------- MODULE EngineLifecycleRefinement -------------------------
(***************************************************************************)
(* Checks that EngineLifecycle, the step-by-step engine, refines the       *)
(* Engine interface (specs/common/Engine.tla), so a connection-level      *)
(* model may compose engines through that interface alone.                *)
(*                                                                         *)
(* The refinement mapping says, for each interface object, which          *)
(* EngineLifecycle state stands for it (Specifying Systems, section 5.8;   *)
(* docs/glossary.md "refinement mapping"). TLC then checks the property   *)
(* Abs!Spec: every EngineLifecycle step, seen through the mapping, obeys   *)
(* every rule of the interface. A step that breaks one is reported as a    *)
(* violated property, with the trace.                                      *)
(*                                                                         *)
(* EngineLifecycle has no send queue, so sendQ maps to an empty channel    *)
(* that never changes: this check covers the lifecycle half of the         *)
(* interface; the queue half is checked by the composed connection model   *)
(* (specs/connection/ConnectionEngines.tla).                               *)
(***************************************************************************)
EXTENDS EngineLifecycle

CONSTANTS QCap, DoneAfterJoin

\* In English: "The steps of a stop call made inline by some goroutine."
StopPcs == {"s_once", "s_onceWait", "s_lock", "s_unlock", "s_close",
            "s_waitRead", "s_unreg", "s_join"}

\* In English: "recvLoop is inside MessageHandlerFunc: running it, waiting
\* inside it, in the restart it makes, or in a Stop the handler called."
HandlerRunning ==
    \/ pc["rv"] \in {"handler", "hWait", "hWaitCaller", "restart"}
    \/ pc["rv"] \in StopPcs /\ ret["rv"] \in {"wait", "restart"}

\* In English: "The join is complete: stop closed stopChan and every
\* goroutine the join counts has exited or never started."
JoinComplete == stopChan /\ \A g \in Joined : Over(g)

\* In English: "The registration: released once stop's Once body has
\* unregistered or suspended the role, registered once Start started the
\* loops, none before."
RegOf == IF once = "done" THEN "released"
         ELSE IF started THEN "registered" ELSE "none"

Abs == INSTANCE Engine WITH
    started    <- started,
    stopChan   <- stopChan,
    sendQ      <- [buf |-> <<>>, cap |-> QCap, closed |-> FALSE],
    handler    <- HandlerRunning,
    doneChan   <- doneChan,
    loopsDone  <- JoinComplete,
    reg        <- RegOf,
    connClosed <- muxDone

\* In English: "EngineLifecycle refines the Engine interface."
RefinesEngine == Abs!Spec
=============================================================================
