----------------------------- MODULE LeiosNotify -----------------------------
(***************************************************************************)
(* Model 12, LeiosNotify: the gOuroboros client's notification loop, its   *)
(* Stop, and a server that answers every request, on one connection.       *)
(*                                                                         *)
(* The protocol is not in the network specification. It follows the        *)
(* reference node (ouroboros-consensus) and CIP-0164; README.md says how   *)
(* authoritative each is.                                                  *)
(*                                                                         *)
(* The client (protocol/leiosnotify/client.go) runs:                       *)
(*   Sync                sends one request and starts the loop.            *)
(*   notificationLoop    takes one notification at a time. While earlier   *)
(*                       requests are still owed (pipelinedRequestNext)    *)
(*                       it waits for the next; when none are, it checks   *)
(*                       quitting and then sends PipelineLimit requests,   *)
(*                       one SendMessage at a time.                        *)
(*   Stop                sets quitting and sends MsgQuit.                  *)
(* In gOuroboros today nothing orders Stop against the loop's refill, so   *)
(* MsgQuit can land in the middle of it. StopLocksBurst models the fix:    *)
(* one lock held from the quitting check through the sends, and by Stop.   *)
(*                                                                         *)
(* Questions:                                                              *)
(*   NoRequestAfterQuit   does a request ever follow MsgQuit on the wire?  *)
(*   ClientNoViolation    does the client ever see a reply its state does  *)
(*                        not allow (MsgDone with requests unanswered)?    *)
(*   LoopCanProgress      while the loop waits and the client has not      *)
(*                        quit, is a notification still owed for every     *)
(*                        request the loop is counting on?                 *)
(*   EveryRequestAnswered once both sides are done, was every request on   *)
(*                        the wire answered?                               *)
(*   Deadlock             TLC checks it; the only stop is Ended.           *)
(*                                                                         *)
(* Sources (README.md has links):                                          *)
(*   [R1] ouroboros-consensus ec239d57f618, .../LeiosNotify/Type.hs        *)
(*        126-162: Idle(client) -Req-> Busy, Idle -MsgQuit-> Quit,         *)
(*        Busy(server) -notification or MsgCanceled-> Idle,                *)
(*        Quit(server) -MsgDone-> Done.                                    *)
(*   [R2] .../LeiosNotify/Client.hs 131-236: the client pipelines          *)
(*        requests; on terminate it pipelines MsgQuit and sends nothing    *)
(*        more (drainThePipe); MsgCanceled before MsgQuit disconnects      *)
(*        the peer (104-111).                                              *)
(*   [R3] .../LeiosNotify/Server.hs 51-57, 94-134: once MsgQuit arrives    *)
(*        the server answers every outstanding request with MsgCanceled,   *)
(*        then MsgDone.                                                    *)
(*   [G1] gOuroboros 61046085, protocol/leiosnotify/client.go (Sync,       *)
(*        notificationLoop, Stop, messageHandler) and server.go            *)
(*        (serveRequestNext, handleQuit).                                  *)
(*   [G2] protocol/protocol.go sendLoop: a request sent after MsgQuit is   *)
(*        written if replies are still owed (Busy lets the client          *)
(*        pipeline it) and otherwise held for agency that never returns.   *)
(*                                                                         *)
(* Not modelled: ErrStopNotificationProcess and its drain (covered by      *)
(* TestNotificationLoopDrainsOnStop), byte budgets, timeouts, and which   *)
(* notification a reply carries.                                           *)
(*                                                                         *)
(* Symbols are explained in specs/01-keepalive/KeepAlive.tla's header.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    PipelineLimit,        \* requests per refill (Config.PipelineLimit)
    MaxRequests,          \* stop refilling after this many (keeps it finite)
    StopLocksBurst,       \* FALSE today; TRUE: the fix (one lock, Sync checks quitting)
    SyncChecksQuitFirst,  \* TRUE: Sync checks quitting before "loop already running"
                          \* FALSE: the order at PR 3160 head cfa1edeb
    CancelIsErrorBeforeQuit, \* FALSE today; TRUE: MsgCanceled before MsgQuit is refused [R2]
    RogueCancel,          \* TRUE: the server may cancel before MsgQuit (misbehaving)
    ServerCancelsOnQuit,  \* TRUE as in [R3]; FALSE is a mutation
    SourceDry             \* TRUE: the server has no notification to give (nil RequestNextFunc)

VARIABLES
    loop,       \* the loop: "Off", "Wait" (for a notification), "Burst" (refilling)
    burstLeft,  \* requests the current refill still has to send
    pipelined,  \* pipelinedRequestNext: notifications owed before the next refill
    quitting,   \* Stop has run
    inbox,      \* notifications handed to the loop and not yet taken
    owed,       \* requests on the wire the client has no reply to yet
    sent,       \* requests the client has written in all
    held,       \* requests the client queued after MsgQuit that were never written
    c2s,        \* client-to-server messages in flight, oldest first
    s2c,        \* server-to-client messages in flight, oldest first
    srv,        \* the server: "Idle", "Busy", "Quit", "Done"
    cli,        \* the client: "Run", "Done", "Violation", "Refused"
    reqAfterQuit, \* a request was written after MsgQuit
    answered    \* requests the server has answered

\* Literally: "vars is defined as the tuple of all fourteen variables."
vars == <<loop, burstLeft, pipelined, quitting, inbox, owed, sent, held,
          c2s, s2c, srv, cli, reqAfterQuit, answered>>

\* In English: "MsgQuit is on the wire, or has been read by the server."
\* Literally: "QuitSent is defined as quitting."
QuitSent == quitting

\* In English: "The loop is off, nothing is owed, queued, sent or held, nothing
\* is in flight, the server is idle, the client is running, and nothing has
\* been answered."
\* Literally: "Init is defined as: loop equals "Off" and burstLeft equals 0 and
\*   pipelined equals 0, and quitting equals FALSE and inbox equals 0 and owed
\*   equals 0 and sent equals 0 and held equals 0, and c2s equals the empty
\*   sequence and s2c equals the empty sequence, and srv equals "Idle" and cli
\*   equals "Run", and reqAfterQuit equals FALSE and answered equals 0."
Init ==
    /\ loop = "Off" /\ burstLeft = 0 /\ pipelined = 0
    /\ quitting = FALSE /\ inbox = 0 /\ owed = 0 /\ sent = 0 /\ held = 0
    /\ c2s = <<>> /\ s2c = <<>>
    /\ srv = "Idle" /\ cli = "Run"
    /\ reqAfterQuit = FALSE /\ answered = 0

\* In English: "The client writes a request [G2]. Before MsgQuit it always
\* goes out. After it, it goes out only if replies are still owed (the
\* client's state is still Busy, which lets it pipeline); otherwise it is
\* held for agency that never comes back." Gives the next values of owed,
\* sent, held, c2s and reqAfterQuit.
\* Literally: "WriteRequest is defined as: if quitting is true and owed equals
\*   0, then held in the next state equals held plus 1, and owed, sent, c2s and
\*   reqAfterQuit are unchanged; else c2s in the next state equals c2s with
\*   "Req" appended, and owed in the next state equals owed plus 1, and sent in
\*   the next state equals sent plus 1, and reqAfterQuit in the next state
\*   equals (reqAfterQuit, or quitting), and held is unchanged."
WriteRequest ==
    IF quitting /\ owed = 0
    THEN /\ held' = held + 1                              \* held, never written
         /\ UNCHANGED <<owed, sent, c2s, reqAfterQuit>>
    ELSE /\ c2s' = Append(c2s, "Req")                     \* written
         /\ owed' = owed + 1
         /\ sent' = sent + 1
         /\ reqAfterQuit' = (reqAfterQuit \/ quitting)    \* remember if MsgQuit went first
         /\ UNCHANGED held

\* --- The client. ----------------------------------------------------------

\* In English: "What Sync does if called now [G1]: refuse because Stop has
\* run (with the fix), refuse because the loop is still running, or send."
\* Which refusal comes first is SyncChecksQuitFirst; after Stop the loop
\* stays in Wait until the protocol ends, so the order is visible.
\* Literally: "SyncAnswer is defined as: if StopLocksBurst is true and quitting
\*   is true and (SyncChecksQuitFirst is true, or loop equals "Off"), then
\*   "ShuttingDown"; else if loop does not equal "Off" then "Running"; else
\*   "Sends"."
SyncAnswer ==
    IF StopLocksBurst /\ quitting /\ (SyncChecksQuitFirst \/ loop = "Off")
        THEN "ShuttingDown"
    ELSE IF loop /= "Off" THEN "Running"
    ELSE "Sends"

\* In English: "Sync, when it would send: send one request, reset the
\* counter, and start the loop."
\* Literally: "Sync is defined as: cli equals "Run" and sent is less than
\*   MaxRequests, and SyncAnswer equals "Sends", and WriteRequest, and
\*   pipelined in the next state equals 0 and loop in the next state equals
\*   "Wait", and burstLeft, quitting, inbox, s2c, srv, cli and answered are
\*   unchanged."
Sync ==
    /\ cli = "Run" /\ sent < MaxRequests
    /\ SyncAnswer = "Sends"
    /\ WriteRequest
    /\ pipelined' = 0 /\ loop' = "Wait"
    /\ UNCHANGED <<burstLeft, quitting, inbox, s2c, srv, cli, answered>>

\* In English: "The loop takes a notification. If more are owed it waits
\* again; otherwise it checks quitting and stops, or, with requests left,
\* starts a refill." With StopLocksBurst the check and the refill are one
\* critical section with Stop, which Stop below honours.
\* Literally: "LoopTake is defined as: cli equals "Run" and loop equals "Wait"
\*   and inbox is greater than 0, and inbox in the next state equals inbox
\*   minus 1, and if pipelined is greater than 0, then pipelined in the next
\*   state equals pipelined minus 1 and loop in the next state equals "Wait",
\*   and burstLeft is unchanged; else if quitting is true or sent plus
\*   PipelineLimit is greater than MaxRequests, then loop in the next state
\*   equals "Off" and pipelined and burstLeft are unchanged; else loop in the
\*   next state equals "Burst" and burstLeft in the next state equals
\*   PipelineLimit, and pipelined is unchanged; and quitting, owed, sent, held,
\*   c2s, s2c, srv, cli, reqAfterQuit and answered are unchanged."
LoopTake ==
    /\ cli = "Run" /\ loop = "Wait" /\ inbox > 0
    /\ inbox' = inbox - 1
    /\ IF pipelined > 0
       THEN /\ pipelined' = pipelined - 1 /\ loop' = "Wait"
            /\ UNCHANGED burstLeft
       ELSE IF quitting \/ sent + PipelineLimit > MaxRequests
            THEN /\ loop' = "Off" /\ UNCHANGED <<pipelined, burstLeft>>
            ELSE /\ loop' = "Burst" /\ burstLeft' = PipelineLimit
                 /\ UNCHANGED pipelined
    /\ UNCHANGED <<quitting, owed, sent, held, c2s, s2c, srv, cli,
                   reqAfterQuit, answered>>

\* In English: "One SendMessage of the refill. After the last, the loop
\* expects PipelineLimit - 1 more notifications than the one it waits for."
\* Literally: "LoopSend is defined as: cli equals "Run" and loop equals "Burst"
\*   and burstLeft is greater than 0, and WriteRequest, and burstLeft in the
\*   next state equals burstLeft minus 1, and if burstLeft equals 1, then loop
\*   in the next state equals "Wait" and pipelined in the next state equals
\*   PipelineLimit minus 1, else loop and pipelined are unchanged; and
\*   quitting, inbox, s2c, srv, cli and answered are unchanged."
LoopSend ==
    /\ cli = "Run" /\ loop = "Burst" /\ burstLeft > 0
    /\ WriteRequest
    /\ burstLeft' = burstLeft - 1
    /\ IF burstLeft = 1
       THEN loop' = "Wait" /\ pipelined' = PipelineLimit - 1
       ELSE UNCHANGED <<loop, pipelined>>
    /\ UNCHANGED <<quitting, inbox, s2c, srv, cli, answered>>

\* In English: "Stop, once: set quitting and write MsgQuit, which is legal
\* in Idle and pipelined in Busy. With the fix it waits while a refill holds
\* the lock."
\* Literally: "Stop is defined as: cli equals "Run" and quitting is not true,
\*   and it is not the case that (StopLocksBurst is true and loop equals
\*   "Burst"), and quitting in the next state equals TRUE, and c2s in the next
\*   state equals c2s with "Quit" appended, and loop, burstLeft, pipelined,
\*   inbox, owed, sent, held, s2c, srv, cli, reqAfterQuit and answered are
\*   unchanged."
Stop ==
    /\ cli = "Run" /\ ~quitting
    /\ ~(StopLocksBurst /\ loop = "Burst")               \* the fix: wait for the refill
    /\ quitting' = TRUE
    /\ c2s' = Append(c2s, "Quit")
    /\ UNCHANGED <<loop, burstLeft, pipelined, inbox, owed, sent, held, s2c,
                   srv, cli, reqAfterQuit, answered>>

\* In English: "The client reads the oldest reply [R1][G1]. A notification
\* or MsgCanceled must answer an owed request; a notification goes to the
\* loop. MsgCanceled before MsgQuit is refused with the fix [R2]. MsgDone
\* must come after MsgQuit with nothing owed."
\* Literally: "ClientRecv is defined as: cli equals "Run" and s2c does not
\*   equal the empty sequence, and, letting m be the head of s2c: in the case m
\*   equals "Note", (if owed equals 0 then cli in the next state equals
\*   "Violation" and owed and inbox are unchanged, else owed in the next state
\*   equals owed minus 1 and inbox in the next state equals inbox plus 1 and
\*   cli is unchanged); in the case m equals "Canceled", (if owed equals 0 then
\*   cli in the next state equals "Violation" and owed and inbox are unchanged;
\*   else if CancelIsErrorBeforeQuit is true and quitting is not true, then cli
\*   in the next state equals "Refused" and owed and inbox are unchanged; else
\*   owed in the next state equals owed minus 1 and cli and inbox are
\*   unchanged); in the case m equals "Done", (if quitting is true and owed
\*   equals 0 then cli in the next state equals "Done" and owed and inbox are
\*   unchanged, else cli in the next state equals "Violation" and owed and
\*   inbox are unchanged); and s2c in the next state equals the tail of s2c,
\*   and loop, burstLeft, pipelined, quitting, sent, held, c2s, srv,
\*   reqAfterQuit and answered are unchanged."
ClientRecv ==
    /\ cli = "Run" /\ s2c /= <<>>
    /\ LET m == Head(s2c) IN
       CASE m = "Note" ->
              IF owed = 0 THEN cli' = "Violation" /\ UNCHANGED <<owed, inbox>>
              ELSE owed' = owed - 1 /\ inbox' = inbox + 1 /\ UNCHANGED cli
         [] m = "Canceled" ->
              IF owed = 0 THEN cli' = "Violation" /\ UNCHANGED <<owed, inbox>>
              ELSE IF CancelIsErrorBeforeQuit /\ ~quitting
                   THEN cli' = "Refused" /\ UNCHANGED <<owed, inbox>>
                   ELSE owed' = owed - 1 /\ UNCHANGED <<cli, inbox>>
         [] m = "Done" ->
              IF quitting /\ owed = 0 THEN cli' = "Done" /\ UNCHANGED <<owed, inbox>>
              ELSE cli' = "Violation" /\ UNCHANGED <<owed, inbox>>
    /\ s2c' = Tail(s2c)
    /\ UNCHANGED <<loop, burstLeft, pipelined, quitting, sent, held, c2s, srv,
                   reqAfterQuit, answered>>

\* --- The server. ----------------------------------------------------------

\* In English: "In Idle the server handles the oldest message: a request
\* makes it Busy; MsgQuit makes it answer MsgDone and finish [R1][R3]. A
\* request after that is the first of a new run the client knows nothing
\* about, and the server serves it (it restarts after MsgDone)."
\* Literally: "ServerRead is defined as: c2s does not equal the empty sequence
\*   and srv is a member of the set containing "Idle" and "Done", and, letting
\*   m be the head of c2s: if m equals "Req", then srv in the next state equals
\*   "Busy" and s2c is unchanged, else srv in the next state equals "Done" and
\*   s2c in the next state equals s2c with "Done" appended; and c2s in the next
\*   state equals the tail of c2s, and loop, burstLeft, pipelined, quitting,
\*   inbox, owed, sent, held, cli, reqAfterQuit and answered are unchanged."
ServerRead ==
    /\ c2s /= <<>> /\ srv \in {"Idle", "Done"}
    /\ LET m == Head(c2s) IN
       IF m = "Req"
       THEN srv' = "Busy" /\ UNCHANGED s2c
       ELSE srv' = "Done" /\ s2c' = Append(s2c, "Done")
    /\ c2s' = Tail(c2s)
    /\ UNCHANGED <<loop, burstLeft, pipelined, quitting, inbox, owed, sent,
                   held, cli, reqAfterQuit, answered>>

\* In English: "In Busy the server answers: a notification if its source
\* has one, or MsgCanceled once MsgQuit has arrived [R3] (or at any time,
\* if it misbehaves)."
\* Literally: "ServerAnswer of m is defined as: srv equals "Busy", and (m
\*   equals "Note" and SourceDry is not true, or m equals "Canceled" and
\*   (RogueCancel is true, or ServerCancelsOnQuit is true and QuitSent is
\*   true)), and srv in the next state equals "Idle", and s2c in the next state
\*   equals s2c with m appended, and answered in the next state equals answered
\*   plus 1, and loop, burstLeft, pipelined, quitting, inbox, owed, sent, held,
\*   c2s, cli and reqAfterQuit are unchanged."
ServerAnswer(m) ==
    /\ srv = "Busy"
    /\ \/ m = "Note" /\ ~SourceDry
       \/ m = "Canceled" /\ (RogueCancel \/ (ServerCancelsOnQuit /\ QuitSent))
    /\ srv' = "Idle"
    /\ s2c' = Append(s2c, m)
    /\ answered' = answered + 1
    /\ UNCHANGED <<loop, burstLeft, pipelined, quitting, inbox, owed, sent,
                   held, c2s, cli, reqAfterQuit>>

\* In English: "The connection is over: the client finished or hung up."
\* Literally: "Ended is defined as: cli does not equal "Run"."
Ended == cli /= "Run"

\* In English: "A step is a client step, a server step, or, once the connection
\* is over, nothing."
\* Literally: "Next is defined as: Sync, or LoopTake, or LoopSend, or Stop, or
\*   ClientRecv, or ServerRead, or ServerAnswer of "Note", or ServerAnswer of
\*   "Canceled", or Ended is true and vars is unchanged."
Next ==
    \/ Sync \/ LoopTake \/ LoopSend \/ Stop \/ ClientRecv
    \/ ServerRead \/ ServerAnswer("Note") \/ ServerAnswer("Canceled")
    \/ Ended /\ UNCHANGED vars

\* In English: "Start in Init, and from then on every step is a Next step."
\* Literally: "Spec is defined as: Init holds at the start, and always, every
\*   step is a Next step or a step that leaves vars unchanged."
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* In English: "No request was written after MsgQuit [R2]."
\* Literally: "NoRequestAfterQuit is defined as: reqAfterQuit is not true."
NoRequestAfterQuit == ~reqAfterQuit

\* In English: "The client never saw a reply its state did not allow."
\* Literally: "ClientNoViolation is defined as: cli does not equal
\*   "Violation"."
ClientNoViolation == cli /= "Violation"

\* In English: "While the loop waits and the client has not quit, the
\* notifications it counts on (the one it waits for and pipelined more) are
\* all still coming: handed over, or owed by the server."
\* Literally: "LoopCanProgress is defined as: if cli equals "Run" and loop
\*   equals "Wait" and quitting is not true, then inbox plus owed is greater
\*   than or equal to pipelined plus 1."
LoopCanProgress ==
    (cli = "Run" /\ loop = "Wait" /\ ~quitting) =>
        inbox + owed >= pipelined + 1

\* In English: "When the client is done, every request the server read was
\* answered, and nothing is left in flight."
\* Literally: "EveryRequestAnswered is defined as: if cli equals "Done", then
\*   (answered equals sent, and c2s equals the empty sequence, and srv is a
\*   member of the set containing "Idle" and "Done")."
EveryRequestAnswered ==
    cli = "Done" => (answered = sent /\ c2s = <<>> /\ srv \in {"Idle", "Done"})

\* In English: "With the fix, Sync after Stop reports the shutdown, whether
\* or not the loop is still running."
\* Literally: "SyncAfterStopReportsShutdown is defined as: if StopLocksBurst is
\*   true and cli equals "Run" and quitting is true, then SyncAnswer equals
\*   "ShuttingDown"."
SyncAfterStopReportsShutdown ==
    (StopLocksBurst /\ cli = "Run" /\ quitting) => SyncAnswer = "ShuttingDown"

\* Probes, EXPECTED to be violated: each claims something never happens.
\* In English: "Stop never runs during a refill."
\* Literally: "ProbeNoStopDuringBurst is defined as: it is not the case that
\*   (quitting is true and loop equals "Burst")."
ProbeNoStopDuringBurst == ~(quitting /\ loop = "Burst")
\* In English: "The client never finishes cleanly."
\* Literally: "ProbeNeverDone is defined as: cli does not equal "Done"."
ProbeNeverDone == cli /= "Done"
\* In English: "The server never cancels a request."
\* Literally: "ProbeNeverCanceled is defined as: for all i in 1 through the
\*   length of s2c, element i of s2c does not equal "Canceled"."
ProbeNeverCanceled == \A i \in 1..Len(s2c) : s2c[i] /= "Canceled"
\* In English: "A request is never held after MsgQuit."
\* Literally: "ProbeNeverHeld is defined as: held equals 0."
ProbeNeverHeld == held = 0
\* In English: "The loop is never still running after Stop."
\* Literally: "ProbeLoopNeverRunsAfterStop is defined as: it is not the case
\*   that (cli equals "Run" and quitting is true and loop does not equal
\*   "Off")."
ProbeLoopNeverRunsAfterStop == ~(cli = "Run" /\ quitting /\ loop /= "Off")
=============================================================================
