------------------------ MODULE LocalStateQueryCodec ------------------------
(***************************************************************************)
(* Which Shelley block queries the gOuroboros client sends, how it encodes *)
(* their set arguments, and which ones the gOuroboros server decodes,      *)
(* beside what a reference node decodes and answers.                       *)
(*                                                                         *)
(* A cell of the table is an era, a query and the filter a caller passes   *)
(* (nil, empty or non-empty). The model does no byte arithmetic: a set     *)
(* argument has one of three shapes on the wire, a plain array, an array   *)
(* behind tag 258, or CBOR null.                                           *)
(*                                                                         *)
(* Sources.                                                                *)
(*   ouroboros-consensus ec239d57f618,                                     *)
(*   ouroboros-consensus-cardano/src/shelley/Ouroboros/Consensus/Shelley/  *)
(*   Ledger/Query.hs:                                                      *)
(*   [Q1] 739, 765, 773: GetNonMyopicMemberRewards, GetStakePoolParams and *)
(*        GetStakeDelegDeposits encode their set with cardano-binary's     *)
(*        toCBOR, tag 258 in every era (golden                             *)
(*        Query_Shelley_GetStakePoolParams ends d9010280).                 *)
(*   [Q2] 742, 750, 760 (encode) and 855, 859, 864 (decode):               *)
(*        GetUTxOByAddress (6), GetFilteredDelegationsAndRewardAccounts    *)
(*        (10) and GetUTxOByTxIn (15) carry their set with                 *)
(*        LC.toEraCBOR @era / LC.fromEraCBOR @era.                         *)
(*   [Q3] 842-848, 871, 885, 886 and the Conway set queries 26, 30, 31:    *)
(*        requireCG refuses the query before Conway.                       *)
(*   [Q4] 872, 882, 498, 503: GetGovState (24) and GetAccountState (29)    *)
(*        are decoded without requireCG and supported on every version.    *)
(*   [Q5] 886, 507: GetFuturePParams (33) is decoded from Conway.          *)
(*   Goldens: golden/cardano/QueryVersion3/CardanoNodeToClientVersion19/   *)
(*   Query_<Era>_<Query>.                                                  *)
(*   cardano-ledger 1210d37fe6bd:                                          *)
(*   [L1] libs/cardano-ledger-core/src/Cardano/Ledger/Core/Era.hs 232-242: *)
(*        toEraCBOR and fromEraCBOR use the era's lowest protocol version; *)
(*        libs/cardano-ledger-core/internal/Cardano/Ledger/Internal/       *)
(*        Definition/Era.hs 95-140: Shelley 2, Allegra 3, Mary 4, Alonzo   *)
(*        5, Babbage 7, Conway 9, Dijkstra 12.                             *)
(*   [L2] libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Encoding/   *)
(*        Encoder.hs 479-490: encodeSet writes tag 258 from version 9.     *)
(*   [L3] libs/cardano-ledger-binary/src/Cardano/Ledger/Binary/Decoding/   *)
(*        Decoder.hs 933-952: decodeSet refuses tag 258 from 2 to 8 and    *)
(*        permits it, without enforcing it, from 9.                        *)
(*                                                                         *)
(* The gOuroboros code it is compared with:                                *)
(*   [G3] protocol/localstatequery/client.go (62fa36d1) 594, 674, 892: the *)
(*        three filters; fix/localstatequery-era-set-encoding eraFilterSet.*)
(*   [G4] client.go 941-945: GetAccountState refused before Conway;        *)
(*        fix/localstatequery-account-state-all-eras refuses only Byron.   *)
(*   [G5] protocol/localstatequery/queries.go 81, 244: no query type 33;   *)
(*        fix/localstatequery-decode-future-pparams adds                   *)
(*        ShelleyFuturePParamsQuery.                                       *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* README section "Reading a formula literally".                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    EraSetRule,        \* "main" or "fixed": the client's filter sets (N48)
    AccountStateRule,  \* "main" or "fixed": the client's era guard (N49)
    FuturePParamsRule, \* "main" or "fixed": the server's query 33 (N50)
    KnownDifferences   \* client queries left out of the offer check

VARIABLES era, query, filter

\* In English: the three things a table cell is made of.
\* Literally: "vars is defined as the tuple of era, query and filter."
vars == <<era, query, filter>>

\* In English: the Shelley-based eras, numbered as gOuroboros numbers them:
\* 1 Shelley, 2 Allegra, 3 Mary, 4 Alonzo, 5 Babbage, 6 Conway, 7 Dijkstra.
\* Literally: "Eras is defined as the integers from 1 to 7."
Eras == 1..7
\* In English: Conway's number.
\* Literally: "Conway is defined as 6."
Conway == 6

\* In English: the lowest protocol version of each era, which is the
\* version the reference encodes and decodes an era's query arguments at.
\* [L1]
\* Literally: "LowVersion of e is defined as: in the case e equals 1, 2; in
\*   the case e equals 2, 3; in the case e equals 3, 4; in the case e equals
\*   4, 5; in the case e equals 5, 7; in the case e equals 6, 9; in every
\*   other case, 12."
LowVersion(e) == CASE e = 1 -> 2 [] e = 2 -> 3 [] e = 3 -> 4 [] e = 4 -> 5
                   [] e = 5 -> 7 [] e = 6 -> 9 [] OTHER -> 12

\* In English: the queries whose set is written in the era's encoding. [Q2]
\* Literally: "EraSetQueries is defined as the set containing
\*   "UTxOByAddress", "FilteredDelegations" and "UTxOByTxIn"."
EraSetQueries == {"UTxOByAddress", "FilteredDelegations", "UTxOByTxIn"}
\* In English: the queries whose set is written with cardano-binary, tag
\* 258 in every era. [Q1]
\* Literally: "BinarySetQueries is defined as the set containing
\*   "NonMyopic", "StakePoolParams" and "StakeDelegDeposits"."
BinarySetQueries == {"NonMyopic", "StakePoolParams", "StakeDelegDeposits"}
\* In English: the Conway-only queries that carry a set. [Q3]
\* Literally: "ConwaySetQueries is defined as the set containing
\*   "DRepStakeDistr", "SPOStakeDistr" and "Proposals"."
ConwaySetQueries == {"DRepStakeDistr", "SPOStakeDistr", "Proposals"}
\* In English: every query that carries a set.
\* Literally: "SetQueries is defined as the union of EraSetQueries,
\*   BinarySetQueries and ConwaySetQueries."
SetQueries == EraSetQueries \cup BinarySetQueries \cup ConwaySetQueries
\* In English: the queries the gOuroboros client has a call for, in this
\* table.
\* Literally: "ClientQueries is defined as the union of SetQueries and the
\*   set containing "AccountState" and "GovState"."
ClientQueries == SetQueries \cup {"AccountState", "GovState"}
\* In English: the argument-free queries whose decoding the server side is
\* checked for.
\* Literally: "ServerQueries is defined as the set containing
\*   "AccountState", "GovState", "Constitution", "RatifyState" and
\*   "FuturePParams"."
ServerQueries ==
    {"AccountState", "GovState", "Constitution", "RatifyState", "FuturePParams"}
\* In English: the queries a reference node refuses before Conway. [Q3]
\* Literally: "ConwayOnly is defined as the union of ConwaySetQueries and
\*   the set containing "Constitution", "RatifyState" and "FuturePParams"."
ConwayOnly == ConwaySetQueries \cup {"Constitution", "RatifyState", "FuturePParams"}
\* In English: every query in the table.
\* Literally: "Queries is defined as the union of ClientQueries and
\*   ServerQueries."
Queries == ClientQueries \cup ServerQueries
\* In English: what the caller passes as the filter.
\* Literally: "Filters is defined as the set containing "nil", "empty" and
\*   "some"."
Filters == {"nil", "empty", "some"}

(***************************************************************************)
(* The reference node.                                                     *)
(***************************************************************************)

\* In English: a reference node decodes and answers query q in era e
\* exactly when q is not Conway-only or e is Conway or later. [Q3] [Q4] [Q5]
\* Literally: "RefAnswers of e and q is defined as: q is a member of
\*   ConwayOnly implies e is greater than or equal to Conway."
RefAnswers(e, q) == q \in ConwayOnly => e >= Conway

\* In English: the shape the reference writes q's set in, in era e: the
\* era-encoded sets carry the tag from version 9, the others always do; a
\* query with no set has the shape "none". [Q1] [Q2] [L2]
\* Literally: "RefShape of e and q is defined as: in the case q is a member
\*   of EraSetQueries, if LowVersion of e is at least 9 then "tagged" else
\*   "array"; in the case q is a member of SetQueries, "tagged"; in every
\*   other case, "none"."
RefShape(e, q) ==
    CASE q \in EraSetQueries -> IF LowVersion(e) >= 9 THEN "tagged" ELSE "array"
      [] q \in SetQueries    -> "tagged"
      [] OTHER               -> "none"

\* In English: a reference node decodes shape s as q's argument in era e:
\* null is never a set; an era-encoded set may carry the tag only from
\* version 9 and need not; a cardano-binary set must carry it; a query
\* with no argument takes none. [L3] [Q1]
\* Literally: "NodeDecodes of e, q and s is defined as: s is not "null",
\*   and q in EraSetQueries implies (s equals "tagged" implies LowVersion
\*   of e is at least 9), and q in BinarySetQueries implies s equals
\*   "tagged", and q in ConwaySetQueries implies s is "array" or
\*   "tagged", and q not in SetQueries implies s equals "none"."
NodeDecodes(e, q, s) ==
    /\ s # "null"
    /\ q \in EraSetQueries => (s = "tagged" => LowVersion(e) >= 9)
    /\ q \in BinarySetQueries => s = "tagged"
    /\ q \in ConwaySetQueries => s \in {"array", "tagged"}
    /\ q \notin SetQueries => s = "none"

(***************************************************************************)
(* gOuroboros.                                                             *)
(***************************************************************************)

\* In English: under rule r, the gOuroboros client sends q in era e: the
\* Conway set queries and GetGovState only from Conway (recorded, not
\* changed); GetAccountState from Conway on main, and in every Shelley era
\* with the fix. [G4]
\* Literally: "GoSendsBy of r, e and q is defined as: in the case q is a
\*   member of ConwaySetQueries or q equals "GovState", e is at least
\*   Conway; in the case q equals "AccountState", e is at least Conway;
\*   in every other case, TRUE."
GoSendsBy(r, e, q) ==
    CASE q \in ConwaySetQueries \/ q = "GovState" -> e >= Conway
      [] q = "AccountState" /\ r = "main"          -> e >= Conway
      [] OTHER                                     -> TRUE

\* In English: under rule r, the shape the gOuroboros client writes q's
\* set in, for filter f. On main the UTxO filters are the caller's slice
\* as it is, so nil becomes null, and the delegations filter is always
\* tagged. The fix (eraFilterSet) tags the three filters from Conway only
\* and sends nil as the empty set. The cardano-binary and Conway sets are
\* always tagged and nil is the empty set. [G3]
\* Literally: "GoShapeBy of r, e, q and f is defined as: in the case r
\*   equals "fixed" and q is a member of EraSetQueries, if e is at least
\*   Conway then "tagged" else "array"; in the case q is "UTxOByAddress"
\*   or "UTxOByTxIn", if f equals "nil" then "null" else "array"; in the
\*   case q equals "FilteredDelegations", "tagged"; in the case q is a
\*   member of SetQueries, "tagged"; in every other case, "none"."
GoShapeBy(r, e, q, f) ==
    CASE r = "fixed" /\ q \in EraSetQueries ->
             IF e >= Conway THEN "tagged" ELSE "array"
      [] q \in {"UTxOByAddress", "UTxOByTxIn"} ->
             IF f = "nil" THEN "null" ELSE "array"
      [] q = "FilteredDelegations" -> "tagged"
      [] q \in SetQueries          -> "tagged"
      [] OTHER                     -> "none"

\* In English: under rule r, the gOuroboros server decodes query q (in any
\* era; the era is the callback's to judge). Main has no query type 33.
\* [G5]
\* Literally: "GoDecodesBy of r and q is defined as: q equals
\*   "FuturePParams" implies r equals "fixed"."
GoDecodesBy(r, q) == q = "FuturePParams" => r = "fixed"

\* In English: the rules this configuration runs.
\* Literally: "GoSends of e and q is defined as GoSendsBy of
\*   AccountStateRule, e and q; GoShape of e, q and f is defined as
\*   GoShapeBy of EraSetRule, e, q and f; GoDecodes of q is defined as
\*   GoDecodesBy of FuturePParamsRule and q."
GoSends(e, q) == GoSendsBy(AccountStateRule, e, q)
GoShape(e, q, f) == GoShapeBy(EraSetRule, e, q, f)
GoDecodes(q) == GoDecodesBy(FuturePParamsRule, q)

(***************************************************************************)
(* The table: every cell is an initial state, and nothing moves.           *)
(***************************************************************************)

\* In English: any era, any query, any filter.
\* Literally: "Init is defined as: era is a member of Eras, and query is a
\*   member of Queries, and filter is a member of Filters."
Init == era \in Eras /\ query \in Queries /\ filter \in Filters
\* In English: a cell does not change.
\* Literally: "Next is defined as: vars is unchanged."
Next == UNCHANGED vars
\* In English: start in a cell and stay there.
\* Literally: "Spec is defined as: Init, and always either Next or vars
\*   unchanged."
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

\* In English: every set argument the client sends is one a reference node
\* decodes in that era (N48; decodeSet [L3]).
\* Literally: "ClientSetsDecode is defined as: query is a member of
\*   ClientQueries and GoSends of era and query imply NodeDecodes of era,
\*   query and GoShape of era, query and filter."
ClientSetsDecode ==
    query \in ClientQueries /\ GoSends(era, query)
        => NodeDecodes(era, query, GoShape(era, query, filter))

\* In English: every set argument the client sends has the shape the
\* reference writes (N48; the Query_<Era>_* goldens).
\* Literally: "ClientSetsAsReference is defined as: query is a member of
\*   ClientQueries and GoSends of era and query imply GoShape of era, query
\*   and filter equals RefShape of era and query."
ClientSetsAsReference ==
    query \in ClientQueries /\ GoSends(era, query)
        => GoShape(era, query, filter) = RefShape(era, query)

\* In English: the client offers every query a reference node answers in
\* that era, except the known differences (N49; [Q4]).
\* Literally: "ClientOffersAnswered is defined as: query is a member of
\*   ClientQueries without the members of KnownDifferences, and RefAnswers
\*   of era and query, imply GoSends of era and query."
ClientOffersAnswered ==
    query \in ClientQueries \ KnownDifferences /\ RefAnswers(era, query)
        => GoSends(era, query)

\* In English: the client never sends a query a reference node refuses.
\* Literally: "ClientSendsAnswered is defined as: query is a member of
\*   ClientQueries and GoSends of era and query imply RefAnswers of era and
\*   query."
ClientSendsAnswered ==
    query \in ClientQueries /\ GoSends(era, query) => RefAnswers(era, query)

\* In English: the server decodes every query a reference node decodes in
\* some era (N50; [Q5]).
\* Literally: "ServerDecodesAnswered is defined as: query is a member of
\*   ServerQueries and RefAnswers of era and query imply GoDecodes of
\*   query."
ServerDecodesAnswered ==
    query \in ServerQueries /\ RefAnswers(era, query) => GoDecodes(query)

\* In English: the server decodes only what a reference node decodes in
\* that era. gOuroboros does not hold this: it hands a Conway-only query
\* sent in an earlier era to the callback, which knows the era. Checked
\* only by a probe.
\* Literally: "ServerRefusesAsReference is defined as: query is a member of
\*   ServerQueries and GoDecodes of query imply RefAnswers of era and
\*   query."
ServerRefusesAsReference ==
    query \in ServerQueries /\ GoDecodes(query) => RefAnswers(era, query)

(***************************************************************************)
(* The Go tests' cells, counted on main.                                   *)
(***************************************************************************)

\* In English: TestEraFilterSetEncoding's 35 cells: five calls (address
\* filter empty and nil, delegations nil, txin filter empty and nil) in
\* seven eras; on main a cell fails when its shape is not the reference's.
\* Literally: "EraSetCellsFailingOnMain is defined as the set of tuples c
\*   in the product of Eras and the set of the five calls such that
\*   GoShapeBy of "main", c's era, c's query and c's filter is not
\*   RefShape of c's era and c's query."
EraSetCellsFailingOnMain ==
    {c \in Eras \X {<<"UTxOByAddress", "empty">>, <<"UTxOByAddress", "nil">>,
                    <<"FilteredDelegations", "nil">>,
                    <<"UTxOByTxIn", "empty">>, <<"UTxOByTxIn", "nil">>} :
        GoShapeBy("main", c[1], c[2][1], c[2][2]) # RefShape(c[1], c[2][1])}

\* In English: 23 of the 35 cells fail on main, as the Go test does.
\* Literally: "assume the number of members of EraSetCellsFailingOnMain
\*   equals 23."
ASSUME Cardinality(EraSetCellsFailingOnMain) = 23

\* In English: TestGetAccountStateEveryShelleyEra fails in five eras on
\* main: Shelley through Babbage.
\* Literally: "assume the set of eras e such that RefAnswers of e and
\*   "AccountState" and not GoSendsBy of "main", e and "AccountState"
\*   equals the integers from 1 to 5."
ASSUME {e \in Eras : RefAnswers(e, "AccountState")
                     /\ ~GoSendsBy("main", e, "AccountState")} = 1..5

\* In English: TestDecodeGetFuturePParamsQuery's two cells, Conway and
\* Dijkstra, are the eras where the reference decodes query 33 and main
\* does not.
\* Literally: "assume the set of eras e such that RefAnswers of e and
\*   "FuturePParams" and not GoDecodesBy of "main" and "FuturePParams"
\*   equals the set containing 6 and 7."
ASSUME {e \in Eras : RefAnswers(e, "FuturePParams")
                     /\ ~GoDecodesBy("main", "FuturePParams")} = {6, 7}
=============================================================================
