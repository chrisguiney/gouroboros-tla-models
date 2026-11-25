------------------------------ MODULE TxBodyId ------------------------------
(***************************************************************************)
(* What gOuroboros hashes for a transaction body's id, as a table over     *)
(* abstract bodies: the bytes shape it hashes against the reference's      *)
(* "Blake2b-256 of the body's CBOR serialization".                         *)
(*                                                                         *)
(* A body is a fee (two values stand for "two different bodies"), whether  *)
(* it carries the bytes it was decoded from, whether it is a Dijkstra body *)
(* with an empty, non-nil CIP-159 map (keys 24 to 27), and whether it can  *)
(* be encoded at all. The hash is modelled as collision-free: an id is the *)
(* thing hashed, so two ids are equal exactly when the hashed bytes are.   *)
(*                                                                         *)
(* Sources:                                                                *)
(*   [S1] cardano-ledger 1210d37fe6bd eras/shelley/formal-spec/            *)
(*        crypto-details.tex 64-69: "txid ... is implemented as the        *)
(*        BLAKE2b-256 hash of the CBOR serialization of the transaction    *)
(*        body".                                                           *)
(*   [R1] cardano-ledger 1210d37fe6bd eras/dijkstra/impl/src/Cardano/      *)
(*        Ledger/Dijkstra/TxBody.hs 518-552 encodeTxBodyRaw: Omit on an    *)
(*        empty map at keys 24 to 27, so such a body encodes as the body   *)
(*        without them; 449-452: the decoder refuses an empty one, so no   *)
(*        decoded body carries one. A reference body always keeps its      *)
(*        bytes, so an unencodable body cannot arise there.                *)
(*                                                                         *)
(* gOuroboros ledger/common/tx.go:                                         *)
(*   [G1] main before #3141 (d0b95845 719-721): Id() hashes b.Cbor(); a    *)
(*        body built in code has none, so every such body gets the hash of *)
(*        empty input.                                                     *)
(*   [G2] #3141 first draft (review follow-up in DRIFT L2): hashes the     *)
(*        encoding when no bytes are stored, but a Dijkstra body with an   *)
(*        empty CIP-159 map failed to encode and fell back to the empty-   *)
(*        input hash, so {TxFee:5} and {TxFee:6} collided again.           *)
(*   [G3] #3141 (bcd8a77b, TransactionBodyId 734-746 and                   *)
(*        ledger/dijkstra/dijkstra.go): stored bytes if any, else the      *)
(*        encoding with empty maps omitted; an unencodable body gets the   *)
(*        zero id rather than a hash that looks real.                      *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    GoRule  \* "main" [G1], "draft" [G2] or "fix" [G3]

VARIABLE body  \* the one body this behaviour takes the id of

\* In English: "Every abstract body. A decoded body never has an empty
\*   CIP-159 map [R1] and is always encodable (it has its bytes)."
\* Literally: "Bodies is defined as the set of records b whose fee is 5 or
\*   6 and whose stored, emptyMap and encodable are booleans, such that if
\*   stored of b then emptyMap of b is false and encodable of b is true."
Bodies == {b \in [fee : {5, 6}, stored : BOOLEAN, emptyMap : BOOLEAN,
                  encodable : BOOLEAN] :
              b.stored => (~b.emptyMap /\ b.encodable)}

\* In English: "The hash of the reference serialization of a body: its
\*   contents, with an empty CIP-159 map omitted [R1]. Every id below is a
\*   record of what was hashed, so ids compare as hashes do."
\* Literally: "Encode of b is defined as the record whose kind is "body"
\*   and whose fee is the fee of b."
Encode(b) == [kind |-> "body", fee |-> b.fee]

\* In English: "The hash of empty input, the same for every body."
\* Literally: "EmptyInput is defined as the record whose kind is
\*   "emptyInput" and whose fee is 0."
EmptyInput == [kind |-> "emptyInput", fee |-> 0]

\* In English: "The zero id: all zero bytes, not a hash of anything."
\* Literally: "Zero is defined as the record whose kind is "zero" and
\*   whose fee is 0."
Zero == [kind |-> "zero", fee |-> 0]

\* In English: "The reference id: the hash of the serialization." [S1]
\* Literally: "RefId of b is defined as Encode of b."
RefId(b) == Encode(b)

\* In English: "Does the encoder gOuroboros uses produce bytes for b? Not
\*   for an unencodable body, and, in the first draft, not for one with an
\*   empty CIP-159 map." [G2][G3]
\* Literally: "GoEncodes of b is defined as: encodable of b, and not
\*   (GoRule equals "draft" and emptyMap of b)."
GoEncodes(b) == b.encodable /\ ~(GoRule = "draft" /\ b.emptyMap)

\* In English: "gOuroboros's id: the stored bytes' hash when there are
\*   bytes; otherwise the empty-input hash on main [G1], the encoding's
\*   hash or the empty-input hash in the draft [G2], the encoding's hash or
\*   the zero id with the fix [G3]."
\* Literally: "GoId of b is defined as: if stored of b then Encode of b;
\*   else if GoRule equals "main" then EmptyInput; else if GoEncodes of b
\*   then Encode of b; else if GoRule equals "draft" then EmptyInput;
\*   else Zero."
GoId(b) ==
    IF b.stored THEN Encode(b)
    ELSE IF GoRule = "main" THEN EmptyInput
    ELSE IF GoEncodes(b) THEN Encode(b)
    ELSE IF GoRule = "draft" THEN EmptyInput
    ELSE Zero

\* In English: "Pick any one body; nothing changes after that."
\* Literally: "Init is defined as: body is a member of Bodies."
Init == body \in Bodies

\* In English: "A table has no steps: the body stays as it is."
\* Literally: "Next is defined as: body is unchanged."
Next == UNCHANGED body

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or body
\*   stays the same."
Spec == Init /\ [][Next]_body

\* In English: "For every body the reference can represent, gOuroboros's
\*   id is the hash of the body's serialization." [S1]
\* Literally: "IdAsBlake2bOfBodyEncoding is defined as: if encodable of
\*   body then GoId of body equals RefId of body."
IdAsBlake2bOfBodyEncoding == body.encodable => GoId(body) = RefId(body)

\* In English: "A body the reference could not represent gets no id that
\*   looks real: the zero id, never the hash of something."
\* Literally: "UnencodableGetsZeroId is defined as: if not encodable of
\*   body then GoId of body equals Zero."
UnencodableGetsZeroId == ~body.encodable => GoId(body) = Zero
=============================================================================
