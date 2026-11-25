------------------------- MODULE ConstructorEncoding ------------------------
(***************************************************************************)
(* The bytes gOuroboros's ConstructorEncoder writes for a Plutus Data     *)
(* constructor, against plutus's encodeData, as a table over abstract     *)
(* inputs. A datum's hash is the hash of these bytes, so equal shapes     *)
(* here mean equal hashes, and a different shape means a different hash.  *)
(*                                                                         *)
(* An input is the constructor's tag family, the Go value the caller      *)
(* hands over as the fields, and the kinds of item inside it. An encoding *)
(* is abstracted to the shape of the field list's head and the encoding   *)
(* of each kind of item.                                                   *)
(*                                                                         *)
(* Sources. IntersectMBO/plutus commit bdc12f105a98:                       *)
(*   [R1] plutus-core/plutus-core/src/PlutusCore/Data.hs 147-160           *)
(*        encodeData: Constr writes its tag (121-127, 1280-1400, or 102    *)
(*        around a definite pair) and then `encode ds`, the Serialise list *)
(*        instance: 0x80 when empty, an indefinite list otherwise. A List  *)
(*        is written the same way.                                         *)
(*   [R2] Data.hs 185-198 encodeBs: a byte string longer than 64 bytes is  *)
(*        written as an indefinite byte string of 64-byte chunks.          *)
(*   [R3] plutus-core/plutus-core/test/CBOR/DataStability.hs: the vectors  *)
(*        auction_1-1 and future-increase-margin-5 (second encodings).     *)
(*                                                                         *)
(* The gOuroboros code it is compared with is cbor/constructor.go          *)
(* ConstructorEncoder.MarshalCBOR:                                         *)
(*   [G1] main (parent of ad7a4f25): the fields value is handed to the     *)
(*        library as is: a slice or array as a definite list, nil as null. *)
(*   [G2] fix/cbor-constructor-indefinite-fields ad7a4f25 (PR #3290):      *)
(*        plutusFieldList turns nil or an empty slice into 0x80 and a      *)
(*        non-empty slice into an indefinite list; a Go array, or a value  *)
(*        with its own MarshalCBOR (IndefLengthList), is written as given. *)
(*        Items inside are written by the library on both commits.         *)
(* Checked in Go on ad7a4f25: [2]uint64{1,2} gives d879820102;             *)
(* []any{[]any{1}} gives d8799f8101ff; a 65-byte field gives a definite    *)
(* 5841 string; IndefLengthList{} gives d8799fff. On the parent nil gives *)
(* d879f6 and []any{1} gives d8798101.                                     *)
(*                                                                         *)
(* HOW TO READ THE SYMBOLS: see specs/keepalive/KeepAlive.tla and the      *)
(* "Reading a formula literally" table in the top-level README.            *)
(***************************************************************************)

CONSTANTS
    Containers, \* Go values tried as fields, a subset of AllContainers
    ItemKinds,  \* item kinds tried inside them, a subset of AllItems
    GoRule      \* "main" [G1] or "fix" [G2]

VARIABLE input  \* the one constructor this behaviour encodes

\* In English: "The Go values a caller may pass as the fields: nil, an
\*   empty slice, a slice, a Go array, and an IndefLengthList."
\* Literally: "AllContainers is defined as the set containing "nil",
\*   "emptySlice", "slice", "goArray" and "indefList"."
AllContainers == {"nil", "emptySlice", "slice", "goArray", "indefList"}

\* In English: "Kinds of item inside the fields: an integer, a byte
\*   string of at most 64 bytes, a longer one, a nested Data list given as
\*   a []any, and one given as an IndefLengthList."
\* Literally: "AllItems is defined as the set containing "int",
\*   "shortBytes", "longBytes", "nestedSlice" and "nestedIndef"."
AllItems == {"int", "shortBytes", "longBytes", "nestedSlice", "nestedIndef"}

\* In English: "Every family, container and set of item kinds; nil and an
\*   empty slice hold no items."
\* Literally: "Inputs is defined as the set of records r whose family is
\*   a member of the set containing "121-127", "1280-1400" and "102", whose
\*   container is a member of Containers and whose items is a subset of
\*   ItemKinds, such that the container of r is not "nil" or
\*   "emptySlice", or the items of r is the empty set."
Inputs == {r \in [family : {"121-127", "1280-1400", "102"},
                  container : Containers, items : SUBSET ItemKinds] :
              r.container \notin {"nil", "emptySlice"} \/ r.items = {}}

\* In English: "plutus's field list: 0x80 when empty, indefinite
\*   otherwise." [R1]
\* Literally: "RefHead of i is defined as: if the items of i is the empty
\*   set then "empty", else "indef"."
RefHead(i) == IF i.items = {} THEN "empty" ELSE "indef"

\* In English: "How plutus writes each kind of item." [R1] [R2]
\* Literally: "RefItem of k is defined as: if k is "int" then "int", else
\*   if k is "shortBytes" then "bytes", else if k is "longBytes" then
\*   "chunkedBytes", else "indefList"."
RefItem(k) ==
    IF k = "int" THEN "int"
    ELSE IF k = "shortBytes" THEN "bytes"
    ELSE IF k = "longBytes" THEN "chunkedBytes"
    ELSE "indefList"

\* In English: "How the library writes each kind of item, on both
\*   commits: a long byte string definite, a []any list definite."
\* Literally: "GoItem of k is defined as: if k is "int" then "int", else
\*   if k is "shortBytes" then "bytes", else if k is "longBytes" then
\*   "definiteBytes", else if k is "nestedSlice" then "defList", else
\*   "indefList"."
GoItem(k) ==
    IF k = "int" THEN "int"
    ELSE IF k = "shortBytes" THEN "bytes"
    ELSE IF k = "longBytes" THEN "definiteBytes"
    ELSE IF k = "nestedSlice" THEN "defList"
    ELSE "indefList"

\* In English: "main's field list: null for nil, 0x80 for an empty slice
\*   or array, definite for a non-empty one, and an IndefLengthList as
\*   itself (9fff when empty)." [G1]
\* Literally: "GoMainHead of i is defined as: if the container of i is
\*   "nil" then "null", else if the container of i is "indefList" then
\*   (if the items of i is empty then "indefEmpty" else "indef"), else if
\*   the items of i is empty then "empty", else "def"."
GoMainHead(i) ==
    IF i.container = "nil" THEN "null"
    ELSE IF i.container = "indefList"
         THEN (IF i.items = {} THEN "indefEmpty" ELSE "indef")
    ELSE IF i.items = {} THEN "empty"
    ELSE "def"

\* In English: "The fix's field list: nil and empty slices as 0x80, a
\*   non-empty slice indefinite, a Go array definite, an IndefLengthList
\*   as itself." [G2]
\* Literally: "GoFixHead of i is defined as: if the container of i is
\*   "indefList" then (if the items of i is empty then "indefEmpty" else
\*   "indef"), else if the items of i is empty then "empty", else if the
\*   container of i is "goArray" then "def", else "indef"."
GoFixHead(i) ==
    IF i.container = "indefList"
    THEN (IF i.items = {} THEN "indefEmpty" ELSE "indef")
    ELSE IF i.items = {} THEN "empty"
    ELSE IF i.container = "goArray" THEN "def"
    ELSE "indef"

\* In English: "The shape of plutus's bytes for this constructor."
\* Literally: "RefBytes of i is defined as the record whose head is
\*   RefHead of i and whose items is the set of RefItem of k for every k in
\*   the items of i."
RefBytes(i) == [head |-> RefHead(i), items |-> {RefItem(k) : k \in i.items}]

\* In English: "The shape of gOuroboros's bytes, by the rule this config
\*   names."
\* Literally: "GoBytes of i is defined as the record whose head is (if
\*   GoRule equals "main" then GoMainHead of i, else GoFixHead of i) and
\*   whose items is the set of GoItem of k for every k in the items of i."
GoBytes(i) ==
    [head |-> IF GoRule = "main" THEN GoMainHead(i) ELSE GoFixHead(i),
     items |-> {GoItem(k) : k \in i.items}]

\* In English: "Pick any one input."
\* Literally: "Init is defined as: input is a member of Inputs."
Init == input \in Inputs

\* In English: "A table has no steps: the input stays as it is."
\* Literally: "Next is defined as: input is unchanged."
Next == UNCHANGED input

\* In English: "Start with Init, and take only Next steps (or none)."
\* Literally: "Spec is defined as: Init, and always either Next or input
\*   stays the same."
Spec == Init /\ [][Next]_input

\* In English: "gOuroboros writes the bytes plutus's encodeData writes, so
\*   the datum hashes agree."
\* Literally: "BytesAsPlutusEncodeData is defined as: GoBytes of input
\*   equals RefBytes of input."
BytesAsPlutusEncodeData == GoBytes(input) = RefBytes(input)
=============================================================================
