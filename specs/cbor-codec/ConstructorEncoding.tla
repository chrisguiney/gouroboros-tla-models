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
(*   [R4] Data.hs 147-166 encodeData Map: a definite map (encodeMapLen),   *)
(*        its pairs in the Data value's list order, each key and value     *)
(*        written by encodeData, so long byte strings are chunked and      *)
(*        lists indefinite inside a map as anywhere else.                  *)
(*   [R5] Data.hs 170-182 encodeInteger: an integer outside the 64-bit    *)
(*        range is tag 2 or 3 around encodeBs of its magnitude, so a       *)
(*        magnitude longer than 64 bytes is chunked.                       *)
(*   [R6] Data.hs 269-271 decodeList, decodeListOf: a constructor's fields *)
(*        are a list; Data has no constructor whose fields are not.        *)
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
(*   [G3] fix/cbor-constructor-indefinite-fields 3d91ad2f: every list at   *)
(*        any depth (slice, array or IndefLengthList) is 0x80 when empty   *)
(*        and indefinite otherwise; byte strings over 64 bytes are written *)
(*        as an indefinite string of 64-byte chunks. Maps are written as   *)
(*        given: a Go map definite with its members unconverted, an        *)
(*        IndefLengthMap indefinite.                                       *)
(*   [G4] 635905f9 on that branch: a Go map, cbor.Map or                   *)
(*        IndefLengthMap item is a definite map whose keys and values are  *)
(*        converted like any item. A Go map has no order, so its pairs are *)
(*        written in the order of their encoded keys, the order the        *)
(*        encoder already used; that is the plutus Map with that list.     *)
(*   [G5] origin/main 5b8eeea4 merged into that branch: ConstructorDecoder *)
(*        refuses fields that are not a list, but MarshalCBOR still writes *)
(*        a non-list fields value (a scalar, or a value whose MarshalCBOR  *)
(*        writes no list) as given. Items are matched by Go type, so a     *)
(*        named byte slice or array (PlutusV1Script) and a big.Int value   *)
(*        (not a pointer) are written by the library: a long one as one   *)
(*        definite string, a large big.Int as tag 2 around one.           *)
(*   [G6] the fix on that branch: items are matched by kind, so every     *)
(*        byte slice or array without its own MarshalCBOR, and every       *)
(*        big.Int value, is chunked; a fields value that is not a list is  *)
(*        refused.                                                         *)
(*   [G7] c03e5b5a on that branch: plutusByteKind copies the bytes with    *)
(*        reflect.Copy, which needs identical element types, so a slice or *)
(*        array of a named uint8 type ([]NamedByte) panics at any length.  *)
(*        The library writes such a value as a byte string.                *)
(*   [G8] the fix: the bytes are read element by element, so a named      *)
(*        element type is a byte string like any other.                    *)
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
    GoRule      \* "main" [G1], "fix" [G2], "plutus" [G3], "plutusMap" [G4]
                \* "plutusKinds" [G6][G7] or "plutusElemKinds" [G8]

VARIABLE input  \* the one constructor this behaviour encodes

\* In English: "The Go values a caller may pass as the fields: nil, an
\*   empty slice, a slice, a Go array, an IndefLengthList, and a value that
\*   is not a list (an integer, or a type whose MarshalCBOR writes no list)."
\* Literally: "AllContainers is defined as the set containing "nil",
\*   "emptySlice", "slice", "goArray", "indefList" and "scalar"."
AllContainers == {"nil", "emptySlice", "slice", "goArray", "indefList",
                  "scalar"}

\* In English: "Kinds of item inside the fields: an integer, a byte
\*   string of at most 64 bytes, a longer one, a nested Data list given as
\*   a []any, one given as an IndefLengthList, the map kinds below, a byte
\*   string over 64 bytes given as a named byte slice (PlutusV1Script),
\*   a big.Int value whose magnitude is over 64 bytes, and a short and a
\*   long byte string given as a slice of a named uint8 type."
\* Literally: "AllItems is defined as the set containing "int",
\*   "shortBytes", "longBytes", "nestedSlice", "nestedIndef", the map
\*   kinds, "namedLongBytes", "bigIntValueLong", "namedElemShortBytes"
\*   and "namedElemLongBytes"."
AllItems == {"int", "shortBytes", "longBytes", "nestedSlice", "nestedIndef",
             "mapShort", "mapLongBytes", "mapNestedSlice", "indefMapShort",
             "namedLongBytes", "bigIntValueLong", "namedElemShortBytes",
             "namedElemLongBytes"}

\* In English: "The map item kinds: a Go map with short members, one with
\*   a byte string over 64 bytes as a key or value, one with a []any list
\*   as a value, and an IndefLengthMap with short members."
\* Literally: "MapItems is defined as the set containing "mapShort",
\*   "mapLongBytes", "mapNestedSlice" and "indefMapShort"."
MapItems == {"mapShort", "mapLongBytes", "mapNestedSlice", "indefMapShort"}

\* In English: "Every family, container and set of item kinds; nil, an
\*   empty slice and a value that is not a list hold no items."
\* Literally: "Inputs is defined as the set of records r whose family is
\*   a member of the set containing "121-127", "1280-1400" and "102", whose
\*   container is a member of Containers and whose items is a subset of
\*   ItemKinds, such that the container of r is not "nil", "emptySlice"
\*   or "scalar", or the items of r is the empty set."
Inputs == {r \in [family : {"121-127", "1280-1400", "102"},
                  container : Containers, items : SUBSET ItemKinds] :
              r.container \notin {"nil", "emptySlice", "scalar"}
                  \/ r.items = {}}

\* In English: "plutus's field list: 0x80 when empty, indefinite
\*   otherwise; fields that are not a list are no Data at all." [R1] [R6]
\* Literally: "RefHead of i is defined as: if the container of i is
\*   "scalar" then "refused", else if the items of i is the empty set then
\*   "empty", else "indef"."
RefHead(i) ==
    IF i.container = "scalar" THEN "refused"
    ELSE IF i.items = {} THEN "empty" ELSE "indef"

\* In English: "How plutus writes each kind of item." [R1] [R2]
\* Literally: "RefItem of k is defined as: if k is "int" then "int", else
\*   if k is "shortBytes" then "bytes", else if k is "longBytes" then
\*   "chunkedBytes", else "indefList"."
RefItem(k) ==
    IF k \in {"namedLongBytes", "namedElemLongBytes"}
    THEN "chunkedBytes"                                    \* [R2]
    ELSE IF k = "namedElemShortBytes" THEN "bytes"
    ELSE IF k = "bigIntValueLong" THEN "chunkedBignum"    \* [R5]
    ELSE IF k \in {"mapShort", "indefMapShort"} THEN "defMap"
    ELSE IF k = "mapLongBytes" THEN "defMapChunkedBytes"
    ELSE IF k = "mapNestedSlice" THEN "defMapIndefList"
    ELSE IF k = "int" THEN "int"
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
    IF k \in {"namedLongBytes", "namedElemLongBytes"} THEN "definiteBytes"
    ELSE IF k = "namedElemShortBytes" THEN "bytes"
    ELSE IF k = "bigIntValueLong" THEN "definiteBignum"
    ELSE IF k = "mapShort" THEN "defMap"
    ELSE IF k = "mapLongBytes" THEN "defMapDefiniteBytes"
    ELSE IF k = "mapNestedSlice" THEN "defMapDefList"
    ELSE IF k = "indefMapShort" THEN "indefMap"
    ELSE IF k = "int" THEN "int"
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
    IF i.container = "scalar" THEN "scalar"
    ELSE IF i.container = "nil" THEN "null"
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
    IF i.container = "scalar" THEN "scalar"
    ELSE IF i.container = "indefList"
    THEN (IF i.items = {} THEN "indefEmpty" ELSE "indef")
    ELSE IF i.items = {} THEN "empty"
    ELSE IF i.container = "goArray" THEN "def"
    ELSE "indef"

\* In English: "3d91ad2f's field list (and [G4]'s): plutusList writes 0x80
\*   for no items and an indefinite list otherwise, whatever the list
\*   container; a value that is not a list is written as given." [G3] [G5]
\* Literally: "GoPlutusHead of i is defined as: if the container of i is
\*   "scalar" then "scalar", else if the items of i is the empty set then
\*   "empty", else "indef"."
GoPlutusHead(i) ==
    IF i.container = "scalar" THEN "scalar"
    ELSE IF i.items = {} THEN "empty" ELSE "indef"

\* In English: "The fix's field list: as GoPlutusHead, but a value that is
\*   not a list is refused." [G6]
\* Literally: "GoKindsHead of i is defined as: if the container of i is
\*   "scalar" then "refused", else GoPlutusHead of i."
GoKindsHead(i) ==
    IF i.container = "scalar" THEN "refused" ELSE GoPlutusHead(i)

\* In English: "How 3d91ad2f writes each kind of item: plutusBytes chunks a
\*   long byte string, plutusList writes any nested list indefinite." [G3]
\* Literally: "GoPlutusItem of k is defined as: if k is "int" then "int",
\*   else if k is "shortBytes" then "bytes", else if k is "longBytes" then
\*   "chunkedBytes", else "indefList"."
GoPlutusItem(k) ==
    IF k \in MapItems \cup {"namedLongBytes", "bigIntValueLong",
                         "namedElemShortBytes", "namedElemLongBytes"}
    THEN GoItem(k)
    ELSE IF k = "int" THEN "int"
    ELSE IF k = "shortBytes" THEN "bytes"
    ELSE IF k = "longBytes" THEN "chunkedBytes"
    ELSE "indefList"

\* In English: "How [G4] writes each kind of item: as 3d91ad2f does, and
\*   every map definite with its keys and values converted." [G4]
\* Literally: "GoPlutusMapItem of k is defined as: if k is "mapShort" or
\*   "indefMapShort" then "defMap", else if k is "mapLongBytes" then
\*   "defMapChunkedBytes", else if k is "mapNestedSlice" then
\*   "defMapIndefList", else GoPlutusItem of k."
GoPlutusMapItem(k) ==
    IF k \in {"mapShort", "indefMapShort"} THEN "defMap"
    ELSE IF k = "mapLongBytes" THEN "defMapChunkedBytes"
    ELSE IF k = "mapNestedSlice" THEN "defMapIndefList"
    ELSE GoPlutusItem(k)

\* In English: "How the fix writes each kind of item: as [G4] does, with a
\*   named byte slice and a big.Int value chunked like any other." [G6]
\* Literally: "GoKindsItem of k is defined as: if k is "namedLongBytes"
\*   then "chunkedBytes", else if k is "bigIntValueLong" then
\*   "chunkedBignum", else GoPlutusMapItem of k."
GoKindsItem(k) ==
    IF k \in {"namedElemShortBytes", "namedElemLongBytes"} THEN "panic"
    ELSE IF k = "namedLongBytes" THEN "chunkedBytes"
    ELSE IF k = "bigIntValueLong" THEN "chunkedBignum"
    ELSE GoPlutusMapItem(k)

\* In English: "How the fix writes each kind of item: as GoKindsItem, but
\*   a slice of a named uint8 type is a byte string, chunked when long."
\*   [G8]
\* Literally: "GoElemKindsItem of k is defined as: if k is
\*   "namedElemShortBytes" then "bytes", else if k is
\*   "namedElemLongBytes" then "chunkedBytes", else GoKindsItem of k."
GoElemKindsItem(k) ==
    IF k = "namedElemShortBytes" THEN "bytes"
    ELSE IF k = "namedElemLongBytes" THEN "chunkedBytes"
    ELSE GoKindsItem(k)

\* In English: "The shape of plutus's bytes for this constructor."
\* Literally: "RefBytes of i is defined as the record whose head is
\*   RefHead of i and whose items is the set of RefItem of k for every k in
\*   the items of i."
RefBytes(i) == [head |-> RefHead(i), items |-> {RefItem(k) : k \in i.items}]

\* In English: "The shape of gOuroboros's bytes, by the rule this config
\*   names."
\* Literally: "GoBytes of i is defined as the record whose head is
\*   GoMainHead, GoFixHead or GoPlutusHead of i by GoRule, and whose items
\*   is the set of GoPlutusItem of k (GoRule "plutus") or GoItem of k
\*   for every k in the items of i."
GoBytes(i) ==
    [head |-> CASE GoRule = "main"        -> GoMainHead(i)
                [] GoRule = "fix"         -> GoFixHead(i)
                [] GoRule \in {"plutusKinds", "plutusElemKinds"} ->
                        GoKindsHead(i)
                [] OTHER                  -> GoPlutusHead(i),
     items |-> CASE GoRule = "plutus"    -> {GoPlutusItem(k) : k \in i.items}
                 [] GoRule = "plutusMap" -> {GoPlutusMapItem(k) : k \in i.items}
                 [] GoRule = "plutusKinds" ->
                        {GoKindsItem(k) : k \in i.items}
                 [] GoRule = "plutusElemKinds" ->
                        {GoElemKindsItem(k) : k \in i.items}
                 [] OTHER                -> {GoItem(k) : k \in i.items}]

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
