/-
Conformance vectors, and their JSON form.

A vector is one assertion about the model that any Candid implementation can check:
a field-id hash, whether a type table is well formed, whether one type is a subtype
of another, or what a value coerces to at another type. `conformance/README.md` specifies the JSON; this file is the reference
reader and writer for it, and the two must agree.

The JSON is data, not a grammar: a type is its table and a root, exactly as the model
holds it (`Candid/Types.lean`), so a runner in any language can read vector #1 before
it has a `.did` parser. Field ids are numbers, never names -- the two are
indistinguishable at the type level, and leaving names out means a runner does not need
the hash to read a type.
-/

import Candid
import Lean.Data.Json

namespace Oracle

open Candid Lean

/-- The version of the vector format this file reads and writes. -/
def formatVersion : Nat := 0

/-- A type as written down: a table that has not been checked yet, and a root. A vector
may carry a malformed one on purpose, so checking it is the reader's job, not the
parser's. -/
structure Fixture where
  table : RawTypeTable
  root : Slot

instance : Coe (RawTypeTable × Slot) Fixture := ⟨fun (t, r) => ⟨t, r⟩⟩

/-- Check a fixture's table and then its root: the two steps every caller takes. -/
def Fixture.check? (f : Fixture) : Option ((t : TypeTable) × t.Root) := do
  let t ← f.table.check
  let r ← t.root? f.root
  return ⟨t, r⟩

/-- What a vector asserts. A subtype vector names two well-formed types; one that does
not is a broken vector, since subtyping is not defined on a malformed type. A coerce
vector's value has the type it is coerced from, and the expected result, if there is
one, has the type it is coerced to: coercion is only defined on well-typed values. -/
inductive Assertion where
  | hash (name : String) (want : FieldId)
  | wellFormed (type : Fixture) (want : Bool)
  | subtype (sub sup : Fixture) (want : Bool)
  /-- `value : src ~> want : dst`, or no such value when `want` is `none`. -/
  | coerce (value : Value) (src dst : Fixture) (want : Option Value)

structure Vector where
  /-- Unique within the suite. Human-readable, and stable: a runner's list of known
  divergences is keyed on it. -/
  id : String
  assertion : Assertion

/-! ## Names

The spelling of each primitive and annotation is the `.did` keyword for it. -/

def _root_.Candid.Prim.name : Prim → String
  | .null => "null" | .bool => "bool" | .nat => "nat" | .int => "int"
  | .nat8 => "nat8" | .nat16 => "nat16" | .nat32 => "nat32" | .nat64 => "nat64"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32" | .int64 => "int64"
  | .float32 => "float32" | .float64 => "float64"
  | .text => "text" | .reserved => "reserved" | .empty => "empty"
  | .principal => "principal"

def _root_.Candid.Prim.all : List Prim :=
  [ .null, .bool, .nat, .int, .nat8, .nat16, .nat32, .nat64
  , .int8, .int16, .int32, .int64, .float32, .float64
  , .text, .reserved, .empty, .principal ]

def _root_.Candid.Prim.ofName? (s : String) : Option Prim := Prim.all.find? (·.name == s)

def _root_.Candid.FuncAnnot.name : FuncAnnot → String
  | .query => "query" | .oneway => "oneway" | .compositeQuery => "composite_query"

def _root_.Candid.FuncAnnot.ofName? : String → Option FuncAnnot
  | "query" => some .query
  | "oneway" => some .oneway
  | "composite_query" => some .compositeQuery
  | _ => none

/-! ## Writing -/

/-- A primitive is its name; a reference is its table index. -/
def _root_.Candid.Slot.toJson : Slot → Json
  | .prim p => .str p.name
  | .ref r => .num r

def labelledToJson (fs : List (FieldId × Slot)) : Json :=
  .arr (fs.map fun (id, s) => Json.arr #[.num id.toNat, s.toJson]).toArray

def slotsToJson (ss : List Slot) : Json := .arr (ss.map Slot.toJson).toArray

def _root_.Candid.Composite.toJson : Composite → Json
  | .opt t => .mkObj [("opt", t.toJson)]
  | .vec t => .mkObj [("vec", t.toJson)]
  | .record fs => .mkObj [("record", labelledToJson fs)]
  | .variant fs => .mkObj [("variant", labelledToJson fs)]
  | .func args rets ann => .mkObj [("func", .mkObj
      [ ("args", slotsToJson args), ("rets", slotsToJson rets)
      , ("annots", .arr (ann.map (Json.str ·.name)).toArray) ])]
  | .service ms => .mkObj [("service",
      .arr (ms.map fun (n, s) => Json.arr #[.str n, s.toJson]).toArray)]

def Fixture.toJson (f : Fixture) : Json :=
  .mkObj [("table", .arr (f.table.entries.map Composite.toJson)), ("root", f.root.toJson)]

/-! Values. Every number in a value is a decimal string, so that no reader loses
precision -- a JSON number past 2^53 does not survive most parsers -- and a float is its
bit pattern in hex, so that every NaN and both zeros survive too. -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- `n` as exactly `width` lowercase hex digits. -/
def hexFixed (width n : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i => hexDigit (n / 16 ^ i % 16))

def bytesToHex (bs : PrincipalBytes) : String := String.join (bs.map (hexFixed 2 ·.toNat))

partial def valueToJson : Value → Json
  | .null => .null
  | .bool b => .bool b
  | .nat n => .mkObj [("nat", .str (toString n))]
  | .int i => .mkObj [("int", .str (toString i))]
  | .nat8 n => .mkObj [("nat8", .str (toString n))]
  | .nat16 n => .mkObj [("nat16", .str (toString n))]
  | .nat32 n => .mkObj [("nat32", .str (toString n))]
  | .nat64 n => .mkObj [("nat64", .str (toString n))]
  | .int8 i => .mkObj [("int8", .str (toString i.toInt))]
  | .int16 i => .mkObj [("int16", .str (toString i.toInt))]
  | .int32 i => .mkObj [("int32", .str (toString i.toInt))]
  | .int64 i => .mkObj [("int64", .str (toString i.toInt))]
  | .float32 b => .mkObj [("float32", .str (hexFixed 8 b.toNat))]
  | .float64 b => .mkObj [("float64", .str (hexFixed 16 b.toNat))]
  | .text s => .mkObj [("text", .str s)]
  | .opt v => .mkObj [("opt", valueToJson v)]
  | .vec vs => .mkObj [("vec", .arr (vs.map valueToJson).toArray)]
  | .record fs => .mkObj [("record",
      .arr (fs.map fun (id, v) => Json.arr #[.num id.toNat, valueToJson v]).toArray)]
  | .variant id v => .mkObj [("variant", .arr #[.num id.toNat, valueToJson v])]
  | .principal id => .mkObj [("principal", .str (bytesToHex id))]
  | .service id => .mkObj [("service", .str (bytesToHex id))]
  | .func id m => .mkObj [("func", .arr #[.str (bytesToHex id), .str m])]

/-- An expected coercion: the value, or `"reject"` when there is none. -/
def expectToJson : Option Value → Json
  | some v => .mkObj [("value", valueToJson v)]
  | none => .str "reject"

/-- One vector, on one line. Written by hand rather than through `Json.compress` so that
`id` and `kind` come first: `compress` sorts keys, and a file read by people as often
as by programs should lead with what a line is about. -/
def Vector.render (v : Vector) : String :=
  let field (k : String) (j : Json) := s!",{(Json.str k).compress}:{j.compress}"
  let head (kind : String) :=
    s!"\{\"id\":{(Json.str v.id).compress},\"kind\":{(Json.str kind).compress}"
  match v.assertion with
  | .hash name want =>
    head "hash" ++ field "name" (.str name) ++ field "expect" (.num want.toNat) ++ "}"
  | .wellFormed t want =>
    head "wellformed" ++ field "type" t.toJson ++ field "expect" (.bool want) ++ "}"
  | .subtype a b want =>
    head "subtype" ++ field "sub" a.toJson ++ field "sup" b.toJson ++
      field "expect" (.bool want) ++ "}"
  | .coerce v a b want =>
    head "coerce" ++ field "value" (valueToJson v) ++ field "from" a.toJson ++
      field "to" b.toJson ++ field "expect" (expectToJson want) ++ "}"

/-- A whole file: one vector per line, so that a change to the model shows up in a diff
as exactly the vectors whose answers it changed. -/
def renderFile (vs : List Vector) : String :=
  s!"\{\"version\":{formatVersion},\"vectors\":[\n" ++
    ",\n".intercalate (vs.map Vector.render) ++ "\n]}\n"

/-! ## Reading

Strict: an unknown key, a missing key, or a value of the wrong shape is an error. A
reference reader that tolerated those would let a vector mean something its author
did not write. -/

def objFields (j : Json) : Except String (List (String × Json)) := do
  return (← j.getObj?).toList

/-- The object's keys, exactly. -/
def expectKeys (j : Json) (keys : List String) : Except String Unit := do
  let got := (← objFields j).map (·.1)
  unless got.length == keys.length && keys.all (got.contains ·) do
    throw s!"expected keys {keys}, got {got}"

def _root_.Candid.Slot.fromJson? : Json → Except String Slot
  | .str s => match Prim.ofName? s with
    | some p => return .prim p
    | none => throw s!"unknown primitive type {repr s}"
  | j => do return .ref (← j.getNat?)

def fieldIdFromJson? (j : Json) : Except String FieldId := do
  let n ← j.getNat?
  unless n < UInt32.size do throw s!"field id {n} does not fit in 32 bits"
  return n.toUInt32

def pairFromJson? (key : Json → Except String α) (j : Json) : Except String (α × Slot) := do
  match (← j.getArr?).toList with
  | [k, s] => return (← key k, ← Slot.fromJson? s)
  | _ => throw "expected a two-element array"

def slotsFromJson? (j : Json) : Except String (List Slot) := do
  (← j.getArr?).toList.mapM Slot.fromJson?

def labelledFromJson? (j : Json) : Except String (List (FieldId × Slot)) := do
  (← j.getArr?).toList.mapM (pairFromJson? fieldIdFromJson?)

def _root_.Candid.Composite.fromJson? (j : Json) : Except String Composite := do
  match ← objFields j with
  | [("opt", t)] => return .opt (← Slot.fromJson? t)
  | [("vec", t)] => return .vec (← Slot.fromJson? t)
  | [("record", fs)] => return .record (← labelledFromJson? fs)
  | [("variant", fs)] => return .variant (← labelledFromJson? fs)
  | [("func", f)] =>
    expectKeys f ["args", "rets", "annots"]
    let ann ← (← (← f.getObjVal? "annots").getArr?).toList.mapM fun a => do
      let s ← a.getStr?
      match FuncAnnot.ofName? s with
      | some a => pure a
      | none => throw s!"unknown function annotation {repr s}"
    return .func (← slotsFromJson? (← f.getObjVal? "args"))
      (← slotsFromJson? (← f.getObjVal? "rets")) ann
  | [("service", ms)] =>
    return .service (← (← ms.getArr?).toList.mapM (pairFromJson? Json.getStr?))
  | _ => throw s!"not a table entry: {j.compress}"

/-- A decimal string, in canonical form: what `toString` writes and nothing else, so
`"007"`, `"+7"`, `"-0"` and `"1_000"` are all errors. -/
def natFromJson? (j : Json) : Except String Nat := do
  let s ← j.getStr?
  match s.toNat? with
  | some n => if toString n == s then return n else throw s!"not canonical decimal: {repr s}"
  | none => throw s!"not a decimal natural: {repr s}"

def intFromJson? (j : Json) : Except String Int := do
  let s ← j.getStr?
  match s.toInt? with
  | some i => if toString i == s then return i else throw s!"not canonical decimal: {repr s}"
  | none => throw s!"not a decimal integer: {repr s}"

/-- A natural below `2^bits`. -/
def boundedNat? (bits : Nat) (j : Json) : Except String Nat := do
  let n ← natFromJson? j
  unless n < 2 ^ bits do throw s!"{n} does not fit in nat{bits}"
  return n

/-- An integer in two's-complement range for `bits`. -/
def boundedInt? (bits : Nat) (j : Json) : Except String Int := do
  let i ← intFromJson? j
  unless -(2 ^ (bits - 1) : Int) ≤ i && i < 2 ^ (bits - 1) do
    throw s!"{i} does not fit in int{bits}"
  return i

def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Lowercase hex digits, read as one number. -/
def hexDigits? (s : String) : Except String Nat :=
  s.toList.foldlM (init := 0) fun acc c => match hexValue? c with
    | some d => pure (acc * 16 + d)
    | none => throw s!"not lowercase hex: {repr s}"

/-- Exactly `width` lowercase hex digits. -/
def hexFixed? (width : Nat) (j : Json) : Except String Nat := do
  let s ← j.getStr?
  unless s.length == width do throw s!"expected {width} hex digits: {repr s}"
  hexDigits? s

def bytesFromHex? (j : Json) : Except String PrincipalBytes := do
  let s ← j.getStr?
  unless s.length % 2 == 0 do throw s!"odd number of hex digits: {repr s}"
  let cs := s.toList
  (List.range (cs.length / 2)).mapM fun i =>
    return (← hexDigits? (String.ofList [cs[2 * i]!, cs[2 * i + 1]!])).toUInt8

partial def valueFromJson? (j : Json) : Except String Value := do
  match j with
  | .null => return .null
  | .bool b => return .bool b
  | _ =>
  match ← objFields j with
  | [("nat", n)] => return .nat (← natFromJson? n)
  | [("int", i)] => return .int (← intFromJson? i)
  | [("nat8", n)] => return .nat8 (← boundedNat? 8 n).toUInt8
  | [("nat16", n)] => return .nat16 (← boundedNat? 16 n).toUInt16
  | [("nat32", n)] => return .nat32 (← boundedNat? 32 n).toUInt32
  | [("nat64", n)] => return .nat64 (← boundedNat? 64 n).toUInt64
  | [("int8", i)] => return .int8 (Int8.ofInt (← boundedInt? 8 i))
  | [("int16", i)] => return .int16 (Int16.ofInt (← boundedInt? 16 i))
  | [("int32", i)] => return .int32 (Int32.ofInt (← boundedInt? 32 i))
  | [("int64", i)] => return .int64 (Int64.ofInt (← boundedInt? 64 i))
  | [("float32", b)] => return .float32 (← hexFixed? 8 b).toUInt32
  | [("float64", b)] => return .float64 (← hexFixed? 16 b).toUInt64
  | [("text", s)] => return .text (← s.getStr?)
  | [("opt", v)] => return .opt (← valueFromJson? v)
  | [("vec", vs)] => return .vec (← (← vs.getArr?).toList.mapM valueFromJson?)
  | [("record", fs)] =>
    return .record (← (← fs.getArr?).toList.mapM fun f => do
      match (← f.getArr?).toList with
      | [id, v] => return (← fieldIdFromJson? id, ← valueFromJson? v)
      | _ => throw "expected a two-element array")
  | [("variant", f)] =>
    match (← f.getArr?).toList with
    | [id, v] => return .variant (← fieldIdFromJson? id) (← valueFromJson? v)
    | _ => throw "expected a two-element array"
  | [("principal", id)] => return .principal (← bytesFromHex? id)
  | [("service", id)] => return .service (← bytesFromHex? id)
  | [("func", f)] =>
    match (← f.getArr?).toList with
    | [id, m] => return .func (← bytesFromHex? id) (← m.getStr?)
    | _ => throw "expected a two-element array"
  | _ => throw s!"not a value: {j.compress}"

def expectFromJson? : Json → Except String (Option Value)
  | .str "reject" => return none
  | j => do
    expectKeys j ["value"]
    return some (← valueFromJson? (← j.getObjVal? "value"))

def Fixture.fromJson? (j : Json) : Except String Fixture := do
  expectKeys j ["table", "root"]
  let entries ← (← (← j.getObjVal? "table").getArr?).mapM Composite.fromJson?
  return { table := { entries }, root := ← Slot.fromJson? (← j.getObjVal? "root") }

def Vector.fromJson? (j : Json) : Except String Vector := do
  let id ← (← j.getObjVal? "id").getStr?
  let assertion ← (do
    match ← (← j.getObjVal? "kind").getStr? with
    | "hash" =>
      expectKeys j ["id", "kind", "name", "expect"]
      return .hash (← (← j.getObjVal? "name").getStr?) (← fieldIdFromJson? (← j.getObjVal? "expect"))
    | "wellformed" =>
      expectKeys j ["id", "kind", "type", "expect"]
      return .wellFormed (← Fixture.fromJson? (← j.getObjVal? "type"))
        (← (← j.getObjVal? "expect").getBool?)
    | "subtype" =>
      expectKeys j ["id", "kind", "sub", "sup", "expect"]
      return .subtype (← Fixture.fromJson? (← j.getObjVal? "sub"))
        (← Fixture.fromJson? (← j.getObjVal? "sup")) (← (← j.getObjVal? "expect").getBool?)
    | "coerce" =>
      expectKeys j ["id", "kind", "value", "from", "to", "expect"]
      return .coerce (← valueFromJson? (← j.getObjVal? "value"))
        (← Fixture.fromJson? (← j.getObjVal? "from")) (← Fixture.fromJson? (← j.getObjVal? "to"))
        (← expectFromJson? (← j.getObjVal? "expect"))
    | k => throw s!"unknown vector kind {repr k}" : Except String Assertion)
  return { id, assertion }

/-- Read a file's text. A vector that does not parse names itself in the error. -/
def parseFile (text : String) : Except String (List Vector) := do
  let j ← Json.parse text
  expectKeys j ["version", "vectors"]
  let version ← (← j.getObjVal? "version").getNat?
  unless version == formatVersion do
    throw s!"vector format version {version}; this reader understands {formatVersion}"
  (← (← j.getObjVal? "vectors").getArr?).toList.mapM fun v =>
    match Vector.fromJson? v with
    | .ok v => pure v
    | .error e => throw s!"{e} in vector {v.compress}"

/-! ## Evaluating -/

def relStr (b : Bool) : String := if b then "<:" else "!<:"

/-- `none` if the model agrees with the assertion, otherwise what went wrong. -/
def Assertion.disagreement : Assertion → Option String
  | .hash name want =>
    let got := hashFieldName name
    if got == want then none else some s!"got {got}, want {want}"
  | .wellFormed t want =>
    let got := t.check?.isSome
    if got == want then none else some s!"got {got}, want {want}"
  | .subtype a b want =>
    match a.check?, b.check? with
    | some ⟨A, a⟩, some ⟨B, b⟩ =>
      let got := decSubtype A B a b
      if got == want then none else some s!"got {relStr got}, want {relStr want}"
    | _, _ => some "a type is malformed, so subtyping is not defined on it"
  | .coerce v a b want =>
    match a.check?, b.check? with
    | some ⟨A, a⟩, some ⟨B, b⟩ =>
      if !A.hasType v a.1 then some "the value does not have the type it is coerced from"
      else if want.any (!B.hasType · b.1) then
        some "the expected value does not have the type it is coerced to"
      else
        let got := coerceResult A B v a.1 b.1
        if got == want then none
        else some s!"got {(expectToJson got).compress}, want {(expectToJson want).compress}"
    | _, _ => some "a type is malformed, so coercion is not defined on it"

end Oracle
