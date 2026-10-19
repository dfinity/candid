/-
Conformance vectors, and their JSON form.

A vector is one assertion about the model that any Candid implementation can check:
a field-id hash, whether a type table is well formed, or whether one type is a subtype
of another. `conformance/README.md` specifies the JSON; this file is the reference
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
not is a broken vector, since subtyping is not defined on a malformed type. -/
inductive Assertion where
  | hash (name : String) (want : FieldId)
  | wellFormed (type : Fixture) (want : Bool)
  | subtype (sub sup : Fixture) (want : Bool)

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

end Oracle
