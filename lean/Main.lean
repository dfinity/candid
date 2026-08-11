/-
The reference executable.

Slice 1 runs a fixed set of checks and exits nonzero on any failure, so CI is
actually verifying behaviour rather than only that the model compiles. It will grow
into the differential oracle that reads conformance vectors -- at which point these
checks become the first vectors.
-/

import Candid

open Candid
open Candid.TypeExpr

structure Check where
  name : String
  ok : Bool
  detail : String

def verdictStr : Verdict → String
  | some true => "<:"
  | some false => "!<:"
  | none => "budget exhausted"

/-- A subtype question about two types that carry no references. -/
def expectSub (a b : TypeExpr) (want : Bool) (name : String) : Check :=
  let got := decSubtype (.ofExpr a) (.ofExpr b)
  { name := name
    ok := got == some want
    detail := s!"got {verdictStr got}, want {verdictStr (some want)}" }

/-- A subtype question about two types with their own type tables. -/
def expectSubIn (a b : ClosedType) (want : Bool) (name : String) : Check :=
  let got := decSubtype a b
  { name := name
    ok := got == some want
    detail := s!"got {verdictStr got}, want {verdictStr (some want)}" }

def expectHash (input : String) (want : UInt32) : Check :=
  let got := hashFieldName input
  { name := s!"hash {repr input} = {want}"
    ok := got == want
    detail := s!"got {got}" }

def expectWellFormed (c : ClosedType) (want : Bool) (name : String) : Check :=
  { name := name
    ok := c.wellFormed == want
    detail := s!"got {c.wellFormed}, want {want}" }

/-! ## Field-id hash

Values computed independently from the spec formula. `"é"` is the discriminating
case: hashing UTF-8 bytes gives 43654, hashing characters would give 233. -/

def hashChecks : List Check :=
  [ expectHash "" 0
  , expectHash "Ok" 17724
  , expectHash "Err" 3456837
  , expectHash "id" 23515
  , expectHash "value" 834174833
  , expectHash "é" 43654 ]

/-! ## Primitives, top and bottom -/

def primChecks : List Check :=
  [ expectSub nat nat true "nat <: nat"
  , expectSub nat int true "nat <: int"
  , expectSub int nat false "int !<: nat"
  , expectSub nat8 nat false "nat8 !<: nat (no width subtyping)"
  , expectSub nat nat8 false "nat !<: nat8"
  , expectSub nat32 int32 false "nat32 !<: int32"
  , expectSub text reserved true "text <: reserved"
  , expectSub (.func [] [] []) reserved true "func <: reserved"
  , expectSub empty text true "empty <: text"
  , expectSub empty (.vec nat) true "empty <: vec nat"
  , expectSub text nat false "text !<: nat"
  , expectSub (.service []) .principal true "service <: principal"
  , expectSub .principal (.service []) false "principal !<: service" ]

/-! ## Options

Every type is a subtype of every option -- the spec's four `opt` rules with their
negative premises eliminated. The `text <: opt nat` case is the surprising one, and
it is deliberate: a receiver that cannot decode the value sees `null`. -/

def optChecks : List Check :=
  [ expectSub nat (.opt nat) true "nat <: opt nat"
  , expectSub null (.opt nat) true "null <: opt nat"
  , expectSub reserved (.opt nat) true "reserved <: opt nat"
  , expectSub text (.opt nat) true "text <: opt nat (special opt rule)"
  , expectSub (.opt text) (.opt nat) true "opt text <: opt nat (special opt rule)"
  , expectSub (.opt nat) nat false "opt nat !<: nat"
  , expectSub (.opt nat) reserved true "opt nat <: reserved" ]

/-! ## Vectors -/

def vecChecks : List Check :=
  [ expectSub (.vec nat) (.vec int) true "vec nat <: vec int"
  , expectSub (.vec int) (.vec nat) false "vec int !<: vec nat"
  , expectSub (.vec nat) nat false "vec nat !<: nat" ]

/-! ## Records

A subtype may add fields and specialise field types. It may also *omit* a field the
supertype declares, provided that field accepts `null` -- the rule that makes records
extensible in both inbound and outbound position. -/

def recordChecks : List Check :=
  [ expectSub (recordOf [("x", nat)]) (recordOf []) true
      "record {x:nat} <: record {}"
  , expectSub (recordOf [("x", nat), ("y", text)]) (recordOf [("x", nat)]) true
      "record {x;y} <: record {x} (field added)"
  , expectSub (recordOf [("x", nat)]) (recordOf [("x", int)]) true
      "record {x:nat} <: record {x:int} (field specialised)"
  , expectSub (recordOf [("x", int)]) (recordOf [("x", nat)]) false
      "record {x:int} !<: record {x:nat}"
  , expectSub (recordOf [("x", nat)]) (recordOf [("x", nat), ("y", .opt text)]) true
      "record {x} <: record {x; y:opt text} (omitted field accepts null)"
  , expectSub (recordOf [("x", nat)]) (recordOf [("x", nat), ("y", reserved)]) true
      "record {x} <: record {x; y:reserved}"
  , expectSub (recordOf [("x", nat)]) (recordOf [("x", nat), ("y", text)]) false
      "record {x} !<: record {x; y:text} (omitted field rejects null)"
  , expectSub (recordOf [("x", nat)]) (recordOf [("y", nat)]) false
      "record {x} !<: record {y}" ]

/-! ## Variants

Dual to records: a subtype may *drop* tags, and every tag it carries must exist in
the supertype. Adding tags is only sound behind an `opt`. -/

def variantChecks : List Check :=
  [ expectSub (variantOf []) (variantOf [("a", nat)]) true
      "variant {} <: variant {a}"
  , expectSub (variantOf [("a", nat)]) (variantOf [("a", nat), ("b", text)]) true
      "variant {a} <: variant {a; b} (tag dropped)"
  , expectSub (variantOf [("a", nat), ("b", text)]) (variantOf [("a", nat)]) false
      "variant {a; b} !<: variant {a} (tag added)"
  , expectSub (variantOf [("a", nat)]) (variantOf [("a", int)]) true
      "variant {a:nat} <: variant {a:int}"
  , expectSub (.opt (variantOf [("a", nat), ("b", text)])) (.opt (variantOf [("a", nat)])) true
      "opt variant {a; b} <: opt variant {a} (tag added behind opt)" ]

/-! ## Functions

Parameters generalise, results specialise, and both behave like tuple-shaped
records. Because the parameter premise is contravariant, the two directions are not
symmetric, and it is worth spelling out which is which:

- **Dropping** a parameter is always allowed. The premise is
  `record{args'} <: record{args}`, so the supertype's parameters sit on the subtype
  side of that record comparison, making a shorter parameter list the *wider* record.
  A callee that ignores what the caller sends cannot break.
- **Adding** a parameter requires it to accept `null`, since the premise then omits
  a field the supertype declares.
- Results mirror this exactly: adding is free, dropping requires accepting `null`.

Annotations must match as sets. -/

def funcChecks : List Check :=
  [ expectSub (.func [int] [nat] []) (.func [nat] [int] []) true
      "func (int) -> (nat) <: func (nat) -> (int)"
  , expectSub (.func [nat] [int] []) (.func [int] [nat] []) false
      "func (nat) -> (int) !<: func (int) -> (nat)"
    -- Parameters: dropping is free, adding needs to accept null.
  , expectSub (.func [] [] []) (.func [nat] [] []) true
      "func () -> () <: func (nat) -> () (parameter dropped, always allowed)"
  , expectSub (.func [.opt nat] [] []) (.func [] [] []) true
      "func (opt nat) -> () <: func () -> () (optional parameter added)"
  , expectSub (.func [nat] [] []) (.func [] [] []) false
      "func (nat) -> () !<: func () -> () (added parameter rejects null)"
    -- Results: adding is free, dropping needs to accept null.
  , expectSub (.func [] [nat] []) (.func [] [] []) true
      "func () -> (nat) <: func () -> () (result added, always allowed)"
  , expectSub (.func [] [] []) (.func [] [.opt nat] []) true
      "func () -> () <: func () -> (opt nat) (optional result dropped)"
  , expectSub (.func [] [] []) (.func [] [nat] []) false
      "func () -> () !<: func () -> (nat) (dropped result rejects null)"
  , expectSub (.func [] [] [.query]) (.func [] [] []) false
      "annotations must agree"
  , expectSub (.func [] [] [.query]) (.func [] [] [.query]) true
      "matching annotations agree" ]

/-! ## Services -/

def serviceChecks : List Check :=
  [ expectSub (.service [("m", .func [] [] [])]) (.service []) true
      "service {m} <: service {}"
  , expectSub (.service []) (.service [("m", .func [] [] [])]) false
      "service {} !<: service {m}"
  , expectSub (.service [("m", .func [] [nat] [])]) (.service [("m", .func [] [] [])]) true
      "service method specialised" ]

/-! ## Recursive types across two independent tables

These are the cases the reference-pair memo exists for. `selfLoop` and `twoCycle`
denote the same infinite type through different table shapes, which is why the memo
has to be keyed on reference pairs rather than on unfolded expressions -- the
expressions never repeat, the reference pairs do. -/

/-- `type S = record { next : S }`, as one self-referential entry. -/
def selfLoop : ClosedType :=
  { table := { entries := #[ recordOf [("next", .ref 0)] ] }, root := .ref 0 }

/-- The same type unrolled across two entries. -/
def twoCycle : ClosedType :=
  { table := { entries := #[ recordOf [("next", .ref 1)], recordOf [("next", .ref 0)] ] }
    root := .ref 0 }

/-- `type S = record { next : S; extra : nat }`. -/
def selfLoopWith (extra : TypeExpr) : ClosedType :=
  { table := { entries := #[ recordOf [("next", .ref 0), ("extra", extra)] ] }, root := .ref 0 }

/-- A table entry that is a bare reference: rejected, and it is the reference case
that would otherwise make following a reference an unbounded walk. -/
def bareRefEntry : ClosedType :=
  { table := { entries := #[ .ref 0 ] }, root := .ref 0 }

/-- A table entry that is a primitive: also rejected. `spec/Candid.md:1227` -- "The
type table may only contain composite types (no `<primtype>`)." -/
def primEntry : ClosedType :=
  { table := { entries := #[ nat ] }, root := .ref 0 }

/-- A reference with no entry to resolve to. -/
def danglingRef : ClosedType :=
  { table := { entries := #[] }, root := .ref 3 }

def recursiveChecks : List Check :=
  [ expectSubIn selfLoop selfLoop true
      "self-loop <: itself (memo terminates)"
  , expectSubIn selfLoop twoCycle true
      "self-loop <: two-cycle (same type, different table shape)"
  , expectSubIn twoCycle selfLoop true
      "two-cycle <: self-loop"
  , expectSubIn (selfLoopWith nat) (selfLoopWith int) true
      "recursive record, field specialised"
  , expectSubIn (selfLoopWith int) (selfLoopWith nat) false
      "recursive record, field not specialised"
  , expectSubIn (selfLoopWith nat) selfLoop true
      "recursive record with extra field <: without it"
  , expectWellFormed selfLoop true "self-loop is well formed"
  , expectWellFormed twoCycle true "two-cycle is well formed"
  , expectWellFormed bareRefEntry false "bare reference as a table entry is malformed"
  , expectWellFormed primEntry false "primitive as a table entry is malformed"
  , expectWellFormed (.ofExpr principal) true "principal is a primitive, not a reftype"
  , expectWellFormed danglingRef false "dangling reference is malformed"
  , expectWellFormed (.ofExpr (.record [(0, nat), (0, text)])) false
      "duplicate field id is malformed" ]

/-! ## Transitivity spot-check

The spec keeps transitivity as a design goal, and the unusual `opt` rules exist to
preserve it. This is not a proof -- it is the shape the eventual property test and
the Lean theorem take. -/

def transitivityChecks : List Check :=
  let a := recordOf [("x", nat)]
  let b := recordOf [("x", nat), ("y", .opt text)]
  let c := recordOf [("x", int)]
  [ expectSub a b true "transitivity: a <: b"
  , expectSub b c true "transitivity: b <: c"
  , expectSub a c true "transitivity: therefore a <: c" ]

def allChecks : List Check :=
  hashChecks ++ primChecks ++ optChecks ++ vecChecks ++ recordChecks ++
  variantChecks ++ funcChecks ++ serviceChecks ++ recursiveChecks ++
  transitivityChecks

def main : IO UInt32 := do
  let failures := allChecks.filter (fun c => !c.ok)
  for c in allChecks do
    if c.ok then
      IO.println s!"ok    {c.name}"
    else
      IO.println s!"FAIL  {c.name} -- {c.detail}"
  IO.println ""
  if failures.isEmpty then
    IO.println s!"{allChecks.length} checks passed"
    return 0
  else
    IO.eprintln s!"{failures.length} of {allChecks.length} checks failed"
    return 1
