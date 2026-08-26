/-
The reference executable.

It runs a fixed set of checks and exits nonzero on any failure, so CI is actually
verifying behaviour rather than only that the model compiles. It will grow into the
differential oracle that reads conformance vectors -- at which point these checks
become the first vectors.

Every type here carries a table, because composites live only in the table
(`Types.lean`). `atom` is a primitive, `entry` is a single composite, and
`close do ... intern ...` builds the two-or-more-entry cases.
-/

import Candid

open Candid
open Candid.Slot
open Candid.Composite

structure Check where
  name : String
  ok : Bool
  detail : String
  /-- A gap the model is known to have. Reported, but not a build failure -- and if
  it starts passing, *that* is a failure, so a fix cannot land unnoticed. Nothing is
  marked at the moment; the field exists so that a gap can be recorded as a check
  that runs rather than as prose that does not. -/
  known : Bool := false

/-- Record a check as a known gap rather than a requirement. -/
def Check.asKnown (c : Check) : Check := { c with known := true }

/-- A type that needs no table: a primitive. -/
def atom (p : Prim) : ClosedType := .ofPrim p

/-- A type that is one composite, named by the root. -/
def entry (c : Composite) : ClosedType := closeOne c

def relStr (b : Bool) : String := if b then "<:" else "!<:"

/-- A subtype question about two types, each carrying its own table. -/
def expectSub (a b : ClosedType) (want : Bool) (name : String) : Check :=
  let got := decSubtype a b
  { name := name
    ok := got == want
    detail := s!"got {relStr got}, want {relStr want}" }

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
  [ expectSub (atom .nat) (atom .nat) true "nat <: nat"
  , expectSub (atom .nat) (atom .int) true "nat <: int"
  , expectSub (atom .int) (atom .nat) false "int !<: nat"
  , expectSub (atom .nat8) (atom .nat) false "nat8 !<: nat (no width subtyping)"
  , expectSub (atom .nat) (atom .nat8) false "nat !<: nat8"
  , expectSub (atom .nat32) (atom .int32) false "nat32 !<: int32"
  , expectSub (atom .text) (atom .reserved) true "text <: reserved"
  , expectSub (entry (.func [] [] [])) (atom .reserved) true "func <: reserved"
  , expectSub (atom .empty) (atom .text) true "empty <: text"
  , expectSub (atom .empty) (entry (.vec nat)) true "empty <: vec nat"
  , expectSub (atom .text) (atom .nat) false "text !<: nat"
  , expectSub (entry (.service [])) (atom .principal) true "service <: principal"
  , expectSub (atom .principal) (entry (.service [])) false "principal !<: service" ]

/-! ## Options

Every type is a subtype of every option -- the spec's four `opt` rules with their
negative premises eliminated. The `text <: opt nat` case is the surprising one, and
it is deliberate: a receiver that cannot decode the value sees `null`. -/

def optChecks : List Check :=
  [ expectSub (atom .nat) (entry (.opt nat)) true "nat <: opt nat"
  , expectSub (atom .null) (entry (.opt nat)) true "null <: opt nat"
  , expectSub (atom .reserved) (entry (.opt nat)) true "reserved <: opt nat"
  , expectSub (atom .text) (entry (.opt nat)) true "text <: opt nat (special opt rule)"
  , expectSub (entry (.opt text)) (entry (.opt nat)) true
      "opt text <: opt nat (special opt rule)"
  , expectSub (entry (.opt nat)) (atom .nat) false "opt nat !<: nat"
  , expectSub (entry (.opt nat)) (atom .reserved) true "opt nat <: reserved" ]

/-! ## Vectors -/

def vecChecks : List Check :=
  [ expectSub (entry (.vec nat)) (entry (.vec int)) true "vec nat <: vec int"
  , expectSub (entry (.vec int)) (entry (.vec nat)) false "vec int !<: vec nat"
  , expectSub (entry (.vec nat)) (atom .nat) false "vec nat !<: nat" ]

/-! ## Records

A subtype may add fields and specialise field types. It may also *omit* a field the
supertype declares, provided that field accepts `null` -- the rule that makes records
extensible in both inbound and outbound position. -/

/-- `record { x : nat; y : opt text }`. Two entries: the `opt` needs one of its own. -/
def recordWithOptField : ClosedType := close do
  let o ← intern (.opt text)
  intern (recordOf [("x", nat), ("y", o)])

def recordChecks : List Check :=
  [ expectSub (entry (recordOf [("x", nat)])) (entry (recordOf [])) true
      "record {x:nat} <: record {}"
  , expectSub (entry (recordOf [("x", nat), ("y", text)])) (entry (recordOf [("x", nat)]))
      true "record {x;y} <: record {x} (field added)"
  , expectSub (entry (recordOf [("x", nat)])) (entry (recordOf [("x", int)])) true
      "record {x:nat} <: record {x:int} (field specialised)"
  , expectSub (entry (recordOf [("x", int)])) (entry (recordOf [("x", nat)])) false
      "record {x:int} !<: record {x:nat}"
  , expectSub (entry (recordOf [("x", nat)])) recordWithOptField true
      "record {x} <: record {x; y:opt text} (omitted field accepts null)"
  , expectSub (entry (recordOf [("x", nat)])) (entry (recordOf [("x", nat), ("y", reserved)]))
      true "record {x} <: record {x; y:reserved}"
  , expectSub (entry (recordOf [("x", nat)])) (entry (recordOf [("x", nat), ("y", text)]))
      false "record {x} !<: record {x; y:text} (omitted field rejects null)"
  , expectSub (entry (recordOf [("x", nat)])) (entry (recordOf [("y", nat)])) false
      "record {x} !<: record {y}" ]

/-! ## Variants

Dual to records: a subtype may *drop* tags, and every tag it carries must exist in
the supertype. Adding tags is only sound behind an `opt`. -/

/-- `opt variant { ... }`. -/
def optVariant (alts : List (String × Slot)) : ClosedType := close do
  let v ← intern (variantOf alts)
  intern (.opt v)

def variantChecks : List Check :=
  [ expectSub (entry (variantOf [])) (entry (variantOf [("a", nat)])) true
      "variant {} <: variant {a}"
  , expectSub (entry (variantOf [("a", nat)])) (entry (variantOf [("a", nat), ("b", text)]))
      true "variant {a} <: variant {a; b} (tag dropped)"
  , expectSub (entry (variantOf [("a", nat), ("b", text)])) (entry (variantOf [("a", nat)]))
      false "variant {a; b} !<: variant {a} (tag added)"
  , expectSub (entry (variantOf [("a", nat)])) (entry (variantOf [("a", int)])) true
      "variant {a:nat} <: variant {a:int}"
  , expectSub (optVariant [("a", nat), ("b", text)]) (optVariant [("a", nat)]) true
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

/-- `func (opt nat) -> ()`. -/
def funcOptParam : ClosedType := close do
  let o ← intern (.opt nat)
  intern (.func [o] [] [])

/-- `func () -> (opt nat)`. -/
def funcOptResult : ClosedType := close do
  let o ← intern (.opt nat)
  intern (.func [] [o] [])

def funcChecks : List Check :=
  [ expectSub (entry (.func [int] [nat] [])) (entry (.func [nat] [int] [])) true
      "func (int) -> (nat) <: func (nat) -> (int)"
  , expectSub (entry (.func [nat] [int] [])) (entry (.func [int] [nat] [])) false
      "func (nat) -> (int) !<: func (int) -> (nat)"
    -- Parameters: dropping is free, adding needs to accept null.
  , expectSub (entry (.func [] [] [])) (entry (.func [nat] [] [])) true
      "func () -> () <: func (nat) -> () (parameter dropped, always allowed)"
  , expectSub funcOptParam (entry (.func [] [] [])) true
      "func (opt nat) -> () <: func () -> () (optional parameter added)"
  , expectSub (entry (.func [nat] [] [])) (entry (.func [] [] [])) false
      "func (nat) -> () !<: func () -> () (added parameter rejects null)"
    -- Results: adding is free, dropping needs to accept null.
  , expectSub (entry (.func [] [nat] [])) (entry (.func [] [] [])) true
      "func () -> (nat) <: func () -> () (result added, always allowed)"
  , expectSub (entry (.func [] [] [])) funcOptResult true
      "func () -> () <: func () -> (opt nat) (optional result dropped)"
  , expectSub (entry (.func [] [] [])) (entry (.func [] [nat] [])) false
      "func () -> () !<: func () -> (nat) (dropped result rejects null)"
  , expectSub (entry (.func [] [] [.query])) (entry (.func [] [] [])) false
      "annotations must agree"
  , expectSub (entry (.func [] [] [.query])) (entry (.func [] [] [.query])) true
      "matching annotations agree" ]

/-! ## Services

A method's type is a reference like any other -- the spec is explicit that "the
serialised data type representing a method type must denote a function type"
(`spec/Candid.md:1223`), so it is an index into the table, not an inline function. -/

/-- A service, interning each method type first. -/
def serviceOf (ms : List (String × Composite)) : ClosedType := close do
  let slots ← ms.mapM fun (name, c) => do return (name, ← intern c)
  intern (.service slots)

def serviceChecks : List Check :=
  [ expectSub (serviceOf [("m", .func [] [] [])]) (serviceOf []) true
      "service {m} <: service {}"
  , expectSub (serviceOf []) (serviceOf [("m", .func [] [] [])]) false
      "service {} !<: service {m}"
  , expectSub (serviceOf [("m", .func [] [nat] [])]) (serviceOf [("m", .func [] [] [])]) true
      "service method specialised" ]

/-! ## Well-formedness rules that are not structural

Two rules from the spec that the shape of a `Composite` does not enforce on its own.
The second is the only rule that has to look through the table, since a method's type
is a slot like any other. -/

/-- `spec/Candid.md:211`: "The result list of a `oneway` function must be empty." -/
def onewayWithResult : ClosedType := entry (.func [] [nat] [.oneway])

def onewayWithoutResult : ClosedType := entry (.func [nat] [] [.oneway])

/-- `spec/Candid.md:1223`: "The serialised data type representing a method type must
denote a function type." -/
def serviceWithPrimMethod : ClosedType := entry (.service [("m", nat)])

def serviceWithVecMethod : ClosedType := close do
  let v ← intern (.vec nat)
  intern (.service [("m", v)])

def wellFormedChecks : List Check :=
  [ expectWellFormed onewayWithResult false "oneway with a result is malformed"
  , expectWellFormed onewayWithoutResult true "oneway without results is well formed"
  , expectWellFormed (entry (.func [] [nat] [.query])) true
      "query with a result is well formed"
  , expectWellFormed serviceWithPrimMethod false
      "service method that is a primitive is malformed"
  , expectWellFormed serviceWithVecMethod false
      "service method that is not a function is malformed"
  , expectWellFormed (serviceOf [("m", .func [] [] [])]) true
      "service method that is a function is well formed" ]

/-! ## Recursive types across two independent tables

These are the cases the reference-pair accounting exists for. `selfLoop` and
`twoCycle` denote the same infinite type through different table shapes, so the
recursion only stops because descending through a pair of references records it in
`seen`, and meeting that pair again means the obligation is already assumed. -/

/-- `type S = record { next : S }`, as one self-referential entry. -/
def selfLoop : ClosedType :=
  { table := { entries := #[ recordOf [("next", .ref 0)] ] }, root := .ref 0 }

/-- The same type unrolled across two entries. -/
def twoCycle : ClosedType :=
  { table := { entries := #[ recordOf [("next", .ref 1)], recordOf [("next", .ref 0)] ] }
    root := .ref 0 }

/-- `type S = record { next : S; extra : nat }`. -/
def selfLoopWith (extra : Slot) : ClosedType :=
  { table := { entries := #[ recordOf [("next", .ref 0), ("extra", extra)] ] }, root := .ref 0 }

/-- A reference with no entry to resolve to. -/
def danglingRef : ClosedType := { table := .empty, root := .ref 3 }

/- No check here for a primitive or a bare reference used as a table entry: an entry
is a `Composite`, so neither is representable. The spec's rule
(`spec/Candid.md:1227`) still has force, but it belongs to the decoder, which has to
reject a primitive opcode in an entry position when it parses wire bytes. -/

def recursiveChecks : List Check :=
  [ expectSub selfLoop selfLoop true
      "self-loop <: itself (the reference pair is consumed once)"
  , expectSub selfLoop twoCycle true
      "self-loop <: two-cycle (same type, different table shape)"
  , expectSub twoCycle selfLoop true
      "two-cycle <: self-loop"
  , expectSub (selfLoopWith nat) (selfLoopWith int) true
      "recursive record, field specialised"
  , expectSub (selfLoopWith int) (selfLoopWith nat) false
      "recursive record, field not specialised"
  , expectSub (selfLoopWith nat) selfLoop true
      "recursive record with extra field <: without it"
  , expectWellFormed selfLoop true "self-loop is well formed"
  , expectWellFormed twoCycle true "two-cycle is well formed"
  , expectWellFormed (atom .principal) true "principal is a primitive, not a reftype"
  , expectWellFormed danglingRef false "dangling reference is malformed"
    -- A dangling reference is not a type, so it gets neither the top nor the bottom
    -- rule for free. Deliberate: `<:` reported without looking is the dangerous
    -- direction for a compatibility gate.
  , expectSub danglingRef (atom .reserved) false "dangling reference !<: reserved"
  , expectSub (atom .empty) danglingRef false "empty !<: dangling reference"
  , expectWellFormed (entry (.record [(0, nat), (0, text)])) false
      "duplicate field id is malformed" ]

/-! ## `vec`-omega: a cycle that alternates sides

`T.0 = vec T.1` and `T.1 = vec T.0`, so both entries denote the same infinite type,
`vec (vec (vec ...))`, and the answer is `true` in both directions.

Neither side is ever the same entry twice running, so the recursion goes `(0, 1)`,
then `(1, 0)`, then back to `(0, 1)`. Nothing is getting structurally smaller along
the way: the pair accounting is the only thing that can stop it, and it does -- the
third state finds its pair already recorded in `seen`. -/

def vecOmegaTable : TypeTable := { entries := #[ .vec (.ref 1), .vec (.ref 0) ] }

def vecOmegaEven : ClosedType := { table := vecOmegaTable, root := .ref 0 }
def vecOmegaOdd : ClosedType := { table := vecOmegaTable, root := .ref 1 }

def vecOmegaChecks : List Check :=
  [ expectWellFormed vecOmegaEven true "vec-omega: T.0 is well formed"
  , expectWellFormed vecOmegaOdd true "vec-omega: T.1 is well formed"
  , expectSub vecOmegaEven vecOmegaOdd true "vec-omega <: its own unrolling"
  , expectSub vecOmegaOdd vecOmegaEven true "vec-omega's unrolling <: it" ]

/-! ## Contravariance: `seen` swaps with the tables

The parameter premise of the function rule swaps the two tables, so it must swap the
pair accounting with them. A pair `(i, j)` is about `A`'s `i` and `B`'s `j`; read
unswapped inside the swapped call it is about `B`'s `i` and `A`'s `j`, which is a
different question, and subtyping is not symmetric.

The witness below reduces `contraOuter <: contraOuter'` to `contraFuncs <:
contraFuncs'`, two functions whose parameter premise asks `contraB.1 <: contraA.2`,
i.e. `vec text <: vec nat` -- false. Reaching that premise records `(1, 2)` in
`seen`, so a procedure that read `seen` unswapped would answer the premise from the
accounting instead, and both queries would come out `true`. -/

/-- `A.0 = record { f : A.1 }`, `A.1 = func (A.2) -> ()`, `A.2 = vec nat`. -/
def contraA : TypeTable :=
  { entries := #[ recordOf [("f", .ref 1)], .func [.ref 2] [] [], .vec nat ] }

/-- `B.0 = record { f : B.2 }`, `B.1 = vec text`, `B.2 = func (B.1) -> ()`. The
indices are deliberately transposed against `contraA`. -/
def contraB : TypeTable :=
  { entries := #[ recordOf [("f", .ref 2)], .vec text, .func [.ref 1] [] [] ] }

def contraOuter : ClosedType := { table := contraA, root := .ref 0 }
def contraOuter' : ClosedType := { table := contraB, root := .ref 0 }
def contraFuncs : ClosedType := { table := contraA, root := .ref 1 }
def contraFuncs' : ClosedType := { table := contraB, root := .ref 2 }

def contraChecks : List Check :=
  [ expectWellFormed contraOuter true "contravariance witness: subtype side is well formed"
  , expectWellFormed contraOuter' true "contravariance witness: supertype side is well formed"
  , expectSub contraFuncs contraFuncs' false
      "func (vec nat) -> () !<: func (vec text) -> () (parameter premise fails)"
  , expectSub contraOuter contraOuter' false
      "record { f : func (vec nat) -> () } !<: record { f : func (vec text) -> () }" ]

/-! ## Transitivity spot-check

The spec keeps transitivity as a design goal, and the unusual `opt` rules exist to
preserve it. This is not a proof -- it is the shape the eventual property test and
the Lean theorem take. -/

def transitivityChecks : List Check :=
  let a := entry (recordOf [("x", nat)])
  let b := recordWithOptField
  let c := entry (recordOf [("x", int)])
  [ expectSub a b true "transitivity: a <: b"
  , expectSub b c true "transitivity: b <: c"
  , expectSub a c true "transitivity: therefore a <: c" ]

def allChecks : List Check :=
  hashChecks ++ primChecks ++ optChecks ++ vecChecks ++ recordChecks ++
  variantChecks ++ funcChecks ++ serviceChecks ++ wellFormedChecks ++
  recursiveChecks ++ vecOmegaChecks ++ contraChecks ++ transitivityChecks

def main : IO UInt32 := do
  let failures := allChecks.filter (fun c => if c.known then c.ok else !c.ok)
  let known := allChecks.filter (·.known)
  for c in allChecks do
    match c.known, c.ok with
    | false, true => IO.println s!"ok    {c.name}"
    | false, false => IO.println s!"FAIL  {c.name} -- {c.detail}"
    | true, false => IO.println s!"known {c.name} -- {c.detail}"
    | true, true => IO.println s!"FAIL  {c.name} -- known gap now passes; promote it"
  IO.println ""
  if failures.isEmpty then
    IO.println s!"{allChecks.length - known.length} checks passed, {known.length} known gaps"
    return 0
  else
    IO.eprintln s!"{failures.length} of {allChecks.length} checks failed"
    return 1
