/-
The hand-written vectors: the cases someone thought of, each named for what it shows.

These were the oracle's built-in checks before vectors existed, and they are the
model's own test suite still -- `lake exe oracle` checks the model against every one.
Unlike the generated vectors (`Oracle/Generate.lean`), whose expectations the model
computes, each expectation here was written down independently of it, so a vector here
can catch the model being wrong.

Every type is a `Fixture`: a raw table and a root, because composites live only in the
table (`Candid/Types.lean`). `atom` is a primitive, `entry` is a single composite, and
`close do ... intern ...` builds the two-or-more-entry cases.
-/

import Oracle.Vector

namespace Oracle

open Candid
open Candid.Slot
open Candid.Composite

/-- A type that needs no table: a primitive. -/
def atom (p : Prim) : Fixture := ⟨.empty, .prim p⟩

/-- A type that is one composite, named by the root. -/
def entry (c : Composite) : Fixture := closeOne c

def expectSub (a b : Fixture) (want : Bool) (id : String) : Vector :=
  ⟨id, .subtype a b want⟩

def expectHash (input : String) (want : UInt32) : Vector :=
  ⟨s!"hash {repr input} = {want}", .hash input want⟩

def expectWellFormed (f : Fixture) (want : Bool) (id : String) : Vector :=
  ⟨id, .wellFormed f want⟩

/-! ## Field-id hash

Values computed independently from the spec formula. `"é"` is the discriminating
case: hashing UTF-8 bytes gives 43654, hashing characters would give 233. -/

def hashChecks : List Vector :=
  [ expectHash "" 0
  , expectHash "Ok" 17724
  , expectHash "Err" 3456837
  , expectHash "id" 23515
  , expectHash "value" 834174833
  , expectHash "é" 43654 ]

/-! ## Primitives, top and bottom -/

def primChecks : List Vector :=
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

def optChecks : List Vector :=
  [ expectSub (atom .nat) (entry (.opt nat)) true "nat <: opt nat"
  , expectSub (atom .null) (entry (.opt nat)) true "null <: opt nat"
  , expectSub (atom .reserved) (entry (.opt nat)) true "reserved <: opt nat"
  , expectSub (atom .text) (entry (.opt nat)) true "text <: opt nat (special opt rule)"
  , expectSub (entry (.opt text)) (entry (.opt nat)) true
      "opt text <: opt nat (special opt rule)"
  , expectSub (entry (.opt nat)) (atom .nat) false "opt nat !<: nat"
  , expectSub (entry (.opt nat)) (atom .reserved) true "opt nat <: reserved" ]

/-! ## Vectors -/

def vecChecks : List Vector :=
  [ expectSub (entry (.vec nat)) (entry (.vec int)) true "vec nat <: vec int"
  , expectSub (entry (.vec int)) (entry (.vec nat)) false "vec int !<: vec nat"
  , expectSub (entry (.vec nat)) (atom .nat) false "vec nat !<: nat" ]

/-! ## Records

A subtype may add fields and specialise field types. It may also *omit* a field the
supertype declares, provided that field accepts `null` -- the rule that makes records
extensible in both inbound and outbound position. -/

/-- `record { x : nat; y : opt text }`. Two entries: the `opt` needs one of its own. -/
def recordWithOptField : Fixture := close do
  let o ← intern (.opt text)
  intern (recordOf [("x", nat), ("y", o)])

def recordChecks : List Vector :=
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
def optVariant (alts : List (String × Slot)) : Fixture := close do
  let v ← intern (variantOf alts)
  intern (.opt v)

def variantChecks : List Vector :=
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
def funcOptParam : Fixture := close do
  let o ← intern (.opt nat)
  intern (.func [o] [] [])

/-- `func () -> (opt nat)`. -/
def funcOptResult : Fixture := close do
  let o ← intern (.opt nat)
  intern (.func [] [o] [])

def funcChecks : List Vector :=
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
      "matching annotations agree"
  , expectSub (entry (.func [] [] [.query, .compositeQuery]))
      (entry (.func [] [] [.compositeQuery, .query])) true
      "annotations agree up to reordering" ]

/-! ## Services

A method's type is a reference like any other -- the spec is explicit that "the
serialised data type representing a method type must denote a function type"
(`spec/Candid.md:1223`), so it is an index into the table, not an inline function. -/

/-- A service, interning each method type first. -/
def serviceOf (ms : List (String × Composite)) : Fixture := close do
  let slots ← ms.mapM fun (name, c) => do return (name, ← intern c)
  intern (.service slots)

def serviceChecks : List Vector :=
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
def onewayWithResult : Fixture := entry (.func [] [nat] [.oneway])

def onewayWithoutResult : Fixture := entry (.func [nat] [] [.oneway])

/-- `spec/Candid.md:1223`: "The serialised data type representing a method type must
denote a function type." -/
def serviceWithPrimMethod : Fixture := entry (.service [("m", nat)])

def serviceWithVecMethod : Fixture := close do
  let v ← intern (.vec nat)
  intern (.service [("m", v)])

def wellFormedChecks : List Vector :=
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
def selfLoop : Fixture :=
  { table := { entries := #[ recordOf [("next", .ref 0)] ] }, root := .ref 0 }

/-- The same type unrolled across two entries. -/
def twoCycle : Fixture :=
  { table := { entries := #[ recordOf [("next", .ref 1)], recordOf [("next", .ref 0)] ] }
    root := .ref 0 }

/-- `type S = record { next : S; extra : nat }`. -/
def selfLoopWith (extra : Slot) : Fixture :=
  { table := { entries := #[ recordOf [("next", .ref 0), ("extra", extra)] ] }, root := .ref 0 }

/-- A root with no entry to resolve to. -/
def danglingRef : Fixture := { table := .empty, root := .ref 3 }

/-- A root that resolves, to an entry whose own reference does not. Answering
`empty <: this` or `this <: reserved` never unfolds the entry, so only checking the
whole table catches it. -/
def danglingBehindRoot : Fixture :=
  { table := { entries := #[.vec (.ref 1)] }, root := .ref 0 }

/- No check here for a primitive or a bare reference used as a table entry: an entry
is a `Composite`, so neither is representable. The spec's rule
(`spec/Candid.md:1227`) still has force, but it belongs to the decoder, which has to
reject a primitive opcode in an entry position when it parses wire bytes. -/

def recursiveChecks : List Vector :=
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
    -- A dangling reference is not a type, so it never reaches subtyping, where the
    -- top and bottom rules would grant it `<:` without looking -- the dangerous
    -- direction for a compatibility gate.
  , expectWellFormed danglingRef false "dangling root is malformed"
  , expectWellFormed danglingBehindRoot false "reference dangling behind the root is malformed"
  , expectWellFormed (entry (.record [(0, nat), (0, text)])) false
      "duplicate field id is malformed" ]

/-! ## `vec`-omega: a cycle that alternates sides

`T.0 = vec T.1` and `T.1 = vec T.0`, so both entries denote the same infinite type,
`vec (vec (vec ...))`, and the answer is `true` in both directions.

Neither side is ever the same entry twice running, so the recursion goes `(0, 1)`,
then `(1, 0)`, then back to `(0, 1)`. Nothing is getting structurally smaller along
the way: the pair accounting is the only thing that can stop it, and it does -- the
third state finds its pair already recorded in `seen`. -/

def vecOmegaTable : RawTypeTable := { entries := #[ .vec (.ref 1), .vec (.ref 0) ] }

def vecOmegaEven : Fixture := { table := vecOmegaTable, root := .ref 0 }
def vecOmegaOdd : Fixture := { table := vecOmegaTable, root := .ref 1 }

def vecOmegaChecks : List Vector :=
  [ expectWellFormed vecOmegaEven true "vec-omega: T.0 is well formed"
  , expectWellFormed vecOmegaOdd true "vec-omega: T.1 is well formed"
  , expectSub vecOmegaEven vecOmegaOdd true "vec-omega <: its own unrolling"
  , expectSub vecOmegaOdd vecOmegaEven true "vec-omega's unrolling <: it" ]

/-! ## Contravariance: the pair accounting swaps with the tables, and keeps direction

The parameter premise of the function rule swaps the two tables, so it must swap the
pair accounting with them -- and each assumption must keep its direction. Two ways to
get it wrong, one witness each, and the model shipped both.

**Reading `seen` unswapped.** A pair `(i, j)` is about `A`'s `i` and `B`'s `j`; read
inside the swapped call it is about `B`'s `i` and `A`'s `j`. The witness reduces
`contraOuter <: contraOuter'` to `contraFuncs <: contraFuncs'`, two functions whose
parameter premise asks `contraB.1 <: contraA.2`, i.e. `vec text <: vec nat` -- false.
Reaching that premise records `(1, 2)`, so a procedure that read it unswapped would
answer the premise from the accounting instead, and both queries would come out
`true`.

**Reading an assumption as its converse.** Swapping `seen` *element-wise* fixes the
indices but turns an assumed `A.i <: B.j` into an assumed `B.j <: A.i`, which does not
follow. `selfParam` is a function taking itself: comparing the `nat` and `int`
versions assumes `A.0 <: B.0`, the parameter premise asks `B.0 <: A.0`, and a
procedure that found the swapped pair would skip the comparison that needs
`int <: nat`. Hence two lists, one per direction (`Subtype.lean`). -/

/-- `A.0 = record { f : A.1 }`, `A.1 = func (A.2) -> ()`, `A.2 = vec nat`. -/
def contraA : RawTypeTable :=
  { entries := #[ recordOf [("f", .ref 1)], .func [.ref 2] [] [], .vec nat ] }

/-- `B.0 = record { f : B.2 }`, `B.1 = vec text`, `B.2 = func (B.1) -> ()`. The
indices are deliberately transposed against `contraA`. -/
def contraB : RawTypeTable :=
  { entries := #[ recordOf [("f", .ref 2)], .vec text, .func [.ref 1] [] [] ] }

def contraOuter : Fixture := { table := contraA, root := .ref 0 }
def contraOuter' : Fixture := { table := contraB, root := .ref 0 }
def contraFuncs : Fixture := { table := contraA, root := .ref 1 }
def contraFuncs' : Fixture := { table := contraB, root := .ref 2 }

/-- `A.0 = func (A.0) -> (r)`: a function that takes itself. -/
def selfParam (r : Slot) : Fixture := { table := { entries := #[ .func [.ref 0] [r] [] ] }, root := .ref 0 }

def selfParamNat : Fixture := selfParam nat
def selfParamInt : Fixture := selfParam int

def contraChecks : List Vector :=
  [ expectWellFormed contraOuter true "contravariance witness: subtype side is well formed"
  , expectWellFormed contraOuter' true "contravariance witness: supertype side is well formed"
  , expectSub contraFuncs contraFuncs' false
      "func (vec nat) -> () !<: func (vec text) -> () (parameter premise fails)"
  , expectSub contraOuter contraOuter' false
      "record { f : func (vec nat) -> () } !<: record { f : func (vec text) -> () }"
  , expectSub selfParamNat selfParamInt false
      "func (A) -> (nat) !<: func (B) -> (int), each taking itself (assumption is not its converse)"
  , expectSub selfParamNat selfParamNat true
      "func (A) -> (nat) <: itself, taking itself" ]

/-! ## Shared sub-types: assumptions outlive the path that made them

Entries `0`..`39` each reference the next one twice, so the table is a chain but the
type it denotes is a binary tree of depth 40 whose subtrees are all shared. Assumptions
scoped to a path re-derive each shared subtree once per path that reaches it --
2^41 - 1 comparisons, days of work for a few hundred bytes of type table. Shared
across the whole run, each pair is compared once. A regression here shows up as CI
timing out rather than as a failed check. -/

/-- `T.i = record { 0 : T.(i+1); 1 : T.(i+1) }` for `i < 40`, ending in `T.40 = last`. -/
def sharedTail (last : Composite) : Fixture :=
  { table := { entries := ((List.range 40).map fun i =>
      Composite.record [(0, .ref (i + 1)), (1, .ref (i + 1))]).toArray.push last }
    root := .ref 0 }

def sharedChecks : List Vector :=
  [ expectSub (sharedTail (.record [(2, nat)])) (sharedTail (.record [])) true
      "shared tails, depth 40: each pair compared once"
  , expectSub (sharedTail (.record [])) (sharedTail (.record [(2, nat)])) false
      "shared tails, depth 40: the failing direction" ]

/-! ## Assumptions made under a failed comparison

`opt` asks nothing of its argument: `t <: opt t'` for every `t` and `t'`. An
implementation that decides it by first *trying* `t <: t'` -- to tell the ordinary rule
from the special one -- has to discard everything that attempt assumed when it fails,
not only the pair that failed. A pair proved inside the attempt may have been proved
*from* the assumption that then failed.

Here the attempt is `X <: Y`. It assumes `X <: Y`, descends into `X' <: Y'`, meets
`X <: Y` again and takes the assumption -- so `X' <: Y'` holds, under that assumption.
Then `nat <: text` fails, and `X <: Y` with it. If `X' <: Y'` is still remembered, the
second field is answered from memory and the record comparison succeeds; it should
not, because `X' <: Y'` needs `X <: Y`. The second vector asks `X' <: Y'` on its own,
where nothing has been remembered yet. -/

/-- `A.0 = record { 0 : X; 1 : X' }`, `X = A.1 = record { 0 : X'; 1 : nat }`,
`X' = A.2 = record { 0 : X }`. -/
def leakA : RawTypeTable :=
  { entries := #[ .record [(0, .ref 1), (1, .ref 2)]
                , .record [(0, .ref 2), (1, nat)]
                , .record [(0, .ref 1)] ] }

/-- `B.0 = record { 0 : opt Y; 1 : Y' }`, `B.1 = opt Y`,
`Y = B.2 = record { 0 : Y'; 1 : text }`, `Y' = B.3 = record { 0 : Y }`. -/
def leakB : RawTypeTable :=
  { entries := #[ .record [(0, .ref 1), (1, .ref 3)]
                , .opt (.ref 2)
                , .record [(0, .ref 3), (1, text)]
                , .record [(0, .ref 2)] ] }

def leakChecks : List Vector :=
  [ expectSub ⟨leakA, .ref 0⟩ ⟨leakB, .ref 0⟩ false
      "record { X; X' } !<: record { opt Y; Y' } (assumption from a failed opt attempt)"
  , expectSub ⟨leakA, .ref 2⟩ ⟨leakB, .ref 3⟩ false
      "X' !<: Y' (the same question, asked first)" ]

/-! ## Transitivity spot-check

The spec keeps transitivity as a design goal, and the unusual `opt` rules exist to
preserve it. This is not a proof -- it is the shape the eventual property test and
the Lean theorem take. -/

def transitivityChecks : List Vector :=
  let a := entry (recordOf [("x", nat)])
  let b := recordWithOptField
  let c := entry (recordOf [("x", int)])
  [ expectSub a b true "transitivity: a <: b"
  , expectSub b c true "transitivity: b <: c"
  , expectSub a c true "transitivity: therefore a <: c" ]

/-! ## Coercion

`v : t ~> v' : t'`, from `spec/Candid.md`, "Coercion". Each expectation was worked
out from the spec's rules by hand; "reject" means no rule applies, so a decoder must
fail. -/

def expectCoerce (v : Value) (a b : Fixture) (want : Option Value) (id : String) : Vector :=
  ⟨id, .coerce v a b want⟩

/-- A record value from named fields, in canonical (ascending id) order. -/
def recordVal (fs : List (String × Value)) : Value :=
  .record (sortFields (fs.map fun (n, v) => (hashFieldName n, v)))

def variantVal (n : String) (v : Value) : Value := .variant (hashFieldName n) v

/-- `opt t`, for a type that is itself a single entry or a primitive. -/
def optOf (t : Slot) : Fixture := entry (.opt t)

/-- `opt opt nat`. -/
def optOptNat : Fixture := close do
  let o ← intern (.opt nat)
  intern (.opt o)

/-- `type R = opt R`. -/
def optCycle : Fixture := { table := { entries := #[.opt (.ref 0)] }, root := .ref 0 }

/-- `type A = opt B; type B = opt A`. -/
def optCycle2 : Fixture :=
  { table := { entries := #[.opt (.ref 1), .opt (.ref 0)] }, root := .ref 0 }

/-- `R`, entry `0`, with `c` built over it as the root. -/
def overOptCycle (c : Composite) : Fixture :=
  { table := { entries := #[.opt (.ref 0), c] }, root := .ref 1 }

/-- `vec opt nat`. -/
def vecOptNat : Fixture := close do
  let o ← intern (.opt nat)
  intern (.vec o)

/-- `record { a : nat; c : <t> }`, with `t` given as a construction. -/
def recordAC (c : TableM Slot) : Fixture := close do
  let t ← c
  intern (recordOf [("a", nat), ("c", t)])

/-- `opt variant { a : nat }`. -/
def optVariantA : Fixture := optVariant [("a", nat)]

def someService : PrincipalBytes := [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x01]

def coercePrimChecks : List Vector :=
  [ expectCoerce (.nat 5) (atom .nat) (atom .nat) (some (.nat 5)) "5 : nat ~> 5 : nat"
  , expectCoerce (.nat 5) (atom .nat) (atom .int) (some (.int 5)) "5 : nat ~> 5 : int"
  , expectCoerce (.int (-5)) (atom .int) (atom .nat) none "-5 : int ~> reject : nat"
  , expectCoerce (.nat8 5) (atom .nat8) (atom .nat) none
      "5 : nat8 ~> reject : nat (no width subtyping)"
  , expectCoerce (.nat16 300) (atom .nat16) (atom .nat16) (some (.nat16 300))
      "300 : nat16 ~> 300 : nat16"
  , expectCoerce (.text "x") (atom .text) (atom .reserved) (some .null)
      "\"x\" : text ~> null : reserved"
  , expectCoerce (.float64 0x7ff8000000000001) (atom .float64) (atom .float64)
      (some (.float64 0x7ff8000000000001)) "NaN with a payload : float64 ~> itself"
  , expectCoerce (.float32 0x80000000) (atom .float32) (atom .float32)
      (some (.float32 0x80000000)) "-0.0 : float32 ~> -0.0 : float32"
  , expectCoerce (.float32 0x3f800000) (atom .float32) (atom .float64) none
      "1.0 : float32 ~> reject : float64"
  , expectCoerce (.service someService) (entry (.service [])) (atom .principal)
      (some (.principal someService)) "service : service {} ~> principal"
  , expectCoerce (.principal someService) (atom .principal) (atom .principal)
      (some (.principal someService)) "principal ~> principal" ]

def coerceOptChecks : List Vector :=
  [ expectCoerce .null (atom .null) (optOf nat) (some .null) "null : null ~> null : opt nat"
  , expectCoerce .null (atom .reserved) (optOf nat) (some .null)
      "null : reserved ~> null : opt nat"
  , expectCoerce .null (optOf nat) (optOf text) (some .null)
      "null : opt nat ~> null : opt text"
  , expectCoerce (.opt (.nat 5)) (optOf nat) (optOf int) (some (.opt (.int 5)))
      "opt 5 : opt nat ~> opt 5 : opt int"
  , expectCoerce (.opt (.text "x")) (optOf text) (optOf nat) (some .null)
      "opt \"x\" : opt text ~> null : opt nat (inner coercion fails)"
  , expectCoerce (.nat 5) (atom .nat) (optOf nat) (some (.opt (.nat 5)))
      "5 : nat ~> opt 5 : opt nat"
  , expectCoerce (.text "x") (atom .text) (optOf nat) (some .null)
      "\"x\" : text ~> null : opt nat"
  , expectCoerce (.nat 5) (atom .nat) optOptNat (some (.opt (.opt (.nat 5))))
      "5 : nat ~> opt opt 5 : opt opt nat"
  , expectCoerce (.text "x") (atom .text) optOptNat (some (.opt .null))
      "\"x\" : text ~> opt null : opt opt nat (only the innermost option is null)"
  , expectCoerce (.opt (.nat 5)) (optOf nat) optOptNat (some (.opt (.opt (.nat 5))))
      "opt 5 : opt nat ~> opt opt 5 : opt opt nat"
  , expectCoerce (.opt (.nat 5)) (optOf nat) (atom .nat) none "opt 5 : opt nat ~> reject : nat"
    -- `5 : nat ~> null : reserved`, so the option around it is not `null`. The model
    -- had this wrong until the candid 0.10 runner disagreed with it.
  , expectCoerce (.nat 5) (atom .nat) (optOf reserved) (some (.opt .null))
      "5 : nat ~> opt null : opt reserved"
  , expectCoerce (.opt (.nat 5)) (optOf nat) (optOf reserved) (some (.opt .null))
      "opt 5 : opt nat ~> opt null : opt reserved"
  ]

/-! ## Coercion at an infinite option

`spec/Candid.md`, "Coercion" > "Options": coercing a value whose type does not accept
`null` at an infinite option is undefined, which is not the same as failing, so nothing
encloses it into `null`, and the message is rejected. A value whose type accepts `null`
coerces as usual. These mirror the assertions in `test/construct.test.did`. -/

def coerceInfiniteOptChecks : List Vector :=
  [ expectCoerce (.nat 5) (atom .nat) optCycle none
      "5 : nat ~> reject : R where R = opt R (undefined)"
  , expectCoerce (.bool true) (atom .bool) optCycle2 none
      "true : bool ~> reject : A where A = opt B, B = opt A (undefined)"
  , expectCoerce (.opt (.bool true)) (optOf bool) optCycle none
      "opt true : opt bool ~> reject : R (undefined, so not null)"
  , expectCoerce (.record [(0, .bool true)]) (entry (.record [(0, bool)]))
      (overOptCycle (.record [(0, .ref 0)])) none
      "record {true} ~> reject : record {R} (a field at R fails the record)"
  , expectCoerce (.vec [.bool true]) (entry (.vec bool)) (overOptCycle (.vec (.ref 0))) none
      "vec {true} ~> reject : vec R (an element at R fails the vector)"
  , expectCoerce (.vec []) (entry (.vec bool)) (overOptCycle (.vec (.ref 0))) (some (.vec []))
      "vec {} : vec bool ~> vec {} : vec R (nothing to coerce)"
  , expectCoerce (.opt .null) optCycle optCycle (some (.opt .null))
      "opt null : R ~> opt null : R (its contents accept null)"
  , expectCoerce .null (atom .null) optCycle (some .null)
      "null : null ~> null : R" ]

def coerceVecChecks : List Vector :=
  [ expectCoerce (.vec [.nat 1, .nat 2]) (entry (.vec nat)) (entry (.vec int))
      (some (.vec [.int 1, .int 2])) "vec {1; 2} : vec nat ~> vec {1; 2} : vec int"
  , expectCoerce (.vec [.int 1, .int (-1)]) (entry (.vec int)) (entry (.vec nat)) none
      "vec {1; -1} : vec int ~> reject : vec nat"
  , expectCoerce (.vec [.text "a"]) (entry (.vec text)) vecOptNat (some (.vec [.null]))
      "vec {\"a\"} : vec text ~> vec {null} : vec opt nat"
    -- Pointwise, with no premise on the types: an empty vector coerces whatever its
    -- element types, although `vec nat !<: vec text`.
  , expectCoerce (.vec []) (entry (.vec nat)) (entry (.vec text)) (some (.vec []))
      "vec {} : vec nat ~> vec {} : vec text (no premise on the element types)" ]

def coerceRecordChecks : List Vector :=
  [ expectCoerce (recordVal [("a", .nat 1), ("b", .text "x")])
      (entry (recordOf [("a", nat), ("b", text)])) (entry (recordOf [("a", int)]))
      (some (recordVal [("a", .int 1)]))
      "record {a = 1; b = \"x\"} ~> record {a = 1} : record {a : int} (field ignored)"
  , expectCoerce (recordVal [("a", .nat 1)]) (entry (recordOf [("a", nat)]))
      (recordAC (intern (.opt nat))) (some (recordVal [("a", .nat 1), ("c", .null)]))
      "record {a = 1} ~> record {a = 1; c = null} : record {a : nat; c : opt nat}"
  , expectCoerce (recordVal [("a", .nat 1)]) (entry (recordOf [("a", nat)]))
      (recordAC (pure reserved)) (some (recordVal [("a", .nat 1), ("c", .null)]))
      "record {a = 1} ~> record {a = 1; c = null} : record {a : nat; c : reserved}"
  , expectCoerce (recordVal [("a", .nat 1)]) (entry (recordOf [("a", nat)]))
      (recordAC (pure nat)) none
      "record {a = 1} ~> reject : record {a : nat; c : nat} (missing field rejects null)"
  , expectCoerce (recordVal [("a", .int (-1))]) (entry (recordOf [("a", int)]))
      (entry (recordOf [("a", nat)])) none
      "record {a = -1} : record {a : int} ~> reject : record {a : nat}"
  , expectCoerce (recordVal [("a", .text "x")]) (entry (recordOf [("a", text)]))
      (close do let o ← intern (.opt nat); intern (recordOf [("a", o)]))
      (some (recordVal [("a", .null)]))
      "record {a = \"x\"} ~> record {a = null} : record {a : opt nat}"
    -- A type lists its fields in no particular order; the value lists them by id.
  , expectCoerce (recordVal [("a", .nat 1), ("b", .nat 2)])
      (entry (recordOf [("b", nat), ("a", nat)])) (entry (recordOf [("b", nat), ("a", nat)]))
      (some (recordVal [("a", .nat 1), ("b", .nat 2)]))
      "record {a = 1; b = 2} ~> itself, at a type listing b before a" ]

def coerceVariantChecks : List Vector :=
  [ expectCoerce (variantVal "a" (.nat 1)) (entry (variantOf [("a", nat), ("b", text)]))
      (entry (variantOf [("a", int)])) (some (variantVal "a" (.int 1)))
      "variant {a = 1} : variant {a : nat; b : text} ~> variant {a = 1} : variant {a : int}"
  , expectCoerce (variantVal "b" (.text "x")) (entry (variantOf [("a", nat), ("b", text)]))
      (entry (variantOf [("a", nat)])) none
      "variant {b = \"x\"} ~> reject : variant {a : nat} (unexpected tag)"
  , expectCoerce (variantVal "b" (.text "x")) (entry (variantOf [("a", nat), ("b", text)]))
      optVariantA (some .null)
      "variant {b = \"x\"} ~> null : opt variant {a : nat} (unexpected tag behind opt)" ]

def coerceRefChecks : List Vector :=
  let f := Value.func someService "m"
  [ expectCoerce f (entry (.func [int] [nat] [])) (entry (.func [nat] [int] [])) (some f)
      "func reference : func (int) -> (nat) ~> func (nat) -> (int)"
  , expectCoerce f (entry (.func [nat] [] [])) (entry (.func [text] [] [])) none
      "func reference : func (nat) -> () ~> reject : func (text) -> ()"
  , expectCoerce f (entry (.func [nat] [] [])) (close do
        let g ← intern (.func [text] [] [])
        intern (.opt g)) (some .null)
      "func reference : func (nat) -> () ~> null : opt func (text) -> ()"
  , expectCoerce (.service someService) (serviceOf [("m", .func [] [] [])]) (serviceOf [])
      (some (.service someService)) "service reference : service {m} ~> service {}"
  , expectCoerce (.service someService) (serviceOf []) (serviceOf [("m", .func [] [] [])])
      none "service reference : service {} ~> reject : service {m}" ]

def coerceChecks : List Vector :=
  coercePrimChecks ++ coerceOptChecks ++ coerceVecChecks ++ coerceRecordChecks ++
  coerceVariantChecks ++ coerceRefChecks ++ coerceInfiniteOptChecks

/-! ## Decoding

Messages written byte by byte, and what deserialising each at the given types yields:
from `spec/Candid.md`, "Binary Format" and "Deserialisation", and from the choices
recorded in `Candid/Wire.lean` where the spec leaves one open. The bytes are written
out here rather than produced by the model's encoder, so that the encoder and the
decoder cannot agree on a mistake. Spaces in the hex are for reading. -/

/-- Hex, with spaces for reading. Malformed hex here is a mistake in this file. -/
def hexBytes (s : String) : ByteArray :=
  match bytesFromHex? (.str (String.ofList (s.toList.filter (· != ' ')))) with
  | .ok bs => ⟨bs.toArray⟩
  | .error e => panic! s!"bad hex in a hand-written vector: {e}"

/-- Types with no table: primitives. -/
def prims (ss : List Slot) : TypeSeq := ⟨.empty, ss⟩

/-- Types built into one table. -/
def typesOf (m : TableM (List Slot)) : TypeSeq :=
  let (roots, entries) := m.run #[]
  ⟨{ entries }, roots⟩

def expectDecode (hex : String) (ts : TypeSeq) (want : Option (List Value)) (id : String) :
    Vector :=
  ⟨id, .decode (hexBytes hex) ts want⟩

def optNatT : TypeSeq := typesOf do return [← intern (.opt nat)]

def recordABT : TypeSeq := typesOf do return [← intern (recordOf [("a", nat), ("b", nat)])]

def variantABT : TypeSeq := typesOf do return [← intern (variantOf [("a", nat), ("b", null)])]

def decodeFramingChecks : List Vector :=
  [ expectDecode "4449444c 00 00" (prims []) (some []) "decode: no arguments"
  , expectDecode "4449444d 00 00" (prims []) none "decode: the magic number is DIDL"
  , expectDecode "4449444c" (prims []) none "decode: nothing after the magic number"
  , expectDecode "4449444c 00" (prims []) none "decode: no argument count"
  , expectDecode "4449444c 00 01 7d 05 00" (prims [nat]) none
      "decode: a byte after the last value"
  , expectDecode "4449444c 00 02 7d 71 05 01 78" (prims [nat, text])
      (some [.nat 5, .text "x"]) "decode: two arguments"
  , expectDecode "4449444c 00 02 7d 71 05 01 78" (prims [nat]) (some [.nat 5])
      "decode: an extra argument is ignored"
  , expectDecode "4449444c 00 02 7d 7e 05 02" (prims [nat]) none
      "decode: an extra argument is ignored, but still decoded"
  , expectDecode "4449444c 00 00" optNatT (some [.null]) "decode: a missing argument at opt is null"
  , expectDecode "4449444c 00 00" (prims [reserved]) (some [.null])
      "decode: a missing argument at reserved is null"
  , expectDecode "4449444c 00 00" (prims [nat]) none "decode: a missing argument at nat" ]

def decodeLebChecks : List Vector :=
  [ expectDecode "4449444c 00 01 7d 05" (prims [nat]) (some [.nat 5]) "decode: nat"
  , expectDecode "4449444c 00 01 7d 85 80 00" (prims [nat]) (some [.nat 5])
      "decode: nat with redundant continuation bytes"
  , expectDecode "4449444c 00 01 7d 80 80 80 80 80 80 80 80 80 02" (prims [nat])
      (some [.nat 18446744073709551616]) "decode: nat 2^64"
  , expectDecode "4449444c 00 01 7d 85" (prims [nat]) none "decode: nat runs past the end"
  , expectDecode "4449444c 00 01 7c ff 7e" (prims [int]) (some [.int (-129)]) "decode: int -129"
  , expectDecode "4449444c 00 01 7c c0 00" (prims [int]) (some [.int 64])
      "decode: int 64 takes two bytes"
  , expectDecode "4449444c 00 01 7c 40" (prims [int]) (some [.int (-64)])
      "decode: int 0x40 is -64" ]

def decodeFixedChecks : List Vector :=
  [ expectDecode "4449444c 00 01 7e 01" (prims [bool]) (some [.bool true]) "decode: bool"
  , expectDecode "4449444c 00 01 7e 02" (prims [bool]) none "decode: bool 2"
  , expectDecode "4449444c 00 01 7a 34 12" (prims [nat16]) (some [.nat16 0x1234])
      "decode: nat16 is little-endian"
  , expectDecode "4449444c 00 01 76 fe ff" (prims [int16]) (some [.int16 (-2)])
      "decode: int16 -2"
  , expectDecode "4449444c 00 01 79 01 02" (prims [nat32]) none "decode: nat32 runs past the end"
  , expectDecode "4449444c 00 01 73 00 00 80 3f" (prims [float32]) (some [.float32 0x3f800000])
      "decode: float32 1.0"
  , expectDecode "4449444c 00 01 72 01 00 00 00 00 00 f8 7f" (prims [float64])
      (some [.float64 0x7ff8000000000001]) "decode: float64 NaN keeps its payload" ]

def decodeTextChecks : List Vector :=
  [ expectDecode "4449444c 00 01 71 03 61 62 63" (prims [text]) (some [.text "abc"])
      "decode: text"
  , expectDecode "4449444c 00 01 71 02 c3 a9" (prims [text]) (some [.text "é"])
      "decode: text is UTF-8"
  , expectDecode "4449444c 00 01 71 02 c0 80" (prims [text]) none
      "decode: text with an overlong UTF-8 sequence"
  , expectDecode "4449444c 00 01 71 03 ed a0 80" (prims [text]) none
      "decode: text with a UTF-16 surrogate"
  , expectDecode "4449444c 00 01 71 05 61 62" (prims [text]) none
      "decode: text runs past the end" ]

def decodeNullChecks : List Vector :=
  [ expectDecode "4449444c 00 02 7f 7d 05" (prims [null, nat]) (some [.null, .nat 5])
      "decode: null takes no bytes"
  , expectDecode "4449444c 00 01 70" (prims [reserved]) (some [.null]) "decode: reserved"
  , expectDecode "4449444c 00 01 6f" (prims [empty]) none "decode: empty has no value"
  , expectDecode "4449444c 00 01 6f" (prims [reserved]) none
      "decode: empty has no value, even where it would be ignored"
  , expectDecode "4449444c 00 01 6f" (prims []) none
      "decode: empty has no value, even as an extra argument" ]

def decodeOptVecChecks : List Vector :=
  [ expectDecode "4449444c 01 6e 7d 01 00 01 2a" optNatT (some [.opt (.nat 42)])
      "decode: opt nat, present"
  , expectDecode "4449444c 01 6e 7d 01 00 00" optNatT (some [.null]) "decode: opt nat, absent"
  , expectDecode "4449444c 01 6e 7d 01 00 02 2a" optNatT none "decode: option tag 2"
  , expectDecode "4449444c 01 6d 7b 01 00 03 01 02 03" (typesOf do return [← intern (.vec nat8)])
      (some [.vec [.nat8 1, .nat8 2, .nat8 3]]) "decode: vec nat8"
  , expectDecode "4449444c 01 6d 7b 01 00 03 01 02" (typesOf do return [← intern (.vec nat8)])
      none "decode: vec runs past the end"
  , expectDecode "4449444c 01 6d 7f 01 00 03" (typesOf do return [← intern (.vec null)])
      (some [.vec [.null, .null, .null]]) "decode: vec null, whose elements take no bytes" ]

/-- `record { a : record {}; b : record {} }`, the two fields sharing one entry. -/
def sharedEmptyRecords : TypeSeq := typesOf do
  let e ← intern (.record [])
  return [← intern (recordOf [("a", e), ("b", e)])]

/-- `type R = record { R }`. -/
def recordLoop : TypeSeq := ⟨{ entries := #[.record [(0, .ref 0)]] }, [.ref 0]⟩

/-- `type R = record { null; R }`. -/
def recordLoopAfterNull : TypeSeq :=
  ⟨{ entries := #[.record [(0, .null), (1, .ref 0)]] }, [.ref 0]⟩

def decodeRecordChecks : List Vector :=
  [ expectDecode "4449444c 01 6c 02 61 7d 62 7d 01 00 01 02" recordABT
      (some [recordVal [("a", .nat 1), ("b", .nat 2)]]) "decode: record { a; b }"
  , expectDecode "4449444c 01 6c 02 62 7d 61 7d 01 00 02 01" recordABT none
      "decode: record fields out of order"
  , expectDecode "4449444c 01 6c 02 61 7d 61 7d 01 00 01 02" recordABT none
      "decode: record field repeated"
  , expectDecode "4449444c 01 6c 01 80 80 80 80 10 7d 01 00 07"
      (typesOf do return [← intern (.record [])]) none
      "decode: field id 2^32 does not fit"
  , expectDecode "4449444c 01 6c 01 ff ff ff ff 0f 7d 01 00 07"
      (typesOf do return [← intern (.record [(0xffffffff, nat)])])
      (some [.record [(0xffffffff, .nat 7)]]) "decode: field id 2^32 - 1 fits"
  , expectDecode "4449444c 01 6c 01 61 71 01 00 02 c0 80"
      (typesOf do return [← intern (.record [])]) none
      "decode: a field the receiver ignores is still decoded"
  , expectDecode "4449444c 02 6c 02 61 01 62 01 6c 00 01 00" sharedEmptyRecords
      (some [recordVal [("a", .record []), ("b", .record [])]])
      "decode: one record entry twice at one position is not a cycle"
  , expectDecode "4449444c 01 6c 01 00 00 01 00" recordLoop none
      "decode: type R = record { R } has no value"
  , expectDecode "4449444c 01 6c 02 00 7f 01 00 01 00" recordLoopAfterNull none
      "decode: type R = record { null; R } has no value" ]

def decodeVariantChecks : List Vector :=
  [ expectDecode "4449444c 01 6b 02 61 7d 62 7f 01 00 01" variantABT
      (some [variantVal "b" .null]) "decode: variant index is the place in id order"
  , expectDecode "4449444c 01 6b 02 61 7d 62 7f 01 00 02" variantABT none
      "decode: variant index past the last alternative"
  , expectDecode "4449444c 01 6b 02 62 7f 61 7d 01 00 00" variantABT none
      "decode: variant alternatives out of order" ]

/-- `n` copies of `opt nat`, as table entries. -/
def optNatEntries (n : Nat) : String := String.join (List.replicate n "6e7d ")

def decodeTableChecks : List Vector :=
  [ expectDecode "4449444c 01 7d 00" (prims []) none "decode: a primitive in the type table"
  , expectDecode "4449444c 00 01 00" (prims []) none "decode: an index past the type table"
  , expectDecode "4449444c 00 01 6e" (prims []) none
      "decode: a composite opcode as an argument type"
  , expectDecode "4449444c 02 6e 7d 6d 7e 01 7d 05" (prims [nat]) (some [.nat 5])
      "decode: unused table entries are allowed"
  , expectDecode "4449444c 01 6e 05 01 7d 05" (prims [nat]) none
      "decode: an unused table entry must still resolve"
  , expectDecode s!"4449444c 41 {optNatEntries 65} 01 c0 00 00" optNatT (some [.null])
      "decode: table index 64 is SLEB128"
  , expectDecode s!"4449444c 41 {optNatEntries 65} 01 40 00" optNatT none
      "decode: table index 64 written as LEB128 is opcode -64"
  , expectDecode "4449444c 01 6a 00 00 01 04 00" (prims []) none
      "decode: unknown function annotation"
  , expectDecode "4449444c 01 6a 00 00 02 01 02 00" (prims []) (some [])
      "decode: a function type with two annotations"
  , expectDecode "4449444c 01 6a 00 01 7d 01 02 00" (prims []) none
      "decode: oneway function with a result"
  , expectDecode "4449444c 01 69 01 01 6d 7d 00" (prims []) none
      "decode: a method that is not a function"
  , expectDecode "4449444c 02 6a 00 00 00 69 02 01 6e 00 01 6d 00 00" (prims []) none
      "decode: methods out of order"
  , expectDecode "4449444c 02 6a 00 00 00 69 01 01 ff 00 00" (prims []) none
      "decode: a method name that is not UTF-8" ]

def decodeRefChecks : List Vector :=
  let funcT := typesOf do return [← intern (.func [] [] [])]
  [ expectDecode "4449444c 00 01 68 01 01 2a" (prims [principal]) (some [.principal [0x2a]])
      "decode: principal"
  , expectDecode "4449444c 00 01 68 00" (prims [principal]) none
      "decode: opaque principal reference"
  , expectDecode "4449444c 00 01 68 02 01 2a" (prims [principal]) none
      "decode: principal reference flag 2"
  , expectDecode s!"4449444c 00 01 68 01 1e {String.join (List.replicate 30 "00")}"
      (prims [principal]) (some [.principal (List.replicate 30 0)])
      "decode: a principal of 30 bytes"
  , expectDecode "4449444c 01 69 00 01 00 01 01 2a" (typesOf do return [← intern (.service [])])
      (some [.service [0x2a]]) "decode: service reference"
  , expectDecode "4449444c 01 6a 00 00 00 01 00 01 01 01 2a 01 6d" funcT
      (some [.func [0x2a] "m"]) "decode: func reference"
  , expectDecode "4449444c 01 6a 00 00 00 01 00 00" funcT none
      "decode: opaque func reference" ]

def decodeCoerceChecks : List Vector :=
  [ expectDecode "4449444c 00 01 7d 05" (prims [int]) (some [.int 5])
      "decode: then coerce, nat at int"
  , expectDecode "4449444c 00 01 7d 05" (prims [text]) none
      "decode: an argument that does not coerce rejects the message"
  , expectDecode "4449444c 00 01 7d 05" (typesOf do return [← intern (.opt text)]) (some [.null])
      "decode: an argument that does not coerce at opt is null" ]

/-- Future types: opcode `-25` (`67`), the first the spec leaves to the future. The
table entry is the opcode, a length and that many bytes; a value is two lengths, `m`
and `n`, then `m` bytes. -/
def decodeFutureChecks : List Vector :=
  [ expectDecode "4449444c 01 67 00 01 00 00 00" (prims [reserved]) (some [.null])
      "decode: a future value at reserved"
  , expectDecode "4449444c 01 67 00 01 00 00 00" optNatT (some [.null])
      "decode: a future value at an option is null"
  , expectDecode "4449444c 01 67 00 01 00 00 00" (prims [nat]) none
      "decode: a future value at nat"
  , expectDecode "4449444c 01 67 00 01 00 00 00" (prims []) (some [])
      "decode: a future value as an extra argument"
  , expectDecode "4449444c 01 67 03 41 42 43 01 00 02 00 68 69" (prims [reserved])
      (some [.null]) "decode: a future type's bytes and a future value's bytes are skipped"
  , expectDecode "4449444c 01 67 00 01 00 00 03" (prims [reserved]) (some [.null])
      "decode: a future value's reference count is ignored"
  , expectDecode "4449444c 01 67 00 01 00 05 00 68" (prims [reserved]) none
      "decode: a future value runs past the end"
  , expectDecode "4449444c 01 67 05 41 42" (prims []) none
      "decode: a future type runs past the end"
  , expectDecode "4449444c 00 01 67 00 00" (prims []) none
      "decode: a future type is not a primitive, so it is not an argument type" ]

def decodeChecks : List Vector :=
  decodeFramingChecks ++ decodeLebChecks ++ decodeFixedChecks ++ decodeTextChecks ++
  decodeNullChecks ++ decodeOptVecChecks ++ decodeRecordChecks ++ decodeVariantChecks ++
  decodeTableChecks ++ decodeRefChecks ++ decodeCoerceChecks ++ decodeFutureChecks

def handwritten : List Vector :=
  hashChecks ++ primChecks ++ optChecks ++ vecChecks ++ recordChecks ++
  variantChecks ++ funcChecks ++ serviceChecks ++ wellFormedChecks ++
  recursiveChecks ++ vecOmegaChecks ++ contraChecks ++ sharedChecks ++ leakChecks ++
  transitivityChecks ++ coerceChecks ++ decodeChecks

end Oracle
