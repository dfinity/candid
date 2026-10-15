/-
The Candid type language, represented finitely -- and flatly.

`coq/MiniCandid.v` models types as a `CoInductive T` -- infinite type trees, with
recursion needing no constructor. Lean 4 accepts `coinductive` only for predicates,
and this model takes no mathlib dependency, so that representation is unavailable. It
would also be the wrong one: it cannot be executed, and it is unlike every
implementation.

Instead recursion is explicit, through a type table -- which is what the binary
format calls it (`spec/Candid.md`: "type definition table") and what `candid_types`
is specified to do with arena indices.

**Nothing here is recursive except the table.** A table entry is a `Composite`; its
children are `Slot`s; and a `Slot` is a primitive or an index -- never an inline
composite. That is the wire format's own shape, not an invention of this model
(`spec/Candid.md:1208`):

```
I : <datatype> -> i8*
I(<primtype>) = T(<primtype>)
I(<comptype>) = sleb128(i)  where type definition i defines T(<datatype>)
```

and the spec draws the conclusion this model is built on: "Because recursion goes
through `T`, this format by construction rules out non-well-founded definitions like
`type t = t`" (`spec/Candid.md:1225`). Two things follow.

- The rule that "the type table may only contain composite types (no `<primtype>`)"
  (`spec/Candid.md:1227`) is a property of the representation rather than a
  well-formedness check. A decoder still has to reject a primitive opcode in an entry
  position; nothing downstream has to re-check it.
- Every recursive call in the subtype procedure passes through a slot pair, so a pair
  of *references* is the only way to recurse -- and the finite set of reference pairs
  bounds the recursion. See `Subtype.lean`.

The price is that a type means nothing without its table, and even `vec nat` needs an
entry. `intern`/`close` below build tables for hand-written types. The surface `.did`
syntax is nested, so the parser will produce a nested AST and flatten it here; that
flattening is also what an encoder does, so it is a component this model needs rather
than a translation it pays for.

On the name: the implementation in `rust/` calls this a `TypeEnv`, but that `TypeEnv`
is a `BTreeMap<String, Type>` (`rust/candid/src/types/type_env.rs:7`) -- a *name*-keyed
environment of `.did` type declarations, which is a different structure from this
index-keyed table. Both will exist here eventually, so `TypeEnv` is reserved for the
one where "environment" is the accurate word.
-/

import Candid.Hash

namespace Candid

/-- Index into a `TypeTable`. -/
abbrev TypeRef := Nat

/-- `<primtype>`, per the grammar at `spec/Candid.md:80` -- which includes
`principal`. Only `func` and `service` are `<reftype>`s. -/
inductive Prim where
  | null | bool | nat | int
  | nat8 | nat16 | nat32 | nat64
  | int8 | int16 | int32 | int64
  | float32 | float64
  | text | reserved | empty
  | principal
  deriving DecidableEq, Repr, Inhabited

/-- `<funcann>`. Annotations are part of a function's type, not decoration. -/
inductive FuncAnnot where
  | query | oneway | compositeQuery
  deriving DecidableEq, Repr

/-- A `<datatype>` in the position where the wire format writes `I`: a primitive, or
an index into the accompanying `TypeTable`.

This is a leaf. Composites live in the table and only in the table, so the whole
type graph is the table -- which is what bounds every recursion over types. -/
inductive Slot where
  | prim (p : Prim)
  | ref (target : TypeRef)
  deriving DecidableEq, Repr, Inhabited

/-- A `<comptype>`: what a table entry is.

Not a recursive type. Its children are `Slot`s, so a composite is one flat node. -/
inductive Composite where
  | opt (inner : Slot)
  | vec (inner : Slot)
  | record (fields : List (FieldId × Slot))
  | variant (alts : List (FieldId × Slot))
  | func (args rets : List Slot) (annots : List FuncAnnot)
  | service (methods : List (String × Slot))
  deriving Repr, Inhabited

/-- A type table as it is parsed or built: `TypeRef` -> `Composite`, not yet checked.
Nothing but `RawTypeTable.check` should consume one; see `TypeTable`. -/
structure RawTypeTable where
  entries : Array Composite
  deriving Repr, Inhabited

namespace RawTypeTable

def size (t : RawTypeTable) : Nat := t.entries.size

def lookup? (t : RawTypeTable) (r : TypeRef) : Option Composite := t.entries[r]?

/-- The empty table, for types that contain no references. -/
def empty : RawTypeTable := { entries := #[] }

end RawTypeTable

/-- No duplicates, by `BEq`. Used for field ids and for method names. -/
def noDups [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDups xs

/-! ## Well-formedness

Checked once per table, by `RawTypeTable.check`, and nowhere after. Nothing recursive
is left to check. A slot's reference must resolve, and no record,
variant or service may repeat a label -- the spec is explicit that a hash collision
between field names in one record is *disallowed* rather than resolved, so duplicate
ids make a type malformed rather than ambiguous.

Two further rules are not structural: a `oneway` function may not have results, and a
service's method type must denote a function. The second is the only rule here that
has to look through the table, since a method's type is a slot like any other.

Function arity is bounded too: "The list of parameters must be shorter than 2^32
values; the same restriction apply to the result list" (`spec/Candid.md:209`).
Nothing that fits in memory violates it, but a theorem quantifies over every list:
`indexedFrom` labels positional arguments with `UInt32`, which wraps, so it is this
bound that keeps the labels of a function's arguments distinct. -/

/-- Does this slot's reference resolve below `bound`? -/
def Slot.wellFormed (bound : Nat) : Slot → Bool
  | .prim _ => true
  | .ref r => r < bound

/-- The slots a composite holds, in no particular order: what has to resolve. -/
def Composite.slots : Composite → List Slot
  | .opt t | .vec t => [t]
  | .record fs | .variant fs => fs.map (·.2)
  | .func args rets _ => args ++ rets
  | .service ms => ms.map (·.2)

/-- Labels must not repeat. Vacuous for the unlabelled composites. -/
def Composite.labelsOk : Composite → Bool
  | .record fs | .variant fs => noDups (fs.map (·.1))
  | .service ms => noDups (ms.map (·.1))
  | .opt _ | .vec _ | .func _ _ _ => true

/-- `spec/Candid.md:211`: "The result list of a `oneway` function must be empty." -/
def Composite.annotsOk : Composite → Bool
  | .func _ rets ann => !ann.contains .oneway || rets.isEmpty
  | .opt _ | .vec _ | .record _ | .variant _ | .service _ => true

/-- `spec/Candid.md:209`: parameter and result lists are shorter than 2^32. -/
def Composite.arityOk : Composite → Bool
  | .func args rets _ => args.length < UInt32.size && rets.length < UInt32.size
  | .opt _ | .vec _ | .record _ | .variant _ | .service _ => true

def Composite.wellFormed (bound : Nat) (c : Composite) : Bool :=
  c.labelsOk && c.annotsOk && c.arityOk && c.slots.all (Slot.wellFormed bound)

/-- `spec/Candid.md:1223`: "The serialised data type representing a method type must
denote a function type." -/
def RawTypeTable.methodsDenoteFuncs (t : RawTypeTable) : Composite → Bool
  | .service ms => ms.all fun (_, s) =>
      match s with
      | .ref r => match t.lookup? r with
        | some (.func _ _ _) => true
        | _ => false
      | .prim _ => false
  | .opt _ | .vec _ | .record _ | .variant _ | .func _ _ _ => true

def RawTypeTable.wellFormed (t : RawTypeTable) : Bool :=
  t.entries.all fun c => c.wellFormed t.size && t.methodsDenoteFuncs c

/-! ## The validated table

Well-formedness is a prerequisite of everything downstream -- subtyping, decoding,
encoding -- so it is a property of the type, not a check each operation repeats on the
parts it happens to reach. An operation that re-checks only what it visits fails
closed for some malformed inputs and not others: a dangling reference *at* a root is
caught, one *behind* a root that the operation answers without unfolding is not.

`TypeTable` is the short name because it is the one APIs take. A decoder or a builder
produces a `RawTypeTable` and checks it once; from then on every reference inside the
table resolves. -/

/-- A well-formed type table. Every value carries the proof, so none is malformed;
`RawTypeTable.check` is how one is obtained at run time. -/
structure TypeTable where
  raw : RawTypeTable
  wf : raw.wellFormed = true

def RawTypeTable.check (t : RawTypeTable) : Option TypeTable :=
  if h : t.wellFormed then some ⟨t, h⟩ else none

namespace TypeTable

def size (t : TypeTable) : Nat := t.raw.size

def lookup? (t : TypeTable) (r : TypeRef) : Option Composite := t.raw.lookup? r

/-- Is this slot a type in this table at all? A primitive always is; a reference is
one exactly when it resolves. -/
def resolves (t : TypeTable) : Slot → Bool
  | .prim _ => true
  | .ref r => (t.lookup? r).isSome

/-- A slot known to resolve in `t`: a type, given its table.

A well-formed table says nothing about a slot handed in beside it, so a root is
checked on its own -- one bounds check. The table is in the *type*, not stored
alongside: one table has many roots (a message's arguments, a service's methods), and
a slot of `A` cannot be passed where a slot of `B` is expected. That is what the
two-table subtype procedure needs most, since the case that matters is a table that
arrived on the wire against the receiver's own, and mixing them up is invisible when
both are the same table.

Rust has no dependent types; its counterpart is a view borrowing its table. -/
abbrev Root (t : TypeTable) := {s : Slot // t.resolves s = true}

def root? (t : TypeTable) (s : Slot) : Option t.Root :=
  if h : t.resolves s then some ⟨s, h⟩ else none

end TypeTable

/-! ## Building tables

A hand-written type has to have its composites interned, since only the table can
hold them. This is the same interning an encoder does when it emits a type table. -/

/-- Table construction: append entries, taking back the slot that names each. -/
abbrev TableM := StateM (Array Composite)

/-- Add an entry, and return the slot that names it. -/
def intern (c : Composite) : TableM Slot := do
  let entries ← get
  set (entries.push c)
  return .ref entries.size

/-- Run a construction into the table it built and the slot it returned. The table is
raw: building one does not check it. -/
def close (m : TableM Slot) : RawTypeTable × Slot :=
  let (root, entries) := m.run #[]
  ({ entries := entries }, root)

/-- The common case: one entry, named by the root. -/
def closeOne (c : Composite) : RawTypeTable × Slot := close (intern c)

/-! Abbreviations for the primitives, so examples read like Candid rather than
like an AST. -/

namespace Slot

def null : Slot := .prim .null
def bool : Slot := .prim .bool
def nat : Slot := .prim .nat
def int : Slot := .prim .int
def nat8 : Slot := .prim .nat8
def nat16 : Slot := .prim .nat16
def nat32 : Slot := .prim .nat32
def nat64 : Slot := .prim .nat64
def int8 : Slot := .prim .int8
def int16 : Slot := .prim .int16
def int32 : Slot := .prim .int32
def int64 : Slot := .prim .int64
def float32 : Slot := .prim .float32
def float64 : Slot := .prim .float64
def text : Slot := .prim .text
def reserved : Slot := .prim .reserved
def empty : Slot := .prim .empty
def principal : Slot := .prim .principal

end Slot

namespace Composite

/-- A record from named fields, hashing the names. -/
def recordOf (fs : List (String × Slot)) : Composite :=
  .record (fs.map fun (n, t) => (hashFieldName n, t))

/-- A variant from named alternatives, hashing the names. -/
def variantOf (fs : List (String × Slot)) : Composite :=
  .variant (fs.map fun (n, t) => (hashFieldName n, t))

end Composite

end Candid
