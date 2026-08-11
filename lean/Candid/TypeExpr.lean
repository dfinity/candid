/-
The Candid type language, represented finitely.

`coq/MiniCandid.v` models types as a `CoInductive T` -- infinite type trees, with
recursion needing no constructor. Lean 4 accepts `coinductive` only for predicates,
and this model takes no mathlib dependency, so that representation is unavailable. It
would also be the wrong one: it cannot be executed, and it is unlike every
implementation.

Instead recursion is explicit, through a `TypeTable` -- which is what the binary
format calls it (`spec/Candid.md`: "type definition table") and what `candid_types`
is specified to do with arena indices.

On the name: the old implementation calls this a `TypeEnv`, but its `TypeEnv` is a
`BTreeMap<String, Type>` (`rust/candid/src/types/type_env.rs:7`) -- a *name*-keyed
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

/-- A Candid type, possibly containing references into an accompanying `TypeTable`. -/
inductive TypeExpr where
  | prim (p : Prim)
  | opt (inner : TypeExpr)
  | vec (inner : TypeExpr)
  | record (fields : List (FieldId × TypeExpr))
  | variant (alts : List (FieldId × TypeExpr))
  | func (args rets : List TypeExpr) (annots : List FuncAnnot)
  | service (methods : List (String × TypeExpr))
  | ref (target : TypeRef)
  deriving Repr, Inhabited

/-- A type table: `TypeRef` -> `TypeExpr`. -/
structure TypeTable where
  entries : Array TypeExpr
  deriving Repr, Inhabited

namespace TypeTable

def size (t : TypeTable) : Nat := t.entries.size

def lookup? (t : TypeTable) (r : TypeRef) : Option TypeExpr := t.entries[r]?

/-- The empty table, for types that contain no references. -/
def empty : TypeTable := { entries := #[] }

end TypeTable

def TypeExpr.isRef : TypeExpr → Bool
  | .ref _ => true
  | _ => false

/-- Is this a `<comptype>`, i.e. a `<constype>` or a `<reftype>`?

`spec/Candid.md:1227` -- "The type table may only contain composite types (no
`<primtype>`)". So this is exactly what may appear as a table entry, and it excludes
both primitives and bare references. -/
def TypeExpr.isComposite : TypeExpr → Bool
  | .opt _ | .vec _ | .record _ | .variant _ | .func _ _ _ | .service _ => true
  | .prim _ | .ref _ => false

/-- No duplicates, by `BEq`. Used for field ids and for method names. -/
def noDups [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDups xs

/- Well-formedness of a type expression against a table of `bound` entries:
every reference resolves, and no record, variant or service repeats a label.

The spec is explicit that a hash collision between field names in one record is
*disallowed* rather than resolved, so duplicate ids make a type malformed rather
than ambiguous. -/
mutual

/-- Every reference resolves below `bound`, and no label is repeated. -/
def TypeExpr.wellFormed (bound : Nat) : TypeExpr → Bool
  | .prim _ => true
  | .ref r => r < bound
  | .opt t | .vec t => t.wellFormed bound
  | .record fs | .variant fs => noDups (fs.map (·.1)) && TypeExpr.wfFields bound fs
  | .func args rets _ => TypeExpr.wfList bound args && TypeExpr.wfList bound rets
  | .service ms => noDups (ms.map (·.1)) && TypeExpr.wfMethods bound ms

def TypeExpr.wfList (bound : Nat) : List TypeExpr → Bool
  | [] => true
  | t :: ts => t.wellFormed bound && TypeExpr.wfList bound ts

def TypeExpr.wfFields (bound : Nat) : List (FieldId × TypeExpr) → Bool
  | [] => true
  | (_, t) :: fs => t.wellFormed bound && TypeExpr.wfFields bound fs

def TypeExpr.wfMethods (bound : Nat) : List (String × TypeExpr) → Bool
  | [] => true
  | (_, t) :: ms => t.wellFormed bound && TypeExpr.wfMethods bound ms

end

/-- A table is well formed when every entry is well formed **and composite**.

The second condition is the spec's own (`spec/Candid.md:1227`), and it is load-bearing
here: since no entry is a primitive or a bare reference, following a reference is a
single step, which is what bounds the subtype recursion. Textual `.did` aliases
(`type A = B;`) must therefore be resolved before they reach this model. -/
def TypeTable.wellFormed (t : TypeTable) : Bool :=
  t.entries.all fun e => e.wellFormed t.size && e.isComposite

/-- Follow at most one reference. Returns `none` on a dangling index.

In a well-formed table the result is never itself a `ref`. That is not yet expressed
in the type, so `Subtype.lean` bounds unfolding explicitly instead of relying on it. -/
def TypeTable.resolve (t : TypeTable) (e : TypeExpr) : Option TypeExpr :=
  match e with
  | .ref r => t.lookup? r
  | _ => some e

/-- A type together with the table its references resolve in.

This is the unit the public API speaks in, because a `TypeExpr` containing a `ref`
means nothing without its table. The first draft of `decSubtype` took one table and
two `TypeExpr`s, which silently assumed both types came from the same table -- false
in the case that matters most, where a type table that arrived on the wire is compared
against the receiver's own type graph. -/
structure ClosedType where
  table : TypeTable
  root : TypeExpr
  deriving Repr, Inhabited

namespace ClosedType

def wellFormed (c : ClosedType) : Bool :=
  c.table.wellFormed && c.root.wellFormed c.table.size

/-- A type containing no references. -/
def ofExpr (e : TypeExpr) : ClosedType := { table := .empty, root := e }

end ClosedType

/-! Abbreviations for the primitives, so examples read like Candid rather than
like an AST. -/

namespace TypeExpr

def null : TypeExpr := .prim .null
def bool : TypeExpr := .prim .bool
def nat : TypeExpr := .prim .nat
def int : TypeExpr := .prim .int
def nat8 : TypeExpr := .prim .nat8
def nat16 : TypeExpr := .prim .nat16
def nat32 : TypeExpr := .prim .nat32
def nat64 : TypeExpr := .prim .nat64
def int8 : TypeExpr := .prim .int8
def int16 : TypeExpr := .prim .int16
def int32 : TypeExpr := .prim .int32
def int64 : TypeExpr := .prim .int64
def float32 : TypeExpr := .prim .float32
def float64 : TypeExpr := .prim .float64
def text : TypeExpr := .prim .text
def reserved : TypeExpr := .prim .reserved
def empty : TypeExpr := .prim .empty
def principal : TypeExpr := .prim .principal

/-- A record from named fields, hashing the names. -/
def recordOf (fs : List (String × TypeExpr)) : TypeExpr :=
  .record (fs.map fun (n, t) => (hashFieldName n, t))

/-- A variant from named alternatives, hashing the names. -/
def variantOf (fs : List (String × TypeExpr)) : TypeExpr :=
  .variant (fs.map fun (n, t) => (hashFieldName n, t))

end TypeExpr

end Candid
