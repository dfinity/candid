/-
Candid subtyping, as a decision procedure over two independent type tables.

Rules are from `spec/Candid.md`, "Upgrading and Subtyping". Three things shape
everything here: two from that section, and one from how types are represented.

**The negative premises are eliminable.** The spec states four rules for `opt`, two
of them with negative premises:

```
    <t> <: <t'>                     not (<t> <: <t'>)
------------------------      ---------------------------
opt <t> <: opt <t'>              opt <t> <: opt <t'>
```

Together those two say `opt t <: opt t'` unconditionally. The same pairing on the
other two rules says `t <: opt t'` whenever `not (null <: t)`, and the remaining
cases (`t` is `null`, `reserved`, or an `opt`) are covered by their own rules. So
**`t <: opt t'` holds for every `t` and `t'`** -- which the spec itself notes at the
top of those rules ("allow, in fact, *any* type to be regarded as a subtype of an
option"), and which `rust/candid/src/types/subtype.rs:293` implements as a catch-all
that only warns.

That collapse is what makes this relation definable as a greatest fixed point at
all: negative premises are non-monotone, so the rule functional would have no gfp.
Restating them as one premise-free rule keeps the relation monotone.

**Two tables, not one.** A `Slot` holding a `ref` is meaningless without its table,
and the case that matters most compares a type table that arrived on the wire against
the receiver's own type graph -- two unrelated tables. The current Rust signature
takes a single `env` for both types (`rust/candid/src/types/subtype.rs:19`), which
works only because callers merge tables first.

**The table bounds the recursion.** A composite's children are slots, and composites
live only in the table (`Types.lean`), so the only way to recurse is through a
pair of *references*: every other slot pair is decided outright. The procedure
therefore carries `todo`, the reference pairs it has not yet assumed, and descending
through a pair removes it. `todo.length` is the termination measure, and the
membership test that decides the branch is exactly the fact that measure needs -- so
the obligation is discharged where the decision is made, and no invariant has to be
threaded through the recursion.

`todo` is the coinductive hypothesis, carried as a complement: a pair this path has
already descended through is one the greatest fixed point lets us assume. Seeding it
costs `|A| x |B|` pairs, and an implementation that carries the assumptions
themselves rather than what is left is bounded by the same count.
-/

import Candid.Types

namespace Candid

/-- Is this slot a type in this table at all? A primitive always is; a reference is
one exactly when it resolves. -/
def TypeTable.resolves (t : TypeTable) : Slot → Bool
  | .prim _ => true
  | .ref r => (t.lookup? r).isSome

/-- `null <: t`, decided syntactically.

The spec's premise `not (null <: <datatype>)` is only ever applied to a concrete
type, and `null` is a subtype of exactly `null`, `reserved`, and any `opt` -- so this
needs no recursion, just one step through the table. -/
def TypeTable.acceptsNull (t : TypeTable) : Slot → Bool
  | .prim .null | .prim .reserved => true
  | .prim _ => false
  | .ref r => match t.lookup? r with
    | some (.opt _) => true
    | _ => false

/-- Label a positional list the way the spec's function rule does: "`NI*` is the
`<nat>` sequence `1`..`|<datatypeNI>*|`". -/
def indexedFrom (i : Nat) : List Slot → List (FieldId × Slot)
  | [] => []
  | t :: ts => (UInt32.ofNat i, t) :: indexedFrom (i + 1) ts

/-- Function annotations must be equal *as sets*, per the spec. -/
def annotsAgree (xs ys : List FuncAnnot) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

/-- Look up a label. -/
def fieldAt (fs : List (FieldId × Slot)) (id : FieldId) : Option Slot :=
  (fs.find? (·.1 == id)).map (·.2)

/-- Look up a method. -/
def methodAt (ms : List (String × Slot)) (name : String) : Option Slot :=
  (ms.find? (·.1 == name)).map (·.2)

/-- Every reference pair of two tables: what `decSubtype` starts out permitted to
assume. -/
def allPairs (A B : TypeTable) : List (TypeRef × TypeRef) :=
  (List.range A.size).flatMap fun i => (List.range B.size).map fun j => (i, j)

/-! ## The procedure

`sub A B todo a b` decides `a <: b`, where `a`'s references resolve in `A` and `b`'s
in `B`, and `todo` holds the reference pairs not yet assumed. `subC` is the same
question one step in, on the composites that two references name, and `subLabels` is
the record rule, which the function rule reuses on its positional arguments and
results.

The measures below are lexicographic on (`todo.length`, phase), where the phase
orders the three so that a step which does not shrink `todo` still descends:
`subC` (2) may call `subLabels` (1), which may call `sub` (0), which shrinks `todo`
before calling `subC` again. -/
mutual

def sub (A B : TypeTable) (todo : List (TypeRef × TypeRef)) : Slot → Slot → Bool
  -- `<datatype> <: reserved` and `empty <: <datatype>`: the top and bottom types.
  -- Each checks that the *other* side is a type at all. A dangling reference is not
  -- one, and granting a subtype relation without looking is the dangerous direction
  -- for a compatibility gate.
  | a, .prim .reserved => A.resolves a
  | .prim .empty, b => B.resolves b

  -- `<primtype> <: <primtype>`, plus `nat <: int`. `principal` is a primitive
  -- (spec/Candid.md:80), so `principal <: principal` needs no rule of its own.
  | .prim p, .prim q => p == q || (p == .nat && q == .int)

  -- A primitive against a composite: only the `opt` rule can apply, since `empty`
  -- and `reserved` are decided above.
  | .prim _, .ref j =>
    match B.lookup? j with
    | some (.opt _) => true
    | _ => false

  -- A composite against a primitive: only `service <actortype> <: principal`.
  | .ref i, .prim q =>
    match q, A.lookup? i with
    | .principal, some (.service _) => true
    | _, _ => false

  -- Two references: the only recursive case, and the only place `todo` shrinks. A
  -- pair no longer in `todo` is one this path has already descended through, so the
  -- coinductive hypothesis discharges it. A pair that was never in `todo` is out of
  -- range, and the lookups catch that first.
  | .ref i, .ref j =>
    match A.lookup? i, B.lookup? j with
    | some x, some y =>
      -- `_hp` is underscored because the value ignores it and the termination proof
      -- below does not: it is the whole argument that this recursion stops.
      if _hp : (i, j) ∈ todo then subC A B (todo.erase (i, j)) x y else true
    | _, _ => false                   -- dangling: not well formed
termination_by (todo.length, 0)
decreasing_by
  exact Prod.Lex.left _ _ (by
    rw [List.length_erase_of_mem _hp]
    exact Nat.sub_lt (List.length_pos_of_mem _hp) Nat.one_pos)

/-- The rules on the composites that a pair of references names. -/
def subC (A B : TypeTable) (todo : List (TypeRef × TypeRef)) : Composite → Composite → Bool
  -- Any type is a subtype of an option. See the header: this single rule is the
  -- spec's four `opt` rules with their negative premises eliminated.
  | _, .opt _ => true

  | .vec x, .vec y => sub A B todo x y

  -- A record may specialise a field's type or add a field. It may also *omit* a
  -- field the supertype has, provided that field accepts `null`.
  | .record fs, .record gs => subLabels A B todo fs gs

  -- A variant may specialise a tag's type or drop a tag. Every tag it does carry
  -- must exist in the supertype.
  | .variant fs, .variant gs =>
    fs.all fun (id, f) =>
      match fieldAt gs id with
      | some g => sub A B todo f g
      | none => false

  -- Parameters generalise, results specialise, and both behave like tuple-shaped
  -- records -- so arguments may be dropped and results added.
  --
  -- The parameter premise swaps the tables, so it swaps `todo` with them: a pair
  -- `(i, j)` is about `A`'s `i` and `B`'s `j`, and reading it unswapped would assert
  -- something about the transposed pair -- a different, and generally false, question.
  | .func args rets ann, .func args' rets' ann' =>
    annotsAgree ann ann'
      && subLabels B A (todo.map Prod.swap) (indexedFrom 1 args') (indexedFrom 1 args)
      && subLabels A B todo (indexedFrom 1 rets) (indexedFrom 1 rets')

  -- Services are records of functions: a method may be specialised or added.
  | .service ms, .service ms' =>
    ms'.all fun (name, g) =>
      match methodAt ms name with
      | some f => sub A B todo f g
      | none => false

  | _, _ => false
termination_by (todo.length, 2)
decreasing_by
  -- The parameter premise hands on a swapped `todo`, which is the same length.
  all_goals (try simp only [List.length_map])
  all_goals exact Prod.Lex.right _ (by omega)

/-- The record rule: every label the supertype declares is either specialised by the
subtype or omitted, and omitting it requires that it accept `null`. -/
def subLabels (A B : TypeTable) (todo : List (TypeRef × TypeRef))
    (fs gs : List (FieldId × Slot)) : Bool :=
  gs.all fun (id, g) =>
    match fieldAt fs id with
    | some f => sub A B todo f g
    | none => B.acceptsNull g
termination_by (todo.length, 1)
decreasing_by exact Prod.Lex.right _ (by omega)

end

/-- Decide `a <: b` for two types carrying their own tables. Total: along any path a
reference pair may be assumed at most once, and there are finitely many. -/
def decSubtype (a b : ClosedType) : Bool :=
  sub a.table b.table (allPairs a.table b.table) a.root b.root

/- Note the argument order flip in the `func` case above: parameters are
contravariant, so the tables swap with the types -- and `todo` swaps with the tables.
Getting either wrong is invisible when both types share one table, which is the
second reason the two-table signature is worth the extra parameter. -/

end Candid
