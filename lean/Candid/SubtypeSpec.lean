/-
Subtyping as a relation, mirroring `spec/Candid.md` rule for rule.

`Subtype.lean` holds the decision procedure; this file holds what it is supposed to
decide. Keeping them apart is the point: the relation is the specification, the
procedure is the implementation, and the theorem connecting them is the obligation
that keeps them honest. `coq/MiniCandid.v` has only the relation, which is why it
cannot be a test oracle.

The relation is a **greatest** fixed point. Recursive types are infinite when
unfolded, so `record { next : S } <: record { next : S }` must hold by consistency
rather than by a finite derivation -- exactly why MiniCandid declares
`CoInductive Subtype`. Lean 4.32 supports coinductive *predicates* (not coinductive
data types, which is why types are finite with explicit references), so the same
construction is available here.

That is only possible because the negative premises in the spec's `opt` rules are
eliminable -- see the header of `Subtype.lean`. A rule functional with negative
premises is non-monotone and has no greatest fixed point, so `toOpt` below stands in
for all four of the spec's `opt` rules.

Two predicates, because there are two syntactic categories: `Subty` relates `Slot`s
and `SubtyC` relates the `Composite`s that a pair of references names. The split is
not bureaucracy -- it is where the model's finiteness lives, since `SubtyC` can only
be reached through `unfold`, one reference pair at a time.

The type tables are *indices* rather than parameters because the `func` rule swaps
them: parameter subtyping is contravariant.
-/

import Candid.Subtype

namespace Candid

mutual

coinductive Subty : TypeTable → TypeTable → Slot → Slot → Prop where
  /-- `<primtype> <: <primtype>` -/
  | prim {A B p} : Subty A B (.prim p) (.prim p)
  /-- `nat <: int` -/
  | natInt {A B} : Subty A B (.prim .nat) (.prim .int)
  /-- `<datatype> <: reserved` -/
  | toReserved {A B a} : Subty A B a (.prim .reserved)
  /-- `empty <: <datatype>` -/
  | fromEmpty {A B b} : Subty A B (.prim .empty) b
  /-- `service <actortype> <: principal`. `principal` is a `<primtype>`
  (`spec/Candid.md:80`), so `principal <: principal` follows from `prim`. -/
  | serviceToPrincipal {A B i ms} :
      A.lookup? i = some (.service ms) → Subty A B (.ref i) (.prim .principal)
  /-- All four `opt` rules of the spec, collapsed: any type is a subtype of any
  option, and a receiver that cannot decode the value sees `null`. Stated at both
  levels because an option is reachable either as the right slot of any pair (here)
  or as the right composite of a reference pair (`SubtyC.toOpt`). -/
  | toOpt {A B a j y} : B.lookup? j = some (.opt y) → Subty A B a (.ref j)
  /-- References are transparent: two of them are related through their entries.
  This is the only rule that reaches `SubtyC`, and the only one that consumes a
  reference pair -- which is what makes the procedure's `todo` a measure. -/
  | unfold {A B i j x y} :
      A.lookup? i = some x → B.lookup? j = some y → SubtyC A B x y →
      Subty A B (.ref i) (.ref j)

coinductive SubtyC : TypeTable → TypeTable → Composite → Composite → Prop where
  /-- See `Subty.toOpt`. -/
  | toOpt {A B x y} : SubtyC A B x (.opt y)
  /-- `vec <t> <: vec <t'>` when `<t> <: <t'>` -/
  | vec {A B x y} : Subty A B x y → SubtyC A B (.vec x) (.vec y)
  /-- A field may be specialised or added; a field the supertype declares may be
  omitted only if it accepts `null`. -/
  | record {A B fs gs} :
      (∀ id g, fieldAt gs id = some g →
        (∃ f, fieldAt fs id = some f ∧ Subty A B f g) ∨
        (fieldAt fs id = none ∧ B.acceptsNull g = true)) →
      SubtyC A B (.record fs) (.record gs)
  /-- A tag may be specialised or dropped; every tag carried must exist in the
  supertype. -/
  | variant {A B fs gs} :
      (∀ id f, fieldAt fs id = some f →
        ∃ g, fieldAt gs id = some g ∧ Subty A B f g) →
      SubtyC A B (.variant fs) (.variant gs)
  /-- Parameters generalise, results specialise, both as tuple-shaped records. Note
  the swapped tables in the parameter premise. The two record composites here are
  synthesised, not table entries: the rule is about labelled slot lists, and
  `.record` is how the spec says to compare them. -/
  | func {A B args rets ann args' rets' ann'} :
      annotsAgree ann ann' = true →
      SubtyC B A (.record (indexedFrom 1 args')) (.record (indexedFrom 1 args)) →
      SubtyC A B (.record (indexedFrom 1 rets)) (.record (indexedFrom 1 rets')) →
      SubtyC A B (.func args rets ann) (.func args' rets' ann')
  /-- Services are records of functions: a method may be specialised or added. -/
  | service {A B ms ms'} :
      (∀ name g, methodAt ms' name = some g →
        ∃ f, methodAt ms name = some f ∧ Subty A B f g) →
      SubtyC A B (.service ms) (.service ms')

end

/-! Smoke checks that the constructors apply as intended. These are not the
interesting theorems; they exist so that a definition which typechecks but cannot be
used gets caught here rather than in slice 2. -/

example (A B : TypeTable) : Subty A B .nat .int := Subty.natInt

example (A B : TypeTable) (a : Slot) : Subty A B a (.prim .reserved) := Subty.toReserved

/-- Any type is a subtype of an `opt`, reached through the supertype's table. -/
example (A B : TypeTable) (a : Slot) (y : Slot) (j : TypeRef)
    (h : B.lookup? j = some (.opt y)) : Subty A B a (.ref j) := Subty.toOpt h

example (A B : TypeTable) : SubtyC A B (.vec .nat) (.vec .int) := SubtyC.vec Subty.natInt

/-- Two references are related through their entries. -/
example (A B : TypeTable) (i j : TypeRef)
    (hi : A.lookup? i = some (.vec .nat)) (hj : B.lookup? j = some (.vec .int)) :
    Subty A B (.ref i) (.ref j) :=
  Subty.unfold hi hj (SubtyC.vec Subty.natInt)

/-- The empty record is a supertype of every record: the field premise is vacuous. -/
example (A B : TypeTable) (fs : List (FieldId × Slot)) :
    SubtyC A B (.record fs) (.record []) := by
  apply SubtyC.record
  intro id g h
  simp [fieldAt] at h

/-
The obligation this file exists to create, and the first proof of the next slice:

    theorem decSubtype_iff (a b : ClosedType) :
        decSubtype a b = true <-> Subty a.table b.table a.root b.root

The statement carries no side condition, because `decSubtype` is total: every
question it is asked, it answers.

Soundness (`true` implies `Subty`) should follow by coinduction on the procedure's
recursion, with the pairs *missing* from `todo` as the coinductive hypothesis -- that
is what `todo` means, and stating it this way is what will confirm the accounting is
right. Completeness is the converse, and needs that assuming a pair already descended
through cannot manufacture a relation that the greatest fixed point excludes.

Well-formedness may turn out to be unnecessary as a hypothesis: a dangling reference
makes the procedure answer `false`, and it equally leaves the relation with no
applicable rule, since `unfold` demands `lookup? = some`. Whether the two agree on
duplicate labels is the same question about `fieldAt` on both sides.

Deliberately not stated with `sorry`: an unproved `theorem` in the build reads as
established once it scrolls past. The properties `coq/MiniCandid.v` establishes
(`subtyping_refl`, `subtyping_trans`, `coerce_roundtrip`, `soundness`,
`transitive_coherence`) attach to `Subty`, and are worth restating here over the full
type language rather than over MiniCandid's nine constructors.
-/

end Candid
