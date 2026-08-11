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
data types, which is why `TypeExpr` is finite with explicit references), so the same
construction is available here.

That is only possible because the negative premises in the spec's `opt` rules are
eliminable -- see the header of `Subtype.lean`. A rule functional with negative
premises is non-monotone and has no greatest fixed point, so `toOpt` below stands in
for all four of the spec's `opt` rules.

The type tables are *indices* rather than parameters because the `func` rule swaps
them: parameter subtyping is contravariant.
-/

import Candid.Subtype

namespace Candid

coinductive Subty : TypeTable → TypeTable → TypeExpr → TypeExpr → Prop where
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
  | serviceToPrincipal {A B ms} : Subty A B (.service ms) (.prim .principal)
  /-- All four `opt` rules of the spec, collapsed. Any type is a subtype of any
  option; a receiver that cannot decode the value sees `null`. -/
  | toOpt {A B a b} : Subty A B a (.opt b)
  /-- `vec <t> <: vec <t'>` when `<t> <: <t'>` -/
  | vec {A B t t'} : Subty A B t t' → Subty A B (.vec t) (.vec t')
  /-- A field may be specialised or added; a field the supertype declares may be
  omitted only if it accepts `null`. -/
  | record {A B fs gs} :
      (∀ id g, fieldAt gs id = some g →
        (∃ f, fieldAt fs id = some f ∧ Subty A B f g) ∨
        (fieldAt fs id = none ∧ B.acceptsNull g = true)) →
      Subty A B (.record fs) (.record gs)
  /-- A tag may be specialised or dropped; every tag carried must exist in the
  supertype. -/
  | variant {A B fs gs} :
      (∀ id f, fieldAt fs id = some f →
        ∃ g, fieldAt gs id = some g ∧ Subty A B f g) →
      Subty A B (.variant fs) (.variant gs)
  /-- Parameters generalise, results specialise, both as tuple-shaped records. Note
  the swapped tables in the parameter premise. -/
  | func {A B args rets ann args' rets' ann'} :
      annotsAgree ann ann' = true →
      Subty B A (.record (indexedFrom 1 args')) (.record (indexedFrom 1 args)) →
      Subty A B (.record (indexedFrom 1 rets)) (.record (indexedFrom 1 rets')) →
      Subty A B (.func args rets ann) (.func args' rets' ann')
  /-- Services are records of functions: a method may be specialised or added. -/
  | service {A B ms ms'} :
      (∀ name g, methodAt ms' name = some g →
        ∃ f, methodAt ms name = some f ∧ Subty A B f g) →
      Subty A B (.service ms) (.service ms')
  /-- References are transparent: a type is related through its table entry. -/
  | unfoldLeft {A B i a' b} :
      A.lookup? i = some a' → Subty A B a' b → Subty A B (.ref i) b
  | unfoldRight {A B a j b'} :
      B.lookup? j = some b' → Subty A B a b' → Subty A B a (.ref j)

/-! Smoke checks that the constructors apply as intended. These are not the
interesting theorems; they exist so that a definition which typechecks but cannot be
used gets caught here rather than in slice 2. -/

example (A B : TypeTable) : Subty A B (.prim .nat) (.prim .int) := Subty.natInt

example (A B : TypeTable) (t : TypeExpr) : Subty A B (.prim .text) (.opt t) := Subty.toOpt

example (A B : TypeTable) (a : TypeExpr) : Subty A B a (.prim .reserved) := Subty.toReserved

example (A B : TypeTable) : Subty A B (.vec (.prim .nat)) (.vec (.prim .int)) :=
  Subty.vec Subty.natInt

/-- The empty record is a supertype of every record: the field premise is vacuous. -/
example (A B : TypeTable) (fs : List (FieldId × TypeExpr)) :
    Subty A B (.record fs) (.record []) := by
  apply Subty.record
  intro id g h
  simp [fieldAt] at h

/-
The obligation this file exists to create, and the first proof of the next slice:

    theorem decSubtype_iff (a b : ClosedType)
        (ha : a.wellFormed = true) (hb : b.wellFormed = true) :
        decSubtype a b = some true <-> Subty a.table b.table a.root b.root

Soundness (`some true` implies `Subty`) should follow by coinduction on the
procedure's recursion, with `seen` as the coinductive hypothesis -- that is what
`seen` *means*, and stating it this way is what will confirm the memo is keyed
correctly. Completeness additionally needs that the budget never runs out on
well-formed input, which is the same fact that would let `fuel` be replaced by a
proper termination measure.

Deliberately not stated with `sorry`: an unproved `theorem` in the build reads as
established once it scrolls past. The properties `coq/MiniCandid.v` establishes
(`subtyping_refl`, `subtyping_trans`, `coerce_roundtrip`, `soundness`,
`transitive_coherence`) attach to `Subty`, and are worth restating here over the full
type language rather than over MiniCandid's nine constructors.
-/

end Candid
