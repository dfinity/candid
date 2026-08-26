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
live only in the table (`Types.lean`), so the only way to recurse is through a pair of
*references*: every other slot pair is decided outright. The procedure carries `seen`,
the reference pairs this path has already assumed -- the coinductive hypothesis, since
meeting a recorded pair again is an obligation the greatest fixed point discharges
rather than one that failed.

Termination is then `remaining`, the number of reference pairs `seen` has *not*
recorded. It is mentioned only by `termination_by`, so the `|A| x |B|` pair space it
counts over is never built when the procedure runs: `seen` grows by one cons per
descent and is read by a scan no longer than the current path. The two facts the
measure needs are produced where the decision is made -- the guard says the pair is
fresh, and the table lookups say its indices are in range -- so no invariant is
threaded through the recursion.
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

/-- Function annotations must be equal *as sets*. The spec identifies annotation
lists "up to reordering" (`spec/Candid.md:207`); comparing them as sets also ignores
repetition, which no `.did` source produces and which changes no answer. -/
def annotsAgree (xs ys : List FuncAnnot) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

/-- Look up a label. -/
def fieldAt (fs : List (FieldId × Slot)) (id : FieldId) : Option Slot :=
  (fs.find? (·.1 == id)).map (·.2)

/-- Look up a method. -/
def methodAt (ms : List (String × Slot)) (name : String) : Option Slot :=
  (ms.find? (·.1 == name)).map (·.2)

/-! ## The measure

Nothing below this heading runs. `termination_by` measures are erased, so `allPairs`
is a proof device: the procedure never materialises the pair space, it only records
the pairs it actually assumes. -/

/-- Every reference pair of two tables. -/
def allPairs (A B : TypeTable) : List (TypeRef × TypeRef) :=
  (List.range A.size).flatMap fun i => (List.range B.size).map fun j => (i, j)

theorem mem_allPairs {A B : TypeTable} {i j : TypeRef}
    (hi : i < A.size) (hj : j < B.size) : (i, j) ∈ allPairs A B := by
  simp only [allPairs, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨i, hi, j, hj, rfl⟩

/-- Reference pairs of `A` against `B` that `seen` does not record. -/
def unseen (A B : TypeTable) (seen : List (TypeRef × TypeRef)) : Nat :=
  (allPairs A B).countP fun p => !seen.contains p

/-- Recording one more pair cannot raise the count. -/
theorem unseen_cons_le (A B : TypeTable) (a : TypeRef × TypeRef)
    (seen : List (TypeRef × TypeRef)) : unseen A B (a :: seen) ≤ unseen A B seen := by
  apply List.countP_mono_left
  intro x _ hx
  simp only [List.contains_cons, Bool.not_eq_true', Bool.or_eq_false_iff] at hx ⊢
  exact hx.2

/-- The general fact the descent needs: a `countP` over a list drops when the
predicate flips to `false` on one member that is present, and nowhere gains. -/
theorem countP_cons_lt [BEq α] [LawfulBEq α] {a : α} {s : List α}
    (hfresh : s.contains a = false) :
    ∀ {l : List α}, a ∈ l →
      (l.countP fun x => !(a :: s).contains x) < (l.countP fun x => !s.contains x)
  | b :: t, hmem => by
    have hmono : ∀ (u : List α),
        (u.countP fun x => !(a :: s).contains x) ≤ (u.countP fun x => !s.contains x) := by
      intro u
      apply List.countP_mono_left
      intro x _ hx
      simp only [List.contains_cons, Bool.not_eq_true', Bool.or_eq_false_iff] at hx ⊢
      exact hx.2
    rcases List.mem_cons.1 hmem with rfl | hmem'
    · -- the head is the fresh member: now recorded, so its indicator drops 1 -> 0
      rw [List.countP_cons_of_neg (by simp), List.countP_cons_of_pos (by simpa using hfresh)]
      exact Nat.lt_succ_of_le (hmono t)
    · -- the fresh member is further in; the head counts on both sides or on neither
      rw [List.countP_cons, List.countP_cons]
      refine Nat.add_lt_add_of_lt_of_le (countP_cons_lt hfresh hmem') ?_
      by_cases hs : b ∈ s
      · simp [hs]
      · by_cases hab : b = a
        · simp [hab]
        · simp [hs, hab]

/-- The measure `sub` descends on: reference pairs not yet assumed, counted in both
orientations. Counting both is what makes the function rule's table swap leave the
measure alone -- see `remaining_swap`. -/
def remaining (A B : TypeTable) (seen : List (TypeRef × TypeRef)) : Nat :=
  unseen A B seen + unseen B A (seen.map Prod.swap)

theorem remaining_swap (A B : TypeTable) (seen : List (TypeRef × TypeRef)) :
    remaining B A (seen.map Prod.swap) = remaining A B seen := by
  simp only [remaining, List.map_map, Prod.swap_swap_eq, List.map_id]
  omega

theorem remaining_cons_lt {A B : TypeTable} {i j : TypeRef} {seen : List (TypeRef × TypeRef)}
    (hi : i < A.size) (hj : j < B.size) (hfresh : seen.contains (i, j) = false) :
    remaining A B ((i, j) :: seen) < remaining A B seen := by
  have hlt : unseen A B ((i, j) :: seen) < unseen A B seen :=
    countP_cons_lt hfresh (mem_allPairs hi hj)
  have hle : unseen B A (((i, j) :: seen).map Prod.swap) ≤ unseen B A (seen.map Prod.swap) := by
    simpa using unseen_cons_le B A (j, i) (seen.map Prod.swap)
  simp only [remaining]
  omega

/-! ## The procedure

`sub A B seen a b` decides `a <: b`, where `a`'s references resolve in `A` and `b`'s
in `B`, and `seen` holds the reference pairs this path has already assumed. `subC` is
the same
question one step in, on the composites that two references name, and `subLabels` is
the record rule, which the function rule reuses on its positional arguments and
results.

The measures below are lexicographic on (`remaining`, phase), where the phase orders
the three so that a step which does not record a pair still descends: `subC` (2) may
call `subLabels` (1), which may call `sub` (0), which records a pair before calling
`subC` again. -/
mutual

def sub (A B : TypeTable) (seen : List (TypeRef × TypeRef)) : Slot → Slot → Bool
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

  -- Two references: the only recursive case, and the only place `seen` grows. A pair
  -- already in `seen` is one this path has descended through, so the coinductive
  -- hypothesis discharges it rather than the recursion repeating it.
  | .ref i, .ref j =>
    -- The three names below are underscored because the *value* ignores them: they
    -- exist for the termination proof, which the unused-variable linter does not see.
    match _hx : A.lookup? i, _hy : B.lookup? j with
    | some x, some y =>
      if _hs : seen.contains (i, j) then true
      else subC A B ((i, j) :: seen) x y
    | _, _ => false                   -- dangling: not well formed
termination_by (remaining A B seen, 0)
decreasing_by
  -- The three facts the measure needs, all produced by the branch itself: the pair
  -- is fresh (`hs`), and each index resolves, so each is in range (`hx`, `hy`).
  simp only [TypeTable.lookup?] at _hx _hy
  exact Prod.Lex.left _ _
    (remaining_cons_lt (Array.getElem?_eq_some_iff.1 _hx).1
      (Array.getElem?_eq_some_iff.1 _hy).1 (by simpa using _hs))

/-- The rules on the composites that a pair of references names. -/
def subC (A B : TypeTable) (seen : List (TypeRef × TypeRef)) : Composite → Composite → Bool
  -- Any type is a subtype of an option. See the header: this single rule is the
  -- spec's four `opt` rules with their negative premises eliminated.
  | _, .opt _ => true

  | .vec x, .vec y => sub A B seen x y

  -- A record may specialise a field's type or add a field. It may also *omit* a
  -- field the supertype has, provided that field accepts `null`.
  | .record fs, .record gs => subLabels A B seen fs gs

  -- A variant may specialise a tag's type or drop a tag. Every tag it does carry
  -- must exist in the supertype.
  | .variant fs, .variant gs =>
    fs.all fun (id, f) =>
      match fieldAt gs id with
      | some g => sub A B seen f g
      | none => false

  -- Parameters generalise, results specialise, and both behave like tuple-shaped
  -- records -- so arguments may be dropped and results added.
  --
  -- The parameter premise swaps the tables, so it swaps `seen` with them: a pair
  -- `(i, j)` is about `A`'s `i` and `B`'s `j`, and reading it unswapped would assert
  -- something about the transposed pair -- a different, and generally false, question.
  | .func args rets ann, .func args' rets' ann' =>
    annotsAgree ann ann'
      && subLabels B A (seen.map Prod.swap) (indexedFrom 1 args') (indexedFrom 1 args)
      && subLabels A B seen (indexedFrom 1 rets) (indexedFrom 1 rets')

  -- Services are records of functions: a method may be specialised or added.
  | .service ms, .service ms' =>
    ms'.all fun (name, g) =>
      match methodAt ms name with
      | some f => sub A B seen f g
      | none => false

  | _, _ => false
termination_by (remaining A B seen, 2)
decreasing_by
  -- The parameter premise swaps the tables, and `remaining` counts both orientations
  -- precisely so that the swap leaves it alone.
  all_goals (try rw [remaining_swap])
  all_goals exact Prod.Lex.right _ (by omega)

/-- The record rule: every label the supertype declares is either specialised by the
subtype or omitted, and omitting it requires that it accept `null`. -/
def subLabels (A B : TypeTable) (seen : List (TypeRef × TypeRef))
    (fs gs : List (FieldId × Slot)) : Bool :=
  gs.all fun (id, g) =>
    match fieldAt fs id with
    | some f => sub A B seen f g
    | none => B.acceptsNull g
termination_by (remaining A B seen, 1)
decreasing_by exact Prod.Lex.right _ (by omega)

end

/-- Decide `a <: b` for two types carrying their own tables. Total: along any path a
reference pair is recorded at most once, and there are finitely many. -/
def decSubtype (a b : ClosedType) : Bool :=
  sub a.table b.table [] a.root b.root

/- Note the argument order flip in the `func` case above: parameters are
contravariant, so the tables swap with the types -- and `seen` swaps with the tables.
Getting either wrong is invisible when both types share one table, which is the
second reason the two-table signature is worth the extra parameter. -/

end Candid
