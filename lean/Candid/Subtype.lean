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
*references*: every other slot pair is decided outright. The procedure carries the
reference pairs it has already assumed -- the coinductive hypothesis, since
meeting a recorded pair again is an obligation the greatest fixed point discharges
rather than one that failed.

It carries them in two lists, one per direction. `seen` holds pairs `(i, j)` assumed
as `A.i <: B.j`; `seenRev` holds pairs `(j, i)` assumed as `B.j <: A.i`, which the
function rule's contravariant parameter premise asks. The premise swaps the tables,
so its obligations are checked against the other list. What it must not do is turn one list into the other: an
assumed `A.i <: B.j` says nothing about `B.j <: A.i`, and reading it as such answers
the converse from the accounting -- `func (A) -> (nat) <: func (B) -> (int)`, each
taking itself, came out `true` that way while the relation rejects it.

Termination is then `remaining`, the number of reference pairs the two lists have
*not* recorded, each over its own orientation. It is mentioned only by
`termination_by`, so the `|A| x |B|` pair space it counts over is never built when the
procedure runs: a list grows by one cons per recorded pair and is read by a scan. The
two facts the measure needs are produced where the decision is made -- the guard says
the pair is fresh, and the table lookups say its indices are in range -- so no
invariant is threaded through the recursion.
-/

import Candid.Types

namespace Candid

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

/-- The measure `run` descends on first: reference pairs not yet assumed, in both
directions -- `A`-against-`B` pairs that `seen` lacks, and `B`-against-`A` pairs that
`seenRev` lacks. -/
def remaining (A B : TypeTable) (seen seenRev : List (TypeRef × TypeRef)) : Nat :=
  unseen A B seen + unseen B A seenRev

theorem remaining_cons_lt {A B : TypeTable} {i j : TypeRef}
    {seen seenRev : List (TypeRef × TypeRef)}
    (hi : i < A.size) (hj : j < B.size) (hfresh : seen.contains (i, j) = false) :
    remaining A B ((i, j) :: seen) seenRev < remaining A B seen seenRev := by
  have hlt : unseen A B ((i, j) :: seen) < unseen A B seen :=
    countP_cons_lt hfresh (mem_allPairs hi hj)
  simp only [remaining]
  omega

theorem remaining_consRev_lt {A B : TypeTable} {i j : TypeRef}
    {seen seenRev : List (TypeRef × TypeRef)}
    (hj : j < B.size) (hi : i < A.size) (hfresh : seenRev.contains (j, i) = false) :
    remaining A B seen ((j, i) :: seenRev) < remaining A B seen seenRev := by
  have hlt : unseen B A ((j, i) :: seenRev) < unseen B A seenRev :=
    countP_cons_lt hfresh (mem_allPairs hj hi)
  simp only [remaining]
  omega

/-! ## The procedure

A worklist. `run` holds the obligations still to discharge and the reference pairs
assumed so far, in each direction (see the header), and takes one obligation at a
time. A slot pair that is not two references is decided outright by `leaf`. A pair of
references is either assumed already, and dropped, or recorded and replaced by the
obligations `expand` finds one step in.

The assumptions are shared by the whole run, not scoped to a path. That is sound
because every premise of every rule is a conjunct: no rule searches, so nothing
backtracks. Any `false` is the answer to the whole question, and the assumptions
recorded on the way to it are discarded with it; a `true` means every obligation was
discharged, including each one that was assumed. Scoping them to a path instead
re-derives every shared sub-type once per path that reaches it, which is exponential
in a table's depth: 2^41 - 1 comparisons for two tables of 41 entries, each entry
referencing the next one twice.

Sharing is also what lets the measure be simple: the lists only grow, and only by
one pair at a time, so (`remaining`, number of pending obligations) descends at every
step. Recording a pair lowers the first; any other step drops an obligation. -/

/-- An obligation `sub <: sup`. `fwd` says which way round the tables are: `sub` in
`A` and `sup` in `B`, or -- for the function rule's contravariant parameter premise --
the reverse. -/
structure Goal where
  fwd : Bool
  sub : Slot
  sup : Slot

/-- A slot pair that needs no unfolding, decided in tables `T` (the subtype's) and `U`
(the supertype's). `none` for a pair of references, the only kind that unfolds. -/
def leaf (T U : TypeTable) : Slot → Slot → Option Bool
  -- `<datatype> <: reserved` and `empty <: <datatype>`: the top and bottom types.
  -- Neither looks at the other side, which is sound only because both tables are
  -- well formed and the roots resolve: every slot reached here is a type.
  | _, .prim .reserved => some true
  | .prim .empty, _ => some true

  -- `<primtype> <: <primtype>`, plus `nat <: int`. `principal` is a primitive
  -- (spec/Candid.md:80), so `principal <: principal` needs no rule of its own.
  | .prim p, .prim q => some (p == q || (p == .nat && q == .int))

  -- A primitive against a composite: only the `opt` rule can apply, since `empty`
  -- and `reserved` are decided above.
  | .prim _, .ref j =>
    match U.lookup? j with
    | some (.opt _) => some true
    | _ => some false

  -- A composite against a primitive: only `service <actortype> <: principal`.
  | .ref i, .prim q =>
    match q, T.lookup? i with
    | .principal, some (.service _) => some true
    | _, _ => some false

  | .ref _, .ref _ => none

/-- The record rule, as obligations: every label the supertype declares is either
specialised by the subtype -- an obligation -- or omitted, which requires that it
accept `null` in `U`, the supertype's table, and is decided here. `none` if one
cannot be omitted. -/
def labelGoals (U : TypeTable) (fwd : Bool) (fs gs : List (FieldId × Slot)) :
    Option (List Goal) :=
  gs.foldr (init := some []) fun (id, g) rest => do
    let rest ← rest
    match fieldAt fs id with
    | some f => some (⟨fwd, f, g⟩ :: rest)
    | none => if U.acceptsNull g then some rest else none

/-- The obligations one step in, on the composites that a pair of references names:
`x` in `T`, the subtype's table, and `y` in `U`, the supertype's. `none` if the pair
fails outright. -/
def expand (T U : TypeTable) (fwd : Bool) : Composite → Composite → Option (List Goal)
  -- Any type is a subtype of an option. See the header: this single rule is the
  -- spec's four `opt` rules with their negative premises eliminated.
  | _, .opt _ => some []

  | .vec x, .vec y => some [⟨fwd, x, y⟩]

  -- A record may specialise a field's type or add a field. It may also *omit* a
  -- field the supertype has, provided that field accepts `null`.
  | .record fs, .record gs => labelGoals U fwd fs gs

  -- A variant may specialise a tag's type or drop a tag. Every tag it does carry
  -- must exist in the supertype.
  | .variant fs, .variant gs =>
    fs.mapM fun (id, f) => (fieldAt gs id).map fun g => ⟨fwd, f, g⟩

  -- Parameters generalise, results specialise, and both behave like tuple-shaped
  -- records -- so arguments may be dropped and results added.
  --
  -- The parameter premise swaps the tables: its obligations face the other way, and
  -- its omitted parameters must accept `null` in `T`, which is now the supertype's
  -- table. An obligation's direction is what selects the assumption list it is
  -- checked against, so an assumed `A.i <: B.j` is never read as `B.j <: A.i`.
  | .func args rets ann, .func args' rets' ann' =>
    if annotsAgree ann ann' then do
      let params ← labelGoals T (!fwd) (indexedFrom 1 args') (indexedFrom 1 args)
      let results ← labelGoals U fwd (indexedFrom 1 rets) (indexedFrom 1 rets')
      some (params ++ results)
    else none

  -- Services are records of functions: a method may be specialised or added.
  | .service ms, .service ms' =>
    ms'.mapM fun (name, g) => (methodAt ms name).map fun f => ⟨fwd, f, g⟩

  | _, _ => none

/-- Discharge `goals`, given the pairs assumed so far: `seen` holds `(i, j)` for an
assumed `A.i <: B.j`, and `seenRev` holds `(j, i)` for an assumed `B.j <: A.i`. -/
def run (A B : TypeTable) (seen seenRev : List (TypeRef × TypeRef)) :
    List Goal → Bool
  | [] => true

  -- Two references, `A` against `B`: the only place `seen` grows.
  | ⟨true, .ref i, .ref j⟩ :: goals =>
    -- The three names below are underscored because the *value* ignores them: they
    -- exist for the termination proof, which the unused-variable linter does not see.
    match _hx : A.lookup? i, _hy : B.lookup? j with
    | some x, some y =>
      if _hs : seen.contains (i, j) then run A B seen seenRev goals
      else match expand A B true x y with
        | some next => run A B ((i, j) :: seen) seenRev (next ++ goals)
        | none => false
    -- Unreachable: the roots resolve, and in a well-formed table so does every slot
    -- an entry holds. The arm exists because `lookup?` returns an `Option`.
    | _, _ => false

  -- Two references, `B` against `A`: the same, against `seenRev`.
  | ⟨false, .ref j, .ref i⟩ :: goals =>
    match _hy : B.lookup? j, _hx : A.lookup? i with
    | some y, some x =>
      if _hs : seenRev.contains (j, i) then run A B seen seenRev goals
      else match expand B A false y x with
        | some next => run A B seen ((j, i) :: seenRev) (next ++ goals)
        | none => false
    | _, _ => false

  | ⟨fwd, a, b⟩ :: goals =>
    match leaf (if fwd then A else B) (if fwd then B else A) a b with
    | some true => run A B seen seenRev goals
    | _ => false
termination_by goals => (remaining A B seen seenRev, goals.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | -- Recording a pair: it is fresh (`hs`), and each index resolves, so each is in
      -- range (`hx`, `hy`).
      simp only [TypeTable.lookup?, RawTypeTable.lookup?] at _hx _hy
      first
        | exact Prod.Lex.left _ _
            (remaining_cons_lt (Array.getElem?_eq_some_iff.1 _hx).1
              (Array.getElem?_eq_some_iff.1 _hy).1 (by simpa using _hs))
        | exact Prod.Lex.left _ _
            (remaining_consRev_lt (Array.getElem?_eq_some_iff.1 _hy).1
              (Array.getElem?_eq_some_iff.1 _hx).1 (by simpa using _hs))

/-- Decide `a <: b`, where `a` is a type in `A` and `b` one in `B`. Total: every step
either records a reference pair, of which there are finitely many, or discharges an
obligation. -/
def decSubtype (A B : TypeTable) (a : A.Root) (b : B.Root) : Bool :=
  run A B [] [] [⟨true, a.1, b.1⟩]

end Candid
