/-
Candid subtyping, as a decision procedure over two independent type tables.

Rules are from `spec/Candid.md`, "Upgrading and Subtyping". Two things about that
section shape everything here.

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

**Two tables, not one.** A `TypeExpr` holding a `ref` is meaningless without its
table, and the case that matters most compares a type table that arrived on the wire
against the receiver's own type graph -- two unrelated tables. The current Rust
signature takes a single `env` for both types
(`rust/candid/src/types/subtype.rs:19`), which works only because callers merge
tables first.
-/

import Candid.TypeExpr

namespace Candid

/-- The result of a subtype question. `none` means the recursion budget ran out.

Returning `Bool` here would mean reporting "not a subtype" for a question the model
never actually answered. -/
abbrev Verdict := Option Bool

namespace Verdict

/-- Short-circuiting conjunction that preserves "unanswered". -/
def and (x : Verdict) (y : Unit → Verdict) : Verdict :=
  match x with
  | some true => y ()
  | some false => some false
  | none => none

/-- `f` holds of every element. Stops at the first `false` or unanswered. -/
def all (f : α → Verdict) : List α → Verdict
  | [] => some true
  | x :: xs => match f x with
    | some true => all f xs
    | r => r

/-- `f` holds of some element. Stops at the first `true`; an unanswered question
anywhere makes the whole disjunction unanswered, since a later `true` cannot be
ruled out. -/
def any (f : α → Verdict) : List α → Verdict
  | [] => some false
  | x :: xs => match f x with
    | some false => any f xs
    | some true => some true
    | none => none

end Verdict

/-- `null <: t`, decided syntactically.

The spec's premise `not (null <: <datatype>)` is only ever applied to a concrete
type, and `null` is a subtype of exactly `null`, `reserved`, and any `opt` -- so this
needs no recursion, just one step through the table. -/
def TypeTable.acceptsNull (e : TypeTable) (t : TypeExpr) : Bool :=
  match e.resolve t with
  | some (.prim .null) | some (.prim .reserved) | some (.opt _) => true
  | _ => false

/-- Label a positional list the way the spec's function rule does: "`NI*` is the
`<nat>` sequence `1`..`|<datatypeNI>*|`". -/
def indexedFrom (i : Nat) : List TypeExpr → List (FieldId × TypeExpr)
  | [] => []
  | t :: ts => (UInt32.ofNat i, t) :: indexedFrom (i + 1) ts

/-- Function annotations must be equal *as sets*, per the spec. -/
def annotsAgree (xs ys : List FuncAnnot) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

/-- Look up a label. -/
def fieldAt (fs : List (FieldId × TypeExpr)) (id : FieldId) : Option TypeExpr :=
  (fs.find? (·.1 == id)).map (·.2)

/-- Look up a method. -/
def methodAt (ms : List (String × TypeExpr)) (name : String) : Option TypeExpr :=
  (ms.find? (·.1 == name)).map (·.2)

/- Structural depth, used only to seed the recursion budget. -/
mutual

/-- Structural depth. A `ref` counts as a leaf; unfolding is budgeted separately. -/
def TypeExpr.depth : TypeExpr → Nat
  | .prim _ | .ref _ => 1
  | .opt t | .vec t => 1 + t.depth
  | .record fs | .variant fs => 1 + TypeExpr.depthFields fs
  | .func args rets _ => 1 + Nat.max (TypeExpr.depthList args) (TypeExpr.depthList rets)
  | .service ms => 1 + TypeExpr.depthMethods ms

def TypeExpr.depthList : List TypeExpr → Nat
  | [] => 0
  | t :: ts => Nat.max t.depth (TypeExpr.depthList ts)

def TypeExpr.depthFields : List (FieldId × TypeExpr) → Nat
  | [] => 0
  | (_, t) :: fs => Nat.max t.depth (TypeExpr.depthFields fs)

def TypeExpr.depthMethods : List (String × TypeExpr) → Nat
  | [] => 0
  | (_, t) :: ms => Nat.max t.depth (TypeExpr.depthMethods ms)

end

/-- `sub A B seen fuel a b` decides `a <: b`, where `a`'s references resolve in `A`
and `b`'s in `B`.

`seen` is the coinductive hypothesis: a pair of *references* already under
consideration. Recursive types make the relation a greatest fixed point, so
re-encountering a pair means the obligation is discharged, not that it failed.

**Keying the memo on reference pairs is not enough**, and the `vecOmega` checks in
`Main.lean` are the witness: a cycle whose states always have a reference on exactly one side
never reaches this memo point, so `seen` stays empty and no `fuel` value suffices.
Rust keys on *expression* pairs and inserts whenever either side is a variable
(`rust/candid/src/types/subtype.rs:214`), which closes that cycle -- and unfolded
expressions do not in fact nest without bound, since unfolding only ever replaces a
reference at the top, leaving every state a subterm of a root or of an entry.

So `fuel` is not a placeholder for a measure that exists: for this algorithm there
is none. Either the memo is keyed on expression pairs -- terminating, but the proof
then needs "all reachable states lie in a finite set" threaded through -- or the
representation changes so that every recursive call passes through a reference pair.
-/
def sub (A B : TypeTable) (seen : List (TypeRef × TypeRef)) : Nat → TypeExpr → TypeExpr → Verdict
  | 0, _, _ => none
  | fuel + 1, a, b =>
    match a, b with
    -- Both sides are references: the memo point.
    | .ref i, .ref j =>
      if seen.contains (i, j) then some true
      else match A.lookup? i, B.lookup? j with
        | some a', some b' => sub A B ((i, j) :: seen) fuel a' b'
        | _, _ => some false          -- dangling: not well formed
    -- One side is a reference. Well-formed tables hold only composite types, so this
    -- unfolds at most once before making structural progress.
    | .ref i, _ =>
      match A.lookup? i with
      | some a' => sub A B seen fuel a' b
      | none => some false
    | _, .ref j =>
      match B.lookup? j with
      | some b' => sub A B seen fuel a b'
      | none => some false

    -- `<datatype> <: reserved` and `empty <: <datatype>`: the top and bottom types.
    | _, .prim .reserved => some true
    | .prim .empty, _ => some true

    -- Any type is a subtype of an option. See the header: this single rule is the
    -- spec's four `opt` rules with their negative premises eliminated.
    | _, .opt _ => some true

    | .prim p, .prim q =>
      -- `<primtype> <: <primtype>`, plus `nat <: int`. `principal` is a primitive
      -- (spec/Candid.md:80), so `principal <: principal` needs no rule of its own.
      some (p == q || (p == .nat && q == .int))

    -- `service <actortype> <: principal`.
    | .service _, .prim .principal => some true

    | .vec t, .vec t' => sub A B seen fuel t t'

    -- A record may specialise a field's type or add a field. It may also *omit* a
    -- field the supertype has, provided that field accepts `null`.
    | .record fs, .record gs =>
      Verdict.all (fun (id, g) =>
        match fieldAt fs id with
        | some f => sub A B seen fuel f g
        | none => some (B.acceptsNull g)) gs

    -- A variant may specialise a tag's type or drop a tag. Every tag it does carry
    -- must exist in the supertype.
    | .variant fs, .variant gs =>
      Verdict.all (fun (id, f) =>
        match fieldAt gs id with
        | some g => sub A B seen fuel f g
        | none => some false) fs

    -- Parameters generalise, results specialise, and both behave like tuple-shaped
    -- records -- so arguments may be dropped and results added.
    --
    -- The parameter premise swaps the tables, so it must swap the memo with them: an
    -- entry `(i, j)` means "A's `i` against B's `j`", and reading it unswapped in the
    -- swapped call asserts `B`'s `i` against `A`'s `j` -- a different, and generally
    -- false, question. See the `contra` checks in `Main.lean`.
    | .func args rets ann, .func args' rets' ann' =>
      if annotsAgree ann ann' then
        Verdict.and
          (sub B A (seen.map Prod.swap) fuel
            (.record (indexedFrom 1 args')) (.record (indexedFrom 1 args)))
          fun _ => sub A B seen fuel (.record (indexedFrom 1 rets)) (.record (indexedFrom 1 rets'))
      else some false

    -- Services are records of functions: a method may be specialised or added.
    | .service ms, .service ms' =>
      Verdict.all (fun (name, g) =>
        match methodAt ms name with
        | some f => sub A B seen fuel f g
        | none => some false) ms'

    | _, _ => some false

/-- A budget that is generous rather than tight: every path may unfold each
reference pair once (`|A| x |B|`), descending the structure between unfoldings. -/
def budgetFor (a b : ClosedType) : Nat :=
  let pairs := (a.table.size + 1) * (b.table.size + 1)
  pairs * (a.root.depth + b.root.depth + 2) + 2

/-- Decide `a <: b` for two types carrying their own tables.

`none` means the budget was exhausted. Well-formed input *can* provoke it -- see
the `vecOmega` checks in `Main.lean` -- so `none` is a real answer callers must handle, not a
theoretical one. -/
def decSubtype (a b : ClosedType) : Verdict :=
  sub a.table b.table [] (budgetFor a b) a.root b.root

/- Note the argument order flip in the `func` case above: parameters are
contravariant, so the tables swap with the types -- and the memo swaps with the
tables. Getting either wrong is invisible when both types share one table, which is
the second reason the two-table signature is worth the extra parameter. -/

end Candid
