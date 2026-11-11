/-
Type equivalence: whether two types are the same type.

Two types are the same when they unfold to the same infinite tree: a name is the same
type as its definition, and two tables that share structure differently can still hold
the same type. Field and method lists are compared as sets, since the spec identifies
them up to reordering, and so are function annotations (`annotsAgree`).

Mutual subtyping is not equivalence. `record {}` and `record { a : opt nat }` are each a
subtype of the other, since a record may omit a field that accepts `null`, but they are
not the same type.

The textual syntax needs this: an annotation `(e : s)` is accepted at `t` only when
`s` and `t` are the same type (`lean/Spec/TextValues.md`, Section 5.1). Encoding
vectors will need it too, to check that bytes decode to the type they were encoded at.

**The procedure** is the subtype procedure's worklist (`Subtype.lean`) with one
direction instead of two. Equivalence is the greatest relation closed under its rules,
so a pair of references met again is assumed rather than re-derived. Every rule's
premises are a conjunction, so any `false` answers the whole question and nothing
backtracks. The measure is the same: reference pairs not yet assumed, then pending
obligations.
-/

import Candid.Subtype

namespace Candid

/-- Two slots that need no unfolding: `none` for a pair of references. A primitive is
only ever the same type as itself, and never the same as a composite. -/
def equivLeaf : Slot → Slot → Option Bool
  | .prim p, .prim q => some (p == q)
  | .ref _, .ref _ => none
  | _, _ => some false

/-- The same labels, each once, paired up as obligations; `none` if the label sets
differ. Well-formed tables do not repeat a label, so equal lengths and every label of
`fs` present in `gs` make the sets equal. -/
def pairLabels [BEq α] (fs gs : List (α × Slot)) : Option (List (Slot × Slot)) :=
  if fs.length != gs.length then none
  else fs.mapM fun (l, f) => ((gs.find? (·.1 == l)).map (·.2)).map fun g => (f, g)

/-- The obligations one step in, on the composites a pair of references names. -/
def equivExpand : Composite → Composite → Option (List (Slot × Slot))
  | .opt x, .opt y | .vec x, .vec y => some [(x, y)]
  | .record fs, .record gs | .variant fs, .variant gs => pairLabels fs gs
  | .func args rets ann, .func args' rets' ann' =>
    if annotsAgree ann ann' && args.length == args'.length && rets.length == rets'.length
    then some (args.zip args' ++ rets.zip rets')
    else none
  | .service ms, .service ms' => pairLabels ms ms'
  | .future op d, .future op' d' => if op == op' && d == d' then some [] else none
  | _, _ => none

/-- Discharge `goals`, each a type of `A` against one of `B`, given the reference pairs
assumed so far. -/
def equivRun (A B : TypeTable) (seen : List (TypeRef × TypeRef)) :
    List (Slot × Slot) → Bool
  | [] => true
  | (.ref i, .ref j) :: goals =>
    match _hx : A.lookup? i, _hy : B.lookup? j with
    | some x, some y =>
      if _hs : seen.contains (i, j) then equivRun A B seen goals
      else match equivExpand x y with
        | some next => equivRun A B ((i, j) :: seen) (next ++ goals)
        | none => false
    -- Unreachable for roots that resolve in well-formed tables.
    | _, _ => false
  | (a, b) :: goals =>
    match equivLeaf a b with
    | some true => equivRun A B seen goals
    | _ => false
termination_by goals => (unseen A B seen, goals.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | simp only [TypeTable.lookup?, RawTypeTable.lookup?] at _hx _hy
      exact Prod.Lex.left _ _
        (countP_cons_lt (by simpa using _hs)
          (mem_allPairs (Array.getElem?_eq_some_iff.1 _hx).1
            (Array.getElem?_eq_some_iff.1 _hy).1))

/-- Are `a`, a type in `A`, and `b`, a type in `B`, the same type? -/
def decEquiv (A B : TypeTable) (a : A.Root) (b : B.Root) : Bool :=
  equivRun A B [] [(a.1, b.1)]

end Candid
