/-
Generated vectors: every pair drawn from a small universe of types, with the model's
answer as the expectation.

These cannot catch the model being wrong -- the model wrote the answers. What they catch
is another implementation disagreeing with it, over far more pairs than anyone would
write by hand, and that is the point of having a reference model at all. Disagreements
found here are findings about one side or the other; which side is the follow-up.

The universe is chosen, not exhaustive: every primitive against every primitive, and
then a set of small types meant to reach every rule with arguments on both sides of
it. Growing it is cheap -- the files are generated -- but every type added multiplies
the pair count, so a type earns its place by exercising something the others do not.
-/

import Oracle.Vector

namespace Oracle.Generate

open Candid

/-- A type to generate: what to call it, and how to intern it. The name is Candid
syntax, so that a vector's id can be pasted into a `.did` file. -/
structure Gen where
  name : String
  build : TableM Slot

def Gen.fixture (g : Gen) : Fixture := close g.build

def prim (p : Prim) : Gen := ⟨p.name, pure (.prim p)⟩

def opt (g : Gen) : Gen := ⟨s!"opt {g.name}", do intern (.opt (← g.build))⟩

def vec (g : Gen) : Gen := ⟨s!"vec {g.name}", do intern (.vec (← g.build))⟩

def fieldsName (fs : List (String × Gen)) : String :=
  if fs.isEmpty then "{}" else "{ " ++ "; ".intercalate (fs.map fun (n, g) => s!"{n} : {g.name}") ++ " }"

def buildFields (fs : List (String × Gen)) : TableM (List (String × Slot)) :=
  fs.mapM fun (n, g) => do return (n, ← g.build)

def record (fs : List (String × Gen)) : Gen :=
  ⟨s!"record {fieldsName fs}", do intern (Composite.recordOf (← buildFields fs))⟩

def variant (fs : List (String × Gen)) : Gen :=
  ⟨s!"variant {fieldsName fs}", do intern (Composite.variantOf (← buildFields fs))⟩

def func (args rets : List Gen) (ann : List FuncAnnot := []) : Gen :=
  let list (gs : List Gen) := "(" ++ ", ".intercalate (gs.map (·.name)) ++ ")"
  let annots := String.join (ann.map (" " ++ ·.name))
  ⟨s!"func {list args} -> {list rets}{annots}", do
    let a ← args.mapM (·.build)
    let r ← rets.mapM (·.build)
    intern (.func a r ann)⟩

def service (ms : List (String × Gen)) : Gen :=
  ⟨s!"service {fieldsName ms}", do intern (.service (← buildFields ms))⟩

/-- A recursive type: `body` is given the slot that names the type being defined. The
entry is reserved before `body` runs, since `body` may intern entries of its own that
refer to it. -/
def knot (name : String) (body : Slot → TableM Composite) : Gen :=
  ⟨s!"({name})", do
    let i := (← get).size
    modify (·.push default)
    let c ← body (.ref i)
    modify (·.set! i c)
    return .ref i⟩

/-! ## The universe -/

def null := prim .null
def bool := prim .bool
def nat := prim .nat
def int := prim .int
def text := prim .text
def reserved := prim .reserved
def empty := prim .empty

/-- The arguments composites are built over: the numeric pair that is related, an
unrelated primitive, the three that accept `null`, and the bottom type. -/
def inner : List Gen := [null, bool, nat, int, text, reserved, empty]

def recursive : List Gen :=
  [ knot "R = opt R" fun r => pure (.opt r)
  , knot "V = vec V" fun v => pure (.vec v)
  , knot "L = record { head : nat; tail : opt L }" fun l => do
      let o ← intern (.opt l)
      return Composite.recordOf [("head", .nat), ("tail", o)]
  , knot "L = record { head : int; tail : opt L }" fun l => do
      let o ← intern (.opt l)
      return Composite.recordOf [("head", .int), ("tail", o)]
  , knot "T = variant { leaf : null; node : T }" fun t =>
      pure (Composite.variantOf [("leaf", .null), ("node", t)])
  , knot "F = func (F) -> ()" fun f => pure (.func [f] [] []) ]

/-- The primitives paired with composites. Pairs of two primitives are all in
`primitives` already. -/
def smallPrims : List Gen :=
  [ null, bool, nat, int, prim .nat8, text, reserved, empty, prim .principal ]

def smallComposites : List Gen :=
  (inner ++ [opt nat]).map opt ++
  (inner ++ [vec nat]).map vec ++
  [ record [], record [("b", nat)] ] ++ (inner ++ [opt nat]).map (fun g => record [("a", g)]) ++
  [ record [("a", nat), ("b", text)], record [("a", nat), ("b", opt nat)] ] ++
  [ variant [], variant [("b", nat)] ] ++ inner.map (fun g => variant [("a", g)]) ++
  [ variant [("a", nat), ("b", text)] ] ++
  [ func [] [], func [] [] [.query], func [] [] [.compositeQuery], func [] [] [.oneway]
  , func [nat] [], func [int] [], func [opt nat] [], func [nat, text] []
  , func [] [nat], func [] [int], func [] [opt nat], func [] [nat, text] ] ++
  [ service [], service [("m", func [] [])], service [("m", func [] [nat])]
  , service [("m", func [] [] [.query])], service [("n", func [] [])] ] ++
  recursive

/-- Every pair with its subtype from `subs` and its supertype from `sups`, each type in
its own table. -/
def pairs (subs sups : List Gen) : List Vector :=
  subs.flatMap fun a => sups.filterMap fun b =>
    let (sub, sup) := (a.fixture, b.fixture)
    -- Every generated type is well formed; a pair that is not would be a bug here.
    match sub.check?, sup.check? with
    | some ⟨A, x⟩, some ⟨B, y⟩ =>
      some ⟨s!"{a.name} <:? {b.name}", .subtype sub sup (decSubtype A B x y)⟩
    | _, _ => none

def primitives : List Vector := pairs (Prim.all.map prim) (Prim.all.map prim)

def smallTypes : List Vector :=
  pairs smallPrims smallComposites ++ pairs smallComposites smallPrims ++
  pairs smallComposites smallComposites

/-- Types the generator built that were not well formed. Expected to be empty: the
oracle fails if it is not, since `pairs` drops them silently. -/
def malformed : List String :=
  (Prim.all.map prim ++ smallComposites).filterMap fun g =>
    if g.fixture.check?.isSome then none else some g.name

end Oracle.Generate
