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

/-! ## Coercion

Every sample value of every type in the universe, coerced at every type. The samples
are drawn from the type, a few per type: enough to reach each coercion rule, not every
value of every shape. -/

/-- The identity of every generated reference value. Coercion never looks at it. -/
def someId : PrincipalBytes := [0x2a]

def primSamples : Prim → List Value
  | .null | .reserved => [.null]
  | .bool => [.bool true]
  | .nat => [.nat 5]
  | .int => [.int (-5)]
  | .nat8 => [.nat8 255] | .nat16 => [.nat16 65535]
  | .nat32 => [.nat32 4294967295] | .nat64 => [.nat64 18446744073709551615]
  | .int8 => [.int8 (-128)] | .int16 => [.int16 (-32768)]
  | .int32 => [.int32 (-2147483648)] | .int64 => [.int64 (-9223372036854775808)]
  | .float32 => [.float32 0x3f800000] | .float64 => [.float64 0x3ff0000000000000]
  | .text => [.text "x"]
  | .empty => []
  | .principal => [.principal someId]

/-- Sample values of `t`, unfolding at most `fuel` references deep. An option and a
vector give an empty and a non-empty one; a variant gives one value per tag. -/
def samples (T : TypeTable) : Nat → Slot → List Value
  | _, .prim p => primSamples p
  | 0, .ref _ => []
  | fuel + 1, .ref r => match T.lookup? r with
    | some (.opt t) => .null :: ((samples T fuel t).take 1).map .opt
    | some (.vec t) => .vec [] :: ((samples T fuel t).take 1).map (.vec [·])
    | some (.record fs) =>
      match fs.mapM fun (id, t) => (samples T fuel t).head?.map (id, ·) with
      | some vs => [.record (sortFields vs)]
      | none => []
    | some (.variant fs) => fs.filterMap fun (id, t) => (samples T fuel t).head?.map (.variant id)
    | some (.func _ _ _) => [.func someId "m"]
    | some (.service _) => [.service someId]
    | none => []

/-- A value in the textual syntax, for vector ids. Numbers carry their type, since the
same number is a different value at a different width. -/
partial def showValue : Value → String
  | .null => "null"
  | .bool b => toString b
  | .nat n => s!"{n}"
  | .int i => s!"({i} : int)"
  | .nat8 n => s!"({n} : nat8)" | .nat16 n => s!"({n} : nat16)"
  | .nat32 n => s!"({n} : nat32)" | .nat64 n => s!"({n} : nat64)"
  | .int8 i => s!"({i.toInt} : int8)" | .int16 i => s!"({i.toInt} : int16)"
  | .int32 i => s!"({i.toInt} : int32)" | .int64 i => s!"({i.toInt} : int64)"
  | .float32 b => s!"(float32 bits {hexFixed 8 b.toNat})"
  | .float64 b => s!"(float64 bits {hexFixed 16 b.toNat})"
  | .text t => (Lean.Json.str t).compress
  | .opt v => s!"opt {showValue v}"
  | .vec vs => "vec {" ++ "; ".intercalate (vs.map showValue) ++ "}"
  | .record fs => "record {" ++ "; ".intercalate (fs.map fun (id, v) => s!"{id} = {showValue v}") ++ "}"
  | .variant id v => s!"variant \{{id} = {showValue v}}"
  | .principal id => s!"principal \"{bytesToHex id}\""
  | .service id => s!"service \"{bytesToHex id}\""
  | .func id m => s!"func \"{bytesToHex id}\".{m}"

/-- `type R = opt R`. -/
def infiniteOpt : Gen := knot "R = opt R" fun r => pure (.opt r)

/-- `type A = opt B; type B = opt A`: an infinite option two entries long. -/
def infiniteOpt2 : Gen := ⟨"(A = opt B; B = opt A)", do
  let i := (← get).size
  modify fun es => (es.push (.opt (.ref (i + 1)))).push (.opt (.ref i))
  return .ref i⟩

/-- Types that hold an infinite option somewhere inside. Coercion at one is undefined
for a value whose type does not accept `null` (`spec/Candid.md`, "Coercion" >
"Options"), and so is any coercion that needs it; these are where that shows. Not part
of `smallComposites`, so the subtyping files do not grow with them. -/
def holdsInfiniteOpt : List Gen :=
  [ infiniteOpt2, record [("a", infiniteOpt)], vec infiniteOpt, variant [("a", infiniteOpt)] ]

/-- Every type a sample is drawn from, and every type it is coerced at. -/
def coerceUniverse : List Gen := Prim.all.map prim ++ smallComposites ++ holdsInfiniteOpt

/-- A generated type, checked, with its samples. Every generated type is well formed;
`malformed` reports one that is not. -/
def Gen.checked? (g : Gen) : Option (Fixture × (T : TypeTable) × T.Root) := do
  let f := g.fixture
  let ⟨T, r⟩ ← f.check?
  return ⟨f, T, r⟩

def coercions : List Vector :=
  coerceUniverse.flatMap fun a => match a.checked? with
    | none => []
    | some ⟨fa, A, ra⟩ => (samples A 3 ra.1).flatMap fun v =>
      coerceUniverse.filterMap fun b => do
        let ⟨fb, B, rb⟩ ← b.checked?
        return ⟨s!"{showValue v} : {a.name} ~> {b.name}",
          .coerce v fa fb (coerceResult A B v ra.1 rb.1)⟩

/-! ## Decoding

Every sample value, encoded at its own type by the model's encoder and decoded at that
type again. These are the wire format's positive cases, one per sample rather than one
per pair of types: what a value becomes at another type is what `coercions` asserts
already. The ways a message can be malformed are written by hand, since an encoder only
produces messages that are not. -/

def decodes : List Vector :=
  coerceUniverse.flatMap fun a => match a.checked? with
    | none => []
    | some ⟨fa, A, ra⟩ => (samples A 3 ra.1).filterMap fun v => do
      let bs ← encode A [ra.1] [v]
      return ⟨s!"decode {showValue v} : {a.name}",
        .decode bs ⟨fa.table, [fa.root]⟩ (deserialize bs A [ra.1])⟩

/-! ## Properties

Three of the properties `spec/Candid.md` lists for coercion, checked over every
generated sample rather than proved. Each is a claim about the model, so a violation is
a finding about it, or about the spec: the vectors are the model's answers whatever
they are.

- **Roundtripping**: `v : t ~> v : t`. (The spec states an equivalence, but its other
  direction, from `v : t ~> v : t` to `v : t`, is about values that are not well typed,
  and the samples all are.)
- **Well-typedness**: `v : t ~> v' : t'` implies `v' : t'`.
- **Soundness**: `t <: t'` implies that no `v : t` fails to coerce at `t'`. It may be
  undefined: that is the spec's exception, at an infinite option.

Each returns a description of every counterexample. -/

def propertyViolations : List String :=
  coerceUniverse.flatMap fun a => match a.checked? with
    | none => []
    | some ⟨_, A, ra⟩ => (samples A 3 ra.1).flatMap fun v =>
      let typed := if A.hasType v ra.1 then [] else
        [s!"sample {showValue v} does not have type {a.name}"]
      let roundtrip := if coerceResult A A v ra.1 ra.1 == some v then [] else
        [s!"roundtripping: {showValue v} : {a.name} does not coerce to itself"]
      typed ++ roundtrip ++ coerceUniverse.flatMap fun b => match b.checked? with
        | none => []
        | some ⟨_, B, rb⟩ =>
          match (coerce A B v ra.1 rb.1).run with
          | .ok (some w) => if B.hasType w rb.1 then [] else
              [s!"well-typedness: {showValue v} : {a.name} ~> {showValue w}, not of type {b.name}"]
          | .ok none => if decSubtype A B ra rb then
              [s!"soundness: {a.name} <: {b.name}, but {showValue v} does not coerce"]
            else []
          | .error _ => []

/-- The wire format roundtrips: every sample encodes, and the bytes decode to the same
value at the same type, in a table that differs from the one written at most in the
order of each entry's members. Compared by encoding the entries, which sorts them. -/
def wireViolations : List String :=
  coerceUniverse.flatMap fun a => match a.checked? with
    | none => []
    | some ⟨_, A, ra⟩ => (samples A 3 ra.1).filterMap fun v =>
      let what := s!"{showValue v} : {a.name}"
      match encode A [ra.1] [v] with
      | none => some s!"wire: {what} does not encode"
      | some bs => match decode bs with
        | .error e => some s!"wire: {what} does not decode: {e.msg} at byte {e.pos}"
        | .ok m =>
          let entries (T : TypeTable) := T.raw.entries.toList.map Composite.encode
          if m.values != [v] then some s!"wire: {what} decodes to another value"
          else if m.types != [ra.1] then some s!"wire: {what} decodes at another type"
          else if entries m.table != entries A then some s!"wire: {what} decodes with another table"
          else if deserialize bs A [ra.1] != some [v] then
            some s!"wire: {what} does not deserialise to itself"
          else none

/-- Types the generator built that were not well formed. Expected to be empty: the
oracle fails if it is not, since `pairs` drops them silently. -/
def malformed : List String :=
  (Prim.all.map prim ++ smallComposites ++ holdsInfiniteOpt).filterMap fun g =>
    if g.fixture.check?.isSome then none else some g.name

end Oracle.Generate
