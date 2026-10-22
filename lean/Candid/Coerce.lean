/-
Coercion: `v : t ~> v' : t'`, as a function.

Rules are from `spec/Candid.md`, "Coercion". There `V`, `T` and `T'` are inputs and `V'`
the output, and the relation is meant to be functional, so the model states it as a
function: `coerce A B v t u` is the `v'` with `v : t ~> v' : u`, `none` if there is
none, or `Undefined` (below). It is only asked about well-typed values (`TypeTable.hasType`); on anything else
its answer means nothing.

Two tables, as for subtyping: `t` is a type in `A`, the table that came with the
value, and `u` a type in `B`, the receiver's.

**The `opt` rules lose their negative premises here too, for a different reason.** Two
of the spec's rules for an expected `opt` say "and else goes to `null`": `not (exists
<w>. <v> : <t> ~> <w> : <t'>)`. For a function, that premise is the `none` branch of
a match, so the four rules are one case split on whether the inner coercion
succeeded -- unless it is undefined. The other two are `null` when the actual type accepts `null` (its value is
`null`, or the actual type is `reserved`), and a `null <: <t>` premise is
`TypeTable.acceptsNull`.

**Three outcomes, not two.** Coercing a value whose type does not accept `null` at an
`opt` type asks the same question one `opt` deeper, about the *same value*:

```
not (null <: <t>)
<v> : <t> ~> <v'> : <t'>
--------------------------------
<v> : <t> ~> opt <v'> : opt <t'>
```

At an *infinite option*, `type R = opt R`, that is the question being asked, and the
"else goes to `null`" rule would make it depend on its own negation. The spec settles it
(`spec/Candid.md`, "Coercion" > "Options"): the coercion is *undefined*, which is not the
same as failing. A premise `not (exists <w>. ...)` holds only where coercion is defined,
so no enclosing option recovers, nor does anything else, and deserialisation fails. So
`coerce` has three outcomes: a value, a failure (`none`, which the `opt` rules turn into
`null`), and `Undefined` (an exception, which they pass on). `OptionT`'s `<|>` is that
distinction: it recovers from `none` and passes an exception through. `coerceResult` is what a
decoder reports for one argument, where the last two both mean a rejected message.

That is the behaviour `candid` has had since 0.10.20 and `test/construct.test.did`
asserts; the spec said so in #778. The model said `null` here until then.

**Termination.** Every recursive call is on a strictly smaller value, except one: the
`opt` rule above, which keeps the value and peels the expected type. The model peels
the whole chain of `opt`s at once (`optLayers`) and then coerces at what is under it,
so that step happens once per value. The measure is the value's size, with the
`opt`-peeling step one notch above the step under it.

**Obligations.** The spec lists properties of coercion, and these are the theorems
they become, deliberately not stated with `sorry`:

    -- Roundtripping: a well-typed value coerces to itself.
    theorem coerce_refl (A : TypeTable) (t : A.Root) (v : Value) :
        A.hasType v t.1 = true -> (coerce A A v t.1 t.1).run = .ok (some v)

    -- Well-typedness: what coercion produces from a well-typed value has the target
    -- type. The premise is not decoration: at `nat`, `coerce` passes `.bool true`
    -- through unchanged, since it only means anything on the values of `t`.
    theorem coerce_hasType (A B : TypeTable) (t : A.Root) (u : B.Root) (v w : Value) :
        A.hasType v t.1 = true -> (coerce A B v t.1 u.1).run = .ok (some w) ->
          B.hasType w u.1 = true

    -- Soundness: subtyping means no value fails to coerce. MiniCandid's
    -- `coerce_well_defined`, over the full type language, with the spec's exception:
    -- the coercion may be undefined, at an infinite option.
    theorem coerce_total (A B : TypeTable) (t : A.Root) (u : B.Root) (v : Value) :
        Subty A B t.1 u.1 -> A.hasType v t.1 = true -> (coerce A B v t.1 u.1).run ≠ .ok none

All three are checked by `lake exe oracle` over every generated sample value, against every
type in the generator's universe (`Oracle/Generate.lean`, `propertyViolations`).
-/

import Candid.Value

namespace Candid

/-- Why a coercion is undefined. The spec has one reason. -/
inductive Undefined where
  /-- A value whose type does not accept `null`, at an infinite option. -/
  | infiniteOption
  deriving BEq, Repr

/-- A coercion's outcome: a value; a failure, `none`, which the `opt` rules turn into
`null`; or `Undefined`, which nothing recovers from. -/
abbrev Coercion := OptionT (Except Undefined)

/-- `n` applications of `opt`. -/
def wrapOpt : Nat → Value → Value
  | 0, v => v
  | n + 1, v => .opt (wrapOpt n v)

/-- Follow a chain of options from `u`: how many `opt`s there are, and the type under
the last one. `none` for an infinite option, where the chain does not end.

An acyclic chain visits each reference at most once, so `fuel` at `B.size + 1` reaches
its end; running out means a reference repeated. -/
def optLayers (B : TypeTable) (u : Slot) : Nat → Option (Nat × Slot)
  | 0 => none
  | fuel + 1 => match u with
    | .ref r => match B.lookup? r with
      | some (.opt inner) => (optLayers B inner fuel).map fun (n, c) => (n + 1, c)
      | _ => some (0, u)
    | .prim _ => some (0, u)

/-- Is `u` an option type, and of what? -/
def TypeTable.optOf? (B : TypeTable) : Slot → Option Slot
  | .ref r => match B.lookup? r with
    | some (.opt inner) => some inner
    | _ => none
  | .prim _ => none

/-- Insert into a list sorted by field id. -/
def insertField (f : FieldId × Value) : List (FieldId × Value) → List (FieldId × Value)
  | [] => [f]
  | g :: gs => if f.1 < g.1 then f :: g :: gs else g :: insertField f gs

/-- Sort fields into the canonical order: ascending id. -/
def sortFields (fs : List (FieldId × Value)) : List (FieldId × Value) :=
  fs.foldr insertField []

mutual

/-- `v : t ~> v' : u`, with `t` in `A` and `u` in `B`. -/
def coerce (A B : TypeTable) (v : Value) (t u : Slot) : Coercion Value :=
  match B.optOf? u with
  | none => coerceAt A B v t u
  | some inner =>
    if A.acceptsNull t then
      -- The actual type accepts `null`: it is `null`, `reserved`, or an option. Only an
      -- option's `opt <v>` has anything to coerce. `null` coerces into any option,
      -- and so does every value of `reserved` -- the spec's `not (<v> = null)` rule
      -- and its `null` rule give the same answer.
      match v, A.optOf? t with
      | .opt w, some t' => (.opt <$> coerce A B w t' inner) <|> pure .null
      | _, _ => pure .null
    else
      -- The actual type does not accept `null`: try the value under every `opt` the
      -- expected type has. If that fails, the innermost option is `null`, and the ones
      -- around it are still there. At an infinite option it is undefined.
      match optLayers B inner (B.size + 1) with
      | none => throwThe Undefined .infiniteOption
      | some (n, core) =>
        (wrapOpt (n + 1) <$> coerceAt A B v t core) <|> pure (wrapOpt n .null)
termination_by (sizeOf v, 1)

/-- Coercion at a type that is not an option. Also what is under a chain of them, which
is why `reserved` is decided here rather than in `coerce`: `5 : nat ~> opt null : opt
reserved`, since `5 : nat ~> null : reserved`. -/
def coerceAt (A B : TypeTable) (v : Value) (t u : Slot) : Coercion Value :=
  match t, u with
  -- Coercion into `reserved` is the constant map.
  | _, .prim .reserved => pure .null

  -- On primitive types, coercion is the identity, plus `nat <: int`. `empty` is not
  -- reached, since it has no values.
  | .prim p, .prim q =>
    if p == q then pure v
    else match v, p, q with
      | .nat n, .nat, .int => pure (.int n)
      | _, _, _ => failure

  -- A service reference coerces at `principal`, keeping its identity.
  | .ref i, .prim .principal =>
    match v, A.lookup? i with
    | .service id, some (.service _) => pure (.principal id)
    | _, _ => failure

  | .ref i, .ref j =>
    match v, A.lookup? i, B.lookup? j with
    -- Vectors coerce pointwise.
    | .vec ws, some (.vec t'), some (.vec u') =>
      .vec <$> coerceAll A B ws t' u'

    -- Fields in both types are coerced, and fields only in the actual type are
    -- ignored. Fields only in the expected type must accept `null`, and are `null`.
    | .record vs, some (.record fs), some (.record gs) => do
      let present ← coerceFields A B vs fs gs
      let absent ← gs.filterMapM fun (id, g) =>
        if vs.any (·.1 == id) then pure none
        else if B.acceptsNull g then pure (some (id, Value.null))
        else failure
      pure (.record (sortFields (present ++ absent)))

    -- Only a variant value with an expected tag coerces.
    | .variant id w, some (.variant fs), some (.variant gs) =>
      match fieldAt fs id, fieldAt gs id with
      | some t', some u' => .variant id <$> coerce A B w t' u'
      | _, _ => failure

    -- A function or service reference coerces exactly when its type is a subtype of
    -- the expected one, and is unchanged when it does.
    | .func _ _, some (.func _ _ _), some (.func _ _ _)
    | .service _, some (.service _), some (.service _) =>
      match A.root? t, B.root? u with
      | some a, some b => if decSubtype A B a b then pure v else failure
      | _, _ => failure

    | _, _, _ => failure

  | _, _ => failure
termination_by (sizeOf v, 0)

/-- Coerce every element of a vector. -/
def coerceAll (A B : TypeTable) (ws : List Value) (t u : Slot) : Coercion (List Value) :=
  match ws with
  | [] => pure []
  | w :: rest => do
    let w' ← coerce A B w t u
    let rest' ← coerceAll A B rest t u
    pure (w' :: rest')
termination_by (sizeOf ws, 2)

/-- The fields a value carries that the expected type also declares, coerced. Fields
the expected type does not declare are dropped. -/
def coerceFields (A B : TypeTable) (vs : List (FieldId × Value))
    (fs gs : List (FieldId × Slot)) : Coercion (List (FieldId × Value)) :=
  match vs with
  | [] => pure []
  | (id, w) :: rest => do
    let rest' ← coerceFields A B rest fs gs
    match fieldAt gs id with
    | none => pure rest'
    | some u =>
      let some t := fieldAt fs id | failure
      let w' ← coerce A B w t u
      pure ((id, w') :: rest')
termination_by (sizeOf vs, 2)

end

/-- What a decoder reports for one value: the coerced value, or `none` for a rejected
message. With nothing enclosing it, a failed coercion and an undefined one both reject. -/
def coerceResult (A B : TypeTable) (v : Value) (t u : Slot) : Option Value :=
  match (coerce A B v t u).run with
  | .ok r => r
  | .error _ => none

end Candid
