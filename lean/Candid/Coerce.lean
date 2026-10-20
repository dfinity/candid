/-
Coercion: `v : t ~> v' : t'`, as a function.

Rules are from `spec/Candid.md`, "Coercion". There `V`, `T` and `T'` are inputs and `V'`
the output, and the relation is meant to be functional, so the model states it as a
function: `coerce A B v t u` is the `v'` with `v : t ~> v' : u`, or `none` if there is
none. It is only asked about well-typed values (`TypeTable.hasType`); on anything else
its answer means nothing.

Two tables, as for subtyping: `t` is a type in `A`, the table that came with the
value, and `u` a type in `B`, the receiver's.

**The `opt` rules lose their negative premises here too, for a different reason.** Two
of the spec's rules for an expected `opt` say "and else goes to `null`": `not (exists
<w>. <v> : <t> ~> <w> : <t'>)`. For a function, that premise is the `none` branch of
a match, so the four rules are one case split on whether the inner coercion
succeeded. The other two are `null` when the actual type accepts `null` (its value is
`null`, or the actual type is `reserved`), and a `null <: <t>` premise is
`TypeTable.acceptsNull`.

**Where the spec's relation is undefined.** Coercing a value whose type does not accept
`null` at an `opt` type asks the same question one `opt` deeper, about the *same value*:

```
not (null <: <t>)
<v> : <t> ~> <v'> : <t'>
--------------------------------
<v> : <t> ~> opt <v'> : opt <t'>
```

If the expected type is an `opt` cycle, `type R = opt R`, that question is the one being
asked, and the "else goes to `null`" rule makes it depend on its own negation: `5 : nat
~> w : R` holds if and only if it does not. No answer is consistent. The values of `R`
are `null`, `opt null`, `opt opt null`, ...; `5` fits in none of them, and the spec's
rules cannot say so. Yet `nat <: R` holds, since every type is a subtype of an option,
and the spec's soundness property ("`<t> <: <t'> ⇒ ∀ <v> : <t> ∃ <v'>. <v> : <t> ~>
<v'> : <t'>`") requires *some* answer.

The model answers `null`: the receiver cannot decode the value, so it sees `null`, which
is what the `opt` rules are for. `candid` 0.10 instead keeps unwrapping until its
recursion limit, and that error is not one the `opt` rule recovers from, so the whole
decode fails. That contradicts soundness, but so does the spec, which has no answer
to give here. This is a decision the spec has to make.

**Termination.** Every recursive call is on a strictly smaller value, except one: the
`opt` rule above, which keeps the value and peels the expected type. The model peels
the whole chain of `opt`s at once (`optLayers`) and then coerces at what is under it,
so that step happens once per value. The measure is the value's size, with the
`opt`-peeling step one notch above the step under it.

**Obligations.** The spec lists properties of coercion, and these are the theorems
they become, deliberately not stated with `sorry`:

    -- Roundtripping: a well-typed value coerces to itself.
    theorem coerce_refl (A : TypeTable) (t : A.Root) (v : Value) :
        A.hasType v t.1 = true -> coerce A A v t.1 t.1 = some v

    -- Well-typedness: what coercion produces has the target type.
    theorem coerce_hasType (A B : TypeTable) (t : A.Root) (u : B.Root) (v w : Value) :
        coerce A B v t.1 u.1 = some w -> B.hasType w u.1 = true

    -- Soundness: subtyping means every value coerces. MiniCandid's
    -- `coerce_well_defined`, over the full type language.
    theorem coerce_total (A B : TypeTable) (t : A.Root) (u : B.Root) (v : Value) :
        Subty A B t.1 u.1 -> A.hasType v t.1 = true -> (coerce A B v t.1 u.1).isSome

Soundness holds of the model only because of the `opt`-cycle decision above. All
three are checked by `lake exe oracle` over every generated sample value, against every
type in the generator's universe (`Oracle/Generate.lean`, `propertyViolations`).
-/

import Candid.Value

namespace Candid

/-- `n` applications of `opt`. -/
def wrapOpt : Nat → Value → Value
  | 0, v => v
  | n + 1, v => .opt (wrapOpt n v)

/-- Follow a chain of options from `u`: how many `opt`s there are, and the type under
the last one. `none` for an `opt` cycle, where the chain does not end.

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
def coerce (A B : TypeTable) (v : Value) (t u : Slot) : Option Value :=
  match B.optOf? u with
  | none => coerceAt A B v t u
  | some inner =>
    if A.acceptsNull t then
      -- The actual type accepts `null`: it is `null`, `reserved`, or an option. Only an
      -- option's `opt <v>` has anything to coerce. `null` coerces into any option,
      -- and so does every value of `reserved` -- the spec's `not (<v> = null)` rule
      -- and its `null` rule give the same answer.
      match v, A.optOf? t with
      | .opt w, some t' =>
        match coerce A B w t' inner with
        | some w' => some (.opt w')
        | none => some .null
      | _, _ => some .null
    else
      -- The actual type does not accept `null`: try the value under every `opt` the
      -- expected type has. If that fails, the innermost option is `null`, and the ones
      -- around it are still there. See the header for the `opt` cycle.
      match optLayers B inner (B.size + 1) with
      | none => some .null
      | some (n, core) =>
        match coerceAt A B v t core with
        | some w => some (wrapOpt (n + 1) w)
        | none => some (wrapOpt n .null)
termination_by (sizeOf v, 1)

/-- Coercion at a type that is not an option. Also what is under a chain of them, which
is why `reserved` is decided here rather than in `coerce`: `5 : nat ~> opt null : opt
reserved`, since `5 : nat ~> null : reserved`. -/
def coerceAt (A B : TypeTable) (v : Value) (t u : Slot) : Option Value :=
  match t, u with
  -- Coercion into `reserved` is the constant map.
  | _, .prim .reserved => some .null

  -- On primitive types, coercion is the identity, plus `nat <: int`. `empty` is not
  -- reached, since it has no values.
  | .prim p, .prim q =>
    if p == q then some v
    else match v, p, q with
      | .nat n, .nat, .int => some (.int n)
      | _, _, _ => none

  -- A service reference coerces at `principal`, keeping its identity.
  | .ref i, .prim .principal =>
    match v, A.lookup? i with
    | .service id, some (.service _) => some (.principal id)
    | _, _ => none

  | .ref i, .ref j =>
    match v, A.lookup? i, B.lookup? j with
    -- Vectors coerce pointwise.
    | .vec ws, some (.vec t'), some (.vec u') =>
      (coerceAll A B ws t' u').map .vec

    -- Fields in both types are coerced, and fields only in the actual type are
    -- ignored. Fields only in the expected type must accept `null`, and are `null`.
    | .record vs, some (.record fs), some (.record gs) => do
      let present ← coerceFields A B vs fs gs
      let absent ← gs.filterMapM fun (id, g) =>
        if vs.any (·.1 == id) then some none
        else if B.acceptsNull g then some (some (id, Value.null))
        else none
      some (.record (sortFields (present ++ absent)))

    -- Only a variant value with an expected tag coerces.
    | .variant id w, some (.variant fs), some (.variant gs) =>
      match fieldAt fs id, fieldAt gs id with
      | some t', some u' => (coerce A B w t' u').map (.variant id)
      | _, _ => none

    -- A function or service reference coerces exactly when its type is a subtype of
    -- the expected one, and is unchanged when it does.
    | .func _ _, some (.func _ _ _), some (.func _ _ _)
    | .service _, some (.service _), some (.service _) =>
      match A.root? t, B.root? u with
      | some a, some b => if decSubtype A B a b then some v else none
      | _, _ => none

    | _, _, _ => none

  | _, _ => none
termination_by (sizeOf v, 0)

/-- Coerce every element of a vector. -/
def coerceAll (A B : TypeTable) (ws : List Value) (t u : Slot) : Option (List Value) :=
  match ws with
  | [] => some []
  | w :: rest => do
    let w' ← coerce A B w t u
    let rest' ← coerceAll A B rest t u
    some (w' :: rest')
termination_by (sizeOf ws, 2)

/-- The fields a value carries that the expected type also declares, coerced. Fields
the expected type does not declare are dropped. -/
def coerceFields (A B : TypeTable) (vs : List (FieldId × Value))
    (fs gs : List (FieldId × Slot)) : Option (List (FieldId × Value)) :=
  match vs with
  | [] => some []
  | (id, w) :: rest => do
    let rest' ← coerceFields A B rest fs gs
    match fieldAt gs id with
    | none => some rest'
    | some u =>
      let t ← fieldAt fs id
      let w' ← coerce A B w t u
      some ((id, w') :: rest')
termination_by (sizeOf vs, 2)

end

end Candid
