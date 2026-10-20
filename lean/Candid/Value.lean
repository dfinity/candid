/-
Candid values, and what it means for one to have a type.

The spec describes values through their textual syntax (`spec/Candid.md`, "Values"),
which is untyped: "The types of these values are assumed to be known from context, so
the syntax does not attempt to be self-describing." This model tags numbers by width
instead, so that `5 : nat8` and `5 : nat` are different values. The tag costs nothing a
type would not supply anyway. It means a value can be read without its type, which
matters for a conformance vector: a runner can build the value before it parses
anything else.

**Floats are their bits.** `float32` and `float64` hold the IEEE 754 encoding, not a
Lean `Float`. Coercion is the identity on floats, so nothing here does arithmetic on
them, and a bit pattern keeps what a `Float` would lose or make unequal: the sign of a
zero, and a NaN's payload. Float *edge cases* are therefore not edge cases of coercion
at all. They belong to the textual syntax, which this model does not have yet.

**`null` is one value.** The spec writes `null` for the value of type `null`, for an
absent option, and for "the" value of `reserved` (coercion "is arbitrarily using `null`
as the value of `reserved`"). Rust's `IDLValue` has three constructors for these. The
model follows the spec, and a runner translates by type.

**Records are canonical.** A record value lists its fields in strictly ascending id
order, which is the order the wire format sends them in. `hasType` requires it and
`coerce` produces it, so two record values are equal exactly when they are equal as
lists. Without that, roundtripping (`v : t ~> v : t`) would only hold up to
reordering.
-/

import Candid.Subtype

namespace Candid

/-- A principal, service or function reference's identity: the principal's bytes.
The spec puts no bound on its length, and neither does this model. -/
abbrev PrincipalBytes := List UInt8

inductive Value where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  | nat8 (n : UInt8) | nat16 (n : UInt16) | nat32 (n : UInt32) | nat64 (n : UInt64)
  | int8 (i : Int8) | int16 (i : Int16) | int32 (i : Int32) | int64 (i : Int64)
  /-- The IEEE 754 binary32 encoding. -/
  | float32 (bits : UInt32)
  /-- The IEEE 754 binary64 encoding. -/
  | float64 (bits : UInt64)
  | text (s : String)
  | opt (v : Value)
  | vec (vs : List Value)
  /-- Fields in strictly ascending id order; see the header. -/
  | record (fields : List (FieldId × Value))
  | variant (id : FieldId) (v : Value)
  | principal (id : PrincipalBytes)
  | service (id : PrincipalBytes)
  | func (service : PrincipalBytes) (method : String)
  deriving BEq, Repr, Inhabited

/-- Strictly ascending: no repeats, and in the order the wire format sends fields. -/
def ascending : List FieldId → Bool
  | a :: b :: rest => a < b && ascending (b :: rest)
  | _ => true

/-- Does a primitive value have this primitive type? `reserved` has the one value
`null`, and `empty` has none. -/
def Value.hasPrim : Value → Prim → Bool
  | .null, .null | .null, .reserved => true
  | .bool _, .bool => true
  | .nat _, .nat | .int _, .int => true
  | .nat8 _, .nat8 | .nat16 _, .nat16 | .nat32 _, .nat32 | .nat64 _, .nat64 => true
  | .int8 _, .int8 | .int16 _, .int16 | .int32 _, .int32 | .int64 _, .int64 => true
  | .float32 _, .float32 | .float64 _, .float64 => true
  | .text _, .text => true
  | .principal _, .principal => true
  | _, _ => false

/-! ## Typing

`v : t`, the spec's "`<v>` has inherently type `<t>`". It recurses on the value, so it
terminates whatever the type graph looks like: a recursive type is unfolded only as
far as a value goes. -/

mutual

/-- `v : t`, where `t` is a type in `T`. -/
def TypeTable.hasType (T : TypeTable) : Value → Slot → Bool
  | v, .prim p => v.hasPrim p
  | v, .ref r => match v, T.lookup? r with
    | .null, some (.opt _) => true
    | .opt w, some (.opt t) => T.hasType w t
    | .vec ws, some (.vec t) => T.hasTypeAll ws t
    | .record vs, some (.record fs) =>
      ascending (vs.map (·.1)) && vs.length == fs.length && T.hasFields vs fs
    | .variant id w, some (.variant fs) =>
      match fieldAt fs id with
      | some t => T.hasType w t
      | none => false
    | .service _, some (.service _) => true
    | .func _ _, some (.func _ _ _) => true
    | _, _ => false

/-- Every value has type `t`. -/
def TypeTable.hasTypeAll (T : TypeTable) : List Value → Slot → Bool
  | [], _ => true
  | w :: ws, t => T.hasType w t && T.hasTypeAll ws t

/-- Every field the value carries is declared, at a type the value has. With the
lengths equal and the value's ids distinct, that is every declared field. -/
def TypeTable.hasFields (T : TypeTable) :
    List (FieldId × Value) → List (FieldId × Slot) → Bool
  | [], _ => true
  | (id, w) :: vs, fs =>
    (match fieldAt fs id with
      | some t => T.hasType w t
      | none => false) && T.hasFields vs fs

end

end Candid
