/-
Elaboration: what an expression means at a type (`lean/Spec/TextValues.md`, Section 5).

`elaborate T e t` is the rule `e ⇐ t ⇝ v` for a type `t` in table `T`: `some v`, or `none`
when the expression is rejected at that type. It recurses on the expression, so it
terminates whatever the type graph: a recursive type is unfolded only as far as the
expression goes.

**Annotations** carry a type of their own, written as a nested `TypeExpr`. It is
flattened into a table of its own (`TypeExpr.toTable?`, in `Flatten.lean`), checked for
well-formedness, and compared with the expected type by `decEquiv`. The expression inside is then elaborated
in the annotation's table, which is why `elaborate` takes the table as an argument rather
than a parameter. Names in an annotation resolve in an environment of type
definitions; the model's is empty, so a name is rejected.

**Well-annotated** expressions (Section 5.1) are checked by `wellAnnotated`, separately:
every annotation inside an expression must hold, even one inside a field or argument
that elaboration ignores, or at `reserved`.
-/

import Candid.Text.Flatten
import Candid.Equiv
import Candid.Coerce
import Candid.Float

namespace Candid.Text

/-- An integer literal at a primitive type: in range, or nothing. -/
def intAt (z : Int) : Prim → Option Value
  | .nat => if 0 ≤ z then some (.nat z.toNat) else none
  | .int => some (.int z)
  | .nat8 => if 0 ≤ z && z < 2 ^ 8 then some (.nat8 z.toNat.toUInt8) else none
  | .nat16 => if 0 ≤ z && z < 2 ^ 16 then some (.nat16 z.toNat.toUInt16) else none
  | .nat32 => if 0 ≤ z && z < 2 ^ 32 then some (.nat32 z.toNat.toUInt32) else none
  | .nat64 => if 0 ≤ z && z < 2 ^ 64 then some (.nat64 z.toNat.toUInt64) else none
  | .int8 => if -2 ^ 7 ≤ z && z < 2 ^ 7 then some (.int8 (Int8.ofInt z)) else none
  | .int16 => if -2 ^ 15 ≤ z && z < 2 ^ 15 then some (.int16 (Int16.ofInt z)) else none
  | .int32 => if -2 ^ 31 ≤ z && z < 2 ^ 31 then some (.int32 (Int32.ofInt z)) else none
  | .int64 => if -2 ^ 63 ≤ z && z < 2 ^ 63 then some (.int64 (Int64.ofInt z)) else none
  | _ => none

/-- The fields of a record type the expression does not have: each is `null` if its
type accepts it, and the record is rejected otherwise. -/
def fillFields (T : TypeTable) (given : List FieldId) (gs : List (FieldId × Slot)) :
    Option (List (FieldId × Value)) :=
  (gs.filter fun (id, _) => !given.contains id).mapM fun (id, t) =>
    if T.acceptsNull t then some (id, .null) else none

mutual

/-- `e ⇐ t ⇝ v`, for `t` in `T`. -/
def elaborate : TypeTable → Expr → Slot → Option Value
  | T, .ann e te, t => do
    let ⟨S, s⟩ ← te.toTable?
    let r ← T.root? t
    guard (decEquiv S T s r)
    elaborate S e s.1
  | _, _, .prim .reserved => some .null
  | _, .int z, .prim p => intAt z p
  | _, .float neg m b x, .prim .float32 =>
    some (.float32 (roundLiteral binary32 neg m b x).toUInt32)
  | _, .float neg m b x, .prim .float64 =>
    some (.float64 (roundLiteral binary64 neg m b x).toUInt64)
  | _, .text bs, .prim .text => (String.fromUTF8? ⟨bs.toArray⟩).map .text
  | _, .bool b, .prim .bool => some (.bool b)
  | _, .null, .prim .null => some .null
  | _, .principal p, .prim .principal => some (.principal p)
  | T, e, .ref r =>
    match e, T.lookup? r with
    | .null, some (.opt _) => some .null
    | .opt e, some (.opt t) => (elaborate T e t).map .opt
    | .vec es, some (.vec t) => (elaborateList T es t).map .vec
    | .blob bs, some (.vec (.prim .nat8)) => some (.vec (bs.map .nat8))
    | .record fs, some (.record gs) => do
      let given ← elaborateFields T fs gs
      let filled ← fillFields T (fs.map (·.1)) gs
      return .record (sortFields (given ++ filled))
    | .variant id e, some (.variant gs) => do
      let t ← fieldAt gs id
      return .variant id (← elaborate T e t)
    | .service p, some (.service _) => some (.service p)
    | .func p m, some (.func _ _ _) => some (.func p m)
    | _, _ => none
  | _, _, _ => none

def elaborateList : TypeTable → List Expr → Slot → Option (List Value)
  | _, [], _ => some []
  | T, e :: es, t => return (← elaborate T e t) :: (← elaborateList T es t)

/-- The expression's fields that the type has, elaborated; the others are ignored. -/
def elaborateFields : TypeTable → List (FieldId × Expr) → List (FieldId × Slot) →
    Option (List (FieldId × Value))
  | _, [], _ => some []
  | T, (id, e) :: fs, gs =>
    match fieldAt gs id with
    | some t => return (id, ← elaborate T e t) :: (← elaborateFields T fs gs)
    | none => elaborateFields T fs gs

end

mutual

/-- Every annotation in the expression holds (Section 5.1). -/
def wellAnnotated : Expr → Bool
  | .ann e te =>
    (match te.toTable? with
      | some ⟨S, s⟩ => (elaborate S e s.1).isSome
      | none => false) && wellAnnotated e
  | .opt e | .variant _ e => wellAnnotated e
  | .vec es => wellAnnotatedList es
  | .record fs => wellAnnotatedFields fs
  | .int _ | .float .. | .text _ | .bool _ | .null | .blob _
  | .principal _ | .service _ | .func _ _ => true

def wellAnnotatedList : List Expr → Bool
  | [] => true
  | e :: es => wellAnnotated e && wellAnnotatedList es

def wellAnnotatedFields : List (FieldId × Expr) → Bool
  | [] => true
  | (_, e) :: fs => wellAnnotated e && wellAnnotatedFields fs

end

/-- Arguments at their types, position by position (Section 5.9). Arguments beyond the
types are ignored, and types beyond the arguments must accept `null`. -/
def elaborateArgsFrom (T : TypeTable) : List Expr → List Slot → Option (List Value)
  | _, [] => some []
  | e :: es, t :: ts => return (← elaborate T e t) :: (← elaborateArgsFrom T es ts)
  | [], t :: ts => if T.acceptsNull t then (.null :: ·) <$> elaborateArgsFrom T [] ts else none

def elaborateArgs (T : TypeTable) (es : List Expr) (ts : List Slot) : Option (List Value) :=
  if es.all wellAnnotated then elaborateArgsFrom T es ts else none

/-- Text read as an argument sequence at `ts`, types in `T`: the values, or `none` when
it is rejected, whether by the parser or by elaboration. -/
def readArgs (src : String) (T : TypeTable) (ts : List Slot) : Option (List Value) :=
  match parseArgs src with
  | .ok es => elaborateArgs T es ts
  | .error _ => none

end Candid.Text
