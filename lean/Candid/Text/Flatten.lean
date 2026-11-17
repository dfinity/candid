/-
Flattening: a nested type expression, as written, into entries of a type table.

Each composite becomes an entry, pushed after the entries of its parts, and the slot
that names it is returned. A name becomes the slot the environment gives it: in an
annotation the environment is empty, so a name is rejected; in a description
(`Candid/Did/Check.lean`) it is the slot reserved for the name's definition, which is how
a recursive type ends up as a cycle in the table rather than an infinite expansion.
-/

import Candid.Text.Parse

namespace Candid.Text

abbrev FlatM := ExceptT String (StateM (Array Composite))

def pushEntry (c : Composite) : FlatM Slot := do
  let entries ← get
  set (entries.push c)
  return .ref entries.size

section
variable (env : String → Option Slot)

mutual

def flatten : TypeExpr → FlatM Slot
  | .prim p => return .prim p
  | .name n => match env n with
    | some s => return s
    | none => throw s!"unbound type name {n}"
  | .opt t => do pushEntry (.opt (← flatten t))
  | .vec t => do pushEntry (.vec (← flatten t))
  | .record fs => do pushEntry (.record (← flattenFields fs))
  | .variant fs => do pushEntry (.variant (← flattenFields fs))
  | .func args rets ann => do pushEntry (.func (← flattenList args) (← flattenList rets) ann)
  | .service ms => do pushEntry (.service (← flattenMethods ms))

def flattenList : List TypeExpr → FlatM (List Slot)
  | [] => return []
  | t :: ts => return (← flatten t) :: (← flattenList ts)

def flattenFields : List (FieldId × TypeExpr) → FlatM (List (FieldId × Slot))
  | [] => return []
  | (id, t) :: fs => return (id, ← flatten t) :: (← flattenFields fs)

def flattenMethods : List (String × TypeExpr) → FlatM (List (String × Slot))
  | [] => return []
  | (m, t) :: ms => return (m, ← flatten t) :: (← flattenMethods ms)

end

end

/-- The table an annotation's type is flattened into, and its root. `none` if a name
appears, since an annotation's environment is empty, or the type is malformed: a
repeated field id, or a `oneway` function with results. -/
def TypeExpr.toTable? (t : TypeExpr) : Option ((T : TypeTable) × T.Root) :=
  match (flatten (fun _ => none) t).run.run #[] with
  | (.ok root, entries) => do
    let T ← ({ entries } : RawTypeTable).check
    let r ← T.root? root
    return ⟨T, r⟩
  | (.error _, _) => none

end Candid.Text
