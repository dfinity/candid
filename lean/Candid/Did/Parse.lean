/-
The syntax of descriptions (`lean/Spec/Did.md`, Section 5): type definitions, then an
optional service declaration.

Types are parsed by the parser of `Candid/Text/Parse.lean`, which already reads them for
annotations; this adds the forms around them. Imports are kept as written, and expanded
by `Import.lean`.
-/

import Candid.Text.Parse

namespace Candid.Did

open Candid.Text

/-- A service declaration, `S` in Section 5.2: the service type, as a `methods` list or a
name, and the initialization arguments if it is a constructor. -/
structure ServiceDecl where
  init : Option (List TypeExpr)
  service : TypeExpr
  deriving Repr

/-- An import: whether it is `import service`, and the path it names. -/
structure Import where
  service : Bool
  ref : String
  deriving Repr

/-- A description, as parsed: imports and definitions in order, and the service
declaration. -/
structure Desc where
  imports : List Import := []
  defs : List (String × TypeExpr)
  service : Option ServiceDecl
  deriving Repr

/-- A `definition`: a type definition or an import. -/
inductive Item where
  | type (x : String) (t : TypeExpr)
  | imp (i : Import)

section
variable (ts : Array Token)

def fuel : Nat := 2 * ts.size + 2

/-- `"type" identifier "=" type`, after `type`. -/
def definition : P (String × TypeExpr) := do
  let x ← match ← next ts with
    | .ident x => pure x
    | t => throw s!"expected a type name, got {t.describe}"
  expect ts "="
  return (x, ← type ts (fuel ts))

/-- `"import" ["service"] text-literal`, after `import`. -/
def importDecl : P Import := do
  let service ← if (← peekAt ts 0) == some (.keyword "service") then
      modify (· + 1); pure true
    else pure false
  return { service, ref := ← liftE (utf8? (← textLit ts)) }

/-- Definitions, separated by `;`, with one after the last optional. -/
def definitions : Nat → P (List Item)
  | 0 => throw tooDeep
  | n + 1 => do
    let item? ← match ← peekAt ts 0 with
      | some (.keyword "type") =>
        modify (· + 1)
        let (x, t) ← definition ts
        pure (some (Item.type x t))
      | some (.keyword "import") =>
        modify (· + 1)
        pure (some (.imp (← importDecl ts)))
      | _ => pure none
    match item? with
    | none => return []
    | some d => if ← accept ts ";" then return d :: (← definitions n) else return [d]

/-- `service`, after the keyword: an optional name, then `:`, optional parameters and
`->`, and a `methods` list or a type name. -/
def serviceDecl : P ServiceDecl := do
  if let some (.ident _) := ← peekAt ts 0 then modify (· + 1)
  expect ts ":"
  let init ← if ← isPunct ts "(" then
      let ps ← params ts (fuel ts)
      expect ts "->"
      pure (some ps)
    else pure none
  let service ← if ← isPunct ts "{" then
      pure (TypeExpr.service (← methods ts (fuel ts)))
    else match ← next ts with
      | .ident x => pure (.name x)
      | t => throw s!"expected a service type, got {t.describe}"
  return { init, service }

/-- `description`, and nothing after it. -/
def description : P Desc := do
  let items ← definitions ts (ts.size + 1)
  let imports := items.filterMap fun | .imp i => some i | .type .. => none
  let defs := items.filterMap fun | .type x t => some (x, t) | .imp _ => none
  let service ← if (← peekAt ts 0) == some (.keyword "service") then
      modify (· + 1)
      let s ← serviceDecl ts
      let _ ← accept ts ";"
      pure (some s)
    else pure none
  if (← get) < ts.size then throw s!"unexpected {(← next ts).describe}"
  return { imports, defs, service }

end

def parseDesc (src : String) : Except String Desc := do
  let ts ← lex src
  (description ts).run' 0

end Candid.Did
