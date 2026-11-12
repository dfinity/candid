/-
The syntax of descriptions (`lean/Spec/Did.md`, Section 5): type definitions, then an
optional service declaration.

Types are parsed by the parser of `Candid/Text/Parse.lean`, which already reads them for
annotations; this adds the two forms around them. Imports are outside the draft, so a
description with one is rejected here.
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

/-- A description, as parsed: definitions in order, and the service declaration. -/
structure Desc where
  defs : List (String × TypeExpr)
  service : Option ServiceDecl
  deriving Repr

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

/-- Definitions, separated by `;`, with one after the last optional. -/
def definitions : Nat → P (List (String × TypeExpr))
  | 0 => throw tooDeep
  | n + 1 => do
    match ← peekAt ts 0 with
    | some (.keyword "type") =>
      modify (· + 1)
      let d ← definition ts
      if ← accept ts ";" then return d :: (← definitions n) else return [d]
    | some (.keyword "import") => throw "imports are outside this draft (Did.md, Section 5.1)"
    | _ => return []

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
  let defs ← definitions ts (ts.size + 1)
  let service ← if (← peekAt ts 0) == some (.keyword "service") then
      modify (· + 1)
      let s ← serviceDecl ts
      let _ ← accept ts ";"
      pure (some s)
    else pure none
  if (← get) < ts.size then throw s!"unexpected {(← next ts).describe}"
  return { defs, service }

end

def parseDesc (src : String) : Except String Desc := do
  let ts ← lex src
  (description ts).run' 0

end Candid.Did
