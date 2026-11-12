/-
What a description means (`lean/Spec/Did.md`, Section 6): an interface.

**The table.** Every definition whose right-hand side is a composite type, such as
`type list = opt record { head : nat; tail : list }`, owns one entry of the table,
reserved before anything is flattened, so that a name can refer to its entry before the
entry is written: that is how recursion becomes a cycle in the table. A definition that
is a primitive, or another name, owns nothing; its name denotes whatever the chain of
names reaches (`resolveName`).

Each owned entry is then filled by flattening the definition's right-hand side. Flattening
pushes the outermost composite last, so it is popped off the end and moved into the
reserved entry; nothing can refer to it at the end, since a part is pushed before the
whole that contains it.

**Productivity** (Section 6.1) is a chain of names that never reaches anything else. With
*n* definitions, a chain that is still a name after *n* steps has repeated one, so
`resolveName` takes *n* as its fuel and running out is the rejection, not a bound.

**Well-formedness** (Section 6.3) is the table's: `RawTypeTable.check` rejects a method
that is not a function and a `oneway` function with results, in every entry, whether a
root refers to it or not. Every definition is in the table, so every definition is
checked.
-/

import Candid.Did.Import
import Candid.Text.Flatten

namespace Candid.Did

open Candid.Text

/-- The meaning of a description (Section 6.4), as slots in one table. -/
structure Interface where
  table : TypeTable
  /-- Each defined name, in the order defined, and the type it denotes. -/
  types : List (String × Slot)
  /-- The service declaration: none, a service, or a constructor with its
  initialization arguments. -/
  service : Option (Option (List Slot) × Slot)

def ownsEntry : TypeExpr → Bool
  | .name _ | .prim _ => false
  | _ => true

/-- The slot a defined name denotes. `owned` gives the reserved entry of each name whose
definition is composite. -/
def resolveName (defs : List (String × TypeExpr)) (owned : String → Option Slot) :
    Nat → String → Except String Slot
  | 0, x => throw s!"type name {x} is not productive"
  | n + 1, x =>
    match defs.lookup x with
    | none => throw s!"unbound type name {x}"
    | some (.name y) => resolveName defs owned n y
    | some (.prim p) => return .prim p
    | some _ => match owned x with
      | some s => return s
      | none => throw s!"unreachable: {x} owns no entry"

/-- Flatten each composite definition into the entry reserved for it. -/
def fillEntries (env : String → Option Slot) : List (Nat × TypeExpr) → FlatM Unit
  | [] => return
  | (k, t) :: rest => do
    let _ ← flatten env t
    let entries ← get
    match entries.back? with
    | some c => set (entries.pop.setIfInBounds k c)
    | none => throw "unreachable: flattening a composite pushed nothing"
    fillEntries env rest

def checkDesc (d : Desc) : Except String Interface := do
  let names := d.defs.map (·.1)
  unless noDups names do throw "a type name is defined twice"
  if let some x := names.find? (primOfName? · |>.isSome) then
    throw s!"{x} is the name of a primitive type"
  let owners := (d.defs.filter (ownsEntry ·.2))
  let owned (x : String) : Option Slot :=
    (owners.findIdx? (·.1 == x)).map .ref
  let slots ← names.mapM (resolveName d.defs owned d.defs.length)
  let types := names.zip slots
  let env (x : String) := types.lookup x
  let build : FlatM (Option (Option (List Slot) × Slot)) := do
    set (Array.replicate owners.length (Composite.record []))
    fillEntries env ((List.range owners.length).zip (owners.map (·.2)))
    d.service.mapM fun s => do
      let init ← s.init.mapM (flattenList env)
      return (init, ← flatten env s.service)
  let (result, entries) := build.run.run #[]
  let service ← result
  let some table := ({ entries } : RawTypeTable).check
    | throw "a type is not well-formed: a method that is not a function, or a oneway function with results"
  if let some (_, s) := service then
    match s with
    | .ref r => match table.lookup? r with
      | some (.service _) => pure ()
      | _ => throw "the service declaration is not a service type"
    | .prim _ => throw "the service declaration is not a service type"
  return { table, types, service }

/-- The interface of the description `src`, read at `rootLocation` with the environment
`files` to fetch its imports from, or why it is rejected. -/
def checkDescIn (files : Files) (src : String) : Except String Interface :=
  expand ((rootLocation, src) :: files) >>= checkDesc

/-- As `checkDescIn`, `none` when the description is rejected. -/
def readDescIn (files : Files) (src : String) : Option Interface :=
  (checkDescIn files src).toOption

/-- A description with nothing to import from. -/
def readDesc (src : String) : Option Interface := readDescIn [] src

end Candid.Did
