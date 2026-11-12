/-
Imports (`lean/Spec/Did.md`, Section 5.3): a description and those it imports, expanded
into one description without imports, which `Check.lean` then gives its meaning.

**Paths** name descriptions, segments separated by `/`. An import's path is resolved
against the directory of the description that contains it, and normalized textually
(`normalize`), so equal files have equal paths. `..` with nothing before it stays in a
relative path, naming the parent directory. `Files`, the descriptions the environment
can read, is keyed by path, normalized the same way; the description being read is
`main.did`.

**Loading** is a depth-first walk from the description being read, carrying the chain
of imports that led to the current one. A description already in that chain is a cycle.
One already loaded along another chain is not read again. The walk records each
description after those it imports.

**Methods** are counted by the description they come from (`provides`): the set of
descriptions whose own service declarations contribute, reached through `import
service` edges alone. A description two chains reach is in the set once, so a diamond of
`import service` merges its methods once, and a plain `import` never adds to the set.
-/

import Candid.Did.Parse

namespace Candid.Did

open Candid.Text

/-- The descriptions the environment can read, by path. -/
abbrev Files := List (String × String)

/-- The path of the description being read. -/
def rootLocation : String := "main.did"

/-- The text before the last `/`, if there is one. -/
def beforeLastSlash (s : String) : Option String :=
  match s.toList.reverse.dropWhile (· != '/') with
  | [] => none
  | _ :: rest => some (String.ofList rest.reverse)

/-- Remove `.` and empty segments, and let `..` remove the segment before it, unless that
is `..` too. With nothing before it, `..` stays in a relative path and is dropped from an
absolute one. -/
def normalizeSegments (absolute : Bool) (segs : List String) : List String :=
  (segs.foldl (fun acc s =>
    if s == "." || s.isEmpty then acc
    else if s == ".." then
      match acc with
      | top :: rest => if top == ".." then s :: acc else rest
      | [] => if absolute then [] else [s]
    else s :: acc) []).reverse

/-- A path in normal form (`lean/Spec/Did.md`, Section 5.3). -/
def normalize (p : String) : String :=
  let absolute := p.startsWith "/"
  let body := "/".intercalate (normalizeSegments absolute (p.splitOn "/"))
  if absolute then "/" ++ body else body

/-- The path an import `ref` names, in the description at the normalized path `base`. -/
def resolvePath (base ref : String) : Except String String := do
  if ref.isEmpty then throw "an empty import names no file"
  if ref.startsWith "/" then return normalize ref
  let dir := match beforeLastSlash base with
    | some d => d ++ "/"
    | none => ""
  return normalize (dir ++ ref)

mutual

/-- The type names a type expression uses. -/
def typeNames : TypeExpr → List String
  | .prim _ => []
  | .name n => [n]
  | .opt t | .vec t => typeNames t
  | .record fs | .variant fs => fieldNames fs
  | .func args rets _ => listNames args ++ listNames rets
  | .service ms => methodNames ms

def listNames : List TypeExpr → List String
  | [] => []
  | t :: ts => typeNames t ++ listNames ts

def fieldNames : List (FieldId × TypeExpr) → List String
  | [] => []
  | (_, t) :: fs => typeNames t ++ fieldNames fs

def methodNames : List (String × TypeExpr) → List String
  | [] => []
  | (_, t) :: ms => typeNames t ++ methodNames ms

end

/-- Every type name a description uses, in its definitions and its service declaration. -/
def Desc.names (d : Desc) : List String :=
  listNames (d.defs.map (·.2)) ++
    match d.service with
    | none => []
    | some s => listNames (s.init.getD []) ++ typeNames s.service

/-- A description as loaded: its path, its parse, and the paths of its imports,
resolved, with whether each is `import service`. -/
structure Loaded where
  loc : String
  desc : Desc
  imports : List (Bool × String)

def Loaded.importsResolved (loc : String) (d : Desc) : Except String (List (Bool × String)) :=
  d.imports.mapM fun i => return (i.service, ← resolvePath loc i.ref)

/-- Load `loc` and everything it imports into `done`, each after its imports. `path` is
the chain of imports from the description being read to `loc`. The fuel is the number of
descriptions the environment has: a chain longer than that repeats a description, which
the cycle check rejects first. -/
def load (files : Files) : Nat → List String → List Loaded → String → Except String (List Loaded)
  | 0, _, _, loc => throw s!"unreachable: the import graph ran out of fuel at {loc}"
  | n + 1, path, done, loc => do
    if path.contains loc then throw s!"an import cycle through {loc}"
    if done.any (·.loc == loc) then return done
    let some text := files.lookup loc | throw s!"cannot read {loc}"
    let d ← parseDesc text
    let imports ← Loaded.importsResolved loc d
    let mut acc := done
    for (_, l) in imports do
      acc ← load files n (loc :: path) acc l
    return acc ++ [{ loc, desc := d, imports }]

/-- The descriptions reachable from `todo` by following `edge`, besides those in `seen`,
each visited once. Each step either pops a path already seen or marks one seen, so
the descriptions plus all their imports are enough fuel. -/
def reachFrom (all : List Loaded) (edge : Bool → Bool) :
    Nat → List String → List String → List String
  | 0, seen, _ => seen
  | _, seen, [] => seen
  | n + 1, seen, loc :: todo =>
    if seen.contains loc then reachFrom all edge n seen todo
    else
      let next := ((all.find? (·.loc == loc)).map fun l =>
        (l.imports.filter (edge ·.1)).map (·.2)).getD []
      reachFrom all edge n (seen ++ [loc]) (next ++ todo)

/-- `loc` and every description it imports, directly or indirectly, following `edge`. -/
def reach (all : List Loaded) (edge : Bool → Bool) (loc : String) : List String :=
  reachFrom all edge (all.length + (all.map (·.imports.length)).sum + 1) [] [loc]

/-- The methods a description's own service declaration lists: written out, or those of
the service type a name resolves to among `defs`. -/
def ownMethods (defs : List (String × TypeExpr)) : Nat → TypeExpr →
    Except String (List (String × TypeExpr))
  | _, .service ms => return ms
  | n + 1, .name x => match defs.lookup x with
    | some t => ownMethods defs n t
    | none => throw s!"unbound type name {x}"
  | 0, .name x => throw s!"type name {x} is not productive"
  | _, _ => throw "an imported service declaration is not a service type"

/-- The expansion of the description at `rootLoc`, given the environment. -/
def expandAt (files : Files) (rootLoc : String) : Except String Desc := do
  let files := files.map fun (l, t) => (normalize l, t)
  let rootLoc := normalize rootLoc
  let all ← load files (files.length + 1) [] [] rootLoc
  let defs := all.flatMap (·.desc.defs)
  for l in all do
    let defined := (reach all (fun _ => true) l.loc).flatMap fun m =>
      ((all.find? (·.loc == m)).map (·.desc.defs.map (·.1))).getD []
    if let some x := l.desc.names.find? (!defined.contains ·) then
      throw s!"{l.loc} uses {x}, which neither it nor its imports define"
  -- The descriptions whose own service declarations a description's methods come from.
  let provides (loc : String) : List String :=
    (reach all id loc).filter fun m => ((all.find? (·.loc == m)).bind (·.desc.service)).isSome
  let methodsOf (loc : String) : Except String (List (String × TypeExpr)) := do
    let ms ← (provides loc).flatMapM fun m => do
      match (all.find? (·.loc == m)).bind (·.desc.service) with
      | some s => ownMethods defs (defs.length + 1) s.service
      | none => return []
    unless noDups (ms.map (·.1)) do throw s!"{loc} merges two methods with one name"
    return ms
  for l in all do
    for (svc, m) in l.imports do
      if svc then
        let some e := all.find? (·.loc == m) | throw s!"unreachable: {m} was not loaded"
        if (provides m).isEmpty then throw s!"{m} is imported as a service, and provides none"
        if (e.desc.service.bind (·.init)).isSome then
          throw s!"{m} is imported as a service, and declares a constructor"
    let _ ← methodsOf l.loc
  let some root := all.find? (·.loc == rootLoc)
    | throw "unreachable: the description being read was not loaded"
  let service ← if root.imports.any (·.1) then
      pure (some { init := root.desc.service.bind (·.init),
                   service := .service (← methodsOf rootLoc) })
    else pure root.desc.service
  return { defs, service }

/-- The expansion of the description at `rootLocation`. -/
def expand (files : Files) : Except String Desc := expandAt files rootLocation

end Candid.Did
