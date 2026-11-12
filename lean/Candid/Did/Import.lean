/-
Imports (`lean/Spec/Did.md`, Section 5.3): a description and those it imports, expanded
into one description without imports, which `Check.lean` then gives its meaning.

**Locations** are paths, segments separated by `/`, which is what a URI reference without
a scheme or authority is. An import is resolved against the directory of the description
that contains it, and `.` and `..` segments are removed (RFC 3986, Section 5.2.4), so
every location is in one normal form and equal locations are equal strings. The
environment is `Files`, the descriptions it can fetch by location.

**Loading** is a depth-first walk from the description being read, carrying the path
from it. A location on that path is a cycle. One already loaded by another path is not
read again. The walk records each description after those it imports.

**Methods** are counted by the description they come from (`provides`): the set of
descriptions whose own service declarations contribute, reached through `import
service` edges alone. A description two paths reach is in the set once, so a diamond of
`import service` merges its methods once, and a plain `import` never adds to the set.
-/

import Candid.Did.Parse

namespace Candid.Did

open Candid.Text

/-- The descriptions the environment can fetch, by location. -/
abbrev Files := List (String × String)

/-- The location of the description being read. -/
def rootLocation : String := "main.did"

/-- Remove `.` and `..` segments, as RFC 3986, Section 5.2.4, does: `..` removes the
segment before it, if any. -/
def removeDots (segs : List String) : List String :=
  (segs.foldl (fun acc s =>
    if s == "." then acc
    else if s == ".." then acc.drop 1
    else s :: acc) []).reverse

/-- Resolve `ref` against the location `base`: an absolute path is taken as it is, and a
relative one is taken from the directory of `base`. -/
def resolveRef (base ref : String) : String :=
  if ref.startsWith "/" then
    "/" ++ "/".intercalate (removeDots ((ref.drop 1).toString.splitOn "/"))
  else
    let dir := (base.splitOn "/").dropLast
    let path := "/".intercalate (removeDots (dir ++ ref.splitOn "/"))
    if base.startsWith "/" && !path.startsWith "/" then "/" ++ path else path

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

/-- A description as loaded: its location, its parse, and the locations of its imports,
resolved, with whether each is `import service`. -/
structure Loaded where
  loc : String
  desc : Desc
  imports : List (Bool × String)

def Loaded.importsResolved (loc : String) (d : Desc) : List (Bool × String) :=
  d.imports.map fun i => (i.service, resolveRef loc i.ref)

/-- Load `loc` and everything it imports into `done`, each after its imports. `path` is
the chain of imports from the description being read to `loc`. The fuel is the number of
descriptions the environment has: a path longer than that repeats a location, which the
cycle check rejects first. -/
def load (files : Files) : Nat → List String → List Loaded → String → Except String (List Loaded)
  | 0, _, _, loc => throw s!"unreachable: the import graph ran out of fuel at {loc}"
  | n + 1, path, done, loc => do
    if path.contains loc then throw s!"an import cycle through {loc}"
    if done.any (·.loc == loc) then return done
    let some text := files.lookup loc | throw s!"cannot fetch {loc}"
    let d ← parseDesc text
    let imports := Loaded.importsResolved loc d
    let mut acc := done
    for (_, l) in imports do
      acc ← load files n (loc :: path) acc l
    return acc ++ [{ loc, desc := d, imports }]

/-- `loc` and every description it imports, directly or indirectly, following `edge`. -/
def reach (all : List Loaded) (edge : Bool → Bool) : Nat → String → List String
  | 0, _ => []
  | n + 1, loc =>
    match all.find? (·.loc == loc) with
    | none => []
    | some l => (l.imports.filter (edge ·.1)).foldl
        (fun acc (_, m) => acc ++ (reach all edge n m).filter (!acc.contains ·)) [loc]

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
  let all ← load files (files.length + 1) [] [] rootLoc
  let fuel := all.length + 1
  let defs := all.flatMap (·.desc.defs)
  let defined (l : Loaded) := (reach all (fun _ => true) fuel l.loc).flatMap fun m =>
    ((all.find? (·.loc == m)).map (·.desc.defs.map (·.1))).getD []
  for l in all do
    if let some x := l.desc.names.find? (!(defined l).contains ·) then
      throw s!"{l.loc} uses {x}, which neither it nor its imports define"
  -- The descriptions whose own service declarations a description's methods come from.
  let provides (loc : String) : List String :=
    (reach all id fuel loc).filter fun m => ((all.find? (·.loc == m)).bind (·.desc.service)).isSome
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
