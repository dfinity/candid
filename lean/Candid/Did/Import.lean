/-
Imports (`lean/Spec/Did.md`, Section 5.3): a description and those it imports, expanded
into one description without imports, which `Check.lean` then gives its meaning.

**Locations** are absolute URIs, compared as strings once resolved. An import's
reference is resolved against the location of the description that contains it by RFC
3986, Section 5.2: `resolveRef` follows the RFC's algorithm step by step, including its
removal of `.` and `..` segments, and drops the fragment, which is not part of a
location. `Files`, the descriptions the environment can fetch, may name them by absolute
URI or by a path, which is taken relative to `file:///`, as is the description being
read, at `main.did`.

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

/-- A URI reference split into its five components, by the regular expression of RFC
3986, Appendix B. An absent component is `none`, which differs from an empty one. -/
structure UriRef where
  scheme : Option String
  authority : Option String
  path : String
  query : Option String
  fragment : Option String

/-- Split `s` at the first character in `stops`: the part before it, and the rest from
it on. -/
def splitAtAny (s : String) (stops : List Char) : String × String :=
  let cs := s.toList
  let before := cs.takeWhile (!stops.contains ·)
  (String.ofList before, String.ofList (cs.drop before.length))

def UriRef.parse (s : String) : UriRef :=
  -- `scheme ":"`, if the text before the first of `:/?#` is nonempty and ends at `:`.
  let (pre, rest) := splitAtAny s [':', '/', '?', '#']
  let (scheme, s) :=
    if !pre.isEmpty && rest.startsWith ":" then (some pre, (rest.drop 1).toString) else (none, s)
  -- `"//" authority`, up to the first of `/?#`.
  let (authority, s) :=
    if s.startsWith "//" then
      let (a, r) := splitAtAny (s.drop 2).toString ['/', '?', '#']
      (some a, r)
    else (none, s)
  let (path, s) := splitAtAny s ['?', '#']
  let (query, s) :=
    if s.startsWith "?" then
      let (q, r) := splitAtAny (s.drop 1).toString ['#']
      (some q, r)
    else (none, s)
  let fragment := if s.startsWith "#" then some (s.drop 1).toString else none
  { scheme, authority, path, query, fragment }

/-- The text before the last `/`, if there is one. -/
def beforeLastSlash (s : String) : Option String :=
  match s.toList.reverse.dropWhile (· != '/') with
  | [] => none
  | _ :: rest => some (String.ofList rest.reverse)

/-- Remove the last segment of `out`, and the `/` before it: RFC 3986, Section 5.2.4,
step 2C. -/
def dropLastSegment (out : String) : String := (beforeLastSlash out).getD ""

/-- RFC 3986, Section 5.2.4, `remove_dot_segments`, step by step. Every step shortens
the input, so its length is enough fuel. -/
def removeDotSegments (input : String) : String :=
  go input.length input ""
where
  go : Nat → String → String → String
  | 0, _, out => out
  | n + 1, inp, out =>
    if inp.isEmpty then out
    else if inp.startsWith "../" then go n (inp.drop 3).toString out
    else if inp.startsWith "./" then go n (inp.drop 2).toString out
    else if inp.startsWith "/./" then go n ("/" ++ (inp.drop 3).toString) out
    else if inp == "/." then go n "/" out
    else if inp.startsWith "/../" then go n ("/" ++ (inp.drop 4).toString) (dropLastSegment out)
    else if inp == "/.." then go n "/" (dropLastSegment out)
    else if inp == "." || inp == ".." then out
    else
      -- Move the first segment, with its leading `/` if any, to the output.
      let lead := if inp.startsWith "/" then "/" else ""
      let (seg, rest) := splitAtAny (inp.drop lead.length).toString ['/']
      go n rest (out ++ lead ++ seg)

/-- RFC 3986, Section 5.2.3: merge a relative path with the base's. -/
def mergePaths (base : UriRef) (path : String) : String :=
  if base.authority.isSome && base.path.isEmpty then "/" ++ path
  else match beforeLastSlash base.path with
    | some dir => dir ++ "/" ++ path
    | none => path

/-- RFC 3986, Section 5.3, without the fragment. -/
def UriRef.recompose (u : UriRef) : String :=
  (u.scheme.map (· ++ ":")).getD "" ++ (u.authority.map ("//" ++ ·)).getD "" ++ u.path ++
    (u.query.map ("?" ++ ·)).getD ""

/-- RFC 3986, Section 5.2.2: the location `ref` denotes, written in the description at
the location `base`, an absolute URI. The fragment is dropped. -/
def resolveRef (base ref : String) : String :=
  let b := UriRef.parse base
  let r := UriRef.parse ref
  let t : UriRef :=
    if r.scheme.isSome then { r with path := removeDotSegments r.path }
    else if r.authority.isSome then
      { r with scheme := b.scheme, path := removeDotSegments r.path }
    else if r.path.isEmpty then
      { b with query := if r.query.isSome then r.query else b.query }
    else if r.path.startsWith "/" then
      { b with path := removeDotSegments r.path, query := r.query }
    else
      { b with path := removeDotSegments (mergePaths b r.path), query := r.query }
  t.recompose

/-- A location as `Files` may write it: an absolute URI as it is, and a path relative to
`file:///`. -/
def absolute (loc : String) : String :=
  if (UriRef.parse loc).scheme.isSome then loc else resolveRef "file:///" loc

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

/-- The descriptions reachable from `todo` by following `edge`, besides those in `seen`,
each visited once. Each step either pops a location already seen or marks one seen, so
the locations plus all their imports are enough fuel. -/
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
  let files := files.map fun (l, t) => (absolute l, t)
  let rootLoc := absolute rootLoc
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
