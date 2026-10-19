/-
The reference executable.

    oracle                  check the model against every vector it has
    oracle write <dir>      write the vector files into <dir>
    oracle check <file>...  check vector files against the model

With no arguments it is the model's test suite, and what `lake test` runs. Every
vector is checked against the model, and also written and read back, so the JSON
reader and writer are tested on everything they will ever be asked to handle.

`write` is how `conformance/vectors/` is produced; CI writes them again and fails if
the committed files differ, so a change to the model shows up as a diff of the answers
it changed. `check` reads files as any other runner would, and is what makes those
files something the model can be held to rather than only something it emits.

Every mode exits nonzero on any failure.
-/

import Oracle

open Oracle

/-- The vector files, by name. -/
def files : List (String × List Vector) :=
  [ ("handwritten.json", handwritten)
  , ("subtype-primitives.json", Generate.primitives)
  , ("subtype-small.json", Generate.smallTypes) ]

/-- Ids that occur more than once. -/
def duplicateIds (vs : List Vector) : List String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut dups := #[]
  for v in vs do
    if seen.contains v.id then dups := dups.push v.id
    seen := seen.insert v.id
  return dups.toList

/-- Check vectors against the model, printing a line per failure. Returns the number
that failed. -/
def checkAll (vs : List Vector) (verbose : Bool) : IO Nat := do
  let mut failed := 0
  for v in vs do
    match v.assertion.disagreement with
    | none => if verbose then IO.println s!"ok    {v.id}"
    | some d =>
      IO.println s!"FAIL  {v.id} -- {d}"
      failed := failed + 1
  return failed

/-- Does a vector survive being written and read back? -/
def roundTrips (v : Vector) : Bool :=
  match Vector.fromJson? =<< Lean.Json.parse v.render with
  | .ok v' => v'.render == v.render
  | .error _ => false

def selfTest : IO UInt32 := do
  let all := files.flatMap (·.2)
  let mut problems := 0
  for g in Generate.malformed do
    IO.println s!"FAIL  generated type is malformed: {g}"
    problems := problems + 1
  for id in duplicateIds all do
    IO.println s!"FAIL  duplicate vector id: {id}"
    problems := problems + 1
  for v in all do
    unless roundTrips v do
      IO.println s!"FAIL  does not survive JSON: {v.id}"
      problems := problems + 1
  -- Hand-written vectors are listed one by one: their names are the documentation.
  -- Generated ones only fail if the JSON or the generator is broken, so a count will do.
  problems := problems + (← checkAll handwritten true)
  for (name, vs) in files.drop 1 do
    problems := problems + (← checkAll vs false)
    IO.println s!"ok    {vs.length} vectors in {name}"
  IO.println ""
  if problems == 0 then
    IO.println s!"{all.length} vectors agree with the model"
    return 0
  else
    IO.eprintln s!"{problems} problems"
    return 1

def writeFiles (dir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll dir
  for (name, vs) in files do
    IO.FS.writeFile (dir / name) (renderFile vs)
    IO.println s!"wrote {vs.length} vectors to {dir / name}"
  return 0

def checkFiles (paths : List String) : IO UInt32 := do
  let mut failed := 0
  let mut total := 0
  for path in paths do
    match parseFile (← IO.FS.readFile path) with
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      return 1
    | .ok vs =>
      for id in duplicateIds vs do
        IO.println s!"FAIL  {path}: duplicate vector id: {id}"
        failed := failed + 1
      failed := failed + (← checkAll vs false)
      total := total + vs.length
  if failed == 0 then
    IO.println s!"{total} vectors agree with the model"
    return 0
  else
    IO.eprintln s!"{failed} of {total} vectors failed"
    return 1

def usage : String :=
  "usage: oracle | oracle write <dir> | oracle check <file>..."

def main : List String → IO UInt32
  | [] => selfTest
  | ["write", dir] => writeFiles dir
  | "check" :: paths@(_ :: _) => checkFiles paths
  | _ => do IO.eprintln usage; return 2
