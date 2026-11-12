/-
Hand-written `did` vectors: a description, and the interface it means, following
`lean/Spec/Did.md`. As in `Oracle/HandwrittenText.lean`, each expected interface is
written down from the document rather than computed by the model, and the ids say what
each case shows. Section numbers in the ids are the document's.

An expected interface is compared with the model's up to equivalence of types, so it is
written in whatever table shape reads best: a recursive type as one entry that refers to
itself, even where the description spells it as two names.

Where `candid` 0.10 answers differently, the document's Appendix A.2 says why; the
runner lists those vectors as known divergences.
-/

import Oracle.HandwrittenText

namespace Oracle

open Candid
open Candid.Slot
open Candid.Composite

def expectDid (text : String) (want : Option IfaceFixture) (id : String)
    (files : List (String × String) := []) : Vector :=
  ⟨s!"did: {id}", .did text files want⟩

/-- A description's expected types, without a service. -/
def defines (text : String) (m : TableM (List (String × Slot))) (id : String)
    (files : List (String × String) := []) : Vector :=
  let (types, entries) := m.run #[]
  expectDid text (some { table := { entries }, types, service := none }) id files

/-- A description's expected types and service declaration. -/
def declares (text : String) (m : TableM (List (String × Slot) × Option (List Slot) × Slot))
    (id : String) (files : List (String × String) := []) : Vector :=
  let ((types, init, s), entries) := m.run #[]
  expectDid text (some { table := { entries }, types, service := some (init, s) }) id files

def rejectsDid (text : String) (id : String) (files : List (String × String) := []) : Vector :=
  expectDid text none id files

/-- An entry that refers to itself: `f` is given the entry's own slot. -/
def recursive (f : Slot → Composite) : TableM Slot := do
  let entries ← get
  let self : Slot := .ref entries.size
  set (entries.push (f self))
  return self

/-- `func () -> ()`. -/
def unitFunc : TableM Slot := intern (.func [] [] [])

/-! ## Lexical structure (Section 3) -/

def didLexChecks : List Vector :=
  [ defines "/* a /* nested */ comment */ type A = nat; // to the end of the line"
      (return [("A", nat)]) "comments between tokens (3)"
  , defines "type A = record { \"opt\" : nat; \"my field\" : nat };"
      (return [("A", ← intern (recordOf [("opt", nat), ("my field", nat)]))])
      "a field named like a keyword, or not like an identifier, is written as text (3)"
  , rejectsDid "type A = record { opt : nat };" "a keyword is not a field name (3)"
  , rejectsDid "type opt = nat;" "a keyword is not a type name (3)"
  , defines "type query = record { query : nat; oneway : opt query }; \
      type F = func (query) -> () query;"
      (do
        -- Entry 0 is the record, entry 1 the option inside it.
        let q ← intern (recordOf [("query", nat), ("oneway", .ref 1)])
        let _ ← intern (.opt q)
        return [("query", q), ("F", ← intern (.func [q] [] [.query]))])
      "annotation names are identifiers elsewhere (3)"
  , rejectsDid "type A = nat; /* unclosed" "an unclosed block comment (3)" ]

/-! ## Types (Section 4) -/

def didPrimChecks : List Vector :=
  let names := ["bool", "nat", "int", "nat8", "nat16", "nat32", "nat64", "int8", "int16",
    "int32", "int64", "float32", "float64", "text", "reserved", "empty", "null", "principal"]
  let prims := [bool, nat, int, nat8, nat16, nat32, nat64, int8, int16, int32, int64,
    float32, float64, text, reserved, empty, null, principal]
  let text := String.join (names.map fun n => s!"type T_{n} = {n}; ")
  [ defines text (return (names.map ("T_" ++ ·)).zip prims) "every primitive type (4.2)"
  , defines "type B = blob;" (return [("B", ← intern (.vec nat8))]) "blob is vec nat8 (4.2)" ]

def didRecordChecks : List Vector :=
  [ defines "type A = record { nat; a : nat; text; 5 : bool; int };"
      (return [("A", ← intern (.record
        [(0, nat), (hashFieldName "a", nat), (hashFieldName "a" + 1, text), (5, bool), (6, int)]))])
      "positional fields are numbered from the field before (4.2)"
  , defines "type A = record { 0x2a : nat; };"
      (return [("A", ← intern (.record [(42, nat)]))]) "a hexadecimal label, and a trailing separator (4.1)"
  , defines "type A = record {}; type B = variant {};"
      (return [("A", ← intern (.record [])), ("B", ← intern (.variant []))])
      "an empty record and an empty variant (4.1)"
  , rejectsDid "type A = record { nat; 0 : text };" "a positional and a labelled field with one id (4.2)"
  , rejectsDid "type A = record { a : nat; a : text };" "a field name repeated (4.2)"
  , rejectsDid "type A = variant { a; a : nat };" "a variant alternative repeated (4.2)"
  , rejectsDid "type A = record { 4294967296 : nat };" "a label past 2^32 - 1 (4.2)"
  , rejectsDid "type A = record { 4294967295 : nat; nat };" "a positional field after id 2^32 - 1 (4.2)"
  , rejectsDid "type A = record { +1 : nat };" "a label is an integer literal without a sign (4.1)"
  , rejectsDid "type A = record { \"\\ff\" : nat };" "a field name that is not UTF-8 (4.2)"
  , defines "type A = variant { a; b : nat; \"c\"; 7 };"
      (return [("A", ← intern (.variant [(hashFieldName "a", null), (hashFieldName "b", nat),
        (hashFieldName "c", null), (7, null)]))])
      "a variant alternative without a type has type null (4.2)" ]

def didFuncChecks : List Vector :=
  [ defines "type F = func (nat, text) -> (bool); type Q = func () -> () query; \
      type C = func () -> () composite_query; type O = func () -> () oneway;"
      (return [ ("F", ← intern (.func [nat, text] [bool] []))
              , ("Q", ← intern (.func [] [] [.query]))
              , ("C", ← intern (.func [] [] [.compositeQuery]))
              , ("O", ← intern (.func [] [] [.oneway])) ])
      "function types, with each mode (4.1)"
  , defines "type F = func (x : nat, y : nat,) -> (x : nat);"
      (return [("F", ← intern (.func [nat, nat] [nat] []))])
      "parameter names have no meaning, and a parameter and a result may share one (4.2)"
  , rejectsDid "type F = func () -> () query oneway;" "two modes (6.3)"
  , rejectsDid "type F = func () -> () query query;" "an annotation twice (6.3)"
  , rejectsDid "type F = func () -> () update;" "a name after the results that is not an annotation (4.1)"
  , rejectsDid "type F = func (x : nat, x : text) -> ();" "a parameter name repeated (4.2)"
  , rejectsDid "type F = func () -> (r : nat, r : nat);" "a result name repeated (4.2)"
  , rejectsDid "type F = func (\"\\ff\" : nat) -> ();" "a parameter name that is not UTF-8 (4.2)" ]

def didServiceTypeChecks : List Vector :=
  [ defines "type S = service { m : (nat) -> (); \"a b\" : () -> () query; };"
      (return [("S", ← intern (.service
        [("m", ← intern (.func [nat] [] [])), ("a b", ← intern (.func [] [] [.query]))]))])
      "a service type, with a method named in text (4.1)"
  , rejectsDid "type S = service { m : () -> (); m : (nat) -> () };" "a method name repeated (4.2)"
  , rejectsDid "type S = service { m : func () -> () };"
      "a method's function type is written without func (4.1)"
  , rejectsDid "type S = service { \"\\ff\" : () -> () };" "a method name that is not UTF-8 (4.2)" ]

/-! ## Descriptions (Section 5) -/

def didDescChecks : List Vector :=
  [ defines "" (return []) "an empty description (5.1)"
  , defines "// only a comment" (return []) "a description of only a comment (5.1)"
  , defines "type A = nat" (return [("A", nat)]) "no semicolon after the last definition (5.1)"
  , rejectsDid "type A = nat type B = nat;" "a semicolon between definitions (5.1)"
  , rejectsDid "type A = nat;;" "two semicolons (5.1)"
  , rejectsDid ";" "a semicolon alone (5.1)"
  , declares "type A = nat service : {}"
      (return ([("A", nat)], none, ← intern (.service [])))
      "no semicolon between the last definition and the service (5.1)"
  , declares "service : {};" (return ([], none, ← intern (.service [])))
      "a semicolon after the service (5.1)"
  , rejectsDid "service : {};;" "two semicolons after the service (5.1)"
  , rejectsDid "service : {}; type A = nat;" "definitions come before the service (5.1)"
  , rejectsDid "service : {}; service : {}" "at most one service (5.1)"
  , declares "service my_service : { m : () -> () }"
      (return ([], none, ← intern (.service [("m", ← unitFunc)])))
      "the name of the service has no meaning (5.2)"
  , rejectsDid "service {}" "a service declaration has a colon (5.1)"
    -- No vector for `import`: the draft leaves it undefined, so neither answer conforms.
  , rejectsDid "type A = nat; type A = nat;" "a name defined twice (5.2)"
  , rejectsDid "type nat = text;" "a definition of a primitive type's name (5.2)"
  , rejectsDid "type reserved = nat; type A = record { reserved };"
      "a definition of a primitive type's name, used (5.2)"
  , declares "service : (nat, l : text) -> { m : () -> () }"
      (return ([], some [nat, text], ← intern (.service [("m", ← unitFunc)])))
      "a service constructor (5.2)"
  , declares "service : () -> {}" (return ([], some [], ← intern (.service [])))
      "a constructor with no arguments is still a constructor (5.2)"
  , rejectsDid "service : (x : nat, x : nat) -> {}" "a constructor's parameter name repeated (5.2)" ]

/-! ## Imports (Section 5.3)

The description being read is at `main.did`, and `files` holds the others by location. -/

def aNat : List (String × String) := [("a.did", "type A = nat;")]

/-- `a.did`, declaring a service with one method `n : (nat) -> ()`. -/
def aService : List (String × String) := [("a.did", "service : { n : (nat) -> () }")]

/-- A service of methods, each `(nat) -> ()` if named `n` and `() -> ()` otherwise. -/
def serviceNamed (names : List String) : TableM Slot := do
  let ms ← names.mapM fun m => do
    return (m, ← intern (.func (if m == "n" then [nat] else []) [] []))
  intern (.service ms)

def didImportChecks : List Vector :=
  [ defines "import \"a.did\"; type B = A;" (return [("A", nat), ("B", nat)])
      "an import brings in definitions (5.3)" (files := aNat)
  , defines "type B = A; import \"a.did\"" (return [("A", nat), ("B", nat)])
      "imports and definitions in any order (5.1)" (files := aNat)
  , defines "import \"sub/x.did\"; type T = X;" (return [("T", nat), ("X", nat), ("Y", nat)])
      "an import is relative to the description that contains it (5.3)"
      (files := [("sub/x.did", "import \"y.did\"; type X = Y;"), ("sub/y.did", "type Y = nat;")])
  , defines "import \"b.did\"; type T = A;" (return [("T", nat), ("A", nat)])
      "names are visible through indirect imports (5.3)"
      (files := [("b.did", "import \"a.did\";")] ++ aNat)
  , defines "import \"sub/../a.did\"; import \"a.did\";" (return [("A", nat)])
      "dot segments are removed, so two imports of one location read it once (5.3)"
      (files := aNat)
  , defines "import \"b.did\"; import \"c.did\";" (return [("A", nat)])
      "a description reached along two paths is included once (5.3)"
      (files := [("b.did", "import \"a.did\";"), ("c.did", "import \"a.did\";")] ++ aNat)
  , let n := 24
    defines "import \"f0.did\"; type T = F0;"
      (return ([("T", nat)] ++ (List.range n).map fun i => (s!"F{i}", nat)))
      "a chain of descriptions, each importing the next twice (5.3)"
      (files := (List.range n).map fun i =>
        (s!"f{i}.did", if i + 1 < n
          then s!"import \"f{i+1}.did\"; import \"f{i+1}.did\"; type F{i} = F{i+1};"
          else s!"type F{i} = nat;"))
  , rejectsDid "import \"a.did\"; type A = nat;" "a name defined in two descriptions (5.3)"
      (files := aNat)
  , rejectsDid "import \"a.did\"; type M = nat;" "an import cycle through the description being read (5.3)"
      (files := [("a.did", "import \"main.did\"; type A = nat;")])
  , rejectsDid "import \"main.did\"; type M = nat;" "a description that imports itself (5.3)"
  , rejectsDid "import \"a.did\";" "an import cycle among imported descriptions (5.3)"
      (files := [("a.did", "import \"b.did\"; type A = nat;"), ("b.did", "import \"a.did\"; type B = nat;")])
  , rejectsDid "import \"missing.did\";" "an import that cannot be fetched (5.3)"
  , rejectsDid "import \"a.did\";" "an imported description that does not parse (5.3)"
      (files := [("a.did", "type = ;")])
  , rejectsDid "import \"a.did\"; type M = nat;"
      "an imported description cannot use a name only its importer defines (5.3)"
      (files := [("a.did", "type A = M;")])
  , rejectsDid "import \"\\ff\";" "an import that is not UTF-8 (5.2)"
  , defines "import \"lib/b.did\"; type T = S;" (return [("T", nat), ("B", nat), ("S", nat)])
      "`..` in a path names the importer's parent directory (5.3)"
      (files := [("lib/b.did", "import \"../shared/s.did\"; type B = S;"),
                 ("shared/s.did", "type S = nat;")])
  , defines "import \"../shared/s.did\"; type T = S;" (return [("T", nat), ("S", nat)])
      "`..` above the directory of the description being read (5.3)"
      (files := [("../shared/s.did", "type S = nat;")])
  , defines "import \"a.did#x\";" (return [("A", nat)])
      "`#` is part of a file name (5.3)" (files := [("a.did#x", "type A = nat;")])
  , defines "import \"./sub//a.did\"; import \"sub/a.did\";" (return [("A", nat)])
      "`.` and empty segments are removed (5.3)" (files := [("sub/a.did", "type A = nat;")])
  , rejectsDid "import \"\"; type M = nat;" "an empty path names no file (5.3)"
  , declares "import service \"a.did\"; service : { m : () -> () }"
      (return ([], none, ← serviceNamed ["m", "n"]))
      "import service merges the imported service's methods (5.3)" (files := aService)
  , declares "import \"a.did\"; service : {}" (return ([], none, ← serviceNamed []))
      "a plain import contributes no methods (5.3)" (files := aService)
  , declares "import \"b.did\"; service : { m : () -> () }" (return ([], none, ← serviceNamed ["m"]))
      "a plain import contributes no methods, not even those its import imports (5.3)"
      (files := [("b.did", "import service \"a.did\";")] ++ aService)
  , declares "import service \"a.did\";" (return ([], none, ← serviceNamed ["n"]))
      "import service without a service declaration of one's own (5.3)" (files := aService)
  , declares "import service \"a.did\"; service : (text) -> { m : () -> () }"
      (return ([], some [text], ← serviceNamed ["m", "n"]))
      "a constructor keeps its arguments, and takes the imported methods (5.3)" (files := aService)
  , rejectsDid "import service \"a.did\";" "import service of a constructor (5.3)"
      (files := [("a.did", "service : (nat) -> { n : (nat) -> () }")])
  , rejectsDid "import service \"a.did\";" "import service of a description that provides no methods (5.3)"
      (files := aNat)
  , declares "import service \"b.did\";" (return ([], none, ← serviceNamed ["n"]))
      "import service of a description whose methods are all imported (5.3)"
      (files := [("b.did", "import service \"a.did\";")] ++ aService)
  , declares "import service \"b.did\"; service : { m : () -> () }"
      (return ([], none, ← serviceNamed ["m", "b", "n"]))
      "a chain of import service (5.3)"
      (files := [("b.did", "import service \"a.did\"; service : { b : () -> () }")] ++ aService)
  , declares "import service \"b.did\"; import service \"c.did\";"
      (return ([], none, ← serviceNamed ["b", "c", "n"]))
      "a diamond of import service merges each description's methods once (5.3)"
      (files := [("b.did", "import service \"a.did\"; service : { b : () -> () }"),
                 ("c.did", "import service \"a.did\"; service : { c : () -> () }")] ++ aService)
  , rejectsDid "import service \"a.did\"; service : { n : () -> () }"
      "two merged methods with one name (5.3)" (files := aService)
  , declares "import service \"a.did\";"
      (do
        let s ← serviceNamed ["n"]
        return ([("S", s)], none, s))
      "import service of a service declared by name (5.3)"
      (files := [("a.did", "type S = service { n : (nat) -> () }; service : S")]) ]

/-! ## Meaning (Section 6) -/

def didNameChecks : List Vector :=
  [ rejectsDid "type A = vec B;" "a name that is not defined (6.1)"
  , rejectsDid "type A = nat; type U = record { x : Missing };"
      "a name that is not defined, in a definition nothing uses (6.1)"
  , rejectsDid "type A = A;" "a name defined as itself (6.1)"
  , rejectsDid "type A = B; type B = A;" "two names defined as each other (6.1)"
  , rejectsDid "type A = B; type B = C; type C = B;" "a name that leads into a cycle (6.1)"
  , defines "type A = B; type B = C; type C = nat;"
      (return [("A", nat), ("B", nat), ("C", nat)]) "a chain of names (6.2)"
  , defines "type list = opt record { head : nat; tail : list };"
      (do
        -- Entry 0 is the option, entry 1 the record inside it.
        let l ← intern (.opt (.ref 1))
        let _ ← intern (recordOf [("head", nat), ("tail", l)])
        return [("list", l)])
      "a recursive type (6.1)"
  , defines "type A = opt B; type B = opt A;"
      (do let s ← recursive (.opt ·); return [("A", s), ("B", s)])
      "two names for the same recursive type (6.2)"
  , defines "type A = vec A; type B = record { B };"
      (do return [("A", ← recursive (.vec ·)), ("B", ← recursive fun b => .record [(0, b)])])
      "recursive types with no finite values are productive (6.1)"
  , defines "type F = func (F) -> (F);"
      (return [("F", ← recursive fun f => .func [f] [f] [])]) "a recursive function type (6.1)" ]

def didWellFormedChecks : List Vector :=
  [ declares "type T = func () -> (); type S = service { m : T }; service : S"
      (do let t ← unitFunc; let s ← intern (.service [("m", t)]); return ([("T", t), ("S", s)], none, s))
      "a method whose type is a name for a function type (6.3)"
  , declares "type A = B; type B = func () -> (); service : { m : A }"
      (do let f ← unitFunc; return ([("A", f), ("B", f)], none, ← intern (.service [("m", f)])))
      "a method whose type is a name for a name for a function type (6.3)"
  , rejectsDid "type S = service { m : T }; type T = opt nat;"
      "a method that is not a function, in a definition nothing uses (6.3)"
  , rejectsDid "type A = opt func () -> (); service : { m : A }" "a method that is an option (6.3)"
  , rejectsDid "type A = nat; service : { m : A }" "a method that is a primitive type (6.3)"
  , rejectsDid "type S = service { m : S };" "a method that is the service itself (6.3)"
  , rejectsDid "type F = func () -> (nat) oneway;" "a oneway function with a result (6.3)"
  , defines "type F = func (nat) -> () oneway;"
      (return [("F", ← intern (.func [nat] [] [.oneway]))]) "a oneway function with parameters (6.3)" ]

def didInterfaceChecks : List Vector :=
  [ declares "type S = service { m : () -> () }; service : S;"
      (do let s ← intern (.service [("m", ← unitFunc)]); return ([("S", s)], none, s))
      "a service declared by name (6.4)"
  , rejectsDid "type F = func () -> (); service : F" "a service declared as a function type (6.4)"
  , rejectsDid "type A = nat; service : A" "a service declared as a primitive type (6.4)"
  , rejectsDid "service : S" "a service declared by a name that is not defined (6.4)"
  , declares "type S = service { next : () -> (S) }; service : (S) -> S"
      (do
        -- Entry 0 is the service, entry 1 its method's type.
        let s ← intern (.service [("next", .ref 1)])
        let _ ← intern (.func [] [s] [])
        return ([("S", s)], some [s], s))
      "a constructor of a recursive service, taking one as its argument (6.4)"
  , rejectsDid "service : (Missing) -> {}" "a constructor argument that is not defined (6.4)" ]

def didChecks : List Vector :=
  didLexChecks ++ didPrimChecks ++ didRecordChecks ++ didFuncChecks ++ didServiceTypeChecks ++
  didDescChecks ++ didImportChecks ++ didNameChecks ++ didWellFormedChecks ++ didInterfaceChecks

end Oracle
