/-
The syntax of textual values (`lean/Spec/TextValues.md`, Section 4), and of the types
that annotations contain.

Parsing produces the abstract syntax of Section 4.2: `Expr`, with every field id
explicit. Labels are hashed, positional fields numbered, and a record that repeats an id
is rejected here, since that does not depend on the type. A type in an annotation is
parsed into `TypeExpr`, which is nested, as written; `Elab.lean` flattens it into a type
table.

The parser is recursive descent over the tokens. Each function takes `fuel`, which
bounds the depth of the calls. Along any chain of calls, every second call at most
consumes a token first, so twice the number of tokens, plus a little, is never exhausted.
-/

import Candid.Text.Lex
import Candid.Principal

namespace Candid.Text

/-- A type as written in an annotation. Names are kept: resolving them is the
environment's business, and the model's environment is empty. -/
inductive TypeExpr where
  | prim (p : Prim)
  | name (n : String)
  | opt (t : TypeExpr)
  | vec (t : TypeExpr)
  | record (fs : List (FieldId × TypeExpr))
  | variant (fs : List (FieldId × TypeExpr))
  | func (args rets : List TypeExpr) (annots : List FuncAnnot)
  | service (methods : List (String × TypeExpr))
  deriving Repr, Inhabited

/-- An expression: the abstract syntax of Section 4.2. -/
inductive Expr where
  | int (z : Int)
  | float (neg : Bool) (m : Nat) (binary : Bool) (exp : Int)
  | text (bytes : List UInt8)
  | bool (b : Bool)
  | null
  | opt (e : Expr)
  | vec (es : List Expr)
  | blob (bytes : List UInt8)
  /-- Field ids distinct, in the order written. -/
  | record (fs : List (FieldId × Expr))
  | variant (id : FieldId) (e : Expr)
  | principal (p : PrincipalBytes)
  | service (p : PrincipalBytes)
  | func (p : PrincipalBytes) (method : String)
  | ann (e : Expr) (t : TypeExpr)
  deriving Repr, Inhabited

/-- Primitive types that are spelled as identifiers. `null` and `principal` are keywords,
and are parsed as such. -/
def primOfName? : String → Option Prim
  | "bool" => some .bool | "nat" => some .nat | "int" => some .int
  | "nat8" => some .nat8 | "nat16" => some .nat16 | "nat32" => some .nat32
  | "nat64" => some .nat64 | "int8" => some .int8 | "int16" => some .int16
  | "int32" => some .int32 | "int64" => some .int64
  | "float32" => some .float32 | "float64" => some .float64
  | "text" => some .text | "reserved" => some .reserved | "empty" => some .empty
  | _ => none

def utf8? (bs : List UInt8) : Except String String :=
  match String.fromUTF8? ⟨bs.toArray⟩ with
  | some s => .ok s
  | none => .error "a name must be UTF-8"

/-- A `label`, if the token is one: an integer literal without a sign below 2^32, or a
name, hashed. -/
def labelOf? : Token → Option (Except String FieldId)
  | .int z false => some (if z < 2 ^ 32 then .ok z.toNat.toUInt32 else .error "field id out of range")
  | .ident s => some (.ok (hashFieldName s))
  | .text bs => some ((utf8? bs).map hashFieldName)
  | _ => none

/-- A `name`, if the token is one. -/
def nameOf? : Token → Option (Except String String)
  | .ident s => some (.ok s)
  | .text bs => some (utf8? bs)
  | _ => none

/-- Number positional fields, given the id of the field before, if any. -/
def numberFrom (prev : Option FieldId) :
    List (Option FieldId × α) → Except String (List (FieldId × α))
  | [] => return []
  | (some id, x) :: rest => return (id, x) :: (← numberFrom (some id) rest)
  | (none, x) :: rest => do
    let id ← match prev with
      | none => pure 0
      | some p =>
        if p == 0xFFFFFFFF then throw "a positional field after id 2^32 - 1" else pure (p + 1)
    return (id, x) :: (← numberFrom (some id) rest)

/-- Give positional fields their ids, then reject a repeated one. A positional field
takes 0 first, and one more than the field before it otherwise. -/
def numberFields (fs : List (Option FieldId × α)) : Except String (List (FieldId × α)) := do
  let numbered ← numberFrom none fs
  unless noDups (numbered.map (·.1)) do throw "a field id is repeated"
  return numbered

abbrev P := StateT Nat (Except String)

section
variable (ts : Array Token)

def peekAt (k : Nat) : P (Option Token) := do return ts[(← get) + k]?

def next : P Token := do
  match ts[← get]? with
  | some t => modify (· + 1); return t
  | none => throw "unexpected end of input"

def isPunct (p : String) : P Bool := do return (← peekAt ts 0) == some (.punct p)

/-- Take the punctuation `p` if it is next. -/
def accept (p : String) : P Bool := do
  if ← isPunct ts p then modify (· + 1); return true else return false

def expect (p : String) : P Unit := do
  let t ← next ts
  unless t == .punct p do throw s!"expected `{p}`, got {t.describe}"

def liftE (x : Except String α) : P α := StateT.lift x

def tooDeep : String := "unreachable: the parser ran out of fuel"

/-- After the opening punctuation of a list: items separated by `sep`, optionally
ending with one, up to `close`. -/
def sepBy (item : P α) (sep close : String) : Nat → P (List α)
  | 0 => throw tooDeep
  | n + 1 => do
    if ← accept ts close then return []
    let x ← item
    if ← accept ts sep then return x :: (← sepBy item sep close n)
    expect ts close
    return [x]

/-- A function type's mode, if one follows. At most one is allowed
(`lean/Spec/Did.md`, Section 4.1). -/
def mode : P (List FuncAnnot) := do
  let a? := match ← peekAt ts 0 with
    | some (.keyword "query") => some FuncAnnot.query
    | some (.keyword "oneway") => some .oneway
    | some (.keyword "composite_query") => some .compositeQuery
    | _ => none
  match a? with
  | some a => modify (· + 1); return [a]
  | none => return []

/-- A parameter list's names must not repeat; the names are then dropped. -/
def dropNames (xs : List (Option String × TypeExpr)) : P (List TypeExpr) := do
  unless noDups (xs.filterMap (·.1)) do throw "a parameter or result name is repeated"
  return xs.map (·.2)

mutual

/-- `type` (`lean/Spec/Did.md`, Section 4.1). -/
def type : Nat → P TypeExpr
  | 0 => throw tooDeep
  | n + 1 => do
    match ← next ts with
    | .ident s => return (match primOfName? s with | some p => .prim p | none => .name s)
    | .keyword "null" => return .prim .null
    | .keyword "principal" => return .prim .principal
    | .keyword "opt" => return .opt (← type n)
    | .keyword "vec" => return .vec (← type n)
    | .keyword "blob" => return .vec (.prim .nat8)
    | .keyword "record" =>
      expect ts "{"
      return .record (← liftE (numberFields (← sepBy ts (fieldType n false) ";" "}" (2 * ts.size))))
    | .keyword "variant" =>
      expect ts "{"
      return .variant (← liftE (numberFields (← sepBy ts (fieldType n true) ";" "}" (2 * ts.size))))
    | .keyword "func" => funcType n
    | .keyword "service" => return .service (← methods n)
    | t => throw s!"expected a type, got {t.describe}"

/-- `field` or `alt`. In a variant, a label alone has type `null`; in a record, a type
alone is positional. -/
def fieldType : Nat → Bool → P (Option FieldId × TypeExpr)
  | 0, _ => throw tooDeep
  | n + 1, variant => do
    let t ← peekAt ts 0
    let labelled := (← peekAt ts 1) == some (.punct ":")
    match t.bind labelOf? with
    | some l =>
      if labelled then
        modify (· + 2)
        return (some (← liftE l), ← type n)
      if variant then
        modify (· + 1)
        return (some (← liftE l), .prim .null)
      return (none, ← type n)
    | none =>
      if variant then throw "expected a variant field"
      return (none, ← type n)

/-- `functype`: `(params) -> (params) mode`. -/
def funcType : Nat → P TypeExpr
  | 0 => throw tooDeep
  | n + 1 => do
    let args ← params n
    expect ts "->"
    let rets ← params n
    return .func args rets (← mode ts)

/-- `params`, with the names checked and dropped. -/
def params : Nat → P (List TypeExpr)
  | 0 => throw tooDeep
  | n + 1 => do
    expect ts "("
    dropNames (← sepBy ts (argType n) "," ")" (2 * ts.size))

/-- `param`: a type, optionally named. A name has no meaning, but must be UTF-8, and
must not repeat within its list (`lean/Spec/Did.md`, Section 4.2). -/
def argType : Nat → P (Option String × TypeExpr)
  | 0 => throw tooDeep
  | n + 1 => do
    if (← peekAt ts 1) == some (.punct ":") then
      if let some name := (← peekAt ts 0).bind nameOf? then
        let name ← liftE name
        modify (· + 2)
        return (some name, ← type n)
    return (none, ← type n)

/-- `methods`: names distinct. -/
def methods : Nat → P (List (String × TypeExpr))
  | 0 => throw tooDeep
  | n + 1 => do
    expect ts "{"
    let ms ← sepBy ts (method n) ";" "}" (2 * ts.size)
    unless noDups (ms.map (·.1)) do throw "a method name is repeated"
    return ms

/-- `method`: a name, and a function type or the name of one. -/
def method : Nat → P (String × TypeExpr)
  | 0 => throw tooDeep
  | n + 1 => do
    let some name := (← next ts) |> nameOf? | throw "expected a method name"
    let name ← liftE name
    expect ts ":"
    if ← isPunct ts "(" then return (name, ← funcType n)
    match ← next ts with
    | .ident s => return (name, .name s)
    | t => throw s!"expected a function type, got {t.describe}"

end

/-- The bytes of a text literal, which must be next. -/
def textLit : P (List UInt8) := do
  match ← next ts with
  | .text bs => return bs
  | t => throw s!"expected a text literal, got {t.describe}"

def principalLit : P PrincipalBytes := do
  let bs ← textLit ts
  let s ← liftE (utf8? bs)
  match principalOfText? s with
  | some p => return p
  | none => throw s!"not the text of a principal: {repr s}"

mutual

/-- `annotated`: an expression, optionally followed by `: <datatype>`. -/
def annotated : Nat → P Expr
  | 0 => throw tooDeep
  | n + 1 => do
    let e ← expr n
    if ← accept ts ":" then return .ann e (← type ts (2 * ts.size + 2))
    return e

/-- `expr`. -/
def expr : Nat → P Expr
  | 0 => throw tooDeep
  | n + 1 => do
    match ← next ts with
    | .punct "(" =>
      let e ← annotated n
      expect ts ")"
      return e
    | .int z _ => return .int z
    | .float neg m b x => return .float neg m b x
    | .text bs => return .text bs
    | .keyword "true" => return .bool true
    | .keyword "false" => return .bool false
    | .keyword "null" => return .null
    | .keyword "opt" => return .opt (← expr n)
    | .keyword "vec" =>
      expect ts "{"
      return .vec (← sepBy ts (annotated n) ";" "}" (2 * ts.size))
    | .keyword "blob" => return .blob (← textLit ts)
    | .keyword "record" =>
      expect ts "{"
      return .record (← liftE (numberFields (← sepBy ts (field n) ";" "}" (2 * ts.size))))
    | .keyword "variant" =>
      expect ts "{"
      let some l := (← next ts) |> labelOf? | throw "expected a variant field"
      let id ← liftE l
      let e ← if ← accept ts "=" then annotated n else pure .null
      expect ts "}"
      return .variant id e
    | .keyword "principal" => return .principal (← principalLit ts)
    | .keyword "service" => return .service (← principalLit ts)
    | .keyword "func" =>
      let p ← principalLit ts
      expect ts "."
      let some m := (← next ts) |> nameOf? | throw "expected a method name"
      return .func p (← liftE m)
    | t => throw s!"expected a value, got {t.describe}"

/-- A record field: `label = annotated`, or `annotated` alone, positional. -/
def field : Nat → P (Option FieldId × Expr)
  | 0 => throw tooDeep
  | n + 1 => do
    if (← peekAt ts 1) == some (.punct "=") then
      if let some l := (← peekAt ts 0).bind labelOf? then
        modify (· + 2)
        return (some (← liftE l), ← annotated n)
    return (none, ← annotated n)

end

/-- `args`, and nothing after it. -/
def args : P (List Expr) := do
  expect ts "("
  let es ← sepBy ts (annotated ts (2 * ts.size + 2)) "," ")" (2 * ts.size)
  if (← get) < ts.size then throw "unexpected input after the arguments"
  return es

end

/-- Parse an argument sequence. -/
def parseArgs (src : String) : Except String (List Expr) := do
  let ts ← lex src
  (args ts).run' 0

end Candid.Text
