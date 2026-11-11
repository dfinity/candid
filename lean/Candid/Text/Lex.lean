/-
The lexical structure of textual values (`lean/Spec/TextValues.md`, Section 3).

Text is divided into tokens from left to right, longest match first. The number and
text scanners below each take the longest prefix the grammar allows and leave the rest,
so a spelling the grammar does not allow, like `1_`, becomes two tokens (`1` and the
identifier `_`), which the parser then rejects. Errors here are only for text that is
no token at all: an unterminated literal or comment, a bad escape, a stray character.

A token keeps what the parser and elaboration need and no more. An integer literal is
its value and whether it was signed, which only a field label asks. A float literal is
exact: a sign and `m * base^exp`, rounded only when elaboration knows the format
(`Candid/Float.lean`). A text literal is bytes, since `\ff` need not be UTF-8: whether
that is acceptable depends on where it is used.
-/

namespace Candid.Text

inductive Token where
  | keyword (k : String)
  | ident (s : String)
  /-- An integer literal: its value, and whether it was written with a sign. -/
  | int (z : Int) (signed : Bool)
  /-- A float literal: `(-1)^neg * m * base^exp`, where `base` is 2 if `binary`, else 10. -/
  | float (neg : Bool) (m : Nat) (binary : Bool) (exp : Int)
  | text (bytes : List UInt8)
  | punct (p : String)
  deriving Repr, BEq, Inhabited

def Token.describe : Token → String
  | .keyword k => s!"keyword {k}"
  | .ident s => s!"identifier {s}"
  | .int z _ => s!"number {z}"
  | .float .. => "a float literal"
  | .text _ => "a text literal"
  | .punct p => s!"`{p}`"

/-- Reserved for the whole of Candid's syntax, including the parts values do not use. -/
def keywords : List String :=
  [ "blob", "composite_query", "false", "func", "import", "null", "oneway", "opt"
  , "principal", "query", "record", "service", "true", "type", "variant", "vec" ]

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- A hexadecimal digit's value, either case. -/
def hexVal? (c : Char) : Option Nat :=
  if isDigit c then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def isHex (c : Char) : Bool := (hexVal? c).isSome

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-! ## Numbers -/

/-- The digits after a first one: digits, each optionally preceded by one underscore.
An underscore not followed by a digit is not taken. Returns the digits without
underscores, and the rest. -/
def digitsAfter (p : Char → Bool) : List Char → List Char × List Char
  | c :: cs =>
    if p c then
      let (ds, r) := digitsAfter p cs
      (c :: ds, r)
    else if c == '_' then
      match cs with
      | d :: cs' =>
        if p d then
          let (ds, r) := digitsAfter p cs'
          (d :: ds, r)
        else ([], c :: d :: cs')
      | [] => ([], [c])
    else ([], c :: cs)
  | [] => ([], [])

/-- `decimal` or `hex`: at least one digit. -/
def digits (p : Char → Bool) : List Char → Option (List Char × List Char)
  | c :: cs =>
    if p c then
      let (ds, r) := digitsAfter p cs
      some (c :: ds, r)
    else none
  | [] => none

def digitsValue (base : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun n c => n * base + (hexVal? c).getD 0) 0

/-- `[sign] decimal`: an exponent, always decimal. -/
def exponent (cs : List Char) : Option (Int × List Char) :=
  let (neg, rest) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  (digits isDigit rest).map fun (ds, r) =>
    let v : Int := digitsValue 10 ds
    (if neg then -v else v, r)

/-- A number, after its sign. `cs` starts with a digit unless there was a sign, and a
sign without a number is an error: neither `+` nor `-` is a token on its own. -/
def lexNumber (neg signed : Bool) (cs : List Char) : Except String (Token × List Char) := do
  let (binary, start) := match cs with
    | '0' :: 'x' :: c :: _ => if isHex c then (true, cs.drop 2) else (false, cs)
    | _ => (false, cs)
  let p := if binary then isHex else isDigit
  let some (whole, r) := digits p start
    | throw "a sign must be immediately followed by a number"
  let (frac, isFloat, r) := match r with
    | '.' :: r' => match digits p r' with
      | some (fs, r'') => (fs, true, r'')
      | none => ([], true, r')
    | _ => ([], false, r)
  let isExp (c : Char) := if binary then c == 'p' || c == 'P' else c == 'e' || c == 'E'
  let (exp, isFloat, r) := match r with
    | c :: r' => if isExp c then
        match exponent r' with
        | some (x, r'') => (x, true, r'')
        | none => (0, isFloat, r)
      else (0, isFloat, r)
    | [] => (0, isFloat, r)
  let m := digitsValue (if binary then 16 else 10) (whole ++ frac)
  if isFloat then
    let scale : Int := (if binary then 4 else 1) * frac.length
    return (.float neg m binary (exp - scale), r)
  else
    return (.int (if neg then -(m : Int) else m) signed, r)

/-! ## Text literals

A state machine over characters, so that it recurses on the input alone. -/

inductive TextState where
  | plain
  /-- After `\`. -/
  | escape
  /-- After `\` and one hexadecimal digit. -/
  | byte (hi : Nat)
  /-- After `\u`. -/
  | brace
  /-- Inside `\u{...}`: the value so far, whether a digit has been read, and whether
  the last character was an underscore. -/
  | codepoint (n : Nat) (any : Bool) (underscore : Bool)

def scalar? (n : Nat) : Option Char :=
  if n ≤ 0x10FFFF && !(0xD800 ≤ n && n ≤ 0xDFFF) then some (Char.ofNat n) else none

/-- The bytes of a text literal, after its opening quote, and the rest. -/
def lexText (st : TextState) (acc : Array UInt8) : List Char → Except String (List UInt8 × List Char)
  | [] => throw "unterminated text literal"
  | c :: cs => match st with
    | .plain =>
      if c == '"' then return (acc.toList, cs)
      else if c == '\\' then lexText .escape acc cs
      else if c.toNat < 0x20 || c.toNat == 0x7F then
        throw s!"raw control character U+{String.ofList (Nat.toDigits 16 c.toNat)} in a text literal"
      else lexText .plain (acc ++ (String.utf8EncodeChar c).toArray) cs
    | .escape => match c with
      | 'n' => lexText .plain (acc.push 0x0A) cs
      | 'r' => lexText .plain (acc.push 0x0D) cs
      | 't' => lexText .plain (acc.push 0x09) cs
      | '\\' => lexText .plain (acc.push 0x5C) cs
      | '"' => lexText .plain (acc.push 0x22) cs
      | '\'' => lexText .plain (acc.push 0x27) cs
      | 'u' => lexText .brace acc cs
      | _ => match hexVal? c with
        | some h => lexText (.byte h) acc cs
        | none => throw s!"unknown escape \\{c}"
    | .byte hi => match hexVal? c with
      | some lo => lexText .plain (acc.push (hi * 16 + lo).toUInt8) cs
      | none => throw "a byte escape needs two hexadecimal digits"
    | .brace =>
      if c == '{' then lexText (.codepoint 0 false false) acc cs
      else throw "expected { after \\u"
    | .codepoint n any underscore =>
      if c == '}' && any && !underscore then
        match scalar? n with
        | some ch => lexText .plain (acc ++ (String.utf8EncodeChar ch).toArray) cs
        | none => throw "\\u{...} is not a Unicode scalar value"
      else if c == '_' && any && !underscore then lexText (.codepoint n any true) acc cs
      else match hexVal? c with
        | some d => lexText (.codepoint (n * 16 + d) true false) acc cs
        | none => throw "malformed \\u{...} escape"

/-! ## Comments -/

/-- Skip to the end of `depth` open block comments. `none` if the input ends first. -/
def skipBlock : Nat → List Char → Option (List Char)
  | 0, cs => some cs
  | n + 1, '*' :: '/' :: cs => skipBlock n cs
  | n + 1, '/' :: '*' :: cs => skipBlock (n + 2) cs
  | n + 1, _ :: cs => skipBlock (n + 1) cs
  | _ + 1, [] => none

/-! ## Tokens -/

/-- The tokens of `cs`. Every step consumes at least one character, so `fuel` at the
input's length plus one is never exhausted. -/
def lexAux : Nat → List Char → Array Token → Except String (Array Token)
  | _, [], acc => return acc
  | 0, _, _ => throw "unreachable: the lexer ran out of fuel"
  | fuel + 1, c :: cs, acc => do
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then return ← lexAux fuel cs acc
    match c, cs with
    | '/', '/' :: rest => lexAux fuel (rest.dropWhile (· != '\n')) acc
    | '/', '*' :: rest => match skipBlock 1 rest with
      | some r => lexAux fuel r acc
      | none => throw "unterminated block comment"
    | '"', rest =>
      let (bs, r) ← lexText .plain #[] rest
      lexAux fuel r (acc.push (.text bs))
    | '-', '>' :: rest => lexAux fuel rest (acc.push (.punct "->"))
    | '-', rest | '+', rest =>
      let (t, r) ← lexNumber (c == '-') true rest
      lexAux fuel r (acc.push t)
    | _, _ =>
      if isDigit c then
        let (t, r) ← lexNumber false false (c :: cs)
        lexAux fuel r (acc.push t)
      else if isIdStart c then
        let (name, r) := (c :: cs).span isIdChar
        let s := String.ofList name
        lexAux fuel r (acc.push (if keywords.contains s then .keyword s else .ident s))
      else if "(){};,.:=".toList.contains c then
        lexAux fuel cs (acc.push (.punct (String.singleton c)))
      else throw s!"unexpected character {repr c}"

def lex (s : String) : Except String (Array Token) := lexAux (s.length + 1) s.toList #[]

end Candid.Text
