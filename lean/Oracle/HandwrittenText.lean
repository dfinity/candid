/-
Hand-written `parse` vectors: text, the types it is read at, and what it reads as,
following `lean/Spec/TextValues.md`. As in `Oracle/Handwritten.lean`, each expectation
is written down from the document rather than computed by the model, and the ids say
what each case shows. Section numbers in the ids are the document's.

Where `candid` 0.10 answers differently, the document's Appendix B.2 says why; the
runner lists those vectors as known divergences.
-/

import Oracle.Handwritten

namespace Oracle

open Candid
open Candid.Slot
open Candid.Composite

def expectParse (text : String) (ts : TypeSeq) (want : Option (List Value)) (id : String) :
    Vector :=
  ⟨s!"text: {id}", .parse text ts want⟩

/-- One type that is one composite. -/
def oneOf (c : Composite) : TypeSeq := typesOf do return [← intern c]

def accepts (text : String) (ts : TypeSeq) (vs : List Value) (id : String) : Vector :=
  expectParse text ts (some vs) id

def rejects (text : String) (ts : TypeSeq) (id : String) : Vector :=
  expectParse text ts none id

/-! ## Lexical structure (Section 3) -/

def textLexChecks : List Vector :=
  [ accepts "( /* a /* nested */ b */ 1 // to the end of the line\n )" (prims [nat]) [.nat 1]
      "comments nest, and a line comment ends at the line feed (3.2)"
  , rejects "(1 /* unclosed)" (prims [nat]) "an unclosed block comment (3.2)"
  , rejects "(record { opt = 1 })" (oneOf (recordOf [("opt", nat)]))
      "a keyword is not a field name (3.3)"
  , accepts "(record { \"opt\" = 1 })" (oneOf (recordOf [("opt", nat)]))
      [.record [(hashFieldName "opt", .nat 1)]] "a field named like a keyword is written as text (3.3)"
  , accepts "(record { nat = 1 })" (oneOf (recordOf [("nat", nat)]))
      [.record [(hashFieldName "nat", .nat 1)]] "a type name is an identifier, not a keyword (3.3)" ]

/-! ## Numbers (Sections 3.4 and 5.3) -/

def textIntChecks : List Vector :=
  [ accepts "(1_000)" (prims [nat]) [.nat 1000] "an underscore separates digits (3.4)"
  , rejects "(1_)" (prims [nat]) "an underscore cannot end a number (3.4)"
  , rejects "(1__0)" (prims [nat]) "an underscore cannot follow another (3.4)"
  , rejects "(0x_ff)" (prims [nat]) "an underscore cannot begin the digits (3.4)"
  , accepts "(0xFF)" (prims [nat]) [.nat 255] "hexadecimal digits in either case (3.4)"
  , rejects "(0X10)" (prims [nat]) "the hexadecimal prefix is lowercase (3.4)"
  , accepts "(+5)" (prims [nat]) [.nat 5] "a signed literal at nat (5.3)"
  , accepts "(-0)" (prims [nat]) [.nat 0] "minus zero at nat (5.3)"
  , rejects "(-1)" (prims [nat]) "a negative literal at nat (5.3)"
  , rejects "(- 5)" (prims [int]) "a sign is part of its number (3.4)"
  , accepts "(-0x10)" (prims [int]) [.int (-16)] "a signed hexadecimal literal (3.4)"
  , accepts "(255, -128, 18446744073709551615, -9223372036854775808)"
      (prims [nat8, int8, nat64, int64])
      [.nat8 255, .int8 (-128), .nat64 18446744073709551615, .int64 (-9223372036854775808)]
      "the ends of the fixed-width ranges (5.3)"
  , rejects "(256)" (prims [nat8]) "past the top of nat8 (5.3)"
  , rejects "(-129)" (prims [int8]) "past the bottom of int8 (5.3)"
  , rejects "(1)" (prims [float64]) "an integer literal at a float type (5.3)"
  , rejects "(1.0)" (prims [nat]) "a float literal at an integer type (5.3)" ]

def textFloatChecks : List Vector :=
  [ accepts "(1.5)" (prims [float32]) [.float32 0x3fc00000] "1.5 at float32 (5.3)"
  , accepts "(0.1, 0.1)" (prims [float32, float64]) [.float32 0x3dcccccd, .float64 0x3fb999999999999a]
      "0.1 rounded to each format (5.3)"
  , accepts "(1.0000000596046448)" (prims [float32]) [.float32 0x3f800001]
      "rounded once, not first to float64 (5.3)"
  , accepts "(1e400, 1e999999999)" (prims [float64, float64])
      [.float64 0x7ff0000000000000, .float64 0x7ff0000000000000] "overflow rounds to infinity (5.3)"
  , accepts "(-1e-400, -0.0)" (prims [float64, float32])
      [.float64 0x8000000000000000, .float32 0x80000000] "a zero keeps the literal's sign (5.3)"
  , accepts "(1_000.5)" (prims [float64]) [.float64 0x408f440000000000]
      "an underscore in a float literal (3.4)"
  , rejects "(.5)" (prims [float64]) "a float literal begins with a digit (3.4)"
  , accepts "(5.)" (prims [float64]) [.float64 0x4014000000000000] "a point with no fraction (3.4)"
  , accepts "(0x1p4, 0x1.8p1)" (prims [float64, float32])
      [.float64 0x4030000000000000, .float32 0x40400000] "hexadecimal float literals (3.4)" ]

/-! ## Text (Sections 3.5 and 5.4) -/

def textTextChecks : List Vector :=
  [ rejects "(\"a\tb\")" (prims [text]) "a raw tab in a text literal (3.5)"
  , rejects "(\"a\nb\")" (prims [text]) "a raw line feed in a text literal (3.5)"
  , accepts "(\"\\t\\n\\r\\\\\\\"\\'\")" (prims [text]) [.text "\t\n\r\\\"'"] "the simple escapes (3.5)"
  , accepts "(\"\u0085\")" (prims [text]) [.text "\u0085"] "a raw C1 control character (3.5)"
  , accepts "(\"\\e2\\98\\83\")" (prims [text]) [.text "☃"] "byte escapes that make UTF-8 (3.5)"
  , rejects "(\"\\ff\")" (prims [text]) "byte escapes that do not make UTF-8, as text (5.4)"
  , accepts "(blob \"\\ff\")" (oneOf (.vec nat8)) [.vec [.nat8 0xff]]
      "byte escapes that do not make UTF-8, as a blob (4.2)"
  , accepts "(blob \"é\")" (oneOf (.vec nat8)) [.vec [.nat8 0xc3, .nat8 0xa9]]
      "a blob of a character is its UTF-8 (3.5)"
  , accepts "(\"\\u{0000000041}\")" (prims [text]) [.text "A"] "leading zeros in a code point (3.5)"
  , rejects "(\"\\u{d800}\")" (prims [text]) "a surrogate is not a scalar value (3.5)"
  , rejects "(\"\\u{110000}\")" (prims [text]) "past the last code point (3.5)"
  , rejects "(\"\\u{}\")" (prims [text]) "an empty code point (3.5)"
  , rejects "(\"\\u{41_}\")" (prims [text]) "an underscore cannot end a code point (3.5)"
  , rejects "(\"\\q\")" (prims [text]) "an unknown escape (3.5)" ]

/-! ## Constructed values (Sections 4.2, 5.5 and 5.6) -/

def textOptVecChecks : List Vector :=
  [ rejects "(5)" (oneOf (.opt nat)) "a value is not made optional (5.5)"
  , accepts "(opt 5)" (oneOf (.opt nat)) [.opt (.nat 5)] "opt (5.5)"
  , accepts "(null, opt null)" (typesOf do let t ← intern (.opt null); return [t, t])
      [.null, .opt .null] "null is absent at opt null, and opt null is present (5.5)"
  , accepts "(vec { 1; 2; })" (oneOf (.vec nat)) [.vec [.nat 1, .nat 2]]
      "a trailing separator in a vector (4.1)"
  , accepts "(vec {})" (oneOf (.vec nat8)) [.vec []] "an empty vector at blob (5.5)"
  , rejects "(blob \"a\")" (oneOf (.vec nat16)) "a blob at a vector of something else (5.5)" ]

def recordAT : TypeSeq := oneOf (recordOf [("a", nat)])

def textRecordChecks : List Vector :=
  [ accepts "(record { a = 1; 2 })" (oneOf (.record [(97, nat), (98, nat)]))
      [.record [(97, .nat 1), (98, .nat 2)]] "a positional field follows the field before it (4.2)"
  , accepts "(record { whatever = 0 })" (oneOf (.record [])) [.record []]
      "a field the type does not have is ignored (5.6)"
  , accepts "(record { a = 1; b = vec { 1; -1 } })" recordAT [.record [(97, .nat 1)]]
      "an ignored field is not elaborated (5.6)"
  , accepts "(record {})" (typesOf do
        let o ← intern (.opt nat)
        return [← intern (recordOf [("a", o), ("b", null), ("c", reserved)])])
      [.record [(97, .null), (98, .null), (99, .null)]]
      "a missing field of type opt, null or reserved is null (5.6)"
  , rejects "(record {})" recordAT "a missing field of type nat (5.6)"
  , rejects "(record { a = 1; 97 = 2 })" (prims [reserved]) "a field id given twice (4.2)"
  , rejects "(record { 4294967295 = 1; 2 })" (prims [reserved])
      "a positional field after the last id (4.2)"
  , rejects "(record { 4294967296 = 1 })" (prims [reserved]) "a field id past 32 bits (4.2)"
  , accepts "(record { 0x61 = 1 })" recordAT [.record [(97, .nat 1)]] "a hexadecimal field id (4.2)"
  , accepts "(variant { a })" (oneOf (variantOf [("a", null), ("b", nat)]))
      [.variant 97 .null] "a variant label alone is null (4.2)"
  , rejects "(variant {})" (oneOf (.variant [])) "a variant has one field (4.1)"
  , rejects "(variant { a; })" (oneOf (variantOf [("a", null)])) "no separator after a variant's field (4.1)"
  , rejects "(variant { c = 1 })" (oneOf (variantOf [("a", null), ("b", nat)]))
      "a variant field the type does not have (5.6)" ]

/-! ## Reserved, empty, references, annotations, arguments -/

def textMiscChecks : List Vector :=
  [ accepts "(vec { 1; -1 })" (prims [reserved]) [.null] "anything is null at reserved (5.2)"
  , rejects "(null)" (prims [empty]) "nothing elaborates at empty (5.8)"
  , accepts "(principal \"aaaaa-aa\", principal \"AAAAA-AA\")" (prims [principal, principal])
      [.principal [], .principal []] "a principal's text, in either case (Appendix A)"
  , rejects "(principal \"aaaaaaa\")" (prims [principal]) "a principal's dashes are checked (Appendix A)"
  , rejects "(principal \"aaaaa-ab\")" (prims [principal]) "a principal's checksum is checked (Appendix A)"
  , rejects "(principal \"w7x7r-cok77-xa\")" (oneOf (.service [])) "a principal is not a service (5.7)"
  , accepts "(service \"aaaaa-aa\")" (oneOf (.service [])) [.service []] "a service reference (5.7)"
  , accepts "(func \"aaaaa-aa\".\"mé\")" (oneOf (.func [nat] [] [.query])) [.func [] "mé"]
      "a function reference, its method named by text (5.7)" ]

def textAnnotationChecks : List Vector :=
  [ accepts "((5 : nat), 6 : nat8)" (prims [nat, nat8]) [.nat 5, .nat8 6]
      "an annotation at its own type (5.1)"
  , rejects "((5 : nat))" (prims [int]) "an annotation does not convert (5.1)"
  , rejects "((1.5 : float64))" (prims [float32]) "an annotation does not narrow (5.1)"
  , rejects "((1 : nat))" (prims [reserved]) "an annotation at reserved (5.1)"
  , rejects "((1 : text))" (prims [reserved]) "an annotation that does not hold (5.1)"
  , accepts "((record { a = 1; b = 2 } : record { b : nat; a : nat }))"
      (oneOf (recordOf [("a", nat), ("b", nat)])) [.record [(97, .nat 1), (98, .nat 2)]]
      "the same type, its fields in another order (5.1)"
  , accepts "((func \"aaaaa-aa\".m : func (x : nat) -> () query))"
      (oneOf (.func [nat] [] [.query])) [.func [] "m"] "an annotation with a function type (5.1)"
  , rejects "((1 : t))" (prims [nat]) "a type name with no definition (5.1)"
  , rejects "(record { a = 1; b = (1 : text) })" recordAT
      "an ignored field must be well-annotated (5.1)" ]

def textArgChecks : List Vector :=
  [ accepts "(1, 2)" (prims [nat]) [.nat 1] "an argument beyond the types is ignored (5.9)"
  , accepts "(1,)" (prims [nat]) [.nat 1] "a trailing comma (4.1)"
  , accepts "()" (typesOf do return [← intern (.opt nat), null]) [.null, .null]
      "missing arguments of type opt and null (5.9)"
  , rejects "()" (prims [nat]) "a missing argument of type nat (5.9)"
  , rejects "(1, (2 : text))" (prims [nat]) "an ignored argument must be well-annotated (5.9)"
  , rejects "(1) 2" (prims [nat]) "input after the arguments" ]

def textChecks : List Vector :=
  textLexChecks ++ textIntChecks ++ textFloatChecks ++ textTextChecks ++ textOptVecChecks ++
  textRecordChecks ++ textMiscChecks ++ textAnnotationChecks ++ textArgChecks

end Oracle
