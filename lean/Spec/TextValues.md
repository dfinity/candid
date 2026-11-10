# Candid Textual Values

**Status:** Draft. Not normative. Until this document replaces the corresponding part of
[spec/Candid.md][CANDID] under the conditions of [REWRITE.md §6](../../REWRITE.md#6-the-ratchet),
that document governs wherever the two disagree. [Appendix B](#appendix-b-differences-from-candid-010-informative)
lists the places where this one decides something the current specification leaves open,
and where it disagrees with `candid` 0.10.

**Abstract.** This document specifies the textual form of Candid values, as written by
people in tools, tests and debugging sessions, and what such text means at a given
Candid type. Reading text is defined in two steps: parsing the text into an expression,
and elaborating that expression at a type into a value. Either step can reject the input.

## Table of Contents

1. [Introduction](#1-introduction)
2. [Overview](#2-overview)
3. [Lexical Structure](#3-lexical-structure)
4. [Expressions](#4-expressions)
5. [Elaboration](#5-elaboration)
6. [Conformance](#6-conformance)
7. [Security Considerations](#7-security-considerations)
8. [References](#8-references)
- [Appendix A. Textual Form of Principals](#appendix-a-textual-form-of-principals)
- [Appendix B. Differences from candid 0.10 (Informative)](#appendix-b-differences-from-candid-010-informative)
- [Appendix C. Examples (Informative)](#appendix-c-examples-informative)

## 1. Introduction

### 1.1. Scope

This document defines:

- the lexical structure of textual values ([Section 3](#3-lexical-structure));
- the syntax of value expressions and of argument sequences ([Section 4](#4-expressions));
- the meaning of an expression at a type: the value it denotes, or that it is rejected
  ([Section 5](#5-elaboration)).

The following are out of scope:

- **The syntax of types.** Annotations ([Section 4.1](#41-grammar)) contain types written
  in the type syntax of [CANDID]. This document refers to that syntax but does not
  define it.
- **Printing.** This document does not say how an implementation prints a value as text.
  It does say which text reads back as a given value, which an implementation that
  prints values can use to check its printer.
- **Reading text without a type.** An implementation MAY offer to read an expression
  when no type is given, inferring one from the expression. This document does not
  define that inference. Without a type, an expression has no meaning here.

### 1.2. Requirements Language

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD
NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to
be interpreted as described in BCP 14 [RFC2119] [RFC8174] when, and only when, they
appear in all capitals, as shown here.

### 1.3. Notation

**Grammar.** Grammars are written in ABNF [RFC5234] with two departures:

1. Terminals denote Unicode scalar values [UNICODE], not bytes. `%x41` is the character
   U+0041, and `%xE000-10FFFF` is a range of characters.
2. Quoted strings are case-sensitive, as if written with the `%s` prefix of [RFC7405].
   `"opt"` matches `opt` and nothing else.

**Rules.** The meaning of an expression is given by rules of the form

```
e ⇐ t ⇝ v    if <premises>
```

read "the expression *e*, elaborated at the type *t*, yields the value *v*, provided
that the premises hold". A rule without premises holds unconditionally. Elaboration is
the least relation closed under the rules; an expression that no rule relates to any
value is *rejected* at that type.

**Values and types.** Values and types are those of the Candid data model [CANDID], and
are written as follows. `nat(n)`, `int(n)`, `nat8(n)` … `int64(n)` are numbers of the
named type. `float32(b)` and `float64(b)` are IEEE 754 [IEEE754] floating-point data,
identified by their bit patterns. `text(s)` holds a sequence of Unicode scalar values.
`bool(b)`, `opt(v)`, `vec(v₁, …, vₙ)`, `record{i₁ = v₁; …; iₙ = vₙ}` with field ids in
ascending order, `variant{i = v}`, `principal(p)`, `service(p)` and `func(p, m)` are as
expected. The single value `null` is the value of type `null`, the absent value of any
option type, and the value of type `reserved`.

**Sequences of bytes and characters.** `⟨b₁, …, bₙ⟩` is a sequence; `‖` concatenates.
`utf8(c)` is the UTF-8 encoding [UNICODE] of the character *c*.

### 1.4. Terminology

**text**
: A sequence of Unicode scalar values. When text arrives as bytes, it is decoded as
  UTF-8, and bytes that are not well-formed UTF-8 MUST be rejected.

**reject**
: To report that the input has no meaning, and to produce no value. How the rejection
  is reported is up to the implementation.

**resolve**
: To replace a type name by the type it is defined as, repeatedly, until the outermost
  form is not a name. Every rule in [Section 5](#5-elaboration) applies to a type after
  it is resolved.

## 2. Overview

Text is read in two steps:

```
text ──parse──▶ expression ──elaborate at t──▶ value of type t
                (Sections 3, 4)                 (Section 5)
```

Parsing does not depend on the type. It turns `record { name = "x"; 5 }` into a record
expression with two fields, the second numbered by position, and it rejects text that
is not well-formed regardless of type, such as an unterminated string or a field id
used twice.

Elaboration is guided by the type, and gives literals their meaning. The literal `5`
denotes `nat8(5)` at `nat8`, `int(5)` at `int`, and nothing at `float64` or `text`.

Elaboration is not coercion. Coercion, defined in [CANDID], converts a value of one
type into a value of another, and is how a decoder takes binary data sent at one type
into the type it expects. Elaboration reads an expression that was written for the
type it is read at. Where the two could differ, elaboration is stricter. The
expression `5` is rejected at `opt nat`, where it would have to be written `opt 5`,
even though coercion would turn a `nat` into an `opt nat`. Two choices do follow the
binary format, because a value written as text should mean the same thing as one sent
in binary. Fields that the type does not mention are ignored
([Section 5.6](#56-records-and-variants)), and missing optional arguments are filled
in ([Section 5.9](#59-argument-sequences)).

## 3. Lexical Structure

### 3.1. Tokens

Text is divided into tokens from left to right, by taking at each point the longest
prefix that forms a token. Whitespace and comments may appear between tokens and are
otherwise ignored. Text that cannot be divided this way MUST be rejected.

```abnf
token       = keyword / identifier / number / text-literal / punctuation
punctuation = "(" / ")" / "{" / "}" / ";" / "," / "." / ":" / "="
whitespace  = %x09 / %x0A / %x0D / %x20
```

The longest-match rule decides cases like `optional`, which is an identifier and not
the keyword `opt` followed by `ional`, and `1e5`, which is one number.

### 3.2. Comments

```abnf
comment       = line-comment / block-comment
line-comment  = "//" *line-char
line-char     = %x00-09 / %x0B-10FFFF
block-comment = "/*" block-body "*/"
```

A `line-comment` extends to the end of the line, not including the line feed.

A `block-body` is any text in which every `/*` begins a nested `block-comment`, and
which contains no `*/` other than those that close one. Block comments therefore nest:
`/* a /* b */ c */` is one comment. A block comment that is not closed MUST be rejected.

### 3.3. Keywords and Identifiers

```abnf
keyword    = "blob" / "composite_query" / "false" / "func" / "import" / "null"
           / "oneway" / "opt" / "principal" / "query" / "record" / "service"
           / "true" / "type" / "variant" / "vec"
identifier = (ALPHA / "_") *(ALPHA / DIGIT / "_")   ; that is not a keyword
```

Keywords are reserved for the whole of Candid's syntax, including the parts this
document does not define, so some keywords never occur in a value. A field named like
a keyword is written as text: `record { "opt" = 1 }`.

Names of types, such as `nat` and `text`, are identifiers, not keywords.

### 3.4. Numbers

```abnf
number     = [sign] (decimal / "0x" hex)
           / [sign] decimal "." [decimal]
           / [sign] decimal ["." [decimal]] ("e" / "E") [sign] decimal
           / [sign] "0x" hex "." [hex]
           / [sign] "0x" hex ["." [hex]] ("p" / "P") [sign] decimal

sign       = "+" / "-"
decimal    = DIGIT *(["_"] DIGIT)
hex        = HEXDIG *(["_"] HEXDIG)
```

`HEXDIG` here includes the lowercase letters `a` to `f`; the prefix `0x` does not have
an uppercase form. An underscore separates digits and has no other effect; the grammar
does not let one begin or end a sequence of digits, or follow another underscore. A sign
is part of its number, so whitespace or a comment between the two leaves a sign that is
not a token, and the text is rejected.

A number is an **integer literal** if it is written in the first form, and a **float
literal** otherwise. The two are distinct in what follows, even when they denote the
same quantity: `1` is an integer literal and `1.0` is a float literal.

The **value of an integer literal** is the integer that its digits denote in base 10,
or in base 16 after `0x`, negated if the sign is `-`. It has no bound.

The **value of a float literal** is a sign and a non-negative rational number:

- The sign is negative if the literal begins with `-`, and positive otherwise.
- After `0x`, the digits before and after the point denote a hexadecimal fraction, and
  `p` gives a power of 2 by which it is multiplied. Otherwise the fraction is decimal,
  and `e` gives a power of 10.

The exponent is always written in decimal. The sign is kept separately so that `-0.0`
and `0.0` remain distinct.

### 3.5. Text Literals

```abnf
text-literal = DQUOTE *(text-char / escape) DQUOTE
text-char    = %x20-21 / %x23-5B / %x5D-7E / %x80-10FFFF
escape       = "\" ( "n" / "r" / "t" / "\" / DQUOTE / "'"
                   / HEXDIG HEXDIG
                   / "u{" hex "}" )
```

A text literal may not contain a raw control character, including a line break, or
the character U+007F; these are written as escapes.

The **value of a text literal** is a sequence of bytes, the concatenation of one
sequence for each `text-char` or `escape` in order:

| Written | Bytes |
|---|---|
| a `text-char` *c* | `utf8(c)` |
| `\n`, `\r`, `\t` | `⟨0x0A⟩`, `⟨0x0D⟩`, `⟨0x09⟩` |
| `\\`, `\"`, `\'` | `⟨0x5C⟩`, `⟨0x22⟩`, `⟨0x27⟩` |
| `\` followed by two hexadecimal digits *h* | the single byte *h* |
| `\u{` *h* `}` | `utf8(c)`, where *c* is the character whose code point is *h* |

In the last form, *h* MUST denote a Unicode scalar value: at most `10FFFF`, and not in
the range `D800` to `DFFF`. Leading zeros are permitted.

The value is bytes rather than characters because a byte escape can produce a sequence
that is not UTF-8, such as `"\ff"`. Such a literal is still a token. Whether its value
is acceptable depends on where it is used: it is acceptable as a `blob`
([Section 4.1](#41-grammar)), and not as text or as a name. A use that requires text
MUST reject a value that is not well-formed UTF-8.

## 4. Expressions

### 4.1. Grammar

The grammar in this section is over the tokens of [Section 3](#3-lexical-structure).
Whitespace and comments may appear between any two tokens.

```abnf
args        = "(" [annotated *("," annotated) [","]] ")"

annotated   = expr [":" type]

expr        = "(" annotated ")"
            / number / text-literal / "true" / "false" / "null"
            / "opt" expr
            / "vec" "{" [annotated *(";" annotated) [";"]] "}"
            / "blob" text-literal
            / "record" "{" [field *(";" field) [";"]] "}"
            / "variant" "{" (label "=" annotated / label) "}"
            / "principal" text-literal
            / "service" text-literal
            / "func" text-literal "." name

field       = label "=" annotated / annotated
label       = decimal / "0x" hex / name
name        = identifier / text-literal
```

`type` is the type syntax of [CANDID].

A sequence, record or argument list may end with a separator. A variant has exactly
one field, so `variant {}` and `variant { a; }` are both rejected.

In a record, `"a" = 1` is a named field and `"a"` alone is a positional field whose
expression is text. One token of lookahead, `=` or not, tells them apart. The same
holds for a numeric label such as `1 = 2` and the positional `1`.

### 4.2. Abstract Syntax

Parsing produces an expression in the following abstract syntax. The meaning of a
parsed expression in [Section 5](#5-elaboration) is defined on this form alone.

```
e ::= intlit(z)                          integer literal with value z
    | floatlit(s, q)                     float literal with sign s and magnitude q
    | textlit(β)                         text literal with bytes β
    | true | false | null
    | opt e
    | vec(e₁, …, eₙ)
    | blob(β)
    | record{i₁ = e₁; …; iₙ = eₙ}        field ids, distinct
    | variant{i = e}
    | principal(p) | service(p) | func(p, m)
    | (e : t)
```

The rest of this section says how the concrete syntax maps to this form, and which
further inputs MUST be rejected during parsing.

**Parentheses.** `( a )` is the expression *a*. `( e : t )` is the annotation
`(e : t)`, and so is `e : t` where the grammar permits it: as an argument, an element
of a vector, or a field value.

**Field ids.** A `label` denotes a field id, a natural number less than 2³²:

- A `decimal` or `hex` label denotes its value. A label whose value is 2³² or more MUST
  be rejected.
- A `name` denotes the field-id hash of [CANDID] applied to the name's bytes. A name
  written as a text literal MUST be well-formed UTF-8.

**Positional fields.** A record field without a label is given an id from its
position. The first field of a record, if positional, is given id 0. Any later
positional field is given one more than the id of the field immediately before it,
whether that field was labelled or positional. A positional field after a field with id
2³² − 1 MUST be rejected. So `record { a = 1; 2 }` gives the second field the id
`hash("a") + 1`.

**Distinct ids.** If two fields of one record have the same id, after labels are
hashed and positions numbered, the record MUST be rejected. This includes two
different names whose hashes collide.

**Variants.** A variant field written as a `label` alone has the value `null`:
`variant { a }` is `variant{hash("a") = null}`.

**References.** In `principal`, `service` and `func`, the text literal MUST be the
textual form of a principal, as defined in
[Appendix A](#appendix-a-textual-form-of-principals), and *p* is that principal. The
method name *m* of a `func` is the name's bytes, which MUST be well-formed UTF-8.

**Blobs.** `blob(β)` takes the bytes β of its text literal as they are; they need not
be UTF-8.

## 5. Elaboration

An expression *e* is elaborated at a type *t*, written `e ⇐ t`. The rules in this
section say which value, if any, it yields. If no rule yields a value, the expression
MUST be rejected at that type.

In each rule, *t* stands for the type after it is resolved. A type name in an annotation
is resolved in the environment of type definitions supplied with the input, which may be
empty.

### 5.1. Annotations

An annotation does not convert. It states the type its expression is written at, and
that type must be the expected one:

```
(e : s) ⇐ t ⇝ v    if s ≡ t  and  e ⇐ s ⇝ v
```

`s ≡ t` holds when *s* and *t* are the same type: equal after every name is replaced by
its definition, expanding recursive types as far as needed. Two types can be the same
without being written the same way. A name and its definition are the same type, and
so are two record types that list the same fields in a different order.

An expression is **well-annotated** if, for every annotated subexpression `(e' : s)`,
`e' ⇐ s` yields a value. The rules of [Sections 5.2 to 5.9](#52-reserved) apply only to
well-annotated expressions. An expression that is not well-annotated MUST be rejected at
every type, including where [Section 5.2](#52-reserved) or
[Section 5.6](#56-records-and-variants) would otherwise ignore it.

### 5.2. Reserved

Every expression that is not an annotation elaborates to `null` at `reserved`:

```
e ⇐ reserved ⇝ null    if e is not of the form (e' : s)
```

### 5.3. Numbers

An integer literal elaborates at each integer type whose range contains its value:

```
intlit(z) ⇐ nat   ⇝ nat(z)     if 0 ≤ z
intlit(z) ⇐ natN  ⇝ natN(z)    if 0 ≤ z < 2^N             (N = 8, 16, 32, 64)
intlit(z) ⇐ int   ⇝ int(z)
intlit(z) ⇐ intN  ⇝ intN(z)    if −2^(N−1) ≤ z < 2^(N−1)  (N = 8, 16, 32, 64)
```

The sign of an integer literal does not matter beyond its value. `+5` and `-0` both
elaborate at `nat`.

A float literal elaborates at each floating-point type by rounding:

```
floatlit(s, q) ⇐ float32 ⇝ float32(round₃₂(s, q))
floatlit(s, q) ⇐ float64 ⇝ float64(round₆₄(s, q))
```

`roundₖ(s, q)` is the binaryk number that the roundTiesToEven attribute of [IEEE754],
Section 4.3.1, gives for the exact number q with the sign s. In particular, a magnitude
too large for the format rounds to infinity, and a result of zero carries the sign *s*,
so `-1e-400` yields negative zero. The literal is rounded once, directly to the
target format. An implementation MUST NOT round it first to a wider format.

An integer literal does not elaborate at a floating-point type, and a float literal does
not elaborate at an integer type. `1` is rejected at `float64` and `1.0` at `nat`.

There is no literal for a NaN; see [Appendix B](#appendix-b-differences-from-candid-010-informative).

### 5.4. Text, Booleans and Null

```
textlit(β) ⇐ text ⇝ text(β)     if β is well-formed UTF-8
true       ⇐ bool ⇝ bool(true)
false      ⇐ bool ⇝ bool(false)
null       ⇐ null ⇝ null
```

### 5.5. Options and Vectors

```
null         ⇐ opt t ⇝ null
opt e        ⇐ opt t ⇝ opt(v)               if e ⇐ t ⇝ v
vec(e₁, …, eₙ) ⇐ vec t ⇝ vec(v₁, …, vₙ)     if eᵢ ⇐ t ⇝ vᵢ for each i
blob(β)      ⇐ vec t ⇝ vec(nat8(b₁), …, nat8(bₙ))   if t is nat8, and β = ⟨b₁, …, bₙ⟩
```

These are the only rules for option types. A value is not implicitly made optional: at
`opt nat`, `opt 5` is accepted and `5` is rejected. At `opt null`, `null` is the
absent value, and `opt null` is the present one.

### 5.6. Records and Variants

A record expression elaborates at a record type field by field, following the type:

```
record{i₁ = e₁; …; iₙ = eₙ} ⇐ record{j₁ : t₁; …; jₘ : tₘ} ⇝ record{j₁ = w₁; …; jₘ = wₘ}
    if, for each k from 1 to m:
       either jₖ = iₗ for some l, and eₗ ⇐ tₖ ⇝ wₖ,
       or     jₖ is no iₗ, tₖ is null, reserved, or an option type, and wₖ = null
```

A field of the expression whose id the type does not have is ignored, as decoding
ignores such a field in binary data. A field of the type that the expression does not
have is filled with `null` if its type has that value, and the record is rejected
otherwise.

A variant expression elaborates if its field is one of the type's:

```
variant{i = e} ⇐ variant{…; i : t; …} ⇝ variant{i = v}    if e ⇐ t ⇝ v
```

### 5.7. References

```
principal(p) ⇐ principal      ⇝ principal(p)
service(p)   ⇐ service {…}    ⇝ service(p)
func(p, m)   ⇐ func (…) → (…) ⇝ func(p, m)
```

A reference is not checked against the service or function type it is elaborated at.
Text alone cannot show whether principal *p* provides a method *m*.

The three kinds of reference do not mix. A `principal` expression is rejected at a
service type, and a `service` expression at `principal`.

### 5.8. Empty

No rule yields a value at `empty`, so every expression is rejected there.

### 5.9. Argument Sequences

An argument sequence elaborates at a sequence of types position by position. Arguments
beyond the types are ignored, and types beyond the arguments are filled as missing
record fields are:

```
(e₁, …, eₙ) ⇐ (t₁, …, tₘ) ⇝ (v₁, …, vₘ)
    if, for each k from 1 to m:
       either k ≤ n, and eₖ ⇐ tₖ ⇝ vₖ,
       or     k > n, tₖ is null, reserved, or an option type, and vₖ = null
```

Every argument MUST still be well-annotated ([Section 5.1](#51-annotations)), including
one that is ignored.

### 5.10. Properties (Informative)

The rules are designed so that the following hold. They are stated here as obligations
on the rules, to be proved about the reference model.

- **Determinism.** For each expression and type, at most one value is yielded.
- **Well-typedness.** If `e ⇐ t ⇝ v`, then `v` is a value of type `t`.
- **Termination.** Elaboration recurses on the expression, so it terminates even at a
  recursive type.

## 6. Conformance

An implementation conforms to this document if, for every text and every type, it
either rejects the text or yields the value given by [Sections 3 to 5](#3-lexical-structure),
and it rejects only where those sections require it or where
[Section 7](#7-security-considerations) permits it.

Conformance vectors, each a text, a type and the expected value or rejection, are
generated from the reference model in [lean/](../) and published under
[conformance/](../../conformance/).

## 7. Security Considerations

Text values are often typed by people and are rarely hostile. They can still come from
outside: a web interface may send typed text to a service that parses it. An
implementation MAY reject a well-formed input for lack of resources, as described for
binary data in [CANDID], and SHOULD bound the following:

- **Nesting.** Every bracket adds a level of recursion to a straightforward parser.
- **Integer literals.** The value of an integer literal is unbounded, and converting a
  long literal from decimal costs time quadratic in its length in a naïve
  implementation.
- **Float literals.** The exponent is unbounded. An implementation SHOULD round
  without computing 10 raised to the exponent: `1e999999999` rounds to infinity, and
  should take no more time to read than `1e999`.

## 8. References

### 8.1. Normative References

[CANDID]
: DFINITY, "Candid Specification", [spec/Candid.md](../../spec/Candid.md). For the type
  syntax, the data model, the field-id hash, and coercion.

[IEEE754]
: IEEE, "IEEE Standard for Floating-Point Arithmetic", IEEE Std 754-2019.

[RFC2119]
: Bradner, S., "Key words for use in RFCs to Indicate Requirement Levels", BCP 14,
  RFC 2119, March 1997.

[RFC4648]
: Josefsson, S., "The Base16, Base32, and Base64 Data Encodings", RFC 4648, October 2006.

[RFC5234]
: Crocker, D., Ed., and P. Overell, "Augmented BNF for Syntax Specifications: ABNF",
  STD 68, RFC 5234, January 2008.

[RFC7405]
: Kyzivat, P., "Case-Sensitive String Support in ABNF", RFC 7405, December 2014.

[RFC8174]
: Leiba, B., "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words", BCP 14,
  RFC 8174, May 2017.

[UNICODE]
: The Unicode Consortium, "The Unicode Standard".

### 8.2. Informative References

[IC-INTERFACE]
: DFINITY, "The Internet Computer Interface Specification", section "Principals".

[WASM]
: WebAssembly Community Group, "WebAssembly Core Specification", section "Text Format:
  Values". The escapes of text literals and the forms of float literals follow it.

## Appendix A. Textual Form of Principals

A principal is a sequence of bytes *p*. Its **canonical textual form** is computed as
follows:

1. Let *c* be the CRC-32 of *p*, as four bytes, most significant first. CRC-32 is the
   checksum of ISO 3309 and ITU-T V.42, the one computed by zlib.
2. Let *s* be the base32 encoding [RFC4648] of `c ‖ p`, in lowercase and without padding.
3. Split *s* into groups of five characters, the last of which may be shorter, and join
   them with `-`.

For example, the empty principal has the form `aaaaa-aa`.

A text denotes the principal *p* if it equals the canonical form of *p*, ignoring the
case of ASCII letters. Any other text MUST be rejected: one that is not base32, whose
checksum does not match, or whose dashes are not where the canonical form puts them.

This document does not bound the length of *p*. The Internet Computer limits principals
to 29 bytes [IC-INTERFACE], and an implementation for it MAY reject a longer one.

## Appendix B. Differences from candid 0.10 (Informative)

This appendix lists where this document decides something [CANDID] does not, and where
it differs from `candid_parser` 0.10, the Rust implementation. Each item that differs
from 0.10 is a proposed change to 0.10, or a decision this draft still has to make.

### B.1. Decided Here, Silent in Candid.md

- The meaning of text at a type ([Section 5](#5-elaboration)). [CANDID] says only that
  types are known from context.
- Fields not in the type are ignored, and missing fields and arguments of type `null`,
  `reserved` or an option type are filled with `null`
  ([Sections 5.6](#56-records-and-variants) and [5.9](#59-argument-sequences)). This
  agrees with 0.10 and with `test/construct.test.did`.
- Every expression elaborates at `reserved` ([Section 5.2](#52-reserved)), agreeing
  with 0.10.
- Keywords cannot be identifiers ([Section 3.3](#33-keywords-and-identifiers)), agreeing
  with 0.10. [CANDID] lists no keywords.
- Comments may appear in values, agreeing with 0.10. [CANDID] defines comments only for
  types.
- Text that is not UTF-8 after byte escapes is rejected as text and accepted as a blob,
  agreeing with 0.10.
- The textual form of principals ([Appendix A](#appendix-a-textual-form-of-principals)).
  [CANDID] calls it a "URI".
- A positional field after id 2³² − 1 is rejected. [CANDID]'s "previous + 1" is
  undefined there.
- A signed hexadecimal integer such as `-0x10` is accepted, agreeing with 0.10.
  [CANDID]'s grammar has hexadecimal only for naturals.

### B.2. Different from candid 0.10

| Input | candid 0.10 | This document |
|---|---|---|
| `record { 4294967295 = 1; 2 }` | panics in a debug build; in a release build the second field gets id 0 | rejected |
| `0X10` | panics | rejected: not a token |
| `(5 : nat)` at `int` | accepted | rejected: an annotation does not convert ([5.1](#51-annotations)) |
| `(1.5 : float64)` at `float32` | accepted, rounded | rejected, as above |
| `(1 : nat)` at `reserved` | accepted | rejected, as above |
| `()` at `(opt nat)` | accepted by `annotate_types`, rejected by `didc encode` | accepted: `(null)` |
| A float literal at `float32` | rounded to `float64`, then to `float32` | rounded once ([5.3](#53-numbers)) |
| `-0` at `nat` | rejected | accepted: 0 |
| `- 5`, `-/* */5` | accepted | rejected: a sign is part of its number |
| `1_`, `1__0` | accepted | rejected |
| `1_000.5` | rejected | accepted |
| `.5` | accepted | rejected |
| `0x1p4` | rejected | accepted: 16 |
| A raw tab, line break or other control character in a text literal | accepted | rejected |
| A principal of more than 29 bytes | rejected | accepted ([Appendix A](#appendix-a-textual-form-of-principals)) |

`candid_parser` also builds a `String` from bytes that may not be UTF-8 before it checks
them, which Rust's rules forbid, even when the check then rejects the literal.

### B.3. Open Issues

- **NaN.** No literal denotes a NaN, so there is no text for a `float32` or `float64`
  value that is one. Neither this document nor 0.10 can write every value of a float
  type.
- **Annotations.** [Section 5.1](#51-annotations) requires the annotated type to be
  the expected one. The alternative is to allow any subtype and coerce, as decoding does.
  That would accept `(5 : nat)` at `int`, but also turn `("x" : text)` at `opt nat` into
  `null` without complaint.

## Appendix C. Examples (Informative)

| Text | Type | Result |
|---|---|---|
| `(5)` | `(nat8)` | `nat8(5)` |
| `(5)` | `(opt nat)` | rejected |
| `(opt 5)` | `(opt nat)` | `opt(nat(5))` |
| `(null)` | `(opt null)` | `null` |
| `(opt null)` | `(opt null)` | `opt(null)` |
| `(0x_ff)` | `(nat)` | rejected: an underscore may not follow `0x` |
| `(0xff)` | `(nat16)` | `nat16(255)` |
| `(1)` | `(float64)` | rejected |
| `(-0.0)` | `(float64)` | `float64(0x8000000000000000)` |
| `(1e400)` | `(float64)` | `float64(0x7FF0000000000000)`, infinity |
| `("\u{2603}")` | `(text)` | `text("☃")` |
| `("\u{26_03}")` | `(text)` | `text("☃")` |
| `("\u{2603")` | `(text)` | rejected: unterminated escape |
| `("\ff")` | `(text)` | rejected: not UTF-8 |
| `(blob "\ff")` | `(blob)` | `vec(nat8(255))` |
| `(record { whatever = 0 })` | `(record {})` | `record{}` |
| `(record { a = 1; 2 })` | `(record { a : nat; 98 : nat })` | `record{97 = nat(1); 98 = nat(2)}` |
| `(record {})` | `(record { a : opt nat })` | `record{97 = null}` |
| `(record { a = 1; 97 = 2 })` | any | rejected: id 97 twice |
| `(variant {})` | `(variant {})` | rejected: no syntax |
| `(vec { 1; -1 })` | `(vec nat)` | rejected: `-1` is not a `nat` |
| `(vec { 1; -1 })` | `(reserved)` | `null` |
| `((1 : text))` | `(reserved)` | rejected: not well-annotated |
| `(principal "aaaaa-aa")` | `(principal)` | `principal(⟨⟩)` |
| `(principal "w7x7r-cok77-xa")` | `(service {})` | rejected: a principal is not a service |
| `(func "aaaaa-aa".m)` | `(func () -> ())` | `func(⟨⟩, "m")` |
| `(1, 2)` | `(nat)` | `(nat(1))` |
| `()` | `(opt nat, null)` | `(null, null)` |

[CANDID]: ../../spec/Candid.md
