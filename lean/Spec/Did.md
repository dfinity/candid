# Candid Interface Descriptions

**Status:** Draft. Not normative. Until this document replaces the corresponding part of
[spec/Candid.md][CANDID] under the conditions of [REWRITE.md §6](../../REWRITE.md#6-the-ratchet),
that document governs wherever the two disagree. [Appendix A](#appendix-a-differences-from-candid-010-informative)
lists the places where this one decides something the current specification leaves open,
and where it disagrees with `candid` 0.10.

**Abstract.** This document specifies the textual syntax of Candid types and of
interface descriptions, the `.did` files that state the types of a service's methods.
Reading a description is defined in three steps: parsing the text into imports,
definitions and an optional service declaration; expanding the imports, which gives one
description without them; and checking that, which gives every name and the service a
type. Any step can reject the input.

## Table of Contents

1. [Introduction](#1-introduction)
2. [Overview](#2-overview)
3. [Lexical Structure](#3-lexical-structure)
4. [Types](#4-types)
5. [Descriptions](#5-descriptions)
6. [Meaning](#6-meaning)
7. [Conformance](#7-conformance)
8. [Security Considerations](#8-security-considerations)
9. [References](#9-references)
- [Appendix A. Differences from candid 0.10 (Informative)](#appendix-a-differences-from-candid-010-informative)
- [Appendix B. Examples (Informative)](#appendix-b-examples-informative)

## 1. Introduction

### 1.1. Scope

This document defines:

- the syntax of types, as written in descriptions and in annotations of textual values
  ([Section 4](#4-types));
- the syntax of a description: imports, type definitions and a service declaration
  ([Section 5](#5-descriptions));
- how imports are expanded ([Section 5.3](#53-imports));
- what a description means: the type each name is defined as, and the type of the
  service, or that the description is rejected ([Section 6](#6-meaning)).

The following are out of scope:

- **File systems.** Where files are, and how an absolute path or a symbolic link
  resolves, is up to the implementation ([Section 5.3](#53-imports)).
- **Comments as documentation.** Tools commonly attach a comment that precedes a
  definition, method or field to it as documentation. Comments have no meaning in this
  document.
- **Printing, and bindings for programming languages.** This document says which text
  denotes a type, not how a type is printed or how it maps into a language.

### 1.2. Requirements Language

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD
NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to
be interpreted as described in BCP 14 [RFC2119] [RFC8174] when, and only when, they
appear in all capitals, as shown here.

### 1.3. Notation

**Grammar.** Grammars are written in ABNF [RFC5234], with the two departures of
[TEXT], Section 1.3: terminals denote Unicode scalar values, and quoted strings are
case-sensitive.

**Types.** Types are those of the Candid data model [CANDID]. A type may be recursive,
so it is in general an infinite tree, with finitely many distinct subtrees. Two types
are the same, written `s ≡ t`, when they are the same tree; field and method lists are
compared without regard to order. This is the equivalence of [TEXT], Section 5.1.

### 1.4. Terminology

**description**
: The text of an interface description, often stored in a file whose name ends in
  `.did`.

**reject**
: To report that the input has no meaning, and to produce no interface. How the
  rejection is reported is up to the implementation.

**resolve**
: To replace a type name by the type expression it is defined as, repeatedly, until the
  outermost form is not a name.

## 2. Overview

A description is read in three steps:

```
text ──parse──▶ imports, definitions ──expand──▶ definitions ──check──▶ interface
                and service                      and service
                (Sections 3 to 5.2)              (Section 5.3)          (Section 6)
```

A description without imports needs no expanding.

Parsing does not depend on what names mean. It turns
`type list = opt record { head : nat; tail : list }` into a definition of the name
`list`, with field names hashed into field ids, and rejects text that is malformed
however its names are defined, such as a record that has two fields with one id.

Expanding reads every description that one imports, and combines their definitions,
and the methods of their services where the import asks for them, into one description.

Checking gives each name the type it denotes. It rejects names that are not defined,
definitions that go round in a circle without reaching a type, such as
`type A = B; type B = A`, and types that cannot occur, such as a service whose method
is not a function.

The result is an **interface**: the type of every defined name, and, if the description
declares a service, the service's type and its initialization arguments, if any.

## 3. Lexical Structure

A description is divided into tokens as textual values are, by [TEXT], Section 3. The
keywords, identifiers, numbers, text literals, punctuation, whitespace and comments
defined there are the tokens of a description too. In particular:

- Names of primitive types, such as `nat` and `text`, are identifiers. `null`,
  `principal` and `blob` are keywords.
- Names of function annotations, such as `query`, are identifiers too. They name an
  annotation only where one can appear ([Section 4.1](#41-grammar)), and are ordinary
  identifiers elsewhere: `record { query : nat }` is a record with a field `query`.
- A field or method name that is a keyword, or that is not an identifier, is written as
  a text literal: `record { "opt" : nat; "my field" : nat }`.
- The arrow `->` is one token.

## 4. Types

### 4.1. Grammar

The grammar in this section is over the tokens of [Section 3](#3-lexical-structure).
Whitespace and comments may appear between any two tokens. `label` and `name` are those
of [TEXT], Section 4.1.

```abnf
type       = identifier
           / "null" / "principal"
           / "opt" type / "vec" type / "blob"
           / "record" "{" [field *(";" field) [";"]] "}"
           / "variant" "{" [alt *(";" alt) [";"]] "}"
           / "func" functype
           / "service" methods

field      = label ":" type / type
alt        = label ":" type / label

functype   = params "->" params *annotation
params     = "(" [param *("," param) [","]] ")"
param      = name ":" type / type
annotation = "query" / "composite_query" / "oneway"

methods    = "{" [method *(";" method) [";"]] "}"
method     = name ":" (functype / identifier)
```

An identifier as a `type` is either the name of a primitive type or a type name
([Section 4.2](#42-abstract-syntax)).

In a record, `a : nat` is a named field and `a` alone is a positional field of type
`a`. In a variant, `a` alone is a field of type `null`. One token of lookahead, `:` or
not, tells them apart.

After a function's results, an identifier is an annotation, and one that is not an
annotation's name ends the function type, so the text is rejected unless the grammar
continues with it, which it never does. Which annotations a function type may have
together is a matter of well-formedness ([Section 6.3](#63-well-formedness)).

Annotation names are not keywords so that adding one does not break descriptions that
already use the name, as a field, a method or a type. `composite_query` was added as a
keyword, and broke any description that used it as a name.

### 4.2. Abstract Syntax

Parsing produces a type expression in the following abstract syntax:

```
t ::= p                                  primitive type
    | x                                  type name
    | opt t | vec t
    | record{i₁ : t₁; …; iₙ : tₙ}        field ids, distinct
    | variant{i₁ : t₁; …; iₙ : tₙ}       field ids, distinct
    | func (t₁, …, tₙ) → (u₁, …, uₘ) A   A: a set of annotations
    | service{m₁ : t₁; …; mₙ : tₙ}       method names, distinct
```

The rest of this section says how the concrete syntax maps to this form, and which
further inputs MUST be rejected during parsing.

**Primitive types.** The identifiers `bool`, `nat`, `int`, `nat8`, `nat16`, `nat32`,
`nat64`, `int8`, `int16`, `int32`, `int64`, `float32`, `float64`, `text`, `reserved`
and `empty`, and the keywords `null` and `principal`, denote the primitive type of that
name. Any other identifier is a type name *x*.

**Blobs.** `blob` is `vec nat8`.

**Field ids.** Labels denote field ids, and record fields without a label are numbered
by position, exactly as in record values ([TEXT], Section 4.2). The rules for distinct
ids apply too: a record or variant type in which two fields have the same id, after
labels are hashed and positions numbered, MUST be rejected.

**Variants.** A variant field written as a `label` alone has type `null`:
`variant { a }` is `variant{hash("a") : null}`.

**Parameters and results.** A `param` may be named. The name has no meaning, but MUST
be well-formed UTF-8, and two parameters, or two results, of one function type MUST NOT
have the same name. A parameter and a result may share a name.

**Methods.** A method name is the name's bytes, which MUST be well-formed UTF-8. Two
methods of one service MUST NOT have the same name. A method written `m : x` has the
type name *x* as its type; [Section 6.3](#63-well-formedness) requires that it resolve
to a function type.

## 5. Descriptions

### 5.1. Grammar

```abnf
description = [definition *(";" definition) [";"]] [service [";"]]

definition  = "type" identifier "=" type
            / "import" ["service"] text-literal

service     = "service" [identifier] ":" [params "->"] (methods / identifier)
```

The definitions, which include imports, come first, separated by semicolons, and the
service declaration, if any, comes last. A semicolon after the last definition is
optional, whether or not a service declaration follows. Imports and type definitions may
come in any order.

### 5.2. Abstract Syntax

Parsing produces a sequence of imports, a sequence of definitions `x₁ = t₁; …; xₙ = tₙ`,
and an optional service declaration. An import is `import r` or `import service r`,
where *r* is the bytes of the text literal, which MUST be well-formed UTF-8. A service
declaration has one of two forms:

```
S ::= s                                  a service
    | (t₁, …, tₙ) → s                    a service constructor, with initialization arguments
```

where *s* is `service{…}`, from `methods`, or a type name, from `identifier`. The
identifier after the keyword `service`, if any, has no meaning. A constructor's
parameters follow the rules for parameters in [Section 4.2](#42-abstract-syntax).

The definitions are the **environment** Γ, which maps each *xᵢ* to *tᵢ*. A description
MUST be rejected if two definitions define the same name, or if a definition defines the
name of a primitive type, such as `type nat = text`.

### 5.3. Imports

Imports are expanded before anything else: the description being read, together with
the descriptions it imports, becomes one description without imports, its
**expansion**, and [Section 6](#6-meaning) gives the expansion its meaning. A
description without imports is its own expansion.

**Paths.** Descriptions are files, and an import names one by its **path**, *r*:
segments separated by `/`. A path that begins with `/` is absolute; any other is
relative to the directory of the file that contains the import. Every other character,
including `?` and `#`, is part of a segment. An empty path names no file, and MUST be
rejected.

Paths are compared after **normalization**, which is textual: a `.` segment and an
empty one are removed, and a `..` segment removes the segment before it, if that is not
also `..`. A `..` with nothing before it remains in a relative path, where it names the
parent directory, and is removed from an absolute one. So `sub/../a.did` and `a.did`
name the same file, and `../shared/a.did` names a file beside the importer's directory.
Two imports name the same description exactly when their normalized paths, made
relative to the same directory, are equal.

Where the file system is, how an absolute path resolves, and whether symbolic links are
followed are up to the implementation. A file that cannot be read, or is not a
description, MUST be rejected.

**The import graph.** The descriptions reachable from the one being read, by following
imports of either kind, are its **imports, direct and indirect**. A description MUST be
rejected if one of them imports it, or if the graph has any other cycle: an import
cycle has no order in which the descriptions could be read, and is a mistake. A
description reached along more than one path is included once.

**Definitions.** The expansion's definitions are those of the description and of all its
imports, direct and indirect. The names form one namespace, so
[Section 5.2](#52-abstract-syntax) rejects the expansion if two of these descriptions
define the same name, even as the same type.

Each description MUST also be **self-contained**: every name in it is defined in it or
in one of its imports, direct or indirect. A description cannot use a name defined only
by a description that imports it, so that every description in the graph can be read on
its own, with the same meaning.

**Methods.** A description D **provides** methods if it declares a service or imports
one with `import service`, and the methods it provides, M(D), are:

- the methods of its own service declaration, if any: those of `service{…}`, or of the
  service type that a type name resolves to in the expansion; and
- M(E), for each description E that D imports with `import service`.

A description that two of these reach is counted once. A plain `import` contributes
definitions and no methods: not those of the imported description, nor any it imports
with `import service`.

For each `import service` of a description E, the description being read MUST be
rejected if E provides no methods, or if E's own service declaration is a constructor.
It MUST also be rejected if two of the methods in any M(D) have the same name.

**The service.** The expansion's service declaration is:

- the description's own, if it has no `import service`;
- otherwise, a service whose methods are M of the description being read, with the
  initialization arguments of its own declaration if that is a constructor.

So a description with no service declaration of its own, but with an `import service`,
declares the imported service.

## 6. Meaning

### 6.1. Names

Every type name in a type expression of the description, in a definition or in the
service declaration, MUST be defined in Γ. A description with a name that is not
defined MUST be rejected, even if nothing uses the definition in which it occurs.

A name *x* is **productive** if resolving it reaches a type expression that is not a
name: the chain *x*, Γ(*x*), Γ(Γ(*x*)), … contains something other than a name. Since Γ
is finite, a name that is not productive is part of a cycle of names, such as
`type A = A` or `type A = B; type B = A`, or leads into one. A description in which any
name is not productive MUST be rejected.

A cycle through a type constructor is productive, and is how a recursive type is
written: in `type list = opt record { head : nat; tail : list }`, resolving `list`
reaches `opt`.

### 6.2. Denotation

In an environment Γ whose names are all defined and productive, every type expression
*t* denotes a type `⟦t⟧`:

```
⟦p⟧                           = p
⟦x⟧                           = ⟦Γ(x)⟧
⟦opt t⟧                       = opt ⟦t⟧
⟦vec t⟧                       = vec ⟦t⟧
⟦record{i₁ : t₁; …}⟧          = record{i₁ : ⟦t₁⟧; …}
⟦variant{i₁ : t₁; …}⟧         = variant{i₁ : ⟦t₁⟧; …}
⟦func (t₁, …) → (u₁, …) A⟧    = func (⟦t₁⟧, …) → (⟦u₁⟧, …) A
⟦service{m₁ : t₁; …}⟧         = service{m₁ : ⟦t₁⟧; …}
```

For a recursive environment these equations do not terminate as a computation, but
they have exactly one solution in which every type is a tree: the tree obtained by
replacing names by their definitions without end. Productivity guarantees that each
replacement eventually yields a constructor or a primitive type, so every node of the
tree is defined. Such a tree has only finitely many distinct subtrees, which is what
lets a type table hold it.

A name and its definition denote the same type, so `type A = B` makes `A` an alias of
`B`, not a new type.

### 6.3. Well-formedness

A type is **well-formed** if:

1. every method of every service type in it has a function type;
2. no function type in it has an annotation twice, or more than one **mode**; and
3. every function type in it annotated `oneway` has no results.

A mode says how a function is called: `query`, `composite_query` or `oneway`, and an
ordinary update call if it has none. A function is called in one way, so `query oneway`
is not well-formed. Every annotation defined so far is a mode. One added later need not
be, and could then combine with a mode: the abstract syntax is a set of annotations
so that it can.

These rules are about types, wherever they come from. A type decoded from binary data
is subject to them too.

Every definition MUST denote a well-formed type, whether or not anything refers to it.
A description with a definition that does not MUST be rejected. So
`type S = service { m : T }; type T = opt nat` is rejected, because the method `m` has
the type `opt nat`.

These conditions are on the denoted type, after names are resolved. `type T = func () -> ();
type S = service { m : T }` is well-formed, and so is a method whose type is a name for a
name for a function type.

### 6.4. The Interface

The meaning of a description is an **interface**: a map from each name *x* defined in
Γ to `⟦x⟧`, and the meaning of the service declaration, which is one of:

- **none**, if the description has no service declaration;
- **service** `⟦s⟧`, for a declaration *s*;
- **constructor** `(⟦t₁⟧, …, ⟦tₙ⟧) → ⟦s⟧`, for a declaration `(t₁, …, tₙ) → s`.

In the last two cases, `⟦s⟧` MUST be a service type, and the description MUST be
rejected otherwise: `service : T` is rejected if `T` names a function type. Each `⟦tᵢ⟧`
MUST be well-formed.

## 7. Conformance

An implementation conforms to this document if, for every description within its scope,
it either rejects the description or yields an interface that agrees with the one
[Sections 4 to 6](#4-types) give, and it rejects only where those sections require it
or where [Section 8](#8-security-considerations) permits it. Two interfaces agree if
they define the same names, each name denotes the same type in both (`≡`), and their
service declarations are of the same form with the same types.

The representation of types is up to the implementation. The reference model holds a
type as a table of entries and a root, as the binary format does, and so a type
defined once may be held as two entries, or two names as one.

Conformance vectors of kind `did`, each a description and the expected interface or a
rejection, are written from the reference model in [lean/](../), whose
[Candid/Did/](../Candid/Did/) implements this document, and published under
[conformance/](../../conformance/). A vector with imports carries the descriptions it
imports, each at a relative path; the description being read is `main.did`, and every
path is relative to its directory.

## 8. Security Considerations

A description is often fetched from a service it describes, which need not be trusted:
a tool that shows a service's interface reads the description the service provides. An
implementation MAY reject a description for lack of resources, as described for binary
data in [CANDID], and SHOULD bound the following:

- **Nesting.** Every bracket adds a level of recursion to a straightforward parser.
- **Chains of names.** A naïve check of productivity follows each name to its end, which
  costs time quadratic in the length of a chain `type A₁ = A₂; type A₂ = A₃; …`.
  Marking names as they are resolved makes it linear.
- **Recursion.** An implementation that expands names, rather than sharing them,
  produces a tree of unbounded size from a recursive type. A type MUST be held with its
  recursion intact, as a graph.
- **Imports.** A description from an untrusted source names files to read, possibly
  outside its own directory. An implementation SHOULD bound how many descriptions an
  import graph may have and how deep it may be, and MAY restrict which directories
  imports can reach. A description that tools generate from a program, as a service
  usually publishes about itself, has no imports.
- **Field ids.** Hash collisions are rejected ([Section 4.2](#42-abstract-syntax)), and
  a description can be crafted to collide. Rejecting it is the required behavior, not a
  failure.

## 9. References

### 9.1. Normative References

[CANDID]
: DFINITY, "Candid Specification", [spec/Candid.md](../../spec/Candid.md). For the data
  model and the field-id hash.

[TEXT]
: "Candid Textual Values", [TextValues.md](TextValues.md). For the lexical structure,
  labels and names, and the equivalence of types.

[RFC2119]
: Bradner, S., "Key words for use in RFCs to Indicate Requirement Levels", BCP 14,
  RFC 2119, March 1997.

[RFC5234]
: Crocker, D., Ed., and P. Overell, "Augmented BNF for Syntax Specifications: ABNF",
  STD 68, RFC 5234, January 2008.

[RFC8174]
: Leiba, B., "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words", BCP 14,
  RFC 8174, May 2017.

## Appendix A. Differences from candid 0.10 (Informative)

This appendix lists where this document decides something [CANDID] does not, and where
it differs from `candid_parser` 0.10, the Rust implementation. Each item that differs
from 0.10 is a proposed change to 0.10, or a decision this draft still has to make.

### A.1. Decided Here, Silent in Candid.md

- Definitions are separated by semicolons, and one after the last is optional, even
  before the service declaration. This agrees with 0.10. [CANDID] writes `<def>;*`.
- A function type has at most one mode ([Section 6.3](#63-well-formedness)), agreeing
  with 0.10. [CANDID] writes `<funcann>*` and allows any annotations together. The
  grammar still allows a list, so that a future annotation that is not a mode can be
  written with one that is.
- A definition is checked whether or not it is used ([Section 6.3](#63-well-formedness)),
  agreeing with 0.10.
- Names of types and fields are those of [TEXT], including the rule that a name written
  as text must be UTF-8, agreeing with 0.10.
- Parameter names do not repeat within a list, agreeing with 0.10. [CANDID] does not
  say.
- The meaning of a description ([Section 6.4](#64-the-interface)). [CANDID] describes
  the parts but not the whole.
- How imports resolve, and what they include ([Section 5.3](#53-imports)). [CANDID]
  says an import refers to a file "by URL" and includes its definitions "textually".
  Imports are file paths, as in 0.10, which reads them from the file system only;
  they are relative to the importing description, as in 0.10; names are visible
  through indirect imports, as in 0.10; a name defined twice is rejected, as in 0.10;
  and import cycles are rejected, as 0.10 does, with a misleading error about a
  duplicate binding. That an imported description cannot use the importer's names is
  [CANDID]'s rule, which 0.10 does not check.
- Names are not qualified by the description that defines them, and will not be: an
  import is a simple way to reuse definitions, not a module system. Candid types are
  structural, so a name is only a label, and a clash between two imported descriptions
  is resolved by defining the type again under another name, which is the same type.

### A.2. Different from candid 0.10

| Input | candid 0.10 | This document |
|---|---|---|
| `type nat = text` | accepted; `nat` still denotes the primitive type everywhere | rejected ([5.2](#52-abstract-syntax)) |
| `type A = record { 4294967295 : nat; nat }` | panics in a debug build | rejected ([TEXT], Section 4.2) |
| `type A = record { query : nat }` | rejected: `query` is a keyword | accepted ([3](#3-lexical-structure)) |
| `import "b.did"`, where `b.did` uses a name that only the importer defines | accepted | rejected: not self-contained ([5.3](#53-imports)) |
| `import "mid.did"`, where `mid.did` has `import service "svc.did"` | `svc.did`'s methods join the importer's service | they do not: a plain import contributes no methods |
| `import service "mid.did"`, where `mid.did` declares no service but has `import service "svc.did"` | rejected: no main service | accepted: `mid.did` provides `svc.did`'s methods |
| `import "sub/../a.did"; import "a.did"` | `a.did` read twice, so its names are defined twice | one description, read once |
| Two merged methods with different names whose field-id hashes collide | rejected | accepted: method names are not hashed |

Each of these is a case that existing descriptions are unlikely to rely on. The lexical
differences of [TEXT], Appendix B.2, apply to descriptions too. Whether
0.10 should change to reject `type nat = text` is not decided; this document rejects it
because the definition could never be used.

### A.3. Open Issues

- **Unknown annotations in binary data.** A decoder that meets an annotation byte it
  does not know rejects the whole message, even if the function type is only in a part
  it would skip, so adding an annotation breaks every older decoder that sees one. A
  function value is encoded the same whatever its annotations, so a decoder could skip
  it instead, and treat a function type with an unknown annotation as a type it can only
  accept as `reserved` or an option, as it does a future type. That is a change to the
  binary format, for the chapter that specifies it.
- **One lexical chapter.** This document borrows its lexical structure from [TEXT]. The
  two should share one chapter when they become one specification.

## Appendix B. Examples (Informative)

| Description | Result |
|---|---|
| (empty) | no names, no service |
| `type A = nat;` | `A` is `nat` |
| `type list = opt record { head : nat; tail : list };` | `list` is a recursive type |
| `type A = B; type B = opt A;` | `A` and `B` are the same type, `opt opt opt …` |
| `type A = B; type B = A;` | rejected: not productive |
| `type A = vec B;` | rejected: `B` is not defined |
| `type A = nat; type A = nat;` | rejected: `A` defined twice |
| `type nat = text;` | rejected: a primitive type's name |
| `type A = record { nat; 0 : text };` | rejected: id 0 twice |
| `type f = func (x : nat, x : nat) -> ();` | rejected: parameter `x` twice |
| `type f = func () -> () query oneway;` | rejected: two modes |
| `type A = record { query : nat };` | `A` has a field named `query` |
| `type f = func () -> (nat) oneway;` | rejected: `oneway` with a result |
| `type S = service { m : T }; type T = opt nat;` | rejected: method `m` is not a function |
| `service : { m : (nat) -> (text) query }` | a service with one method |
| `type S = service {}; service : S` | the service `S` |
| `type F = func () -> (); service : F` | rejected: not a service type |
| `service : (nat) -> { }` | a constructor taking a `nat` |
| `service : { "a b" : () -> () }` | a method named `a b` |
| `type A = nat service : {}` | `A` is `nat`, and an empty service |
| `service : {}; type A = nat;` | rejected: definitions come first |
| `import "a.did"; type B = A;`, with `a.did` holding `type A = nat;` | `A` and `B` are `nat` |
| `import "a.did"; type A = nat;`, with `a.did` holding `type A = nat;` | rejected: `A` defined twice |
| `import "a.did";`, with `a.did` holding `import "main.did";` | rejected: an import cycle |
| `import service "a.did"; service : { m : () -> () }`, with `a.did` declaring `service : { n : () -> () }` | a service with methods `m` and `n` |
| `import "a.did"; service : {}`, with `a.did` declaring `service : { n : () -> () }` | a service with no methods |

[CANDID]: ../../spec/Candid.md
[TEXT]: TextValues.md
