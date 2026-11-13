# Candid Types and Values

**Status:** Draft. Not normative. Until this document replaces the corresponding part of
[spec/Candid.md][CANDID] under the conditions of [REWRITE.md §6](../../REWRITE.md#6-the-ratchet),
that document governs wherever the two disagree. [Appendix A](#appendix-a-differences-from-candidmd-and-candid-010-informative)
lists the places where this one decides something the current specification leaves open,
and where it disagrees with `candid` 0.10.

**Abstract.** This document specifies the Candid data model: the types, the values each
type has, and field ids. It then specifies the two relations that make Candid suitable
for evolving interfaces: subtyping, which says when one type may replace another, and
coercion, which says what a value of one type becomes when it is read at another. The
syntax of types, of values and of messages is specified elsewhere.

## Table of Contents

1. [Introduction](#1-introduction)
2. [Overview](#2-overview)
3. [Types](#3-types)
4. [Values](#4-values)
5. [Subtyping](#5-subtyping)
6. [Coercion](#6-coercion)
7. [Properties (Informative)](#7-properties-informative)
8. [Conformance](#8-conformance)
9. [Security Considerations](#9-security-considerations)
10. [References](#10-references)
- [Appendix A. Differences from Candid.md and candid 0.10 (Informative)](#appendix-a-differences-from-candidmd-and-candid-010-informative)
- [Appendix B. Examples (Informative)](#appendix-b-examples-informative)

## 1. Introduction

### 1.1. Scope

This document defines:

- the types of Candid, what makes a type well-formed, and when two types are the same
  ([Section 3](#3-types));
- the field-id hash ([Section 3.3](#33-field-ids));
- the values of each type ([Section 4](#4-values));
- the subtype relation ([Section 5](#5-subtyping));
- coercion, of a value and of a sequence of arguments ([Section 6](#6-coercion)).

The following are defined elsewhere:

- **Syntax.** Types are written in the syntax of [DID], and values in that of [TEXT].
  This document writes both in the abstract notation of
  [Section 1.3](#13-notation).
- **The binary format.** How types and values are encoded in a message, and how a
  message is decoded, is specified in [CANDID], Section "Binary Format". Decoding a
  message at a type is decoding the values at the types the message carries, then
  coercing them as an argument sequence ([Section 6.8](#68-argument-sequences)).

### 1.2. Requirements Language

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD
NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to
be interpreted as described in BCP 14 [RFC2119] [RFC8174] when, and only when, they
appear in all capitals, as shown here.

### 1.3. Notation

**Types** are written as follows, where *p* is a primitive type
([Section 3.1](#31-primitive-types)), *i* a field id, *m* a method name and *A* a set of
annotations:

```
t ::= p
    | opt t | vec t
    | record{i₁ : t₁; …; iₙ : tₙ}
    | variant{i₁ : t₁; …; iₙ : tₙ}
    | func (t₁, …, tₙ) → (u₁, …, uₘ) A
    | service{m₁ : t₁; …; mₙ : tₙ}
    | future(o, β)
```

**Values** are written `nat(n)`, `int(n)`, `nat8(n)` … `int64(n)` for numbers of the
named type; `float32(b)` and `float64(b)` for floating-point data with the bit pattern
*b*; `bool(b)`, `text(s)`, `null`, `opt(v)`, `vec(v₁, …, vₙ)`,
`record{i₁ = v₁; …; iₙ = vₙ}`, `variant{i = v}`, `principal(p)`, `service(p)` and
`func(p, m)`.

**Rules** are stated as definitions by cases, read in order: the first case that
applies is the one that holds.

### 1.4. Terminology

**accepts null**
: A type accepts null if it is `null`, `reserved` or an option type. These are exactly
  the types that `null` is a value of, and a missing field or argument of such a type is
  read as `null`.

**fails**, **undefined**
: The two ways a coercion can produce no value ([Section 6.1](#61-outcomes)).

## 2. Overview

A Candid interface is a set of method types, and an interface changes over time. A
service upgraded to a new version must still understand the messages old clients send,
and old clients must still understand what the new version replies. Candid makes this
possible in two parts.

**Subtyping** is a relation on types, `t <: t'`, read "*t* may be used where *t'* is
expected". A new version of a service is compatible with the old one when each
method's new type is a subtype of its old one. Subtyping lets a record gain fields, a
function return more results and accept fewer arguments, a variant lose cases, and any
type become optional.

**Coercion** turns a value of the type a message was sent at into a value of the type
the receiver expects: a field the receiver does not know is dropped, a field the sender
did not know is filled with `null`, and a value that does not fit an option is read as
the absent value. A receiver does this as part of decoding every message, without
consulting the subtype relation, except for function and service references.

The two are connected by **soundness** ([Section 7](#7-properties-informative)): if
`t <: t'`, every value of type *t* coerces to a value of type *t'*.

## 3. Types

### 3.1. Primitive Types

The primitive types and their values are:

| Type | Values |
|---|---|
| `nat` | the natural numbers, without bound |
| `int` | the integers, without bound |
| `natN` for N = 8, 16, 32, 64 | the integers from 0 to 2^N − 1 |
| `intN` for N = 8, 16, 32, 64 | the integers from −2^(N−1) to 2^(N−1) − 1 |
| `float32`, `float64` | IEEE 754 [IEEE754] binary32 and binary64 data, one per bit pattern |
| `bool` | true and false |
| `text` | sequences of Unicode scalar values [UNICODE] |
| `null` | the single value `null` |
| `reserved` | the single value `null`, whatever was sent ([Section 6.2](#62-reserved-and-primitive-types)) |
| `empty` | none |
| `principal` | the identities of services and users, each a sequence of at most 29 bytes |

A principal is opaque to Candid: no part of this document looks inside one. The bound
of 29 bytes is the Internet Computer's [IC-INTERFACE], whose principals Candid
describes. A decoder MUST reject a longer one, whether it is a `principal` or the
principal of a reference ([Section 4](#4-values)). How principals are written as text is
in [TEXT], Appendix A.

A float value is its bit pattern, so `+0.0` and `−0.0` are different values, and so are
NaNs with different payloads.

`reserved` is the type of a field whose content is to be ignored, and `empty` the type of
something that cannot occur: a variant case that is never used, or a parameter of a
function reference that will never be called.

### 3.2. Composite Types

**Options.** `opt t` has the values of *t*, wrapped, and the absent value `null`.

**Vectors.** `vec t` is a finite sequence of values of type *t*.

**Records.** `record{i₁ : t₁; …; iₙ : tₙ}` is a value for each field: one of type *tₖ*
for each id *iₖ*. The fields are unordered: two record types that list the same fields
in a different order are the same type.

**Variants.** `variant{i₁ : t₁; …; iₙ : tₙ}` is one of the cases: an id *iₖ* and a value of
type *tₖ*. The cases are unordered. A variant with no cases has no values.

**Functions.** `func (t₁, …, tₙ) → (u₁, …, uₘ) A` is the type of a reference to a
method that takes arguments of types *t₁* … *tₙ* and returns results of types *u₁* …
*uₘ*. Parameters and results are ordered. *A* is a set of annotations, each of which says
something about how the function is called:

- `query`: the function changes no state, so a call may be answered from a replica's
  state without consensus;
- `composite_query`: a query that may itself call queries;
- `oneway`: the caller does not wait for a reply, and there are no results.

These three are **modes**, and a function has at most one; one without any is an update
call. Annotations defined in a later version need not be modes.

**Services.** `service{m₁ : t₁; …; mₙ : tₙ}` is the type of a reference to a service with
methods named *m₁* … *mₙ*, each a sequence of Unicode scalar values, of function types
*t₁* … *tₙ*. The methods are unordered.

**Future types.** `future(o, β)` is a type that a later version of Candid defines and
this one does not: only the binary format can carry one, identified by an opcode *o* and
the bytes β that came with it ([CANDID], Section "Deserialisation of future types").
This version knows nothing of its values, and represents every one of them as `null`.

### 3.3. Field Ids

A field id is a natural number less than 2³². Records and variants are keyed by field
ids, and syntax lets a field be named instead: a name stands for the id that the
**field-id hash** gives it. For a name whose UTF-8 encoding [UNICODE] is the bytes
*b₀* … *bₖ*:

```
hash(b₀ … bₖ) = (b₀·223^k + b₁·223^(k−1) + … + bₖ·223^0) mod 2³²
```

The hash is of the bytes, not of the characters, so a name outside ASCII hashes its
encoding. Once hashed, a name has no further meaning: `record{hash("a") : nat}` and
`record{97 : nat}` are the same type.

Two names may have the same hash. A record or variant type in which two fields have
the same id, whether written as names or as numbers, is not well-formed
([Section 3.5](#35-well-formedness)).

### 3.4. Recursive Types and Equivalence

A type may refer to itself, through a name in [DID] or a type table in the binary format,
so in general a type is an infinite tree. It has only finitely many distinct subtrees,
which is what lets a finite description or table hold it. `type list = opt record {
head : nat; tail : list }` is the tree that unfolds `opt record{…}` without end.

Two types are **equivalent**, `s ≡ t`, when they are the same tree, with the fields of a
record or variant, the methods of a service and the annotations of a function compared
without regard to order. Equivalence does not depend on how a type is written: a name
and its definition are equivalent, and so are two tables that share structure
differently. Every relation in this document respects equivalence.

Equivalence is not subtyping in both directions. `record{}` and `record{a : opt nat}` are
each a subtype of the other ([Section 5](#5-subtyping)), and are not equivalent.

### 3.5. Well-Formedness

A type is **well-formed** if every type in it, at any depth, satisfies:

1. a record or variant has no two fields with the same id;
2. a service has no two methods with the same name, and every method has a function
   type;
3. a function has no annotation twice, and at most one mode;
4. a function annotated `oneway` has no results;
5. a function has fewer than 2³² parameters and fewer than 2³² results.

Everything in the rest of this document is defined for well-formed types only. A
description with a type that is not well-formed is rejected ([DID], Section 6.3), and a
decoder MUST reject a message whose types are not well-formed.

## 4. Values

A value *v* **has type** *t*, written `v : t`, as follows:

- for a primitive type, *v* is one of the values in the table of
  [Section 3.1](#31-primitive-types), tagged with the type: `nat8(5) : nat8`, but not
  `nat8(5) : nat`;
- `null : opt t`, and `opt(v) : opt t` if `v : t`;
- `vec(v₁, …, vₙ) : vec t` if `vₖ : t` for each *k*;
- `record{i₁ = v₁; …; iₙ = vₙ} : record{i₁ : t₁; …; iₙ : tₙ}` if `vₖ : tₖ` for each *k*:
  exactly one value for each field of the type;
- `variant{i = v} : variant{…; i : t; …}` if `v : t`;
- `principal(p) : principal`, for every principal *p*: a sequence of at most 29 bytes;
- `service(p) : service{…}`, for every principal *p* and every service type;
- `func(p, m) : func (…) → (…) A`, for every principal *p*, method name *m* and
  function type;
- `null : future(o, β)`.

A reference value carries no type: whether principal *p* provides a service of a given
type is not something a value can show. [Section 6.6](#66-references) is where reference
types are checked.

## 5. Subtyping

### 5.1. The Relation

The subtype relation `t <: t'` is the greatest relation on well-formed types such that
whenever `t <: t'`, one of the following holds:

1. **Top.** `t'` is `reserved`.
2. **Bottom.** `t` is `empty`.
3. **Primitive types.** `t` and `t'` are the same primitive type.
4. **Naturals.** `t` is `nat` and `t'` is `int`.
5. **Principals.** `t` is a service type and `t'` is `principal`.
6. **Options.** `t'` is an option type, whatever `t` is.
7. **Vectors.** `t = vec s`, `t' = vec s'`, and `s <: s'`.
8. **Records.** `t` and `t'` are record types, and for each field `j : s'` of `t'`,
   either `t` has a field `j : s` with `s <: s'`, or `t` has no field `j` and `s'`
   accepts null.
9. **Variants.** `t` and `t'` are variant types, and for each field `i : s` of `t`, `t'`
   has a field `i : s'` with `s <: s'`.
10. **Functions.** `t = func (t₁, …, tₙ) → (u₁, …, uₘ) A` and
    `t' = func (t'₁, …, t'ₙ') → (u'₁, …, u'ₘ') A'`, where `A = A'`, and:
    - for each parameter *k* ≤ *n* of `t`, either *k* ≤ *n'* and `t'ₖ <: tₖ`, or
      *k* > *n'* and `tₖ` accepts null; and
    - for each result *k* ≤ *m'* of `t'`, either *k* ≤ *m* and `uₖ <: u'ₖ`, or
      *k* > *m* and `u'ₖ` accepts null.
11. **Services.** `t` and `t'` are service types, and for each method `n : s'` of `t'`,
    `t` has a method `n : s` with `s <: s'`.
12. **Future types.** `t` and `t'` are the same future type, `future(o, β)`.

A pair of types not covered by any rule is not related: `nat <: nat8` and
`text <: nat` do not hold.

The relation is the *greatest* one closed under the rules, because recursive types are
infinite: `list <: list` for the recursive `list` of [Section 3.4](#34-recursive-types-and-equivalence)
holds because assuming it is consistent with the rules, not because a finite argument
reaches the end of the type.

### 5.2. What the Rules Allow (Informative)

The rules are designed so that an interface can change in these ways without breaking
its clients:

- **Records** may gain fields when they are results, and lose fields of a type that
  accepts null. Rule 8 allows both, so a record used both as a parameter and as a
  result can still gain optional fields: a party that does not know a field reads it as
  `null`.
- **Variants** may lose cases. To add a case to a variant that is sent to clients, make
  the variant optional: a client that does not know the case reads `null`.
- **Functions** may take fewer arguments and return more results. A parameter type may
  become more general and a result type more specific, as is usual for functions; an
  argument added at the end must accept null.
- **Services** may gain methods, and a method's type may change as functions may.
- **Options.** Any type may become optional (rule 6), and any value that does not fit
  the new option is read as `null` ([Section 6.3](#63-options)). This is what keeps
  subtyping transitive in the presence of rules 8 and 10. A field removed in one
  version and re-added at another type in a later one is still a subtype of the field
  across both changes; a reader that skipped the version in between reads `null`.

An implementation that checks upgrades SHOULD warn when only rule 6 relates an option
to a type that is not `null`, `reserved` or an option, such as `nat <: opt text`: the
change is allowed, but every value sent at the old type will be read as `null`.

### 5.3. Deciding Subtyping (Informative)

Subtyping is decidable, because a pair of types has finitely many pairs of subtrees. A
procedure can keep a set of pairs it has assumed related, return to them as proven when
it meets them again, and check every other pair against the rules.

The rules never search: every condition is a conjunction, and rule 6 holds outright
rather than being tried after another rule fails. A procedure that follows them
exactly can therefore share its assumptions across the whole question. One that tries a
rule and falls back to another when it fails, as an implementation of rule 6 might,
MUST withdraw every assumption made during the failed attempt, not only the one it
started from: a pair proved during the attempt may have been proved from that
assumption. candid 0.10 kept such pairs until 0.10.39, and accepted an incompatible
upgrade because of it.

Assumptions scoped to one path through the types, rather than shared, give the right
answer at a cost exponential in the depth of the types.

## 6. Coercion

### 6.1. Outcomes

Coercing a value *v* of type *t* at a type *t'* is written `C(v : t, t')`. It has one of
three outcomes:

- a **value** *v'*, written `v : t ~> v' : t'`;
- **failure**: no value, and an enclosing option reads the whole as `null`
  ([Section 6.3](#63-options));
- **undefined**: no value, and nothing recovers from it. A coercion that needs an
  undefined one is undefined, and so a message that needs one is rejected.

Coercion is defined for every *v*, *t* and *t'* with `v : t` and both types well-formed.
The rules in Sections 6.2 to 6.7 are cases, taken in order: the first that applies
gives the outcome.

### 6.2. Reserved and Primitive Types

1. If *t'* is `reserved`, the outcome is `null`.
2. If *t* and *t'* are the same primitive type, the outcome is *v*.
3. If *t* is `nat` and *t'* is `int`, `nat(n)` becomes `int(n)`.
4. If *t* and *t'* are both primitive types otherwise, coercion fails.

A float value coerces to itself, bit for bit. No case is needed for `empty`, which has no
values.

### 6.3. Options

If *t'* = `opt u`:

1. If *t* accepts null:
   - if *v* = `opt(w)`, so that *t* = `opt s`: coerce `C(w : s, u)`. A value *w'* gives
     `opt(w')`; failure gives `null`; undefined stays undefined;
   - otherwise, *v* is `null`, or *t* is `reserved`, and the outcome is `null`.
2. Otherwise, if *t'* is an **infinite option**, the outcome is undefined. An infinite
   option is an option type whose content is again an infinite option, such as
   `type R = opt R`, so that removing `opt` never reaches another type.
3. Otherwise, coerce `C(v : t, u)`. A value *w* gives `opt(w)`; failure gives `null`;
   undefined stays undefined.

Case 3 reads a value that is not optional as present, if it coerces at the content
type. Case 1 keeps an absent value absent: at `opt opt nat`, `null` from `opt nat` stays
`null`, rather than becoming `opt(null)`.

Case 2 is undefined, not failure, because case 3 would ask the same question again at
the content type, which is the same infinite option. Reading the result as `null` would
answer a question by its own negation.

### 6.4. Vectors

If *t* = `vec s`, *t'* = `vec s'` and *v* = `vec(v₁, …, vₙ)`: coerce each `C(vₖ : s, s')` in
order. If all give values *v'ₖ*, the outcome is `vec(v'₁, …, v'ₙ)`. Otherwise the first
element that fails or is undefined gives the outcome.

### 6.5. Records and Variants

If *t* and *t'* are record types and *v* = `record{…}`: for each field `j : s'` of *t'*,
in ascending order of *j*:

- if *v* has a field *j*, with value *w* at type *s* in *t*: coerce `C(w : s, s')`;
- otherwise, if *s'* accepts null: the field is `null`;
- otherwise: fail.

If every field gives a value, the outcome is the record of those values. Otherwise the
first field that fails or is undefined gives the outcome. Fields of *v* that *t'* does
not have are ignored.

If *t* and *t'* are variant types and *v* = `variant{i = w}`, with *w* at type *s* in *t*:
if *t'* has a field `i : s'`, coerce `C(w : s, s')`, giving `variant{i = w'}` for a value
*w'* and passing failure or undefinedness on; if it has none, fail.

The order matters only when one part fails and another is undefined, under an enclosing
option: then the earlier part decides between `null` and rejection. It is the order in
which a decoder meets the parts.

### 6.6. References

1. If *t* is a service type and *t'* is `principal`, `service(p)` becomes `principal(p)`.
2. If *t* and *t'* are both function types, or both service types: if `t <: t'`, the
   outcome is *v*; otherwise coercion fails.

A reference is the one kind of value whose type a receiver cannot check against the
value itself, so case 2 checks the types instead. A decoder MUST therefore decide the
subtype relation for the reference types in a message.

### 6.7. Future Types and Other Cases

1. If *t* and *t'* are the same future type, the outcome is `null`.
2. In every case not covered above, coercion fails.

Case 2 covers values and types of different kinds, such as a record value at a variant
type or a vector at `text`.

### 6.8. Argument Sequences

A message carries a sequence of arguments, and a receiver expects a sequence of types.
Coercing `(v₁, …, vₙ) : (t₁, …, tₙ)` at `(t'₁, …, t'ₘ)` treats the sequences as records
with fields numbered by position. For each *k* from 1 to *m*, in order:

- if *k* ≤ *n*: coerce `C(vₖ : tₖ, t'ₖ)`;
- otherwise, if *t'ₖ* accepts null: `null`;
- otherwise: fail.

If every position gives a value, the outcome is the sequence of those values. Otherwise
the first position that fails or is undefined gives the outcome, and the message is
rejected either way. Arguments beyond *m* are ignored.

## 7. Properties (Informative)

The definitions are designed so that the following hold, for well-formed types. They are
obligations on the definitions, checked by the reference model on every value and type
it generates, and to be proved about it:

- **Reflexivity.** `t <: t`.
- **Transitivity.** `t <: t'` and `t' <: t''` imply `t <: t''`.
- **Roundtripping.** If `v : t`, then `v : t ~> v : t`.
- **Well-typedness.** If `v : t` and `v : t ~> v' : t'`, then `v' : t'`.
- **Soundness.** If `t <: t'` and `v : t`, then `C(v : t, t')` does not fail. It can be
  undefined, at an infinite option: for `type R = opt R`, `nat <: R`, and `C(nat(5) : nat, R)`
  is undefined.
- **Equivalence.** If `s ≡ s'` and `t ≡ t'`, then `s <: t` exactly when `s' <: t'`, and
  `C(v : s, t)` and `C(v : s', t')` have the same outcome.

**Coherence does not hold.** Coercing a value at *t'* and then at *t''* can give a
different value from coercing it at *t''* directly, even when `t <: t' <: t''`. The
difference is always that one is `null` where the other is an option value. For example,
`nat <: reserved <: opt nat`: coercing `nat(5)` at `opt nat` directly gives
`opt(nat(5))`, while coercing it at `reserved` first gives `null`, which then stays
`null` at `opt nat`. Subtyping guarantees that a value can
be read, not that every path to it reads the same.

**Completeness does not hold.** Subtyping is sound, but it does not relate every pair
of types for which coercion never fails. `variant{a : nat; b : empty}` is not a subtype
of `variant{a : nat}`, because rule 9 requires each case of the first in the second.
Yet no value has case `b`, since `empty` has no values, so every value of the first
coerces at the second. Such pairs involve a part of a type that no value can occupy.
Subtyping rejects them, which errs on the safe side: it can refuse an upgrade that would
have been harmless, never accept one that is not.

## 8. Conformance

An implementation conforms to this document if:

- it computes the field-id hash of [Section 3.3](#33-field-ids);
- where it decides subtyping, it decides the relation of
  [Section 5.1](#51-the-relation);
- where it coerces a value, as part of decoding or otherwise, it gives the outcome of
  [Section 6](#6-coercion): the same value, failure, or undefinedness. Outside an
  option, failure and undefinedness both reject a message, so an implementation need
  distinguish them only where an option encloses them.

Conformance vectors of kinds `hash`, `wellformed`, `subtype` and `coerce`, and the
coercion inside every `decode` vector, are written from the reference model in
[lean/](../), whose [Candid/Types.lean](../Candid/Types.lean),
[Candid/Hash.lean](../Candid/Hash.lean), [Candid/Value.lean](../Candid/Value.lean),
[Candid/Subtype.lean](../Candid/Subtype.lean) and [Candid/Coerce.lean](../Candid/Coerce.lean)
implement this document, and published under [conformance/](../../conformance/).
[Candid/SubtypeSpec.lean](../Candid/SubtypeSpec.lean) states the relation of
[Section 5.1](#51-the-relation) rule for rule.

## 9. Security Considerations

A receiver decides subtyping and coerces values for types that a sender chose, so both
must be bounded in the size of the types, not in anything a sender controls more
cheaply.

- **Subtyping.** A procedure that shares assumptions across the whole question takes
  time polynomial in the sizes of the two types. One that scopes them to a path takes
  time exponential in their depth: two tables of 41 entries, each referring to the next
twice, ask it 2⁴¹ questions.
- **References.** Every function or service reference in a message asks a subtype
  question ([Section 6.6](#66-references)). An implementation SHOULD remember the
  answer for a pair of types, rather than ask again for every reference of a vector.
- **Infinite options.** Case 3 of [Section 6.3](#63-options) unwraps the expected type
  one option at a time. An implementation MUST detect an infinite option rather than
  unwrap it until it runs out of stack.
- **Field ids.** The field-id hash is not resistant to collisions, and a sender can
  choose names that collide. A colliding type is not well-formed, and rejecting it is
  the required behavior.

## 10. References

### 10.1. Normative References

[CANDID]
: DFINITY, "Candid Specification", [spec/Candid.md](../../spec/Candid.md). For the binary
  format and deserialisation.

[DID]
: "Candid Interface Descriptions", [Did.md](Did.md). For the syntax of types.

[IEEE754]
: IEEE, "IEEE Standard for Floating-Point Arithmetic", IEEE Std 754-2019.

[RFC2119]
: Bradner, S., "Key words for use in RFCs to Indicate Requirement Levels", BCP 14,
  RFC 2119, March 1997.

[RFC8174]
: Leiba, B., "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words", BCP 14,
  RFC 8174, May 2017.

[TEXT]
: "Candid Textual Values", [TextValues.md](TextValues.md). For the syntax of values.

[UNICODE]
: The Unicode Consortium, "The Unicode Standard".

### 10.2. Informative References

[GARRIGUE]
: Garrigue, J., "Programming with Polymorphic Variants", ML Workshop, 1998. The
  field-id hash is the hash of polymorphic variant tags in OCaml.

[IC-INTERFACE]
: DFINITY, "The Internet Computer Interface Specification", section "Principals". The
  origin of the bound on the length of a principal.

[MINICANDID]
: [coq/MiniCandid.v](../../coq/MiniCandid.v): a formalization of subtyping and coercion
  for a fragment of Candid, with proofs of reflexivity, transitivity and soundness.

## Appendix A. Differences from Candid.md and candid 0.10 (Informative)

This appendix lists where this document decides something [CANDID] does not, and where
it differs from `candid` 0.10, the Rust implementation.

### A.1. Decided Here, or Restated

- **One rule for options.** [CANDID] states four rules for `t <: opt t'`, two with
  negative premises. Together they relate every type to every option, which is rule 6
  of [Section 5.1](#51-the-relation). Without negative premises the relation is the
  greatest fixed point of monotone rules, and so is well defined. candid 0.10 agrees.
- **Coercion as cases.** [CANDID] states coercion as rules with negative premises, such
  as "no coercion exists". Here it is a definition by cases with three outcomes, which
  says the same where [CANDID] is defined, and is undefined only at an infinite option,
  as [CANDID] says since #778.
- **The order of a record's fields** ([Section 6.5](#65-records-and-variants)), of a
  vector's elements and of arguments decides between failure and undefinedness. [CANDID]
  does not say. This is candid 0.10's order.
- **Future types.** [CANDID] says how to decode them, but not how they relate to other
  types. Here a future type is a subtype of itself, and the general rules make it a
  subtype of `reserved` and of every option, as `test/subtypes.test.did` asserts. Its
  values are all `null`.
- **Annotations** are a set, compared as sets by rule 10, and a function has at most one
  mode ([Section 3.5](#35-well-formedness)). [CANDID] identifies annotation lists up to
  reordering.
- **Transitivity.** [CANDID]'s statement of transitivity concludes `<t> <: <t'>`, a typo
  for `<t> <: <t''>`.
- **Principals** are at most 29 bytes ([Section 3.1](#31-primitive-types)). [CANDID]
  does not bound them. The Internet Computer and candid 0.10 do, and 0.10 relies on it
  to hold a principal in a fixed-size array.

### A.2. Different from candid 0.10

candid 0.10 agrees with every `subtype` and `coerce` vector, and on the values of every
type. One `decode` vector shows a difference in well-formedness:

| Input | candid 0.10 | This document |
|---|---|---|
| A `oneway` function type with a result | accepted | rejected ([Section 3.5](#35-well-formedness), item 4) |

### A.3. Open Issues

None.

## Appendix B. Examples (Informative)

Values are written without their types where the type is clear from the question.

| Question | Answer |
|---|---|
| `nat <: int` | holds |
| `int <: nat` | does not hold |
| `nat8 <: nat` | does not hold: the fixed-width types are unrelated |
| `text <: opt nat` | holds, by rule 6 |
| `variant{a : nat; b : empty} <: variant{a : nat}` | does not hold, though every value of the first coerces at the second ([Section 7](#7-properties-informative)) |
| `record{a : nat; b : text} <: record{a : int}` | holds: `b` is added |
| `record{a : nat} <: record{a : nat; c : opt text}` | holds: `c` accepts null |
| `record{a : nat} <: record{a : nat; c : text}` | does not hold |
| `variant{a : nat} <: variant{a : nat; b : text}` | holds: `b` is dropped |
| `variant{a : nat; b : text} <: variant{a : nat}` | does not hold |
| `func (int) → (nat) <: func (nat) → (int)` | holds |
| `func (nat, opt text) → () <: func (nat) → ()` | holds: the extra parameter accepts null |
| `func () → () query <: func () → ()` | does not hold: annotations must agree |
| `service{m : func () → ()} <: principal` | holds |
| `C(nat(5) : nat, int)` | `int(5)` |
| `C(int(5) : int, nat)` | fails |
| `C(nat(5) : nat, opt nat)` | `opt(nat(5))` |
| `C(text("x") : text, opt nat)` | `null` |
| `C(nat(5) : nat, opt opt nat)` | `opt(opt(nat(5)))` |
| `C(nat(5) : nat, opt reserved)` | `opt(null)`: `5` coerces to `null` at `reserved` |
| `C(null : opt nat, opt opt nat)` | `null` |
| `C(nat(5) : nat, R)` for `type R = opt R` | undefined |
| `C(record{a = 1; b = "x"}, record{a : int})` | `record{a = int(1)}` |
| `C(record{a = 1}, record{a : nat; c : opt text})` | `record{a = nat(1); c = null}` |
| `C(variant{b = "x"}, variant{a : nat})` | fails |
| `C((nat(1), nat(2)) : (nat, nat), (nat))` | `(nat(1))` |
| `C(() : (), (opt nat, null))` | `(null, null)` |

[CANDID]: ../../spec/Candid.md
[DID]: Did.md
[TEXT]: TextValues.md
