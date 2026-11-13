# Candid Binary Format

**Status:** Draft. Not normative. Until this document replaces the corresponding part of
[spec/Candid.md][CANDID] under the conditions of [REWRITE.md §6](../../REWRITE.md#6-the-ratchet),
that document governs wherever the two disagree. [Appendix A](#appendix-a-differences-from-candidmd-and-candid-010-informative)
lists the places where this one decides something the current specification leaves open,
and where it disagrees with `candid` 0.10.

**Abstract.** This document specifies the binary format of Candid: how a sequence of
values and their types is written as a message, and how a receiver reads a message at
the types it expects. A message carries its own types, so a receiver decodes it at those
and then coerces the values to its own, as [TYPES] defines. The document also says
which messages a receiver may reject for lack of resources.

## Table of Contents

1. [Introduction](#1-introduction)
2. [Overview](#2-overview)
3. [Numbers, Bytes and Text](#3-numbers-bytes-and-text)
4. [Messages](#4-messages)
5. [Types](#5-types)
6. [Values](#6-values)
7. [Deserialisation](#7-deserialisation)
8. [Serialisation](#8-serialisation)
9. [Resource Limits](#9-resource-limits)
10. [Conformance](#10-conformance)
11. [Security Considerations](#11-security-considerations)
12. [References](#12-references)
- [Appendix A. Differences from Candid.md and candid 0.10 (Informative)](#appendix-a-differences-from-candidmd-and-candid-010-informative)
- [Appendix B. Examples (Informative)](#appendix-b-examples-informative)

## 1. Introduction

### 1.1. Scope

This document defines:

- the encodings of numbers, byte sequences and text that the format is built from
  ([Section 3](#3-numbers-bytes-and-text));
- the layout of a message ([Section 4](#4-messages));
- how types are written in a message's type table ([Section 5](#5-types));
- how values are written at those types ([Section 6](#6-values));
- how a receiver reads a message at the types it expects
  ([Section 7](#7-deserialisation)), and what a sender may write
  ([Section 8](#8-serialisation));
- which messages a receiver may reject for lack of resources
  ([Section 9](#9-resource-limits)).

The types, their values, well-formedness, subtyping and coercion are defined in
[TYPES], and this document uses its notation for both. How a message reaches its
receiver, and what the receiver does with the values, is outside Candid.

### 1.2. Requirements Language

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD
NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to
be interpreted as described in BCP 14 [RFC2119] [RFC8174] when, and only when, they
appear in all capitals, as shown here.

### 1.3. Notation

Bytes are written in hexadecimal, two digits each, separated by spaces: `44 49 44 4c`.
The layout of a message is written as a sequence of named parts, where `x^n` is *n*
repetitions of the part *x*. Section numbers of the form "[TYPES], Section 6.8" refer to
the other documents.

### 1.4. Terminology

**decoder**, **encoder**
: A decoder reads messages and an encoder writes them. A **receiver** is a decoder
  given the types it expects.

**wire type**
: The type a message gives a value, as opposed to the **expected type** a receiver
  reads it at.

**rejects**
: A decoder rejects a message by reporting that it is not a valid message at the
  expected types, and yielding no values.

## 2. Overview

A message is a sequence of arguments, each a value with its type. It starts with the
four bytes `DIDL`. Then comes a **type table**: a list of composite types, numbered from
zero, each of which may refer to the others and to itself by number. Then the type of
each argument, as a primitive type or a number in the table. Then the values, one after
another, each written at its type with nothing to mark where it starts or ends.

Because a message carries its types, a receiver need not know what a sender's types
were. It decodes the values at the types in the message, then coerces them to the
types it expects ([TYPES], Section 6.8). A sender's interface may have changed in any
way that subtyping allows, and the receiver still reads what it understands: fields it
does not know are dropped, fields the sender did not know are `null`, and so on.

Decoding is strict. Every byte of a message has one meaning, and a message that breaks
any rule of this document is rejected, wherever the break is, even in a value the
receiver would have dropped.

## 3. Numbers, Bytes and Text

### 3.1. LEB128

**Unsigned LEB128** writes a natural number *n* as groups of 7 bits, least significant
group first, one group per byte in the low 7 bits. Every byte but the last has its high
bit set. The shortest form has no final byte that is zero, other than for *n* = 0, which
is the single byte `00`. For example, 300 is `ac 02`.

**Signed LEB128** (SLEB128) writes an integer *i* the same way, in two's complement:
the groups are those of *i* modulo 2^(7k) for *k* bytes, and the number is read back by
extending the sign from bit 6 of the last byte. The shortest form stops at the first
byte after which every remaining group would only repeat the sign. For example, −129 is
`ff 7e`, 64 is `c0 00`, and −64 is `40`.

A decoder MUST accept a number written with more bytes than the shortest form, such
as `80 80 00` for 0. An encoder SHOULD write the shortest form. A decoder MUST reject a
number whose last byte is missing because the message ends.

These encodings are those of [DWARF], Section 7.6.

### 3.2. Fixed-Width Numbers

A value of `natN` or `intN` is written in *N*/8 bytes, least significant byte first;
`intN` in two's complement. A value of `float32` or `float64` is its IEEE 754 [IEEE754]
bit pattern, written as a `nat32` or `nat64` is. Every bit pattern is a value, so a
decoder accepts any bytes here, including every NaN.

### 3.3. Blobs and Text

A **blob** is a length *n* in LEB128, then *n* bytes. A decoder MUST reject a blob
whose bytes run past the end of the message.

**Text** is a blob whose bytes are the UTF-8 encoding [UNICODE] of a sequence of
Unicode scalar values. A decoder MUST reject text that is not UTF-8, including an
overlong encoding and the encoding of a surrogate code point.

## 4. Messages

A message is:

```
message = magic table arguments values
magic   = 44 49 44 4c
table   = LEB128(n) entry^n
arguments = LEB128(k) typeref^k
values  = value(t₁) value(t₂) … value(tₖ)
```

where `entry` is a type table entry ([Section 5.2](#52-the-type-table)), `typeref` a
reference to a type ([Section 5.1](#51-type-references)), and `value(tⱼ)` the value of
argument *j* written at the type *tⱼ* that the *j*th `typeref` denotes
([Section 6](#6-values)).

A decoder MUST reject a message that does not start with the magic number, and one with
bytes left over after the last value. A message with no arguments is `44 49 44 4c 00
00`.

A result of a function is a message just as its arguments are.

## 5. Types

### 5.1. Type References

A **type reference** is an integer in SLEB128. A non-negative integer *i* refers to
entry *i* of the type table, and a decoder MUST reject a message where *i* is not less
than the number of entries. A negative integer is the opcode of a primitive type:

| Type | Opcode | Byte |
|---|---|---|
| `null` | −1 | `7f` |
| `bool` | −2 | `7e` |
| `nat` | −3 | `7d` |
| `int` | −4 | `7c` |
| `nat8` | −5 | `7b` |
| `nat16` | −6 | `7a` |
| `nat32` | −7 | `79` |
| `nat64` | −8 | `78` |
| `int8` | −9 | `77` |
| `int16` | −10 | `76` |
| `int32` | −11 | `75` |
| `int64` | −12 | `74` |
| `float32` | −13 | `73` |
| `float64` | −14 | `72` |
| `text` | −15 | `71` |
| `reserved` | −16 | `70` |
| `empty` | −17 | `6f` |
| `principal` | −24 | `68` |

A decoder MUST reject a type reference that is any other negative integer: a composite
type is always an entry of the table, never written in place. Since a reference is
SLEB128, entry 64 is `c0 00`; the single byte `40` is −64, which is no type.

### 5.2. The Type Table

Each entry of the table is a composite type. It starts with an opcode in SLEB128, and
what follows depends on the opcode:

| Type | Opcode | Byte | Then |
|---|---|---|---|
| `opt t` | −18 | `6e` | a type reference to *t* |
| `vec t` | −19 | `6d` | a type reference to *t* |
| `record{…}` | −20 | `6c` | LEB128(*n*), then *n* fields |
| `variant{…}` | −21 | `6b` | LEB128(*n*), then *n* fields |
| `func (…) → (…) A` | −22 | `6a` | the parameters, the results, the annotations |
| `service{…}` | −23 | `69` | LEB128(*n*), then *n* methods |
| `future(o, β)` | *o* < −24 | | a blob, β |

**Records and variants.** A field is its id in LEB128, then a type reference to its
type. The fields MUST be in strictly ascending order of id, and each id MUST be less
than 2³²; a decoder MUST reject a table that breaks either rule. Strict order rules out
a repeated id.

**Functions.** The parameters are LEB128(*n*) and then *n* type references, and the
results likewise. The annotations are LEB128(*a*) and then *a* bytes, each one of:

| Annotation | Byte |
|---|---|
| `query` | `01` |
| `oneway` | `02` |
| `composite_query` | `03` |

A decoder MUST reject any other byte as an annotation.

**Services.** A method is its name, as text ([Section 3.3](#33-blobs-and-text)), then a
type reference to its type. The methods MUST be in strictly ascending order of name,
compared by their UTF-8 bytes, which is the order of their code points; a decoder MUST
reject a table that breaks it.

**Future types.** An opcode below −24 is a type that a later version of Candid defines
([TYPES], Section 3.2). It is followed by a blob, which this version does not interpret.
A future type can only be a table entry: a type reference to one is to the entry that
holds it.

A decoder MUST reject any other opcode as an entry, including the opcode of a primitive
type: a table holds only composite types.

### 5.3. The Meaning of a Table

Each entry denotes a type: the one its opcode and members describe, where a type
reference denotes the primitive type or the type of the entry it refers to. Entries may
refer to each other and to themselves in any pattern, so the types they denote are in
general infinite trees ([TYPES], Section 3.4). Since every entry starts with a type
constructor, every reference is productive: there is no entry that only refers to
another.

A decoder MUST reject a message in which any entry of the table, whether or not an
argument refers to it, has a reference that does not resolve, or denotes a type that is
not well-formed ([TYPES], Section 3.5). Among other things, every method of a service
must refer to an entry that is a function type, a `oneway` function must have no
results, and a function must have at most one mode.

The same type can be written as many different tables: an encoder may share entries or
repeat them, and order them as it likes. A decoder MUST NOT depend on how a table is
arranged, only on the types it denotes.

## 6. Values

A value is written at its wire type *t* as follows. The decoder reads a value of *t*
from the bytes, and MUST reject the message if it cannot.

### 6.1. Primitive Values

| Type | Written as |
|---|---|
| `null`, `reserved` | nothing: the value is `null` |
| `empty` | there is no value, and a decoder MUST reject the message |
| `bool` | one byte, `00` for false and `01` for true |
| `nat` | LEB128 ([Section 3.1](#31-leb128)) |
| `int` | SLEB128 |
| `natN`, `intN`, `floatN` | *N*/8 bytes ([Section 3.2](#32-fixed-width-numbers)) |
| `text` | text ([Section 3.3](#33-blobs-and-text)) |
| `principal` | a reference ([Section 6.4](#64-references)) |

A decoder MUST reject a `bool` that is any other byte.

### 6.2. Options and Vectors

A value of `opt t` is the byte `00` for `null`, or the byte `01` followed by a value of
*t* for `opt(v)`. A decoder MUST reject any other first byte.

A value of `vec t` is its length *n* in LEB128, then *n* values of *t*.

### 6.3. Records and Variants

A value of `record{i₁ : t₁; …; iₙ : tₙ}` is the values of its fields, one after the
other, in ascending order of id: the order of the table. Nothing marks where one field
ends, so a record with no fields takes no bytes.

A value of `variant{i₁ : t₁; …; iₙ : tₙ}` is an index *k* in LEB128, then a value of the
field the index names. The index is the field's place, from zero, in ascending order of
id. A decoder MUST reject an index that is not less than *n*.

### 6.4. References

A principal, and the principal of a service reference, is the byte `01`, then a blob of
its bytes. A function reference is the byte `01`, then its principal written as above,
then its method name as text.

A decoder MUST reject a principal of more than 29 bytes ([TYPES], Section 3.1). It MUST
reject any first byte other than `01`: the byte `00` stands, in [CANDID], for a
reference carried outside the message, which this version does not have.

A reference value carries no type, so its wire type is all a receiver knows of it.
Coercing it checks that type against the expected one ([TYPES], Section 6.6).

### 6.5. Future Values

A value of a future type is a length *m* in LEB128, a count *r* in LEB128, and then *m*
bytes. A decoder skips the *m* bytes; the value is `null` ([TYPES], Section 3.2). The
count *r* is of references carried outside the message, which this version does not
have; a decoder MUST ignore it.

A later version of Candid that defines a new type writes its values this way, so that
this version can step over them.

### 6.6. Types Without Values

Every value is finite, and every value of a type with infinitely many nested records is
infinite. Such a type has no values. `type R = record { R }` is one, and so is
`record { null; R }`, while `record { opt R }` has values, since `null` ends the
recursion.

A record takes no bytes of its own, so reading a value of such a type consumes no input
and never reaches the end of the message. A decoder MUST reject a message with a value
of such a type rather than read forever. (A decoder can detect one exactly: it is about
to read a record of some entry at the position where it already began reading a record
of the same entry, enclosing this one.)

Recursion through any other constructor consumes at least one byte per level, so it
ends when the message does.

## 7. Deserialisation

A receiver reads a message at a sequence of expected types `(t'₁, …, t'ₘ)` in four
steps:

1. Read the magic number, the type table and the argument types, and check them
   ([Sections 4 and 5](#4-messages)). This gives the wire types `(t₁, …, tₖ)`.
2. Read one value at each wire type, in order ([Section 6](#6-values)). This gives
   `(v₁, …, vₖ)`.
3. Check that no bytes remain.
4. Coerce `(v₁, …, vₖ) : (t₁, …, tₖ)` at `(t'₁, …, t'ₘ)` as an argument sequence
   ([TYPES], Section 6.8).

The result is the sequence that step 4 gives. The message is rejected if any step
rejects it, and if the coercion fails or is undefined.

Every value is read and checked in step 2, including an argument beyond the expected
ones and a record field the expected type does not have, though coercion will drop them.
A message that is malformed anywhere is rejected.

A receiver need not take the steps one after the other. It MAY coerce each value as it
reads it, or skip building values it will drop, provided it accepts and rejects exactly
the messages the four steps do and yields the same values.

## 8. Serialisation

To send values `(v₁, …, vₖ)` of types `(t₁, …, tₖ)`, an encoder writes a message whose
argument types are equivalent to `(t₁, …, tₖ)` ([TYPES], Section 3.4) and whose values
are `(v₁, …, vₖ)`, so that steps 1 to 3 of [Section 7](#7-deserialisation) give back
exactly those. It MUST write members in the orders [Section 5.2](#52-the-type-table)
requires, and SHOULD write numbers in their shortest form.

An encoder chooses its table: how many entries, in what order, and which it shares.
Two conforming encoders may write different bytes for the same values, so encoders are
compared by what their messages decode to, not by their bytes.

A sender MAY also send a value at a type other than its declared one, if the value has
that type too: a `variant{a : nat; b : text}` value with case `a` can be sent as
`variant{a : nat}`, which takes a smaller table. The receiver coerces from whichever
type the message carries.

## 9. Resource Limits

A receiver's types do not bound the cost of reading a message. Most values take at
least a byte, but those of `null`, `reserved`, and records of nothing else take none. A
vector of such a type can claim any length in a few bytes: `vec null` of length 10⁹ is
`80 94 eb dc 03`. A record type whose two fields have one such type, itself such a
record, doubles the number of values at each level of nesting. These messages are
valid, and reading one can cost more time, memory or stack than any receiver can
afford. Subtyping lets a sender add arguments and record fields that the receiver never
asked for, so a receiver cannot avoid such messages by choosing its types.

A decoder MAY therefore reject a message because reading it needs more of some resource
than the decoder has or allows: stack, memory, an instruction limit, or a limit it sets
on the work per message. Which messages it rejects for this reason depends on the
decoder and its environment, and is not defined here. Such a rejection:

- rejects the whole message. It is not a failed coercion, so no enclosing option turns
  it into `null`, and it does not decide any subtype check;
- SHOULD be reported as such, distinctly from a message that is not valid, and SHOULD
  be an error the caller can handle, not an abort of the program.

A decoder MUST NOT reject a message for any other reason than this document gives.

## 10. Conformance

A decoder conforms to this document if, for every byte string and every sequence of
expected types, it either rejects the message or yields the values of
[Section 7](#7-deserialisation), and rejects only where this document requires it or
where [Section 9](#9-resource-limits) permits it. It MUST NOT abort or fail to
terminate on any input.

An encoder conforms if every message it writes for values of some types is valid, and
reads back at those types as those values.

Conformance vectors of kind `decode`, each a byte string, expected types, and the
expected values or a rejection, are written from the reference model in [lean/](../),
whose [Candid/Wire.lean](../Candid/Wire.lean) implements this document, and published
under [conformance/](../../conformance/). A `decode` vector marked `costly` is a message
the model gives no answer for, since reading it costs more than the model will spend:
a decoder passes it by yielding the values or rejecting the message for lack of
resources, and fails it by aborting.

## 11. Security Considerations

A receiver reads messages from senders it need not trust, so every cost of reading a
message must be bounded by something the receiver controls.

- **Values that take no bytes** ([Section 9](#9-resource-limits)). A decoder SHOULD
  count the values it reads, wherever they are, and stop at a limit, rather than trust
  that a short message is cheap.
- **Lengths.** A length in a message, of a vector, a blob or a table, can be far larger
  than the message. A decoder MUST NOT allocate in proportion to a length before it has
  read what the length promises: a blob longer than the remaining bytes is rejected, and
  a vector's elements are read one at a time.
- **Nesting.** Each level of an option, vector or variant takes at least a byte, so a
  message of *n* bytes can nest values *n* deep. A recursive decoder SHOULD bound its
  depth. Records nest without bytes, but only as deep as the table has entries, unless
  the type has no values ([Section 6.6](#66-types-without-values)), which a decoder MUST
  detect.
- **Numbers.** `nat` and `int` are unbounded, and a number of *b* bytes has 7*b* bits.
  Reading one takes time linear in its length; converting it to decimal, if a receiver
  does, can take time quadratic.
- **Subtype checks.** Every function and service reference in a message makes the
  receiver decide a subtype question about types the sender chose ([TYPES], Section 9).
- **Future types.** A decoder skips a future value by its length without looking
  inside, so a later version's types cost an older receiver nothing beyond their bytes.

## 12. References

### 12.1. Normative References

[IEEE754]
: IEEE, "IEEE Standard for Floating-Point Arithmetic", IEEE Std 754-2019.

[RFC2119]
: Bradner, S., "Key words for use in RFCs to Indicate Requirement Levels", BCP 14,
  RFC 2119, March 1997.

[RFC8174]
: Leiba, B., "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words", BCP 14,
  RFC 8174, May 2017.

[TYPES]
: "Candid Types and Values", [Types.md](Types.md). For the data model,
  well-formedness, equivalence and coercion.

[UNICODE]
: The Unicode Consortium, "The Unicode Standard". For UTF-8.

### 12.2. Informative References

[CANDID]
: DFINITY, "Candid Specification", [spec/Candid.md](../../spec/Candid.md). The current
  specification, which this document is compared with in Appendix A.

[DWARF]
: DWARF Debugging Information Format Committee, "DWARF Debugging Information Format
  Version 5", 2017. Section 7.6 defines LEB128.

## Appendix A. Differences from Candid.md and candid 0.10 (Informative)

This appendix lists where this document decides something [CANDID] does not, and where
it differs from `candid` 0.10, the Rust implementation.

### A.1. Decided Here, or Restated

- **No references outside the message.** [CANDID] writes a message as bytes and a
  sequence of references, and a reference value either as a principal or as `00`, an
  index into that sequence. No platform carries the sequence, and 0.10 rejects `00`
  ("Opaque reference not supported"). Here a message is its bytes, `00` is rejected,
  and the reference count of a future value is ignored.
- **Order of members.** [CANDID] "assumes" that fields are in ascending order of id and
  methods in ascending order of name. Here the order is required, strictly, so a
  decoder rejects a repeated field or method. 0.10 agrees.
- **LEB128 that is not the shortest** is accepted, for every number. [CANDID] does not
  say. 0.10 agrees, except for the opcode of a table entry (A.2).
- **Every entry of the table is checked**, whether or not an argument refers to it.
  [CANDID] does not say. 0.10 agrees.
- **Every value is checked**, including one coercion drops. [CANDID] decodes before it
  coerces, which implies this. 0.10 agrees.
- **Types without values** ([Section 6.6](#66-types-without-values)) are rejected.
  [CANDID] does not mention them. 0.10 agrees.
- **Bytes after the last value** are rejected. [CANDID] implies it, by reading a message
  as the inverse of writing one. 0.10 agrees.
- **Principals** are at most 29 bytes ([TYPES], Section 3.1). 0.10 agrees.
- **Resource limits** ([Section 9](#9-resource-limits)) are as in [CANDID] since #784.

### A.2. Different from candid 0.10

| Input | candid 0.10 | This document |
|---|---|---|
| A `oneway` function type with a result | accepted | rejected ([TYPES], Section 3.5) |
| A table entry's opcode in more than one byte, such as `ee 7f` for `opt` | rejected | accepted ([Section 3.1](#31-leb128)) |

The first difference is in well-formedness, which [TYPES] defines; 0.10's decoder does
not check it. The second is unlikely to matter: no encoder writes an opcode in more than
one byte. 0.10 matches the six composite opcodes as single bytes, and reads every other
number, including a type reference, as LEB128 of any length. The conformance vectors
are `decode: oneway function with a result` and `decode: an entry's opcode with
redundant continuation bytes`.

### A.3. Open Issues

None.

## Appendix B. Examples (Informative)

Each message is read at the types shown.

| Bytes | Expected types | Result |
|---|---|---|
| `44 49 44 4c 00 00` | `()` | `()` |
| `44 49 44 4c 00 00` | `(opt nat)` | `(null)`: a missing argument |
| `44 49 44 4c 00 01 7d 05` | `(nat)` | `(nat(5))` |
| `44 49 44 4c 00 01 7d 05` | `(int)` | `(int(5))`: coerced |
| `44 49 44 4c 00 01 7d 05` | `(opt text)` | `(null)`: does not fit the option |
| `44 49 44 4c 00 01 7d 05 00` | `(nat)` | rejected: a byte after the last value |
| `44 49 44 4c 00 01 7e 02` | `(bool)` | rejected: `02` is not a `bool` |
| `44 49 44 4c 01 6e 7d 01 00 01 05` | `(opt nat)` | `(opt(nat(5)))` |
| `44 49 44 4c 01 6d 7f 01 00 03` | `(vec null)` | `(vec(null, null, null))` |
| `44 49 44 4c 01 6b 02 61 7d 62 7f 01 00 01` | `(variant{a : nat; b : null})` | `(variant{b = null})`: index 1 is `b` |
| `44 49 44 4c 01 6b 02 61 7d 62 7f 01 00 02` | `(variant{a : nat; b : null})` | rejected: no index 2 |
| `44 49 44 4c 01 6b 02 62 7f 61 7d 01 00 00` | `(variant{a : nat; b : null})` | rejected: fields out of order |
| `44 49 44 4c 01 6c 01 00 00 01 00` | `(reserved)` | rejected: `type R = record { R }` has no value, even where it would be dropped |
| `44 49 44 4c 00 01 68 00` | `(principal)` | rejected: a reference outside the message |

The field ids 97 (`61`) and 98 (`62`) are those of the names `a` and `b`.

[CANDID]: ../../spec/Candid.md
