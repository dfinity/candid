# Candid Specification

**Status:** Draft. Not normative. Until these documents replace [spec/Candid.md][CANDID]
under the conditions of [REWRITE.md §6](../../REWRITE.md#6-the-ratchet), that document
governs wherever the two disagree.

**Abstract.** Candid is an interface description language. A service states the types
of its methods in an interface description. Callers and the service exchange values of
those types as binary messages, and people write values as text. The specification is
split into four documents: one for the types and the relations between them, and one
for each way types and values are written down. This page says what each document
covers, how they depend on one another, and how they relate to the reference model,
the conformance vectors and [spec/Candid.md][CANDID].

## Contents

1. [The Documents](#1-the-documents)
2. [How They Fit Together](#2-how-they-fit-together)
3. [Conformance](#3-conformance)
4. [The Model and the Vectors](#4-the-model-and-the-vectors)
5. [Coverage of Candid.md](#5-coverage-of-candidmd)
6. [Differences and Open Issues](#6-differences-and-open-issues)

## 1. The Documents

| Document | Defines |
|---|---|
| [Candid Types and Values][TYPES] | The types, their values and field ids; subtyping, which says when one type may replace another; coercion, which says what a value of one type becomes when it is read at another |
| [Candid Binary Format][BINARY] | How values and their types are written as a message, how a message is read at the types a receiver expects, and which messages a receiver may reject for lack of resources |
| [Candid Interface Descriptions][DID] | The syntax of types and of `.did` files, imports, and the interface a description denotes |
| [Candid Textual Values][TEXT] | The syntax of values as people write them, what such text means at a type, and the textual form of principals |

[TYPES] is the core. The other three each describe one way of writing down what
[TYPES] defines, and say nothing about types or values beyond that.

## 2. How They Fit Together

```
           .did text                 value text                  bytes
               │                         │                         │
        [DID] read, check       [TEXT] parse, elaborate     [BINARY] decode
               │                         │                         │
               ▼                         ▼                         ▼
          an interface:  ──────▶  values at a type  ◀──────  values at the
          a type per name   types                            message's types
          and a service     for annotations                        │
                                                                   │ coerce
                                                                   ▼
                                                     values at the expected types
                                                     [TYPES], Section 6
```

- **Types** come from a description. [DID] turns a `.did` file into an interface, in
  which every name and the service has a type of [TYPES].
- **Messages** carry their own types. [BINARY] reads the types and values a message
  carries, and then coerces the values to the types the receiver expects, as [TYPES]
  defines.
- **Text** is read at a type the reader already has. [TEXT] elaborates an expression at
  that type and gives a value of it. Type annotations inside text use the type syntax of
  [DID].
- **Upgrades** are checked by subtyping ([TYPES], Section 5). The relation guarantees
  that a message sent at a subtype never fails to decode at its supertype
  ([TYPES], Section 7).

[DID] and [TEXT] share one lexical structure, defined in [TEXT], Section 3.

A first reading can follow the order of the table in [Section 1](#1-the-documents):
[TYPES] Sections 2 to 4, then whichever of the other three is of interest, then
[TYPES] Sections 5 and 6.

## 3. Conformance

Each document states what conforming to it means, in its own Conformance section. An
implementation conforms to the documents for what it does, for example:

| An implementation that | conforms to |
|---|---|
| encodes and decodes messages | [TYPES] and [BINARY] |
| checks that one interface may replace another | [TYPES], and [DID] if it reads `.did` files |
| reads `.did` files | [DID] |
| reads values written as text | [TEXT] |

In every document, an implementation rejects an input only where the document requires
it, or where the document permits it, as for an input that costs more resources than the
implementation can afford ([BINARY], Section 9). A decoder also never aborts or runs
forever, whatever the bytes ([BINARY], Section 10).

## 4. The Model and the Vectors

The [reference model](../) is a Lean 4 program that implements all four documents. The
[conformance vectors](../../conformance/) are generated from it, so a disagreement
between the model and a document is a bug in one of them.

| Document | Model | Vector kinds |
|---|---|---|
| [TYPES] | [Types](../Candid/Types.lean), [Hash](../Candid/Hash.lean), [Value](../Candid/Value.lean), [Subtype](../Candid/Subtype.lean), [SubtypeSpec](../Candid/SubtypeSpec.lean), [Coerce](../Candid/Coerce.lean), [Equiv](../Candid/Equiv.lean) | `hash`, `wellformed`, `subtype`, `coerce` |
| [BINARY] | [Wire](../Candid/Wire.lean) | `decode` |
| [DID] | [Did/](../Candid/Did/) | `did` |
| [TEXT] | [Text/](../Candid/Text/), [Principal](../Candid/Principal.lean), [Float](../Candid/Float.lean) | `parse` |

The vectors are JSON, so an implementation in any language can run them without first
having a Candid parser. Their format is in
[conformance/README.md](../../conformance/README.md). The vectors are also run against
`candid` 0.10, the Rust implementation, in CI. Where 0.10 gives a different answer, the
document concerned lists it in an appendix ([Section 6](#6-differences-and-open-issues)).

## 5. Coverage of Candid.md

Every normative part of [CANDID] is covered by one of the four documents. The sections
of [CANDID] are listed here in its order.

| [CANDID] section | Covered by |
|---|---|
| Motivation | Not carried over. See [below](#51-not-carried-over) |
| Type Structure: core grammar, shorthands, comments | [DID] Sections 3 and 4; [TEXT] Section 3.2 |
| Services, Functions, and their names and annotations | [TYPES] Section 3.2; [DID] Section 4 |
| Primitive Data | [TYPES] Section 3.1 |
| Constructed Data: options, vectors, blobs, records, variants, symbolic ids, tuple fields, enumerations | [TYPES] Sections 3.2 and 3.3; [DID] Section 4 |
| References: service, function and principal | [TYPES] Sections 3.1, 3.2 and 4; [TEXT] Appendix A |
| Type Definitions | [DID] Sections 5 and 6; [TYPES] Section 3.4 |
| Imports | [DID] Section 5.3 |
| Interfaces | [DID] Sections 5 and 6.4 |
| Values | [TEXT] Sections 3 to 5 |
| Upgrading and Subtyping: motivation and examples | [TYPES] Sections 2 and 5.2, in part. See [below](#51-not-carried-over) |
| Upgrading and Subtyping: design goals | [TYPES] Section 7, for soundness, completeness, transitivity and coherence. See [below](#51-not-carried-over) |
| Subtyping rules | [TYPES] Section 5.1 |
| Coercion, including tuple types | [TYPES] Section 6 |
| Properties | [TYPES] Section 7, except higher-order soundness. See [below](#51-not-carried-over) |
| Binary Format, Serialisation, notation | [BINARY] Sections 2, 3, 5, 6 and 8 |
| References in the binary format | [BINARY] Section 6.4 and Appendix A.1 |
| Parameters and Results | [BINARY] Section 4 |
| Deserialisation | [BINARY] Section 7 |
| Resource limits | [BINARY] Section 9 |
| Deserialisation of future types | [BINARY] Sections 5.1 and 6.5; [TYPES] Section 6.7 |
| Open Questions | Not carried over. See [below](#51-not-carried-over) |

### 5.1. Not Carried Over

None of the following is normative. Before [CANDID] is replaced, each needs a home or a
decision that it has none.

- **Motivation.** The goals and non-goals of Candid, and why it is not Protocol
  Buffers. These belong in an introduction to Candid, not in its specification.
- **Upgrade examples and the remaining design goals.** [TYPES] Section 5.2 says what an
  interface may change, but has no worked examples, including the higher-order ones. Of
  the design goals, [TYPES] Section 7 states soundness, completeness, transitivity and
  coherence, and which of them hold. Higher-order extensibility, independence from
  source languages, decoding without subtype checks, type erasure, and no covert
  channels are not stated anywhere.
- **Higher-order soundness.** [CANDID] points to `spec/IDL-Soundness.md` for it. The
  reference model does not cover it, and neither does any document here.
- **Open questions.** Default field values, generic type definitions and namespaces for
  imports. These are proposals for the language, and belong in the issue tracker.

## 6. Differences and Open Issues

Each document lists, in an appendix, where it decides something [CANDID] leaves open,
and where it gives a different answer from `candid` 0.10:

| Document | Appendix | Differences from 0.10 |
|---|---|---|
| [TYPES] | [A](Types.md#appendix-a-differences-from-candidmd-and-candid-010-informative) | 1 |
| [BINARY] | [A](Binary.md#appendix-a-differences-from-candidmd-and-candid-010-informative) | 5, including the one in [TYPES] |
| [DID] | [A](Did.md#appendix-a-differences-from-candid-010-informative) | 9 |
| [TEXT] | [B](TextValues.md#appendix-b-differences-from-candid-010-informative) | 16 |

The open issues that are still undecided, across all four documents:

- **Transitivity through `null`.** Adding a field of type `null` breaks the
  transitivity of subtyping ([TYPES], Appendix A.3).
- **Unknown annotations in binary data.** A decoder that sees a function annotation it
  does not know rejects the whole message ([DID], Appendix A.3).
- **One lexical chapter.** [DID] borrows its lexical structure from [TEXT]
  ([DID], Appendix A.3).
- **NaN.** No text denotes a NaN ([TEXT], Appendix B.3).
- **Annotations in text.** Whether an annotation may name a subtype of the expected
  type ([TEXT], Appendix B.3).

[TYPES]: Types.md
[BINARY]: Binary.md
[DID]: Did.md
[TEXT]: TextValues.md
[CANDID]: ../../spec/Candid.md
