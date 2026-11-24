# `crates/` — redesigned Rust implementation

**Status: `candid_types`, `candid_binary` and `candid_value` started.** In a workspace of their own
([Cargo.toml](Cargo.toml)):

- `candid_types`: the type language of [lean/Candid/Types.lean](../lean/Candid/Types.lean)
  and [Hash.lean](../lean/Candid/Hash.lean), and the subtyping of
  [Subtype.lean](../lean/Candid/Subtype.lean);
- `candid_binary`: messages, from [Wire.lean](../lean/Candid/Wire.lean) and
  [DecodeAt.lean](../lean/Candid/DecodeAt.lean): written, and read at the receiver's
  types, which is coercion;
- `candid_value`: the dynamic value of [Value.lean](../lean/Candid/Value.lean), which
  `candid_binary` writes and reads;
- `conformance_tests`: not a library, but the one test that reads
  [conformance/vectors/](../conformance/vectors/) and asks each crate what it can answer:
  the `hash`, `wellformed` and `subtype` vectors, every table the other vectors promise
  is well formed, every `decode` vector's message read at its types, every `coerce`
  vector written at `from` and read at `to` -- alone and in context -- and every value in
  a vector written at its type, giving back the vector's bytes where nothing was coerced.

Nothing here is published to crates.io. See [REWRITE.md](../REWRITE.md) for why this
exists.

```
cargo test --manifest-path crates/Cargo.toml
```

Eventually replaces [rust/](../rust/). That is a long horizon — `rust/` is not
deleted until `candid` v1 is published *and* icp-cli and ic-cdk have migrated, and
0.10.x maintenance continues in parallel throughout.

> **Working in this directory?** Read [CLAUDE.md](CLAUDE.md) first. It lists the
> specific patterns from `rust/` that must not be reproduced here.

## Layering

`candid`, `candid_parser` and `candid_derive` are already ours, so v1 is a new
major version of those crates rather than a new set of names. Only the layer
crates below are new, and they use `_` to match the existing family.

```
ic_principal                    (existing crate; unchanged, already correctly split)
   ↑
candid_types      Types.md, Sections 3 and 5. Slot, Composite, RawTypeTable, TypeTable,
   ↑              Root, TypeRef, FieldId, field-id hash, subtyping.
   │              no_std. No serde, no binary, no global state.
candid_binary     Binary.md. Encoding, and decoding at the receiver's types -- which
   ↑              is coercion (Types.md, Section 6). Values go in and out through
   │              traits, so no derive and no value type is needed. Cost metering.
   ├───────────────────────────┐
candid_value                candid (facade) + derive macro
   Types.md, Section 4:     CandidType trait, native decode trait (no serde),
   the dynamic value        Encode!/Decode!
                               ↑
candid_syntax     Did.md + TextValues.md. One lexer; .did parsing, imports and type
                  checking; value text and printing; spans, diagnostics.
   ↑
candid_bindgen    IR, name mangling, type-selector config, template helpers.

out of tree:      candid_bindgen_{rust,js,ts,motoko}
```

### Why these seams

- **`candid_types` has no global state.** The current implementation keeps four
  `thread_local! RefCell` maps
  ([rust/candid/src/types/internal.rs:692](../rust/candid/src/types/internal.rs#L692)),
  which makes `CandidType::ty()` impure and makes generated `.did` type names
  depend on the order types were first derived. Here, types are built into an
  explicit `TypeTable` passed by the caller, with recursion handled by arena indices.
- **Each crate implements one spec document**, named for it. [lean/Spec/](../lean/Spec/)
  has a core, Types.md, and three ways of writing it down; so there is `candid_types`
  for the core and a crate for each way: `candid_binary`, and `candid_syntax` for the two
  textual ones, which share a lexer.
- **Subtyping is in `candid_types`.** It is a relation on types and needs nothing
  else; Lean keeps it beside the types too. The Lean-mirrored surface is the
  `subtype` module, which reads as a transcription of `lean/Candid/Subtype.lean`.
- **Coercion is decoding at the receiver's types, and lives only in `candid_binary`.**
  Lean decodes a message and then coerces the values. In Rust that would make every
  typed decode build a dynamic value first, so typed decoding would need coercion of
  its own, and two implementations of one behaviour is [CLAUDE.md](CLAUDE.md)
  anti-pattern 6. So the decoder walks the sender's type and the receiver's together
  over the bytes, for a receiver -- the dynamic value, or a derived Rust type -- that
  says what it builds. The speculative `opt` rule is speculative about the *coercion*,
  not the bytes: when the value under an `opt` does not coerce, the decoder skips
  forward to the value's end, validating it, and yields `null`. It never rewinds
  ([Values](#values)). There is no value-to-value
  coercion: the `coerce` vectors run as encode-then-decode, and so can a tool that
  wants to convert a value.
- **`candid_binary` must be usable with zero derive and zero serde.** Anyone writing
  a fuzzer, an interceptor, a `didc`-like tool, or a non-Rust FFI binding needs
  only this crate. It is also the only crate that touches untrusted bytes, which
  makes it the right place to concentrate Kani and fuzzing.
- **The `candid` facade re-exports and little else.** Downstream users depend on
  one crate; the layer crates are for tool authors. That is how the split stays
  fine-grained without forcing ten dependencies into every canister's
  `Cargo.toml`.

## Values

The plan for the value half of `candid_binary`, and for `candid_value`. Built: writing
values, `candid_value`, Lean's `decodeAt`, and reading values at the receiver's types --
steps 1 to 3 of the [order of work](#order-of-work).

### Two traits, one engine

`candid_binary` defines how a value goes in and out, and nothing else does:

```rust
pub trait Encode {
    fn encode(&self, writer: ValueWriter<'_>) -> Result<(), EncodeError>;
}

pub trait Decode<'a>: Sized {
    /// `Ok(None)`: the value does not coerce to `Self` -- the spec's *failure*, which
    /// an enclosing `opt` turns into `null`. `Err`: the message is rejected.
    fn try_decode(reader: ValueReader<'_, 'a>) -> Result<Option<Self>, DecodeError>;
}
```

`candid_value::Value` implements both, and so will derived types. `'a` is the message's
lifetime, so a receiver can borrow text and blobs from it instead of copying: a
`View<'b> { text: &'b str }` implements `Decode<'a>` for every `'a: 'b`.

So the facade's `CandidType` is `Encode` plus `intern_type`, and does not require `Decode`: a
bound such as `for<'a> Decode<'a>` would shut out every borrowing type, even where it
is only encoded. A decoding call site asks for `Decode<'a>` at the message's lifetime,
or for `DecodeOwned` -- `for<'a> Decode<'a>`, as serde's `DeserializeOwned` -- when
the value must outlive the message, which a blanket impl provides. The derive implements
`CandidType`, `Encode` and `Decode`.

**The receiver drives; the decoder decides.** A reader is one value of the message,
paired with the receiver's type for it: a sender's slot and position, and a `Root` in
the receiver's table. The receiver says what shape it is building -- `reader.nat()`,
`reader.record()`, `reader.opt(|inner| ...)` -- and the decoder applies the coercion rule
for that pair of types (`lean/Spec/Types.md`, Section 6): `nat` read as `int`, fields
the receiver lacks skipped, fields the sender lacks filled with `null` if their type
accepts it, the `opt` rules, references checked by `is_subtype`. A receiver never sees a
sender's type, so every coercion rule is written once, in the decoder. A dynamic value,
which has no shape of its own, asks `reader.expected()` and follows the receiver's
type. Calling a method that does not match `expected()` is a bug in the receiver, and
returns an error rather than a wrong value.

**No rewinding.** `lean/Spec/Binary.md`, Section 7, requires every value to be read and checked,
including the ones coercion drops: a failure inside an `opt` yields `null`, but a
malformed byte after it still rejects the message. So when a receiver gives up on a
value (`Ok(None)`), the decoder does not go back to the value's start. It skips from
where it is to the value's end, validating as it goes. Every byte is read once, where
rewind-and-skip would read the bytes of nested `opt`s once per level.

**The decoder is an explicit stack.** It keeps a frame per open record, vector and
variant of the sender's: its type and how far through it is. That is what lets it skip
to a value's end after the receiver has left mid-record, and what makes skipping --
arguments past the receiver's, fields it does not have -- iterative rather than
recursive. Recursion is left only in receivers, which follow the nesting of the values
they build; `Limits::depth` bounds it. The stack also gives the check of Binary.md,
Section 6.6, for free: a record entered at the position where an enclosing frame entered the same
entry.

**A message is an argument sequence.** `Decoder::argument(expected)` gives the reader
for the next argument; past the sender's last, it is a reader of an absent value, which
is `null` if `expected` accepts it and a failure otherwise (`lean/Spec/Types.md`,
Section 6.8).
`Decoder::finish` skips the arguments the receiver did not ask for and rejects bytes
after the last value.

**Results.** Three outcomes, as Section 6.1 of Types.md has them: a value is `Ok(Some(_))`, failure
is `Ok(None)`, and undefined -- reading a value that does not accept `null` at an
infinite option -- is an `Err`, like a malformed message and a resource limit. It is
the answer only once the rest of the message is read, as `decodeAt` has it: an error in
the bytes after it, or a limit they run into, comes first. A
failure an `opt` does not absorb rejects the message too; `Decoder::argument`'s caller
gets it as `Ok(None)` and the facade turns it into an error naming the argument.

**Fast paths are specialisations.** `vec nat8` read into a `&[u8]` or `Vec<u8>`, and
text read into a `&str`, take the bytes in one step. They are the general path with
the loop unrolled, covered by the same vectors (CLAUDE.md, anti-pattern 6): the same
values counted, the same depth checked, and the same error at the same byte.

**References.** A `func` or `service` value coerces only if its type is a subtype of the
expected one. The decoder caches each answer by the pair of table entries, so a vector
of a million references costs one subtype check.

As built: the parts of an `opt`, a `vec`, a record and a variant are handed to the
receiver through closures -- `reader.opt(|inner| ...)`, `reader.record(|fields| ...)`,
`fields.field(id, |value| ...)` -- and each method reads its value to the end before it
returns, whatever the closure did. So the readers are the frames of the explicit stack,
as the writers are, and each knows how far through its value it is: when a receiver
gives up, the method skips the rest of its own value, and a reader the receiver drops
unread is skipped by the one that handed it out. Skipping is a loop over a stack of its
own, which counts and rejects as `decodeValue` does. Once a part fails, nothing more of
the value is read at the receiver's types, as in `decodeAt`; a record field the receiver
does not ask for is still read at its type, so the receiver's type decides the record,
not which fields the receiver keeps. The subtype cache lives for one argument, since the
next may be at another receiver's table. `nat` and `int` come out as `Natural` and
`Integer`, which read the number out as bytes or a fixed-size integer.

### Writing

`Encoder::argument()` gives a `ValueWriter` for the next argument type, and `finish`
fails until every argument has one. A writer checks each value against its type as it
writes it -- `writer.nat(n)` at a `text` is an `EncodeError` -- since a message whose
values do not have its types is not a message. Records are written through
`writer.record()`, whose fields come in the table's order, ascending id: the order a
`TypeTable` keeps them in, and the order a derive can sort its fields into at compile
time. A variant is written by its id; the writer finds the index. Numbers are written in
their shortest form.

As built: `writer.null()` is the one `null` of `candid_value`, written as its type says
-- nothing at `null` and `reserved`, `00` at an `opt`, `00 00` at a future type -- and
`writer.opt()` is the present one. `nat` and `int` are given as their bytes
(`writer.nat(&n.to_le_bytes())`), so `candid_binary` needs no big-number crate. A
`vec nat8` can be written whole, with `writer.blob(bytes)`, which writes the bytes
`writer.vec(len)` and a `nat8` each would. And every value handed out is written: each
writer knows how many values were owed when it was made, so a writer dropped unwritten,
or one whose error was ignored, is found by the writer around it at its next call, and
the message cannot be finished (`EncodeError::Unfinished`). That takes one counter, not a
stack: the writers themselves are the stack, and the borrow checker keeps them in order.

### `candid_value`

`Value` transcribes Lean's (`lean/Candid/Value.lean`), with its three choices:

- **One `null`.** It is the value of `null`, of `reserved`, of an absent option and of a
  future type. A `Value` does not know its type; a receiver's type says which it is.
- **Floats are their bits**, so equality is bitwise: a NaN equals itself, and `-0.0` is
  not `0.0`. Constructors and accessors take and give `f32` and `f64`.
- **Records are canonical**: fields in strictly ascending id, so two equal records are
  equal as lists.

Two more, of Rust's:

- **`nat` and `int` are arbitrary precision**, as `Nat` and `Int`. They wrap
  `num-bigint`, which `candid` 0.10 uses too, but do not expose it: the wrapper is the
  API, so no `num-bigint` release forces a breaking release here, and the storage
  stays free to change -- to hold numbers below 2^64 inline, say, if a benchmark asks
  for it. The decoder hands a receiver the number's bytes, so `candid_binary` needs no
  big-number crate.

  The API is what people do with these numbers, ledger amounts above all: conversion
  to and from the fixed-size integers, `Display` and `FromStr` in decimal, comparison,
  and the common arithmetic. Beyond it, two ways out:

  - **Bytes, always.** `Nat::from_le_bytes`/`to_le_bytes` spell the magnitude in base
    256, least significant byte first -- shortest out, any length in; `Int` does the
    same in two's complement. That is a fact about integers, not about the storage, so
    it never needs to change, and every big-number crate reads and writes it.
  - **`From`/`Into` behind a versioned feature**, `num-bigint-04`, the
    `with-chrono-0_4` shape of `postgres-types`. `num-bigint` 0.5 gets
    `num-bigint-05` beside it, an additive release; the old one goes at a major
    version of this crate, not of `num-bigint`.
- **A blob is not a million values.** `Value::Blob(Vec<u8>)` holds a `vec nat8`, and
  equals the `Value::Vec` of the same `nat8`s. A receiver of type `vec nat8` always
  builds a `Blob`.

Principals are `ic_principal::Principal`. Text syntax -- printing and parsing values --
is `candid_syntax`'s, not this crate's.

### Limits

`Limits` grows two fields:

- `values`: the most values a message may stand for, counting every value wherever it
  is -- skipped, inside another, past the expected arguments. That is Lean's `limit`,
  counted the same way, so that a message one rejects for its count the other does too.
  It is what stops a `vec null` of length 10⁹.
- `depth`: the deepest a receiver may nest.

Both are resource limits (Binary.md, Section 9), with defaults generous for any real
message.

Two costs are bounded but not yet measured or tuned; step 4 settles them:

- **Skipping uses heap, per level of nesting.** Skipping is a loop over a stack of what
  is left to read, kept on the heap: one entry, about 40 bytes, for each level still
  open. Each level is a counted value, so the stack is bounded by `values` -- but at the
  default of 2²², that is up to about 160 MB, more with the `Vec`'s doubling. A message
  can get there in a few hundred bytes of values: records whose values take no bytes nest
  up to `table.len()` deep for each byte. 0.10 skips by recursing on the call stack,
  with no limit on Wasm, where a deep enough message traps; the rewrite never traps here,
  but the constant is large. Options: no entry for a level that has nothing left, smaller
  entries, a default `values` chosen with this cost in mind, or a nesting limit on
  skipping too.
- **A receiver nests on the call stack.** Reading at the receiver's types recurses, some
  frames for each level, up to `depth` = 1024 levels. Whether that fits a Wasm canister's
  stack (often 1 MB) has not been measured. If it does not, a message nested that deep
  traps, as every deep message does in 0.10, which has no limit on Wasm. Measure the
  stack used per level on wasm32, then set the default.

### Lean: `decodeAt`

Lean decodes a message and then coerces its values; Rust does both in one pass. Before
the Rust decoder, Lean gets `decodeAt`: the one pass, written as Rust will be --
reading at a pair of types, skipping on failure -- and a theorem that it gives the same
answer as `decode` followed by `coerce`. The Rust decoder then transcribes `decodeAt`,
as `is_subtype` transcribes `decSubtype`, and the theorem is what says the one pass is
the spec.

As built ([lean/Candid/DecodeAt.lean](../lean/Candid/DecodeAt.lean)): `decodeValueAt`
follows `coerce` case for case, reading where `coerce` is handed a value -- a scalar read
at the sender's type and coerced, an `opt`, `vec`, `record` or `variant` part by part.
Once a value's outcome is decided, it reads on with `decodeValue` to the value's end, so
every byte is read and every value counted once, in `decode`'s order, with `decode`'s
errors. `decodeAt_eq` -- equal to `decode` then `coerceArguments`, the same error at the
same byte included -- is stated, and checked by the oracle on every `decode` and `coerce`
vector and on generated messages built so that a failed value has more to skip; it is
not yet proved.

### Order of work

1. `candid_value`, and writing values. A `decode` vector's values are the receiver's,
   after coercion, so they give back its bytes only where nothing was coerced. The check
   is therefore on the vectors whose own header is the receiver's -- the same table and
   argument types, which the header decoder can already tell -- whose bytes are in
   shortest form, and whose table has no future type: writing their values with that
   header must give their bytes. A future value is the exception to "nothing was
   coerced": its bytes are skipped and it decodes to `null`, which is written back as
   `00 00` (`lean/Candid/Wire.lean`), so a nonempty one does not come back. No vector has
   one yet. The rest wait for step 3, which compares by decoding.
2. Lean's `decodeAt`, and the theorem.
3. Reading values at the receiver's types. Checked by every `decode` vector in full, and
   every `coerce` vector as encode-then-decode.
4. Differential fuzzing against Lean, and the `costly` vectors under `Limits`. Then the
   costs under [Limits](#limits): measure them, test them on adversarial shapes, and
   set the defaults.

   As built so far: `lake exe oracle differential` (`lean/Oracle/Differential.lean`)
   writes random messages, often damaged, with `decodeAt`'s exact answer at a receiver's
   types and a limit on the values; `tests/differential.rs` in `conformance_tests`
   requires the same values, failure, undefined coercion, or rejection at the same byte
   -- and so the same count, since a limit of one value fewer than a message has must
   stop at the same value. The rejections in Lean are `candid_binary`'s kinds, and the
   header's errors are at the start of the item they reject in both. A small corpus is
   committed; CI runs 40,000 more messages from a new seed each time. The `costly`
   vectors are among them: every case at the oracle's limit is one. Left: receivers
   that read in other ways than `Value` does -- other fields, giving up, a vector byte by
   byte where `Value` takes a blob -- which must not change the bytes read, the errors
   or the count; and the costs.

## Naming

Identifiers are shared with [lean/](../lean/) wherever they name the same thing. That
is what turns "subtyping should read as a transcription of its Lean
counterpart" into a checkable property rather than an aspiration.

| | |
|---|---|
| `Slot` | what the binary format calls a type reference: a primitive or a `TypeRef`, never an inline composite |
| `Composite` | a composite type: what a table entry is. Its children are `Slot`s, so it is one flat node |
| `RawTypeTable` | `TypeRef` → `Composite`, index-keyed — what the spec calls the type table — as parsed or built, not yet checked |
| `TypeTable` | a `RawTypeTable` that has passed the well-formedness check: what every API after the decoder or builder takes |
| `TypeRef` | index into a `TypeTable` |
| `Root` | a `Slot` checked to resolve in a given `TypeTable`. In Lean the table is in its type (`t.Root`); in Rust it is a view borrowing its table, `Root<'a>` |
| `FieldId` | a record or variant label: a 32-bit id |
| `CandidType` | the derive trait |
| `TypeEnv` | **reserved**, see below |

Shared names are for *things*. Functions follow Rust's conventions where Lean's would
read oddly: `lookup?` is `lookup`, `size` is `len`, `hashFieldName` is
`hash_field_name`, `decSubtype` is `is_subtype`, `decode` starts as `Decoder::new`,
and `check` returns a `Result` naming the malformed entry where Lean's returns an
`Option`. One difference is in the data: a checked `TypeTable` keeps each entry's
fields, methods and annotations in order, where Lean's keeps them in any order.

`Type` cannot be used in Lean (it is the universe) and `Ty` would violate
[CLAUDE.md](CLAUDE.md) anti-pattern 4, so "Type" is a family prefix and never a whole
name.

`Slot` and `Composite` take no such prefix, because neither is a type: a slot cannot
express one, and a composite means nothing without the table its children index into.
A slot is where the binary format puts a type reference, and a composite is a table
entry ([lean/Spec/Binary.md](../lean/Spec/Binary.md), Section 5). Nothing here is a
nested tree — the type table is the only recursion, which is what the binary format
already does, and what makes the subtype procedure in
[lean/](../lean/) terminate without a depth limit.

`TypeEnv` is deliberately *not* this crate's table. In `rust/` it is a
`BTreeMap<String, Type>`
([rust/candid/src/types/type_env.rs:7](../rust/candid/src/types/type_env.rs#L7)) — a
*name*-keyed environment of `.did` type declarations, which is a different structure
from an index-keyed table, and both will exist here. The name stays reserved for the
`candid_syntax` one, where "environment" is accurate. Spending it on the table is how
the earlier draft of this document ended up describing a "type table" that no
identifier called a table.

## The serde divorce

This is the change that motivates the version bump, so it is worth stating
precisely.

Candid's coercion rule requires **speculative coercion**: when a value cannot be
coerced to the expected type inside an `opt`, the result is `null` rather than an
error, and the receiver has to be able to give up on a value it has started to build.
serde's `Visitor` is a consume-once, move-in API that
provides no "would you accept this?" query, so the current implementation
identifies visitors by string-matching serde's private module paths and `ptr::read`s
them ([rust/candid/src/de.rs:740](../rust/candid/src/de.rs#L740)). serde 1.0.220
moved those paths and broke it. Both bugs fixed in 0.10.34 trace to the same
mismatch.

The replacement makes giving up first-class. A receiver that cannot coerce returns
`Ok(None)`, and the decoder, not the receiver, skips forward past the rest of the
value; nothing goes back over bytes already read.

```rust
pub trait CandidType: Encode {
    /// Add this type's entries to `table`, and return the slot that names it --
    /// as `RawTypeTable::intern` does for one entry. 0.10's `ty()`.
    fn intern_type(table: &mut RawTypeTable) -> Slot;
}

pub trait Decode<'a>: Sized {
    /// Returns Ok(None) when the wire value cannot be coerced to Self.
    /// The decoder skips the rest of the value; the caller does not
    /// rewind. This is the opt-coercion primitive.
    fn try_decode(reader: ValueReader<'_, 'a>) -> Result<Option<Self>, DecodeError>;
}
```

A `ValueReader` exposes Candid-shaped operations — `opt`, `record`, `variant`, `vec` —
not serde's data model ([Values](#values) has the design). Consequences:

- One derive (`#[derive(CandidType)]`) instead of `#[derive(CandidType,
  Deserialize)]`; downstream users stop needing serde as a direct dependency.
- Candid's own attributes (`#[candid(rename = "...")]`) instead of borrowing
  `#[serde(...)]` and then documenting that most of it does not work.
- No second, parallel value-deserializer implementation to drift out of sync, so
  the 0.10.34 bug class becomes structurally impossible.
- `is_human_readable` disappears.
- No `unsafe` in the decode path.

### Scope: serde leaves the data path entirely

"Removed from the decode path" understates this, so state it directly: **no core
crate depends on serde in its default build, and nothing depends on it for encode,
decode or subtyping at any feature setting.**

Encode never used serde. [rust/candid/src/ser.rs](../rust/candid/src/ser.rs)
drives Candid's own `types::Serializer`, and the current docs explain why — "We do
not use Serde's `Serialize` trait because Candid requires serializing types along
with the values" ([rust/candid/src/lib.rs:80](../rust/candid/src/lib.rs#L80)).
Every remaining use is downstream of decoding: `de.rs`, the `Deserialize` impls
under [rust/candid/src/types/](../rust/candid/src/types/), `serde::{de, ser}::Error`
in [error.rs:3](../rust/candid/src/error.rs#L3), and
[utils.rs:4](../rust/candid/src/utils.rs#L4). Take out the decode path and nothing
is holding the dependency up.

So a default `cargo build` of `candid_types`, `candid_binary`, `candid_value` or
the facade resolves no `serde` at all. Three consequences that are
easy to miss:

- **`serde_bytes` goes with it, and it is a default feature today.** Efficient
  `blob` handling is currently spelled `#[serde(with = "serde_bytes")]`, matched by
  string in the derive
  ([rust/candid_derive/src/derive.rs:389](../rust/candid_derive/src/derive.rs#L389)),
  with `CandidType for serde_bytes::ByteBuf` behind a feature that `default`
  enables ([impls.rs:173](../rust/candid/src/types/impls.rs#L173)). v1 owes users a
  native spelling, which is `#[candid(blob)]` on a `Vec<u8>` field — sugar over the
  general adapter mechanism below, so blob costs no separate machinery. What must
  not happen is `Vec<u8>` silently becoming a `vec nat8` of individually encoded
  elements.
- **Foreign-format impls for leaf types are a separate question from the data
  model, and the answer is "optional feature, off by default."** `Nat`, `Int` and
  `Reserved` implement `Serialize`/`Deserialize` today and are tested through JSON,
  CBOR and bincode ([number.rs:576](../rust/candid/src/types/number.rs#L576)) —
  people do put a `candid::Nat` inside a `serde_json` struct.
  [`ic_principal`](../rust/ic_principal/Cargo.toml) already ships exactly the right
  shape for this: an optional `serde` feature, nothing in the default build. A
  `candid_types` feature that adds those impls for `Nat`/`Int` is compatible with
  everything above, because it makes serde a *consumer* of a Candid type rather
  than the mechanism Candid decodes through. What must never come back is a
  `Deserialize` bound anywhere in encode, decode, or subtyping.
- **`candid_bindgen` keeps serde, deliberately.** Binding generation uses it as an
  ordinary config-file deserializer
  ([configs.rs:3](../rust/candid_parser/src/configs.rs#L3),
  [bindings/rust.rs:11](../rust/candid_parser/src/bindings/rust.rs#L11)) — serde
  doing what serde is good at, on config files we define, with no Candid value
  anywhere near it. The objection is to expressing *Candid's* data model through
  serde, not to the crate.

### Foreign types get an adapter, not a serde bridge

Dropping serde raises the obvious question: what about a type from a crate you do
not control? The answer is a local adapter. An earlier draft of this document
floated `candid_serde_compat` — a shim accepting any `serde::Deserialize` type at a
Candid boundary — and it is worth recording why that was rejected, because the
reasoning generalises.

**It cannot supply `intern_type`.** Candid needs a type-table entry; `Serialize` and
`Deserialize` are value-level traits with no type-level reflection. Structure can be
recovered by driving a `Deserialize` impl with an instrumented tracing
deserializer — [serde-reflection](https://github.com/zefchain/serde-reflection) does
exactly this — but that is the same genre of fragility as the visitor
string-matching in [REWRITE.md §1.3](../REWRITE.md#13-serde-is-the-wrong-data-model-and-the-workarounds-are-structural):
multi-pass tracing to enumerate enum variants, hints for containers it cannot infer,
and wrong answers under `#[serde(flatten)]`. It also does nothing for encoding,
since tracing `Serialize` needs a value in hand. The honest ceiling is decode-only
against a Candid type the caller writes by hand — at which point writing a
`CandidType` impl is comparable effort and strictly better.

**It would be a new capability, not a migration aid.** Every field type already
needs `CandidType` for `ty()`
([rust/candid_derive/src/derive.rs:533](../rust/candid_derive/src/derive.rs#L533)),
so a foreign type carrying only serde impls is *already* unusable at a Candid
boundary today. Nothing regresses by declining to build the bridge, and existing
code is unaffected for a different reason: `#[derive(CandidType, Deserialize)]` goes
on compiling, with the `Deserialize` half simply never consulted.

The escape hatch instead mirrors `#[serde(with)]` — a module supplying
`intern_type`, `encode` and `try_decode` for one field:

```rust
#[derive(CandidType)]
struct Job {
    #[candid(blob)]                          // built-in adapter
    payload: Vec<u8>,
    #[candid(with = "my_adapters::uuid_as_text")]
    id: uuid::Uuid,                          // foreign type, local adapter
}
```

Typed, local, both directions, no `unsafe` and no tracing. Library code generic over
`T: DeserializeOwned` at a Candid boundary changes its bound to `T: CandidType` —
a mechanical edit, on a major-version boundary where downstream crates are editing
anyway.

## The derive crate

Rust requires proc macros to live in a dedicated crate, so v1 still has one. It
stays version-locked to the facade for the same reason `candid_derive` is today —
generated code names the runtime's items — but the coupling should be narrowed to
a documented, deliberately small "derive support" surface rather than whatever the
macro happens to reach for.

What it contains is an open question. `CandidType` obviously belongs. The other
two exports do not obviously survive:

- **`candid_method` / `export_service`** collect method signatures across separate
  proc-macro invocations via a `lazy_static! Mutex`
  ([rust/candid_derive/src/func.rs:21](../rust/candid_derive/src/func.rs#L21)).
  The code says so itself:

  ```rust
  // There is no official way to communicate information across proc macro invocations.
  // lazy_static works for now, but may get incomplete info with incremental compilation.
  // See https://github.com/rust-lang/rust/issues/44034
  ```

  This is the same global-state defect as the `thread_local!` type environment,
  in a place where the failure mode is a silently incomplete `.did` file. Emitting
  the interface from Rust source is a worthwhile feature; doing it by accumulating
  state across macro expansions is not the way to keep it.

## Verification posture

`candid_types` and `candid_binary` are written to be checkable, which constrains
their style: pure functions, no interior mutability, no `unsafe`, no trait-object
indirection in the core paths. Concretely this means
[Kani](https://github.com/model-checking/kani) for panic-freedom on the binary
decoder, differential fuzzing against the Lean binary, and — as a stretch —
[Aeneas](https://github.com/AeneasVerif/aeneas) on the LEB128 codec and the
subtype checker. "Written so that it *could* be Aeneas-verified" is a useful
constraint even if the tool is never run. See
[REWRITE.md §3](../REWRITE.md#3-lean-honestly) for the full tiering and what is
explicitly out of scope.
