# `crates/` — redesigned Rust implementation

**Status: reserved, empty.** No content yet. Nothing here is published to
crates.io. See [REWRITE.md](../REWRITE.md) for why this exists.

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
candid_types      Slot, Composite, TypeTable, TypeRef, FieldId, ClosedType,
                  field-id hash. no_std-capable. No serde, no binary, no global state.
   ↑
candid_subtype    Subtyping + coercion decision procedures.
   ↑              Mirrors lean/ 1:1. The verified core.
candid_wire       Type table + memory encoding, untyped:
   ↑              bytes <-> (TypeTable, Vec<Slot>, values). Cost metering.
   ├───────────────────────────┐
candid_value                candid (facade) + derive macro
   Dynamic value repr,      CandidType trait, native decode trait (no serde),
   pretty printing          Encode!/Decode!
                               ↑
candid_syntax     Lexer, AST, .did parsing, type checking, spans, diagnostics.
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
- **`candid_subtype` is a separate crate** specifically so the Lean-mirrored
  surface has a crate boundary. As a module inside something larger, the
  correspondence rots silently.
- **`candid_wire` must be usable with zero derive and zero serde.** Anyone writing
  a fuzzer, an interceptor, a `didc`-like tool, or a non-Rust FFI binding needs
  only this crate. It is also the only crate that touches untrusted bytes, which
  makes it the right place to concentrate Kani and fuzzing.
- **The `candid` facade re-exports and little else.** Downstream users depend on
  one crate; the layer crates are for tool authors. That is how the split stays
  fine-grained without forcing ten dependencies into every canister's
  `Cargo.toml`.

## Naming

Identifiers are shared with [lean/](../lean/) wherever they name the same thing. That
is what turns "`candid_subtype` should read as a transcription of its Lean
counterpart" into a checkable property rather than an aspiration.

| | |
|---|---|
| `Slot` | a `<datatype>` where the wire format writes `I`: a primitive or a `TypeRef`, never an inline composite |
| `Composite` | a `<comptype>`: what a table entry is. Its children are `Slot`s, so it is one flat node |
| `TypeTable` | `TypeRef` → `Composite`, index-keyed — what the spec calls the type definition table |
| `TypeRef` | index into a `TypeTable` |
| `ClosedType` | a `TypeTable` and a root `Slot` together |
| `FieldId` | a record or variant label: a 32-bit id |
| `CandidType` | the derive trait |
| `TypeEnv` | **reserved**, see below |

`Type` cannot be used in Lean (it is the universe) and `Ty` would violate
[CLAUDE.md](CLAUDE.md) anti-pattern 4, so "Type" is a family prefix and never a whole
name.

`Slot` and `Composite` take no such prefix, because neither is a type: a slot cannot
express one, and a composite means nothing without the table its children index into.
Both are named after the grammar position they occupy in `spec/Candid.md`. Nothing
here is a nested tree — the type table is the only recursion, which is what the wire
format already does (`spec/Candid.md:1208`) and what makes the subtype procedure in
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

Candid's coercion rule requires **speculative decoding with backtracking**: when a
value cannot be coerced to the expected type inside an `opt`, the result is `null`
rather than an error. serde's `Visitor` is a consume-once, move-in API that
provides no "would you accept this?" query, so the current implementation
identifies visitors by string-matching serde's private module paths and `ptr::read`s
them ([rust/candid/src/de.rs:740](../rust/candid/src/de.rs#L740)). serde 1.0.220
moved those paths and broke it. Both bugs fixed in 0.10.34 trace to the same
mismatch.

The replacement makes backtracking first-class:

```rust
pub trait CandidType: Sized {
    fn ty(table: &mut TypeTable) -> TypeRef;
    fn encode<E: Encoder>(&self, e: E) -> Result<(), E::Error>;

    /// Returns Ok(None) when the wire value cannot be coerced to Self.
    /// The decoder is left positioned to skip the value; the caller does
    /// not rewind. This is the opt-coercion primitive.
    fn try_decode<D: Decoder>(d: &mut D) -> Result<Option<Self>, D::Error>;

    fn decode<D: Decoder>(d: &mut D) -> Result<Self, D::Error> {
        Self::try_decode(d)?.ok_or_else(|| D::Error::type_mismatch())
    }
}
```

`Decoder` exposes Candid-shaped operations — `read_opt`, `read_record`,
`read_variant`, `read_vec`, `skip_value` — not serde's data model. Consequences:

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

So a default `cargo build` of `candid_types`, `candid_subtype`, `candid_wire`,
`candid_value` or the facade resolves no `serde` at all. Three consequences that are
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

**It cannot supply `ty()`.** Candid needs a type-table entry; `Serialize` and
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

The escape hatch instead mirrors `#[serde(with)]` — a module supplying `ty`,
`encode` and `try_decode` for one field:

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

`candid_subtype` and `candid_wire` are written to be checkable, which constrains
their style: pure functions, no interior mutability, no `unsafe`, no trait-object
indirection in the core paths. Concretely this means
[Kani](https://github.com/model-checking/kani) for panic-freedom on the wire
decoder, differential fuzzing against the Lean binary, and — as a stretch —
[Aeneas](https://github.com/AeneasVerif/aeneas) on the LEB128 codec and the
subtype checker. "Written so that it *could* be Aeneas-verified" is a useful
constraint even if the tool is never run. See
[REWRITE.md §3](../REWRITE.md#3-lean-honestly) for the full tiering and what is
explicitly out of scope.
