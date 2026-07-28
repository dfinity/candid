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
candid_types      Type, Label, Field, Function, TypeEnv, field-id hash.
                  no_std-capable. No serde, no binary, no global state.
   ↑
candid_subtype    Subtyping + coercion decision procedures.
   ↑              Mirrors lean/ 1:1. The verified core.
candid_wire       Type table + memory encoding, untyped:
   ↑              bytes <-> (TypeEnv, Vec<Type>, values). Cost metering.
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
  explicit `TypeEnv` passed by the caller, with recursion handled by arena indices.
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
    fn ty(env: &mut TypeEnv) -> TypeRef;
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
