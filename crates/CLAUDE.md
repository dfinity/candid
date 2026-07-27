# Working in `crates/`

This directory is a redesign, not a port. The existing implementation in
[`rust/`](../rust/) is a **requirements document, not a template.**

Read [../REWRITE.md](../REWRITE.md) for the reasoning behind everything below.

## The `rust/` rule

**Consult it for *what*. Never copy *how*.**

`rust/` encodes years of hard-won knowledge that must not be lost: the spacebomb
defenses, the cost-metering constants, the 471 assertions in [`test/`](../test/),
and every edge case with a CHANGELOG entry behind it. Mine all of it.

Its *designs*, however, are the reason this directory exists. When you find
yourself about to mirror a structure from `rust/`, that is the moment to stop and
design instead. If a behaviour there looks arbitrary, find the CHANGELOG entry or
test that explains it before deciding it is wrong — most of the strange parts are
load-bearing.

## Do not reproduce these

Each one is a real, cited defect in the current implementation.

### 1. No serde in the decode path

Candid coercion needs speculative decode with backtracking; serde's `Visitor` is
consume-once and cannot express it. The current workaround string-matches serde's
private module paths and `ptr::read`s the visitor
([rust/candid/src/de.rs:740](../rust/candid/src/de.rs#L740)); serde 1.0.220 moved
those paths and broke it. Both bugs fixed in 0.10.34 trace to the same mismatch.

Use the native `CandidType::try_decode` returning `Result<Option<Self>, _>`. See
[README.md](README.md#the-serde-divorce).

### 2. No global mutable state

`CandidType::ty()` currently memoises into four `thread_local! RefCell` maps
([rust/candid/src/types/internal.rs:692](../rust/candid/src/types/internal.rs#L692)).
Name uniquification uses an incrementing counter, so generated `.did` type names
depend on the order types were first derived in that thread.

Type derivation must be a pure function. Types are built into an explicit
`TypeEnv` passed by the caller; recursion uses arena indices, not thread-local
interning.

The derive crate has the same defect in a worse place: `candid_method` /
`export_service` accumulate method signatures across proc-macro invocations in a
`lazy_static! Mutex`
([rust/candid_derive/src/func.rs:21](../rust/candid_derive/src/func.rs#L21)),
which the comment there notes "may get incomplete info with incremental
compilation" — i.e. a silently truncated `.did` file. Proc macros do not get to
carry state between expansions.

### 3. `pub` is opt-in, not the default

246 public items across 23 public modules with 8 `#[doc(hidden)]` means every
internal refactor is a semver event. `binary_parser` was public purely by
accident, and a `binread` → `binrw` migration became a breaking change because of
it.

Default to private. A `pub` item needs a reason, and modules are `pub` only when
they are genuinely part of the API contract.

### 4. No abbreviations, no config-by-function-name

Current API: `IDLValue`, `IDLArgs`, `IDLBuilder`, `IDLDeserialize`, `IDLProg`
(prefixing five types with an abbreviation for the thing the crate itself is);
`_ty()` and `_ty_doc()` as public trait methods; `Type` as `Rc<TypeInner>` with
both public; modules named `de` and `ser`; a trait named `Compound`; `check_prog`;
`idl_hash`.

And ten decode functions
([rust/candid/src/lib.rs](../rust/candid/src/lib.rs#L296-L302)) that are the
cartesian product of two independent options:

```
decode_args, decode_args_with_config, decode_args_with_decoding_quota,
decode_args_with_skipping_quota, decode_args_with_decoding_and_skipping_quota,
decode_one, decode_one_with_config, decode_one_with_decoding_quota,
decode_one_with_skipping_quota, decode_one_with_decoding_and_skipping_quota,
```

Write names out. Options go in a config struct or a builder, never into the
function name.

### 5. No `unsafe` in `candid-subtype` or `candid-wire`

These two crates are the verification target. No `unsafe`, no interior
mutability, no trait-object indirection in core paths. This is a hard constraint,
not a preference — it is what makes Kani and Aeneas applicable at all. If you
believe you need `unsafe` for performance, benchmark first and raise it as a
design question.

### 6. One implementation per behaviour

Both 0.10.34 bugs exist because a bulk-decode fast path was a *second* decode
implementation that drifted from the main one. Fast paths are fine; forks of the
decoding logic are not. A fast path must be a specialisation that provably agrees
with the general path, and it must be covered by the same conformance vectors.

## Positive conventions

- **The Lean model in [`lean/`](../lean/) is the specification.** Where Rust and
  Lean disagree, that is a bug in one of them and it gets investigated, not
  papered over. `candid-subtype` in particular should read as a transcription of
  its Lean counterpart.
- **Every behaviour is a conformance vector.** New behaviour lands with vectors in
  [`conformance/`](../conformance/), not just Rust unit tests — the vectors are
  what other implementations consume.
- **`candid-wire` stands alone.** It must be usable with no derive macro and no
  serde. If you need `candid-value` or the facade to make it work, the layering is
  wrong.
- **Untrusted input.** Everything in `candid-wire` parses bytes from the network.
  Bounded allocation, explicit cost accounting, no unbounded recursion.

## Status

Nothing here is published. Nothing carries a compatibility promise until v1. Ugly
intermediate states are expected — see
[REWRITE.md §5](../REWRITE.md#5-how-we-work) for the working model.
