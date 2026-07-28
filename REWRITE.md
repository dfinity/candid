# Candid v1: a staged, additive rewrite

> **`candid` 0.10.x is not affected by anything in this document.** It continues to
> ship bug fixes and releases from `master` exactly as before. Nothing described
> here is published to crates.io, nothing depends on it, and no existing file is
> modified. If you maintain something that depends on `candid`, you can stop
> reading.

This document proposes a staged rewrite of Candid's specification, reference
model, and Rust implementation. It exists so that the reasoning behind it is
written down and citable rather than undocumented.

**Status:** proposal, not scheduled work. **Author:** @lwshang.

---

## 1. Why

Six structural problems in the current implementation, each cited to the code.
None is fixable by an incremental patch, and several are semver breaks on their
own — which is the argument for addressing them together rather than one at a
time.

### 1.1 There is no single source of truth

The prose spec ([spec/Candid.md](spec/Candid.md), 1351 lines), the Coq model
([coq/](coq/)), and the Rust implementation are three independent artifacts that
agree only by manual discipline. When they drift, nothing fails. There is no
document recording where they currently disagree.

### 1.2 The formal model is not load-bearing, and covers the wrong third

[coq/MiniCandid.v](coq/MiniCandid.v) models nine type constructors — `Nat Int Null
Opt Func Service Principal Void Reserved`. There are **no records, no variants, no
vectors, no text, no floats, and no binary format at all.**

It proves real theorems (`soundness`, `transitive_coherence`, `coerce_roundtrip`)
about the genuinely subtle `opt` coercion rule, and it is still maintained — it was
updated for the `service <: principal` change in 0.10.32. But it is not executable,
so it cannot be a test oracle, and it says nothing about the type table, recursive
type graphs, the wire format, or cost metering, which is where our bugs actually
occur. Its only consumer is a CI job that proves it still compiles.

Separately: nobody currently on SDK reads Coq.

### 1.3 serde is the wrong data model, and the workarounds are structural

Candid's coercion rule requires **speculative decoding with backtracking**. From
[spec/Candid.md](spec/Candid.md):

```
not (exists <w>. <v> : <t> ~> <w> : <t'>)
----------------------------------------
opt <v> : opt <t> ~> null : opt <t'>
```

To implement that you must ask the target type "would you accept this value?" and,
on refusal, rewind and produce `null`. serde's `Visitor` is a consume-once, move-in
API with no such query. So [rust/candid/src/de.rs:740](rust/candid/src/de.rs#L740)
identifies the visitor **by string-matching serde's private module paths**, then
`ptr::read`s it because the API gives no way to clone it:

```rust
&& !tid.name.starts_with("serde::de::impls::OptionVisitor<")
// serde v1.0.220 refactored the module path
// This confirms the assertion above that this is not stable.
&& !tid.name.starts_with("serde_core::de::impls::OptionVisitor<")
...
let v = unsafe { std::ptr::read(&visitor) };
```

The comment is the author acknowledging the hazard, and serde 1.0.220 then
realised it.

This is not a theoretical concern. The two most recent releases are both this same
wound ([CHANGELOG.md](CHANGELOG.md)):

- **0.10.34** — decoding a `vec` of fixed-width primitives into newtype elements
  (`struct EventIndex(u32)`) failed with a spurious subtyping error, because the
  bulk-decode fast path fed elements through serde value deserializers that do not
  implement `deserialize_newtype_struct`.
- **0.10.34** — `is_human_readable()` returned `true` inside a `vec` but `false`
  everywhere else, so a `Deserialize` impl that branches on it **silently decoded
  to a different value with no error.**
- **0.10.33** — a `binread` → `binrw` migration leaked into the public API through
  `pub mod binary_parser`, a module that was public purely by accident.

Both 0.10.34 bugs exist because there are two parallel decode implementations that
can drift. That is a consequence of bending Candid onto serde's data model, not a
coding mistake.

### 1.4 Type derivation runs on global mutable state

[rust/candid/src/types/internal.rs:692](rust/candid/src/types/internal.rs#L692)
keeps four `thread_local! RefCell` maps (`ENV`, `DOC_ENV`, `ID`, `NAME`). Name
uniquification uses an incrementing counter, so **the name a type receives in
generated `.did` output depends on the order types were first derived in that
thread.** `CandidType::ty()` is not a pure function. It is also not thread-safe in
any useful sense, and `TypeId` is a hand-rolled reimplementation of
`std::any::TypeId` keyed on a monomorphised function's address.

### 1.5 `pub` was the default, and the API grew by accretion

246 public items across 23 public modules, with only 8 `#[doc(hidden)]`. Internal
machinery — `types::internal`, `types::leb128`, `binary_parser`, the `pretty`
internals — is public, so every internal refactor is a semver event.

The naming has drifted past the point of incremental repair.
[rust/candid/src/lib.rs](rust/candid/src/lib.rs#L296-L302) exports **ten** decode
functions:

```
decode_args, decode_args_with_config,
decode_args_with_decoding_quota, decode_args_with_skipping_quota,
decode_args_with_decoding_and_skipping_quota,
decode_one, decode_one_with_config,
decode_one_with_decoding_quota, decode_one_with_skipping_quota,
decode_one_with_decoding_and_skipping_quota,
```

That is the cartesian product of two independent options encoded into function
names; it should be one function and a config struct. Alongside it: `IDL` prefixed
onto five types for the thing the crate itself is (`IDLValue`, `IDLArgs`,
`IDLBuilder`, `IDLDeserialize`, `IDLProg`); public trait methods named `_ty()` and
`_ty_doc()`; `Type` as an `Rc<TypeInner>` with both halves public; modules named
`de`/`ser`; a trait named `Compound`.

Each of these is a semver break on its own. Fixing them incrementally means a
rename-only major version that delivers no other value and spends the ecosystem's
patience for nothing. They have to be bundled.

### 1.6 The conformance suite cannot bootstrap a new implementation

[test/](test/) holds 471 assertions across six files, and they are good assertions.
But:

- The format is a **bespoke extension of the Candid text grammar**, so you need a
  working Candid text parser before you can run test #1. Anyone implementing
  Candid in a new language hits this wall immediately.
- The only runner lives inside
  [rust/candid_parser/tests/test_suite.rs](rust/candid_parser/tests/test_suite.rs).
- [test/README.md](test/README.md) documents `*.good.did` / `*.bad.did` for parser
  conformance. **There are zero such files in the repo.**
- The README explicitly disclaims encoding coverage, because the binary format is
  non-canonical.
- Subtyping is only tested indirectly through decoding, so a subtype-checker bug
  surfaces only if it also changes a decode outcome.
- It is not versioned or distributable — consuming it means cloning this repo and
  writing a parser for a grammar that exists nowhere else.

Our own [README.md](README.md) lists ten community-maintained Candid
implementations — Haskell, Elm, Kotlin, AssemblyScript, Java, Dart, Motoko, C#,
C++, Python. Every one of their authors had to decide whether writing a Candid
text parser was worth it just to run our tests. We have no idea how many of them
are conformant, and neither do they. That is a suite-packaging failure, not a
community failure.

---

## 2. What we are building

Three new top-level directories. Each is a parallel to something that already
exists and will eventually replace it, and each is named so that **no rename is
needed when the old thing is deleted.**

| New | Replaces | Contains |
|---|---|---|
| [lean/](lean/) | [coq/](coq/), [spec/](spec/) | Lean 4 reference implementation + Verso spec sources |
| [crates/](crates/) | [rust/](rust/) | Redesigned Rust crates |
| [conformance/](conformance/) | [test/](test/) | Machine-readable vectors, generator, runner |

Each directory has its own `README.md` with detail. In brief:

**`lean/`** — a Lean 4 model of Candid that is *executable first and proved
second*. The order matters: `Ty`, `Value`, `subtype`, `coerce`, wire format as
plain functions with `Decidable` instances, compiled by `lake` into a binary,
wired into CI as a differential oracle against the Rust implementation. Only then
do we prove things about those definitions. Inverting this produces MiniCandid
again, in a different language.

The spec is authored with [Verso](https://github.com/leanprover/verso), the Lean
FRO's literate-documentation system (the one used for the official Lean Language
Reference). Prose, inference rules, and elaborated Lean live in one document; the
build fails if the examples stop type-checking. Every rule gets stated twice — as
an inference rule for readers who think in those terms, and as an executable
definition for everyone else.

**`crates/`** — a layered redesign. Provisional shape:

```
ic_principal                    (existing; unchanged, already correctly split)
   ↑
candid_types      Type, Label, Field, Function, TypeEnv, field-id hash.
                  no_std-capable. No serde, no binary, NO GLOBAL STATE.
   ↑
candid_subtype    Subtyping + coercion decision procedures. Mirrors Lean 1:1.
   ↑               The verified core: small, pure, Aeneas-shaped.
candid_wire       Type table + memory encoding, untyped:
   ↑               bytes <-> (TypeEnv, Vec<Type>, values). Cost metering.
   ├───────────────────────────┐
candid_value                candid (facade) + derive macro
   IDLValue equivalent,     CandidType trait, native decode trait (no serde),
   pretty printing          Encode!/Decode!
                               ↑
candid_syntax     Lexer, AST, .did parsing, type checking, spans, diagnostics.
   ↑
candid_bindgen    IR, name mangling, type-selector config, template helpers.

out of tree:      candid_bindgen_{rust,js,ts,motoko}
```

**On naming.** `candid`, `candid_parser`, `candid_derive` and `ic_principal` are
already ours, so v1 is a **new major version of the existing crates, not a new set
of names.** Cargo links semver-incompatible versions side by side, so `candid
0.10.x` and `candid 1.x` can both appear in one dependency graph during migration.

The caveat that actually matters: coexistence works for *linking*, not for *types*.
`candid_0_10::Nat` and `candid_1::Nat` are distinct types, so a project that pulls
both transitively still breaks at the boundary between them. That friction is real
and no naming scheme fixes it — it is what the migration story in §7 has to
address.

Only the genuinely new layer crates need new names, and they use `_` to match the
existing family. crates.io treats `_` and `-` as equivalent for uniqueness, so
publishing `candid_types` also reserves `candid-types`.

Rust still requires proc macros to live in a dedicated crate
([rust-lang/rust#54727](https://github.com/rust-lang/rust/issues/54727)), so a
derive crate persists in v1. The question is only what goes in it — see
[crates/README.md](crates/README.md#the-derive-crate).

**`conformance/`** — vectors as JSON data rather than a Candid-grammar extension,
so an implementer in Go or Python can run vector #1 before writing a text parser.
Generated from the Lean model, which lets us be exhaustive by construction for
small types rather than "whatever someone thought of". Covers encoding (against a
newly-defined canonical encoding profile), subtyping as a first-class relation,
`.did` parsing, and resource exhaustion. Published as a versioned artifact.

---

## 3. Lean, honestly

**What it buys.** Lean 4 compiles to a native binary. That single property is the
whole argument: a Lean reference implementation can be a differential oracle and a
test-vector generator in CI. Coq requires extraction to OCaml, which is why
MiniCandid was never executable and therefore never load-bearing. Beyond that,
`Decidable` instances let us derive a proved-correct decision procedure from a
relation, rather than writing a checker and a relation separately and hoping they
match — which is what [rust/candid/src/types/subtype.rs](rust/candid/src/types/subtype.rs)
(832 lines) and the spec are today.

**What it costs.** Lean is not used anywhere in the team's stack today, so this
would be its first application here. Replacing an unread Coq model with an unread
Lean one is a lateral move *unless the Lean artifact is executable and wired into
CI.* The design rule that prevents that:

> **Every Lean definition must be either (a) reachable from the reference
> executable, or (b) a proof about something that is.** No orphan formalisation.

Additional costs, stated up front: Lean's toolchain moves faster than Coq's, so
`lean-toolchain` is pinned and upgrades are scheduled work. Verso is young; expect
to read its source rather than its docs. We do **not** depend on mathlib.

**Bus factor.** @lwshang has been learning Lean and would own this part, though
applying it to a production project would be new. That is a real single point of
failure and worth naming rather than glossing over. The mitigation is that the
executable oracle delivers value even to someone who cannot read the proofs: it
is a binary that says "Rust and the spec disagree here."

**What we are not attempting.** A full functional-correctness proof of the
production Rust decoder is a multi-year research project. We are pursuing only the
practical tiers:

| Tier | Approach | Verdict |
|---|---|---|
| 1 | Lean binary as differential fuzzing oracle | **Do.** Highest value/cost by far |
| 2 | Exhaustive small-scope vector generation from Lean | **Do.** Fixes the suite and the spec at once |
| 3 | [Kani](https://github.com/model-checking/kani) on the wire decoder for panic-freedom | **Do.** Cheap, no proof engineering, and this code eats untrusted bytes |
| 4 | [Aeneas](https://github.com/AeneasVerif/aeneas) (Rust → Lean) on the LEB128 codec and subtype checker | **Evaluate.** Shapes the API even if never run |
| 5 | End-to-end verified decoder incl. cost metering | **No.** Not realistic |

Tier 4 is worth one note: Aeneas cannot handle `unsafe`, interior mutability, or
serde-style generic traits, so today's decoder is out of reach regardless. But
"written so that it *could* be Aeneas-verified" is a useful design constraint on
`candid_subtype` and `candid_wire` even if we never run the tool.

---

## 4. What this is explicitly not

- **Not a clean-room restart.** The existing implementation is a *requirements
  document*. It encodes years of hard-won knowledge — the spacebomb defenses, the
  cost-metering constants, the 471 assertions, and every edge case with a
  CHANGELOG entry behind it. Losing those is the one thing that would genuinely
  cost us years. We mine it; we do not imitate it.
- **Not a separate repository.** Keeping it here preserves the crates.io
  namespace, the issue tracker users already use, git history, and — most
  importantly — makes the deletion ratchet in §6 enforceable. Across two repos,
  deleting the old thing is always somebody else's problem and never happens.
- **Not a break for anyone on 0.10.x.** v1 is a new major version of the existing
  crates. Cargo links semver-incompatible versions side by side, so 0.10.x keeps
  working and keeps receiving fixes for as long as it needs to. Mixed dependency
  graphs are still a real problem — see the caveat in §2 — but nobody is forced to
  move on our schedule.
- **Not fast at the ecosystem layer.** The code is plausibly multi-month. Getting
  icp-cli, ic-cdk, agent-rs, and canister authors onto it is multi-quarter and gated on
  other teams' release cycles, not on our typing speed. "Done" for this effort
  means *v1 crates exist and pass conformance*, not *everyone has migrated*.

---

## 5. Proposed working model

**Everything is additive.** New code goes in the three new directories. Existing
files are not modified. This is not a style preference — it is the property that
makes everything else work:

- Nothing on `master` can break, because nothing on `master` references the new
  directories.
- There are **structurally zero merge conflicts** with a `master` that keeps
  shipping 0.10.x releases.
- Therefore review of a merge is *"adds files under `lean/`, `crates/`,
  `conformance/`; touches nothing existing; nothing published depends on it"* —
  approvable in minutes without deep review.

**Working branch, merged fortnightly.** Day-to-day work happens on a working
branch pushed directly, so iteration is not gated on review latency. It merges to
`master` **at least every two weeks**, regardless of whether anything feels
finished.

This cadence is the entire discipline, and it exists because we have already run
this experiment and lost. The `next` branch in this repository is **1 commit ahead
of `master` and 109 behind.** It was the same plan. It died from merge cadence, not
from a bad idea. A missed merge is a bug.

**Policy lands on `master` through normal PRs.** Anything that is policy, or that
`master` needs to know about — directory reservations, this document, CI jobs,
CONTRIBUTING changes — goes through the standard process. Only code churn lives on
the branch.

**Unstable means unstable.** Nothing under the new directories is published, and
nothing in it carries a compatibility promise until v1. Ugly intermediate states
are expected and are not review material.

---

## 6. The ratchet

Old artifacts are deleted only when the replacement demonstrably covers them.
Deletion is a normal PR against `master` with the evidence in the description.

| Delete | When | Caveat |
|---|---|---|
| [coq/](coq/) | Lean reproduces every MiniCandid theorem **and** the two models have been diffed | If Lean disagrees with MiniCandid anywhere, that disagreement is the most valuable thing this project will find. Investigate before deleting. |
| [spec/](spec/) | Verso output covers all normative content | `spec/Candid.md` is externally linked from docs sites, other implementations, and papers. Needs a redirect stub, not a `git rm`. |
| [test/](test/) | All 471 assertions exist as conformance vectors and pass | — |
| [rust/](rust/) | `candid` v1 published and icp-cli + ic-cdk migrated | Long horizon. Expect 0.10.x maintenance in parallel throughout. |

Two things in this repo are **not** on the ratchet and need a new home rather than
deletion: `tools/ui` has a live release pipeline
([candid-ui.yml](.github/workflows/candid-ui.yml)) and is a deployed canister that
developer tooling points users at; `tools/candiff` and `tools/didc` are consumers
that should
move to their own repo rather than vanish.

---

## 7. Open questions

These are what the document does not answer. The decisions in §1–§6 are recorded
with their reasoning; new evidence is the reason to revisit one.

- What stays in the derive crate. `CandidType` clearly does. `candid_method` and
  `export_service` need rethinking — they communicate across proc-macro
  invocations through a `lazy_static! Mutex`, which the code itself flags as
  unsound under incremental compilation
  ([func.rs:21](rust/candid_derive/src/func.rs#L21),
  [rust-lang/rust#44034](https://github.com/rust-lang/rust/issues/44034)).
- Migration for mixed dependency graphs, where a project transitively pulls both
  `candid 0.10` and `candid 1` and the two `Nat`/`Principal`/`Type` are distinct
  types. This is the hardest part of the migration and it is unsolved.
- Whether the canonical encoding profile (deterministic type-table ordering, no
  unused entries, shortest-form LEB128) should be normative in the spec or a
  separate conformance profile.
- Whether `candid_serde_compat` — a bridge letting `serde::Deserialize` types be
  used at a Candid boundary during migration — is worth shipping, given that it
  necessarily inherits the bug class described in §1.3. Current thinking: ship it,
  scope it to foreign types you do not control, and make coercion failures loud
  errors rather than best-effort.
- How `spec/` redirects are published once Verso output becomes canonical.
