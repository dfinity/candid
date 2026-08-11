# `lean/` — Lean 4 reference model and specification

**Status: first slice.** Types, the field-id hash, and subtyping — as both a relation
and a decision procedure — with a self-checking executable. Nothing is published and
nothing carries a compatibility promise. See [REWRITE.md](../REWRITE.md) for why this
exists.

Eventually replaces [coq/](../coq/) and [spec/](../spec/), on the conditions in
[REWRITE.md §6](../REWRITE.md#6-the-ratchet).

```
lake build          # build the library and the executable
lake exe oracle     # run the checks; exits nonzero on any disagreement
```

## What goes here

A Lean 4 model of Candid that serves as both the **reference implementation** and,
via [Verso](https://github.com/leanprover/verso), the **specification document**.

## The ordering rule

**Executable first, proved second.**

1. `TypeExpr`, `Value`, `subtype`, `coerce`, and the wire format as plain Lean
   functions with `Decidable` instances.
2. A `lake`-built binary that reads a conformance vector file and reports results.
3. CI wiring: that binary as a differential oracle against the Rust implementation.
4. *Only then*, proofs about those definitions.

Inverting this produces [coq/MiniCandid.v](../coq/MiniCandid.v) again in a
different language: a formalisation that is correct, maintained, and consumed by
nothing except a CI job proving it still compiles.

The rule that keeps it honest:

> Every Lean definition must be either (a) reachable from the reference
> executable, or (b) a proof about something that is. No orphan formalisation.

## What slice 1 established

**Coinductive predicates are available; coinductive data types are not.** Lean 4.32
accepts `coinductive` only for `Prop`-valued definitions — `coinductive T : Type`
fails with "`coinductive` keyword can only be used to define predicates." So
MiniCandid's `CoInductive Subtype : T -> T -> Prop` ports directly and lives in
[Candid/SubtypeSpec.lean](Candid/SubtypeSpec.lean), while its `CoInductive T` does
not. Types are therefore finite, with recursion through explicit references into a
type table — which is what the binary format does anyway, and what `candid_types` is
specified to do with arena indices.

**The spec's negative premises are eliminable.** Two of the four `opt` rules in
`spec/Candid.md` carry negative premises, and a rule functional with negative
premises is non-monotone, so it has no greatest fixed point — the relation would not
be definable coinductively at all. Pairing each negative rule with its positive
counterpart collapses them: `t <: opt t'` holds for *every* `t` and `t'`. The spec
notes this in prose and `rust/candid/src/types/subtype.rs:293` implements it as a
catch-all that only warns. Recording it as one premise-free rule is what makes the
relation monotone.

**Naming.** `Type` is unavailable in Lean (it is the universe), and abbreviating it
to `Ty` would reproduce exactly the defect
[crates/CLAUDE.md](../crates/CLAUDE.md) anti-pattern 4 names. So "Type" is the family
prefix and never the whole name: `TypeExpr`, `TypeTable`, `TypeRef`, with `CandidType`
left for the Rust trait. These identifiers are meant to be **the same in Lean and in
Rust**, which is what makes "`candid_subtype` reads as a transcription of its Lean
counterpart" achievable rather than aspirational.

`TypeTable` rather than the old implementation's `TypeEnv` for two reasons. The spec
calls it a table ("type definition table", `spec/Candid.md:1311`), so the prose and the
identifier now agree — they did not when this was a `TypeEnv` described everywhere as
a table. And `TypeEnv` in `rust/` is a `BTreeMap<String, Type>`
(`rust/candid/src/types/type_env.rs:7`), a *name*-keyed environment of `.did`
declarations, which is a genuinely different structure from this index-keyed table.
Both will exist here eventually, so `TypeEnv` stays reserved for the one where
"environment" is the accurate word. The same names are recorded for the Rust side in
[crates/README.md](../crates/README.md#naming), because
[crates/CLAUDE.md](../crates/CLAUDE.md) asks `candid_subtype` to read as a
transcription of its Lean counterpart, and shared identifiers are most of what makes
that checkable.

**Subtyping relates two type tables, not one.** A `TypeExpr` holding a `ref` means
nothing without its table, so the unit the API speaks in is `ClosedType` — a table
and a root together. The case that matters most compares a type table that arrived on
the wire against the receiver's own type graph, and those are unrelated tables;
`rust/candid/src/types/subtype.rs:19` takes a single `env` for both types, which works
only because callers merge tables first. Two consequences fall out of separating
them: the memo must be keyed on **reference pairs**, since unfolded expressions nest
without bound while reference pairs are bounded by `|A| x |B|`; and the `func` rule's
contravariance swaps the *tables* along with the types, which is invisible when there
is only one table to swap.

## Constraints

- **No mathlib.** We do not need it, and depending on it would dominate build
  times and breakage surface.
- **Pin `lean-toolchain`.** Lean's toolchain moves faster than Coq's. Upgrades are
  scheduled work, not incidental. Currently `v4.32.2`.
- **Verso is young.** Expect to read its source rather than its documentation.
- **No `sorry`.** An unproved `theorem` in the build reads as established once it
  scrolls past. Obligations are written as prose next to the definitions they
  constrain, and become `theorem`s when they are proved.

## Coverage target

The Coq model covers nine type constructors and no binary format. This model must
cover what actually breaks in production:

- [x] Primitive types — the constructors, including the numeric tower's *lack* of
      width subtyping. Float edge cases belong to `Value`, which does not exist yet.
- [x] Records, variants, vectors, text — as types
- [x] Recursive types and the type-table graph
- [x] Subtyping, as a relation with a derived decision procedure
- [ ] Coercion, including the `opt` backtracking rule
- [ ] Binary wire format: type table, memory section, LEB128/SLEB128
- [ ] Cost model / resource exhaustion
- [ ] Textual value syntax

## Deferred, deliberately

Named here so they are obligations rather than oversights.

- **`fuel` in `Candid/Subtype.lean`.** The procedure bounds recursion depth with a
  budget instead of a termination measure, and returns `none` — not `false` — when it
  runs out, so the model never reports an answer it did not compute. The intended
  measure is lexicographic on (reference pairs not yet in `seen`, structural size);
  proving it needs `TypeTable.wellFormed`'s "every entry is composite" invariant
  carried in the type rather than checked separately.
- **`decSubtype_iff`** — that the procedure decides the relation. Stated in
  [Candid/SubtypeSpec.lean](Candid/SubtypeSpec.lean). Soundness should follow by
  coinduction with `seen` as the coinductive hypothesis, which is what `seen` means;
  completeness additionally needs the budget never to run out.
- **Unguarded recursion.** `TypeTable.wellFormed` requires every entry to be a
  `<comptype>` — the spec's own rule (`spec/Candid.md:1227`), which rules out both
  primitives and bare references — but it does not yet require recursion to be
  *productive*. Textual `.did` aliases (`type A = B;`) must be resolved before
  reaching this model.
- **Verso.** Deliberately not in slice 1: bundling an undocumented doc toolchain into
  the slice whose purpose was de-risking the build would have doubled the unknowns.

## Relationship to `coq/`

MiniCandid is not an incomplete implementation — it is a *justification* device. It
exists to show that non-obvious design decisions are sound, and to check that a
proposed spec change can be accommodated by the existing system. This model answers a
different question: given this input, what happens?

[REWRITE.md §6](../REWRITE.md#what-the-coq-condition-means) now states the deletion
condition accordingly — each MiniCandid theorem's *purpose* discharged, rather than a
model-to-model diff, which is not available anyway once one side has finite types and
an explicit table.

What remains worth doing, and is not a deletion gate: checking this model against
MiniCandid on the nine constructors they share. A disagreement there would be a
finding about the spec.

[coq/MiniCandid.v](../coq/MiniCandid.v) proves `subtyping_refl`, `subtyping_trans`,
`coerce_roundtrip`, `coerce_well_defined`, `soundness`, and `transitive_coherence`.
These are real theorems about the genuinely subtle part of the language, they attach
to `Subty` here, and they are worth restating over records, variants, vectors and
recursion rather than over nine constructors. Read it before starting.
