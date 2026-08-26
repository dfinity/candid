# `lean/` — Lean 4 reference model and specification

**Status: first slice.** Types, the field-id hash, and subtyping — as both a relation
and a decision procedure — with a self-checking executable. "Slice" is a label for
what landed in a merge window, applied after the fact; the forward-looking plan is the
coverage checklist below and the tiers in [REWRITE.md §3](../REWRITE.md#3-lean-honestly). Nothing is published and
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

1. The type language, `Value`, `subtype`, `coerce`, and the wire format as plain
   Lean functions with `Decidable` instances.
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

**Composites live only in the type table.** A table entry is a `Composite`, its
children are `Slot`s, and a `Slot` is a primitive or an index — never an inline
composite. That is not a modelling choice so much as the wire format's own shape
(`spec/Candid.md:1208`), and the spec draws the conclusion the model is built on:
"Because recursion goes through `T`, this format by construction rules out
non-well-founded definitions like `type t = t`."

What it bought: the only way for the subtype procedure to recurse is through a pair
of *references*, so the finite set of reference pairs bounds the recursion. The
procedure carries `seen` — the pairs this path has already assumed — and descends by
recording one. The measure is `remaining`, the number of pairs `seen` does *not*
record; it is named only by `termination_by`, so the `|A| x |B|` pair space it counts
over is never built at run time. No fuel, no `Option Bool`, and no "unanswered" state
in the public API. The first version of this model, with
composites nested inside each other, had no such measure: a cycle alternating which
side holds the reference dodged the memo entirely, so no budget decided it.

What it cost: a type means nothing without its table, and even `vec nat` needs an
entry, so hand-written types are built through `intern`/`close`. The `.did` surface
syntax *is* nested, so the parser will produce a nested AST and flatten it — which is
also what an encoder does when it emits a type table, so the flattening pass is a
component this model owes rather than a translation it pays for.

**Naming.** `Type` is unavailable in Lean (it is the universe), and abbreviating it
to `Ty` would reproduce exactly the defect
[crates/CLAUDE.md](../crates/CLAUDE.md) anti-pattern 4 names. So "Type" is the family
prefix and never the whole name: `TypeTable`, `TypeRef`, with `CandidType` left for
the Rust trait. These identifiers are meant to be **the same in Lean and in Rust**,
which is what makes "`candid_subtype` reads as a transcription of its Lean
counterpart" achievable rather than aspirational.

The two names the flat representation introduced are borrowed from the spec's grammar
instead: a `Composite` is a `<comptype>`, and a `Slot` is the `<datatype>` position
that the wire format's `I` fills with either a primitive opcode or an index. Neither
is a "type" — a slot cannot express one and a composite is not meaningful without its
table — so neither takes the `Type` prefix.
[crates/README.md](../crates/README.md#naming) records the same two names for the
Rust side, since the point of sharing identifiers is that they name the same thing.

`TypeTable` rather than `TypeEnv`, the name used in `rust/`, for two reasons. The spec
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

**Subtyping relates two type tables, not one.** A `Slot` holding a `ref` means
nothing without its table, so the unit the API speaks in is `ClosedType` — a table
and a root together. The case that matters most compares a type table that arrived on
the wire against the receiver's own type graph, and those are unrelated tables;
`rust/candid/src/types/subtype.rs:19` takes a single `env` for both types, which works
only because callers merge tables first.

The consequence to keep hold of: the `func` rule's contravariance swaps the *tables*
along with the types, and therefore swaps the reference-pair accounting with the
tables — a pair `(i, j)` is about `A`'s `i` and `B`'s `j`, so reading it unswapped
asserts something about the transposed pair. Both mistakes are invisible when there
is only one table to swap, and the second one shipped in this model before the
`contra` checks in [Main.lean](Main.lean) caught it: it reported `<:` for two types
that are not related.

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
- [x] Well-formedness of types — references resolve, labels do not repeat, a `oneway`
      function has no results, and a method type denotes a function
- [x] Subtyping, as a relation with a derived decision procedure
- [ ] Coercion, including the `opt` backtracking rule
- [ ] Binary wire format: type table, memory section, LEB128/SLEB128
- [ ] Cost model / resource exhaustion
- [ ] Textual value syntax

## Deferred, deliberately

Named here so they are obligations rather than oversights.

- **`decSubtype_iff`** — that the procedure decides the relation. Stated in
  [Candid/SubtypeSpec.lean](Candid/SubtypeSpec.lean). Soundness should follow by
  coinduction, with the pairs recorded in `seen` as the coinductive hypothesis, which
  is what `seen` means. There is no longer a budget premise to discharge: the
  procedure returns `Bool` and is total.
- **The pair accounting is path-scoped, and membership is a scan.** `seen` is
  threaded down a path rather than shared between siblings, which is a faithful
  reading of the coinductive hypothesis and is what lets the measure need no side
  conditions. The cost is that `seen.contains` walks the current path, so a table of
  *n* entries in one long cycle costs O(n²): measured 70 ms at 10,000 entries, 1.6 s
  at 50,000, and 113 s at 400,000, with no stack overflow at any of those depths.
  Sharing the accounting across siblings in a set is also sound for a greatest fixed
  point and is how an implementation gets a polynomial bound; the reference model
  keeps the simpler structure until a conformance vector makes that a problem.
- **Flattening the surface syntax.** A `.did` type is nested; a `Composite`'s
  children are slots. The parser will need the pass that interns nested composites
  into a table, and textual aliases (`type A = B;`) have to be resolved by it —
  `intern`/`close` are only the hand-written-example half of that.
- **Verso.** Deliberately not yet: bundling an undocumented doc toolchain into the
  work whose purpose was de-risking the build would have doubled the unknowns.

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
