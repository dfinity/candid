# `lean/` — Lean 4 reference model and specification

**Status: reserved, empty.** No content yet. See [REWRITE.md](../REWRITE.md) for
why this exists.

## What goes here

A Lean 4 model of Candid that serves as both the **reference implementation** and,
via [Verso](https://github.com/leanprover/verso), the **specification document**.

Eventually replaces [coq/](../coq/) and [spec/](../spec/). See the ratchet in
[REWRITE.md §6](../REWRITE.md#6-the-ratchet) for the conditions under which those
are deleted — in particular, `coq/` is not removed until the two models have been
diffed, because a disagreement between them would be the most valuable finding of
this project.

## The ordering rule

**Executable first, proved second.**

1. `Ty`, `Value`, `subtype`, `coerce`, and the wire format as plain Lean functions
   with `Decidable` instances.
2. A `lake`-built binary that reads a conformance vector file and reports results.
3. CI wiring: that binary as a differential oracle against the Rust implementation.
4. *Only then*, proofs about those definitions.

Inverting this produces [coq/MiniCandid.v](../coq/MiniCandid.v) again in a
different language: a formalisation that is correct, maintained, and consumed by
nothing except a CI job proving it still compiles.

The rule that keeps it honest:

> Every Lean definition must be either (a) reachable from the reference
> executable, or (b) a proof about something that is. No orphan formalisation.

## Constraints

- **No mathlib.** We do not need it, and depending on it would dominate build
  times and breakage surface.
- **Pin `lean-toolchain`.** Lean's toolchain moves faster than Coq's. Upgrades are
  scheduled work, not incidental.
- **Verso is young.** Expect to read its source rather than its documentation.

## Coverage target

The Coq model covers nine type constructors and no binary format. This model must
cover what actually breaks in production:

- [ ] Primitive types, including the numeric tower and float edge cases
- [ ] Records, variants, vectors, text
- [ ] Recursive types and the type-table graph
- [ ] Subtyping, as a relation with a derived decision procedure
- [ ] Coercion, including the `opt` backtracking rule
- [ ] Binary wire format: type table, memory section, LEB128/SLEB128
- [ ] Cost model / resource exhaustion
- [ ] Textual value syntax

## Prior art in this repo

[coq/MiniCandid.v](../coq/MiniCandid.v) proves `subtyping_refl`,
`subtyping_trans`, `coerce_roundtrip`, `coerce_well_defined`, `soundness`, and
`transitive_coherence`. These are real theorems about the genuinely subtle part of
the language and they should be ported, not discarded. Read it before starting.
