# `conformance/` — machine-readable Candid conformance suite

**Status: reserved, empty.** No content yet. See [REWRITE.md](../REWRITE.md) for
why this exists.

## What goes here

A conformance suite that a Candid implementation in *any* language can consume,
plus the generator that produces it from the Lean model in [lean/](../lean/).

Eventually replaces [test/](../test/).

## What is wrong with the current suite

[test/](../test/) contains 471 assertions across six files. They are good
assertions — the problem is packaging, not content.

- **It cannot bootstrap.** The format is a bespoke extension of the Candid text
  grammar, so you need a working Candid text parser before you can run test #1.
  Anyone implementing Candid in a new language hits this wall immediately, and
  this is the likeliest reason there is no ecosystem of conformant third-party
  implementations.
- **The only runner is a Rust test**
  ([rust/candid_parser/tests/test_suite.rs](../rust/candid_parser/tests/test_suite.rs)).
- **Parser conformance has zero cases.** [test/README.md](../test/README.md)
  documents `*.good.did` / `*.bad.did`. There are none in the repo.
- **Encoding is not covered**, which the README explicitly disclaims, because the
  binary format is non-canonical.
- **Subtyping is tested only indirectly** through decoding, so a subtype-checker
  bug surfaces only if it also changes a decode outcome.
- **It is not distributable.** Consuming it means cloning this repo and writing a
  parser for a grammar that exists nowhere else.

## Design

**Vectors are data, not a grammar.** A JSON manifest, roughly:

```jsonc
{
  "id": "opt-coerce-mismatch-to-null",
  "wire": "4449444c...",              // hex
  "expected_type": { /* JSON type AST */ },
  "outcome": "ok",                     // | "reject"
  "value": { /* canonical JSON encoding */ },
  "tags": ["coercion", "opt", "subtyping"]
}
```

The `.test.did` form is kept as a **human authoring front-end** that compiles to
JSON. Readability is not lost; the bootstrap dependency is.

**Generated from Lean, not hand-written.** Enumerate all types up to depth 3 and
all `(actual, expected)` type pairs; compute the spec-mandated result in Lean;
emit vectors. Exhaustive by construction for small types, rather than "whatever
someone thought of". Hand-written vectors remain welcome for regressions and for
cases outside the generated envelope.

**Coverage the current suite lacks:**

- **Encoding**, against a canonical encoding profile — deterministic type-table
  ordering, no unused entries, shortest-form LEB128. This has to be defined before
  it can be tested; see [REWRITE.md §7](../REWRITE.md#7-open-questions).
- **Subtyping directly** — `T <: U` / `T !<: U` as first-class assertions.
- **`.did` parsing** — the `*.good.did` / `*.bad.did` cases that were always
  documented and never written.
- **Resource exhaustion / cost model** as normative.
  [test/spacebomb.test.did](../test/spacebomb.test.did) is a good start; every
  implementation faces the zip-bomb problem and currently invents its own defense.

**Published as a versioned artifact** — data crate, npm package, and a tarball on
GitHub Releases — not a directory reachable only by cloning.

## Migration

All 471 existing assertions must exist as vectors and pass before
[test/](../test/) is deleted. Converting them is the first task here, and it is
also what gives the Lean oracle something to run against on day one.
