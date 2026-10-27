# `lean/` — Lean 4 reference model and specification

**Status: fourth slice.** Types, the field-id hash, subtyping — as both a relation and a
decision procedure — values with coercion, and the binary format in both directions,
with an executable that writes them out
as conformance vectors, reads them back, and is checked against `candid` 0.10 in CI. "Slice" is a label for
what landed in a merge window, applied after the fact; the forward-looking plan is the
coverage checklist below and the tiers in [REWRITE.md §3](../REWRITE.md#3-lean-honestly). Nothing is published and
nothing carries a compatibility promise. See [REWRITE.md](../REWRITE.md) for why this
exists.

Eventually replaces [coq/](../coq/) and [spec/](../spec/), on the conditions in
[REWRITE.md §6](../REWRITE.md#6-the-ratchet).

```
lake build                                    # build the libraries and the executable
lake exe oracle                               # check the model against every vector
lake exe oracle write ../conformance/vectors  # regenerate the committed vectors
lake exe oracle check <file>...               # check vector files against the model
```

Two libraries. `Candid` is the model and imports nothing outside Lean's core.
`Oracle` is about the model: the vector format and its JSON
([Oracle/Vector.lean](Oracle/Vector.lean)), the hand-written vectors
([Oracle/Handwritten.lean](Oracle/Handwritten.lean)), and the generator
([Oracle/Generate.lean](Oracle/Generate.lean)). It uses `Lean.Data.Json`, which is why
it is separate. The format itself is specified in
[conformance/README.md](../conformance/README.md#format-version-0).

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
procedure is a worklist: it carries the obligations still pending and the pairs
already assumed — `seen` and `seenRev`, one list per direction — and each step either
records a pair or discharges an obligation. The measure is (`remaining`, pending
obligations), where `remaining` is the number of pairs the lists do *not* record; it is
named only by `termination_by`, so the `|A| x |B|` pair space it counts over is never
built at run time. No fuel, no `Option Bool`, and no "unanswered" state in the public
API. The first version of this model, with composites nested inside each other, had no
such measure: a cycle alternating which side holds the reference dodged the memo
entirely, so no budget decided it.

The assumptions are shared by the whole run rather than scoped to a path. Every
premise of every rule is a conjunct, so nothing backtracks: a `false` anywhere is the
answer, and a `true` means every assumption was discharged. Path-scoped assumptions
were the earlier design, and they re-derive a shared sub-type once per path reaching
it — exponential in depth, 2^41 - 1 comparisons for a 41-entry chain whose entries
each reference the next twice. Each pair is now compared at most once per direction.

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

**A table is checked once, and the type says so.** Well-formedness is a prerequisite
of subtyping, decoding and encoding alike, so `TypeTable` is a table that carries the
proof, and a decoder or builder produces a `RawTypeTable` and calls `check` on it.
Checking only what an operation visits fails closed for some malformed inputs and not
others: `empty <: t` never unfolds `t`, so a reference dangling behind `t`'s root went
unnoticed while one *at* the root was rejected. `TypeTable` takes the short name
because it is the one nearly every signature names.

**Subtyping relates two type tables, not one.** A `Slot` holding a `ref` means
nothing without its table, so a type is a `t.Root`: a slot checked to resolve in `t`,
with `t` in its type rather than stored beside it. One table has many roots (a
message's arguments, a service's methods), and a root of `A` cannot be passed where a
root of `B` is expected. The case that matters most compares a type table that arrived on
the wire against the receiver's own type graph, and those are unrelated tables;
`rust/candid/src/types/subtype.rs:19` takes a single `env` for both types, which works
only because callers merge tables first.

The consequence to keep hold of: the `func` rule's contravariance swaps the *tables*
along with the types, and therefore swaps the reference-pair accounting with the
tables — while each assumption keeps its direction. The procedure carries two lists,
`seen` for assumed `A <: B` pairs and `seenRev` for assumed `B <: A` pairs, and the
parameter premise exchanges them. This model shipped both ways of getting it wrong.
First it read `seen` unswapped, so a pair `(i, j)` asserted something about the
transposed indices; then it swapped `seen` element-wise, which fixes the indices but
reads an assumed `A.i <: B.j` as `B.j <: A.i` — the converse, which does not follow.
Both reported `<:` for two types that are not related, and both are invisible when
there is only one table to swap. The `contra` vectors in
[Oracle/Handwritten.lean](Oracle/Handwritten.lean) are the witnesses, one per mistake.

## What slice 2 established

**Steps 2 and 3 of the ordering rule, for subtyping.** The executable writes every
vector it knows to [conformance/vectors/](../conformance/vectors/), reads files back as
any runner would, and CI checks both that the committed files are current and that
`rust/candid` agrees with them
([conformance/runners/candid-0.10/](../conformance/runners/candid-0.10/)). The checks
that were built into the executable are now the hand-written vectors, unchanged; the
generated ones pair every type in a small universe with every other.

**The first run found a 0.10 bug, and it is the one this model's design rules out.**
The procedure above shares its assumptions across the whole run, and that is sound
*because nothing backtracks*: any `false` is the final answer, so nothing assumed on
the way to it is ever reused. `rust/candid/src/types/subtype.rs` shares its `gamma` the
same way, but it does backtrack — the `opt` rule tries `t <: t'` and, on failure, falls
through to the special rule. The failed attempt removes only its own pair from
`gamma`, so pairs proved under that assumption survive and answer later questions.
`didc check` accepted a breaking upgrade this way, until 0.10.39 (#775) made a failed
step withdraw every assumption made since it; the vector and the reasoning are in
[Oracle/Handwritten.lean](Oracle/Handwritten.lean) under "Assumptions made under a
failed comparison". The same reasoning is the constraint on `candid_subtype`: if it
ever tries a rule and recovers from the failure, it cannot share assumptions across
that recovery.

**`Check.known` is gone.** The executable could mark one of its checks as a known gap
in the model. None was ever marked, and in a vector file that is the runner's business,
not the vector's: the candid 0.10 runner keeps its own `KNOWN` list, with the same rule
that a listed divergence that starts agreeing is a failure.

## What slice 3 established

**Coercion, through all three steps at once.** [Candid/Value.lean](Candid/Value.lean)
has values and what it means for one to have a type, and
[Candid/Coerce.lean](Candid/Coerce.lean) has `coerce`: the spec's `v : t ~> v' : t'` as
a function, `none` where no rule applies. Vectors of a new kind carry a value, the type
it has, the type it is coerced at, and the result or `"reject"`. The 0.10 runner checks them by encoding the value at its type and
decoding the bytes at the other, since 0.10 coerces only by decoding.

**The negative premises are the `none` branch.** Two of the spec's `opt` rules say
"and else goes to `null`", `not (exists <w>. <v> : <t> ~> <w> : <t'>)`. Stated as a
function, that premise is the failure case of the inner call, so the four rules are one
case split on whether the inner coercion succeeded. Nothing about them needed the
elimination subtyping did.

**Coercion has three outcomes, and the spec had to be fixed to say so.** Coercing a
value whose type does not accept `null` at an `opt` type asks the same question one
`opt` deeper, about the same value. At an *infinite option*, `type R = opt R`, that is
the question being asked, and "else goes to `null`" made it depend on its own negation:
`5 : nat ~> w : R` held exactly when it did not. The model first answered `null`, and
0.10 disagreed: it unwraps the expected type until its recursion limit, an error its
`opt` rule does not recover from, and rejects the message — under an enclosing `opt`,
in a record field and in a vector element too. Looking for which was right turned up
`test/construct.test.did`, which has asserted the rejection since #679, with Motoko
running the same suite. Only the spec had not been updated, and #778 updated it: the
coercion is *undefined*, which is not the same as failing, so nothing recovers from it.

`coerce` therefore returns one of three outcomes: a value; a failure, which the `opt`
rules turn into `null`; or `Undefined`, which they pass on. It is an
`OptionT (Except Undefined)`, so `<|>` is exactly the `opt` rules' recovery. The
generated vectors include types that hold an infinite option in a record field, a
vector element and a variant tag, and the two-entry cycle, and all of them agree with
0.10.

That same step is the only one where the value does not get smaller, so it is also
where termination needed thought. The model peels the expected type's whole chain of
`opt`s at once (`optLayers`) and coerces at what is under it; a chain that does not end
is an infinite option.

**The runner found a bug in the model.** The first run disagreed on every coercion to
`opt reserved`: the model said `null`, 0.10 said `opt null`. 0.10 was right —
`5 : nat ~> null : reserved`, so the option around it is not empty. Once the chain of
`opt`s was peeled, the case for `reserved` was no longer reached. Every hand-written
vector had agreed with the model, and so had the three properties below; it took a
second implementation to see it.

**Three of the spec's properties hold over the generated universe** — roundtripping
(`v : t ~> v : t`), well-typedness (the result has the target type), and soundness
(`t <: t'` means no `v : t` fails to coerce; the spec's exception is the undefined
coercion at an infinite option). `lake exe oracle` checks each for every sample
value against every type and fails on a counterexample. That is a test, not a proof;
see "Deferred, deliberately".

**What a value is.** Numbers carry their width (`5 : nat8` and `5 : nat` are different
values), which the spec's textual syntax leaves to context; a runner can then build a
value without its type. Floats are their IEEE 754 bits, since coercion is the identity
on them and bits keep what a `Float` would make unequal or lose: a NaN's payload and the
sign of a zero. `null` is one value, as in the spec, where Rust's `IDLValue` has
`Null`, `None` and `Reserved`. A record value lists its fields in ascending id order,
the wire format's order, so roundtripping holds as equality rather than up to
reordering.

## What slice 4 established

**The binary format, as a decoder that is strict and an encoder that is one choice of
many.** [Candid/Wire.lean](Candid/Wire.lean) has LEB128, `encode`, `decode` -- the
inverses of the spec's `T` and `M` -- and `deserialize`, which is `decode` followed by
`coerceArgs`, the spec's "tuple types" rule: an argument sequence coerces like a
tuple-shaped record, so an extra argument is ignored and a missing one is `null` where
its type accepts `null`. A new vector kind carries bytes, the types to decode them at,
and the values or `"reject"`.

The encoder exists to generate vectors and for the round-trip check, not as a
specification of bytes: the spec calls type serialisation "a relation", since an encoder
chooses its table. That is why encoding conformance will be judged by decoding (see
[conformance/README.md](../conformance/README.md#still-to-come)) rather than by a
canonical encoding profile, which [REWRITE.md §2](../REWRITE.md#2-what-we-are-building)
now records.

**Decoding needed a termination argument the spec does not mention.** Every value
consumes bytes except a record, whose encoding is only its fields', so `type R = record
{ R }` -- or `record { null; R }` -- recurses without consuming anything. `M` is defined
by recursion on the value, so such a type has no finite value, and nothing decodes at
it. The decoder counts the records on its path that started at the current position and
rejects past the table's size, which by pigeonhole is exactly "the same entry at the
same position again". The measure is (bytes remaining, table size minus that count, the
step's place in its list), and the proof is in the file. `candid` 0.10 agrees on both
vectors; it gets there by rewriting such types to `empty` before decoding.

**Choices the spec leaves open**, each recorded in the file's header: non-shortest
LEB128 is accepted, as 0.10 does (REWRITE.md §7 has the open question); opaque
references are rejected, since a `Value` has no reference table; and every value is
decoded, including an extra argument and a record field the receiver drops, so a
malformed one rejects the message. 0.10 agreed on that last one, which it did not have
to: skipping a value is where a decoder is most tempted to stop checking it.

**The runner found three places where 0.10 is narrower or looser than the spec**, all
recorded as known divergences rather than fixed in either place: it allows at most one
function annotation in a decoded type, it accepts a `oneway` function type with results
from the wire, and it bounds a principal at 29 bytes. The first and third are questions
about the spec as much as about 0.10.

**A fourth property holds over the generated universe**: every sample encodes, and its
bytes decode to the same value at the same type, in a table equal to the one written up
to the order of each entry's members.

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
      width subtyping. A float value is its bits, and coercion is the identity on it,
      so float edge cases belong to the textual value syntax.
- [x] Records, variants, vectors, text — as types
- [x] Recursive types and the type-table graph
- [x] Well-formedness of types — references resolve, labels do not repeat, a `oneway`
      function has no results, and a method type denotes a function
- [x] Subtyping, as a relation with a derived decision procedure
- [x] Values, and coercion, including the `opt` backtracking rule
- [x] Binary wire format: type table, memory section, LEB128/SLEB128 -- decoding,
      and an encoder; not future types (opcodes below `-24`), which the spec says to
      skip and the model rejects
- [ ] Cost model / resource exhaustion
- [ ] Textual value syntax

## Deferred, deliberately

Named here so they are obligations rather than oversights.

- **`decSubtype_iff`** — that the procedure decides the relation. Stated in
  [Candid/SubtypeSpec.lean](Candid/SubtypeSpec.lean). Soundness should follow by
  coinduction, with the pairs recorded in `seen` and `seenRev` as the coinductive
  hypothesis, which is what they mean. Because the assumptions are shared across the
  run, the invariant is about the whole worklist: when it empties, the assumed pairs
  are a set closed under the rules. There is no budget premise to discharge: the procedure
  returns `Bool` and is total.
- **Coercion's properties as theorems.** Roundtripping, well-typedness, and soundness
  against `Subty` are checked by the executable over the generated universe (see
  "What slice 3 established"); the theorems are about every value, and soundness is
  the one MiniCandid proves as `coerce_well_defined`. Stated in prose in
  [Candid/Coerce.lean](Candid/Coerce.lean)'s header, not as `sorry`s.
- **Membership is a scan.** `seen` and `seenRev` are lists, so `contains` walks every
  pair recorded so far, and a table of *n* entries in one long cycle costs O(n²):
  measured 234 ms at 10,000 entries and 6.3 s at 50,000. `run` is tail-recursive, so
  depth costs no stack. A hash set would make this linear in the pairs compared; the
  reference model keeps lists, which the termination measure is stated over, until a
  conformance vector makes that a problem.
- **Flattening the surface syntax.** A `.did` type is nested; a `Composite`'s
  children are slots. The parser will need the pass that interns nested composites
  into a table, and textual aliases (`type A = B;`) have to be resolved by it —
  `intern`/`close` are only the hand-written-example half of that.
- **Future types.** The spec reserves opcodes below `-24` for types an older decoder
  skips by length. The model rejects them; no vector exercises them until it does not.
- **Encoding vectors, and type equivalence.** An encoding vector is a value and a type,
  and the check is that an implementation's bytes decode to an *equivalent* type and
  the same value. Equivalence -- the same infinite tree -- is decidable with the
  subtype procedure's worklist and is not written yet.
- **Unbounded vectors of zero-length values.** `vec null` can claim any length in a
  few bytes, and the decoder builds a value that long. That is the cost model's job.
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
