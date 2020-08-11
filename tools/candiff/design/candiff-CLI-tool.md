# Tool design (`candiff`)

The `candiff` crate provides the `candiff` CLI tool.

The `candiff` tool compares candid data, and gives with human-readable output.

Rather than compare two values textually, the tool is structural, like Candid itself.

Optionally, the tool type-checks the values that it compares, and signals errors when they value to check against the given type.

## Use cases

- General-purpose debugging / development tool for Candid data
- In CI scripts: summarize deviations from expected responses
- Reference implementation for parsing and sanity-checking Candid values.  See https://github.com/dfinity-lab/motoko/issues/1748


## Candiff input format

Accept binary and text options for Candid data to compare:

- raw candid (what `raw` means for `dfx` input/output)
- candid text format

## Candiff output format
 
- No default output when diff is empty
- Human-readable default output when diff is non-empty

The human-readable diff answers the question:

> How do I structurally edit the first value into the second, with the fewest ("small") edits?

## Data and type changes

The tool is structural, like Candid itself.  It does not attempt to
compare candid values that do not share a common type, but we do not
know if this the case or not, a priori.  When provided, this common
type helps inform the output information, but it is not required.
When absent, the tool gives less helpful information on values without
a common type.

### Typing

Two cases:

- Type invariant: Both values have a common type.
- Type varies: Values have non-identical types, related by an edit.

In both cases (type invariant and varying), the user may provide the
types that they know, or not, and these types may or may not be
correct.

The first case is our main use case, where one value and the common
type come from some trusted files, in a CI environment.  In this case,
we want to see if the first value is really classified by the expected
type (if given), and that second value is the same as the first or
not; if the values differ, we want to get a nice summary of how to
edit the first into the second.

Other use cases are extra.  For instance, when the type varies in the
second value, the two values are classified by distinct types, and
comparing those types may also be helpful (optionally, and if
possible).

### Data

The tool's output consists of a DSL of Candid edits.

We summarize the features of this DSL below, leaving details for later.

#### Vector changes

- Insert element(s)
- Remove element(s)
- Replace element(s)

#### Option changes

- null ~~> Some
- Some ~~> null
- (Non-option type is a higher-level change)

#### Variant changes

- Same constructor, change payload
- (New constructor is a higher-level change)

#### Record changes

- Change particular field(s) value
- Remove particular field(s)
- (all other fields are unchanged)
- (Non-record type is a higher-level change)
