` CLI tool

The `candid_diff` package exposes the `candiff` tool for scripting Candid value comparisons that have human-readable error messages.

The tool compares input and output canister messages to those recorded earlier, from earlier run(s).

## Use cases

- General-purpose debugging / development tool for Candid data
- In CI scripts: summarize deviations from expected responses

## Candid input format

Accept binary and text options for Candid data to compare:

- raw candid (what `raw` means for `dfx` input/output)
- candid text format

## Candid output format
 
- No default output when diff is empty
- Human-readable default output when diff is non-empty

The human-readable diff answers the question:

> How do I structurally edit the first value into the second, with the fewest ("small") edits?

## Data and type changes

Rather than compare two values textually, the tool is structural, like Candid itself.

The tool does not attempt to compare candid values that do not share a
common type, but we do not know if this the case or not, a priori.
When provided, this common type helps inform the output information,
but it is not required.  When absent, the tool gives less helpful
information on values without a common type.

### Typing

Two cases:

- Type invariant: Both values have a common type.
- Type varies: Values have unrelated types.

The first case is our main use case, where one value and the common
type come from some trusted files, in a CI environment.

In the second case, we may or may not know the associated types, and
knowing the expected type(s) can help provide more useful output
(probably); still, that's not our main use case.

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
