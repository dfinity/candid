# Candid Type Doc Comments

Date: Mar 12, 2026

## Motivation

Rust canisters often use Rust doc comments as the primary source of interface
documentation. This works well for service methods exported with
`#[candid_method]`, because these doc comments are preserved when generating
textual Candid. However, the same is not true for data types exported through
`#[derive(CandidType)]`.

As a result, generated `.did` files contain method-level documentation, but
drop documentation for:

* type definitions
* record fields
* variant members

This is problematic because much of the semantic meaning of a canister
interface is expressed on the data model rather than on the methods alone.
Request and response types often carry the important descriptions, constraints,
and invariants that downstream users need to understand.

The goal of this proposal is to preserve Rust doc comments on exported Candid
types and their members so that generated `.did` files can act as a more
complete interface document.

## Design

The implementation follows the same overall pattern that is already used for
service method docs: doc comments are collected from Rust source and carried to
the textual Candid printer through a side channel.

The crucial design choice is that docs are **not** stored on the structural type
representation itself. The runtime types in `candid::types` are used for
normalization, equality, hashing, and name assignment. Making docs part of
those structures would either perturb structural equality or require special
rules to ignore docs during comparison. Both would be awkward and fragile.

Instead, the implementation introduces a parallel metadata flow:

1. `candid_derive` extracts Rust doc comments while deriving `CandidType`.
2. `candid::types` memoizes that metadata per Rust `TypeId`.
3. `TypeContainer` translates that metadata to the final exported Candid type
   names when constructing a `TypeEnv`.
4. `candid::pretty::candid` renders the docs when pretty-printing named type
   definitions and their members.

This preserves the current type pipeline while allowing documentation to follow
the exported interface.

### Capturing docs in Rust derives

When deriving `CandidType`, the derive machinery now extracts docs from:

* the struct or enum item itself
* struct fields
* enum variants
* fields nested inside inline record payloads of variants

The same extraction logic is shared with `#[candid_method]`, so line order and
blank lines are preserved consistently.

The derive implementation emits both the existing structural type description
and a second metadata description. Concretely, the `CandidType` trait gains a
new default hook:

```rust
fn _ty_doc() -> internal::TypeDoc {
    internal::TypeDoc::default()
}
```

Manual implementations of `CandidType` remain valid because the new method has
a default implementation.

### Representing type docs

The additional metadata is represented separately from `TypeInner`:

```rust
pub struct TypeDocs {
    pub named: BTreeMap<String, TypeDoc>,
}

pub struct TypeDoc {
    pub docs: Vec<String>,
    pub fields: BTreeMap<u32, FieldDoc>,
}

pub struct FieldDoc {
    pub docs: Vec<String>,
    pub ty: Option<Box<TypeDoc>>,
}
```

`TypeDoc.docs` stores doc lines for a named type definition.

`TypeDoc.fields` stores docs for members of that type. The key is the canonical
field identity used by Candid:

* for named labels, `idl_hash(label)`
* for tuple labels, the numeric field id

`FieldDoc.docs` stores the docs attached to a record field or variant member.

`FieldDoc.ty` stores docs for nested inline record or variant payloads when
those payloads belong to a named exported type.

### Type naming and association

One challenge is that Rust names are not the final names used in textual
Candid. `TypeContainer` already rewrites the type graph to choose stable export
names and to normalize recursive and generic types. Therefore, doc attachment is
resolved at the same stage.

The metadata is first memoized per Rust `TypeId`. When `TypeContainer` decides
to emit a named Candid type in `TypeEnv`, it also stores the corresponding doc
metadata under the exported type name.

This ensures that doc comments remain attached correctly even when:

* fields are sorted canonically by field id
* fields or variants are renamed through `serde(rename = "...")`
* generic or recursive types receive rewritten export names such as `List_1`

### Rendering docs in textual Candid

The existing `DocComments` structure currently stores only service method docs.
It is extended to also carry docs for named type definitions.

When pretty-printing textual Candid, docs are emitted:

* immediately above `type Foo = ...;`
* immediately above record fields
* immediately above variant members
* immediately above fields nested in inline record or variant payloads that are
  rooted under a named type definition

The existing service method behavior remains unchanged.

The result is that Rust definitions such as

```rust
/// Arguments for creating a cashier.
#[derive(CandidType, Deserialize)]
pub struct CashierArgs {
    /// Human-readable display name.
    pub name: String,

    /// Whether this cashier starts enabled.
    pub enabled: bool,
}
```

produce Candid of the form

```did
// Arguments for creating a cashier.
type CashierArgs = record {
  // Whether this cashier starts enabled.
  enabled : bool;
  // Human-readable display name.
  name : text;
};
```

where field order still follows the canonical Candid ordering rules.

## Special Cases

### Tuples

Tuple records are normally printed using tuple shorthand, e.g.

```did
record { nat; text }
```

This syntax has no place to attach docs to individual tuple positions. Therefore
the printer falls back to explicit numeric fields when tuple members carry docs:

```did
record {
  // First element.
  0 : nat;
  // Second element.
  1 : text;
}
```

This preserves the docs without changing the meaning of the Candid type.

### Newtypes

Single-field tuple structs continue to use their existing structural encoding.
Docs on the outer named type are preserved, but docs on the inner field are not
generally representable without changing the generated Candid shape. This
proposal deliberately preserves the existing shape.

### Anonymous inline types in service signatures

This proposal focuses on docs rooted at named exported types. Anonymous inline
record or variant types that appear only directly in service method arguments or
results are not given a separate documentation channel here. Supporting those
would require a second namespace keyed by service methods and argument/result
positions.

## Alternatives

### Docs on `TypeInner`

One alternative is to store docs directly on `TypeInner` and `Field`, and let
the pretty-printer read them from the type tree itself.

This was rejected because those structures are used for structural identity.
Adding docs there would either make otherwise-equal types compare differently,
or require custom equality semantics that ignore docs. Both options would make
the type system more brittle for the sake of a feature that only matters during
export.

### Key docs directly in the pretty-printer

Another option is to keep the core type system unchanged and let
`candid_derive` populate a richer `DocComments` map directly.

This was rejected because `candid_derive` does not know the final exported
Candid names. If docs were keyed too early, they could become detached when the
type graph is normalized, fields are sorted, or export names are rewritten.

### Rebuild a syntax AST

The `candid_parser` crate already has a syntax-level pretty-printer that stores
docs directly on AST nodes. Reusing that machinery by reconstructing an AST from
the runtime type graph was considered as well.

This was rejected as too invasive. It would require a larger refactoring of the
printer pipeline and still would not eliminate the need to transport doc
metadata from Rust derives into that AST.

## Properties

This design preserves the following properties:

* structural type identity is unchanged
* service method docs continue to work as before
* doc extraction preserves line order and blank lines
* doc attachment is stable under canonical field sorting
* doc attachment is stable under renamed fields and variants
* generated `.did` output is deterministic

## Tests

The expected behavior is verified with end-to-end tests in
`rust/candid/tests/types.rs`.

The tests cover:

* docs on named record types
* docs on record fields
* docs on variant types
* docs on variant members
* coexistence with service method docs
* parsing the generated `.did` back through `candid_parser` and verifying that
  docs are attached to the correct AST nodes

These tests complement the existing parser-side doc comment tests in
`rust/candid_parser/tests`, which already cover syntax-level parsing and
pretty-printing of Candid comments.
