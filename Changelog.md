
# Changelog

## 2021-01-12 (Rust 0.6.13)

* Better pretty printer for Candid value

## 2021-01-06

### Rust (0.6.12)

* Support reference types
* Support more native Rust types: HashMap, HashSet, BTreeMap, BTreeSet, i128, u128
* Bug fix for empty record detection when deserializing to native Rust types

### Other

* Test suites for reference types
* `didc encode` supports outputing blob format

## 2020-12-07

### Spec

* Bug fix for opt subtyping
* Formalize definitions of IDL-soundness in Coq

### Rust (0.6.11)

* Support the opt subtyping rules
* Allow using Rust keyword as field label

### Tests

* Add opt subtyping tests

## 2020-11-05

### Spec

* Rewrite description of deserialization [#128](https://github.com/dfinity/candid/pull/128)

### Rust (0.6.9 -- 0.6.10)

* Add result getter for serializer
* Implement CandidType for std::time::SystemTime and Duration

## 2020-10-20

### Spec

* Add service initialization parameters [#88](https://github.com/dfinity/candid/pull/88)
* Reverse subtyping on records and variants [#110](https://github.com/dfinity/candid/pull/110)

### Rust (0.6.4 -- 0.6.8)

* Support service constructor
* Export `init` types in JS binding for service constructor
* Improve pretty-printing for Candid values: underscore for numerals, blob shorthand for `vec nat8`.
* Disable pretty-printing for large vectors.
* Add attribute `#[candid_method]` to derive Candid types for functions.
* Add a feature flag `cdk` to generate candid path specifically for Rust CDK.

### Tools

* Candid UI canister to render a web UI for all running canisters on the network.

## 2020-09-10 (Rust 0.6.2 -- 0.6.3)

* Fix a bug when decoding nested record values.

## 2020-09-10 (Rust 0.6.1)

* Add `encode_args` and `decode_args` functions to encode/decode sequence of arguments.

## 2020-09-02 (Rust 0.6.0)

* Use `ic-types` for Principal (breaking change)
* Support type annotations in parsing Candid values
* Support float e notation
* Support nested comments
* Pretty print decoded candid values
* New lexer using the `logos` crate
* Use `codespan-reporting` to report Rust-like parsing errors

## 2020-08-24

### Rust (0.5.3)

* Fix deserialization to validate type table and detect infinite loop in `type T = record { T }`
* Fix serialization for newtype struct
* Display trait for pretty printing `types::Type`

### Tests

* More test suites for prim and construct types
* Tools for emitting JavaScript tests from Candid test suites

## 2020-08-18

### Tools

* Publish `didc` and `candiff` binary in the release
* Generate JS tests from the Candid test suites

## 2020-08-14

### Spec

* No longer requires the shortest LEB128 number in deserialization [#79](https://github.com/dfinity/candid/pull/79)

### Rust 

* Parser improvements:
  + Floats in fractional number, no e-notation yet
  + Comments (no nested comments)
  + Blob shorthand for `vec nat8` value
  + Fix text parser to valiate utf-8 encoding
* Bounds check for bool and text
* Type annotation for reserved

### Tools

* Initial commit for didc and candiff tools
* Add Candid test suite
