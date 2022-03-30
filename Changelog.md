
# Changelog

## 2022-03-30 (Rust 0.7.11 -- 0.7.14)

* Update service methods in TS bindings to use ActorMethod, the type used by agent-js's Actor class
* Infer the type of `vec {}` to `vec empty` to satisfy subtype checking
* Expose more internal structures

## 2022-01-06 (Rust 0.7.10)

* Bump ic-types to 0.3
* `candid::utils::service_compatible` to check for upgrade compatibility of two service types

## 2021-12-20 

### Rust (0.7.9)

* Generate Rust binding from Candid file (experimental)
* Ignore init args for subtype checking
* Pretty print text value with escape_debug
* More visitors for Nat and Int type

### Candid UI

* Flamegraph when profiling feature is enabled

## 2021-09-30 (Rust 0.7.8)

* Fix `subtype` function to take only one env. To check subtyping from two did files, use `env.merge_type(env2, ty2)` to merge the env and rename variable names.

## 2021-09-09

* Release ARM binary for `didc`
* Refine the spec for opt rules

## 2021-08-17

### Rust (0.7.5 -- 0.7.7)

* Support import when parsing did files with `check_file` function 
* Fix TypeScript binding for reference types

### Candid UI

* Report profiling info when `__get_cycles` method is available
* Add binding generation and subtype checking for Candid UI canister

## 2021-07-07 (Rust 0.7.2 -- 0.7.4)

* Update TypeScript binding to better integrate with dfx
* Set `is_human_readable` to false in Deserializer

## 2021-06-30 (Rust 0.7.1)

* Update JS binding to use `Principal` from `@dfinity/principal`
* Add `#[candid_path("path_to_candid")]` helper attribute to the candid derive macro
* Update `ic-types` to 0.2.0

## 2021-06-03 

### Spec

* Update spec to introduce subtyping check in deserialization [#168](https://github.com/dfinity/candid/pull/168)
* Coq proof for subtype check
* Update test suite to conform with the new spec

### Rust (0.7.0)

#### Breaking changes

* Require full subtype checking in deserialization. This removes undefined behavior when trying to decode
  variant and empty vector at types that are not supertype of the wire type.
* Deserialization requires both `Deserialize` and `CandidType` trait.
* `de::ArgumentDecoder`, `ser::ArgumentEncoder` moved to `utils::{ArgumentDecoder, ArgumentEncoder}`.
* `types::subtype` returns `Result<()>` instead of `bool` for better error message.
* Disable subtyping conversion for opt rules in `IDLValue.annotate_type`.
* Display type annotations for number types.

#### Non-breaking changes

* Better error messages in deserialization
* Remove unnessary `reqwest` dependency
* Implement CandidType for `str`

### Tools

* `didc bind` to support Motoko bindings
* `didc hash` to compute hash of a field name
* `didc decode` can decode blob format
* Candid UI canister

## 2021-04-07 (Rust 0.6.19 -- 0.6.21)

* Fix a bug for serializing recursive values in Rust CDK [#210](https://github.com/dfinity/candid/pull/210)
* Use BigInt in JS/TS binding
* Fix TypeScript binding for tuple
* Rust support for Func and Service value

## 2021-03-17 

### Rust (0.6.18)

* `#[candid_method(init)]` to support init arguments in service actor
* Subtyping check for Candid types
* Handle subtyping for `reserved` and `int` in decoding

### Other

* Benchmark for Rust library with criterion
* `didc check` and `didc subtype` command to check for subtyping
* Conditional running CI for Coq or Rust library

## 2021-03-04 (Rust 0.6.17)

* Support `serde_bytes` for efficient handling of `&[u8]` and `Vec<u8>`

## 2021-02-11

### Rust (0.6.16)

* Typescript binding for Candid
* Support more native Rust types: Path, PathBuf, VecDeque, LinkedList, BinaryHeap, Cow, Cell, RefCell

### Other

* Documentation for type mapping and howto section
* `didc bind` to generate typescript binding

## 2021-02-01

### Rust (0.6.14 -- 0.6.15)

* Generate random Candid values
* Sort method names lexicographically

### Other

* Candid user guide
* More Coq proof for MiniCandid
* `didc random` command and an experimental config file

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
