
# Changelog

## Unreleased

### Candid

* Breaking changes:
  + `pp_args` and `pp_init_args` now require a `&[ArgType]` parameter. The `pp_rets` function has been added, with the signature of the old `pp_args`.

* Non-breaking changes:
  + The following structs have been moved from the `candid_parser` crate to the `candid::types::syntax` module:
    - `IDLType`
    - `IDLTypes`
    - `PrimType`
    - `FuncType`
    - `IDLArgType`
    - `TypeField`
    - `Dec`
    - `Binding`
    - `IDLProg`
    - `IDLInitArgs`

### candid_parser

* Breaking changes:
  + The following structs have been moved to the `candid` crate:
    - `IDLType`
    - `IDLTypes`
    - `PrimType`
    - `FuncType`
    - `IDLArgType`
    - `TypeField`
    - `Dec`
    - `Binding`
    - `IDLProg`
    - `IDLInitArgs`
    As a consequence, the `FromStr` trait is no longer implemented for the following types:
      - `IDLProg`
      - `IDLInitArgs`
      - `IDLType`
      - `IDLTypes`
    You must now use the `parse_idl_prog`, `parse_idl_init_args`, `parse_idl_type` and `parse_idl_types` functions to parse these types, respectively.
  + `pretty_parse` doesn't work anymore with the `IDLProg` and `IDLTypes` types. Use `pretty_parse_idl_prog` and `pretty_parse_idl_types` instead.
  + The `args` field in both `FuncType` and `IDLInitArgs` now have type `Vec<IDLArgType>`.

* Non-breaking changes:
  + Supports parsing the arguments' names for `func` and `service` (init args).
  + Supports collecting line comments as doc comments in the following cases:
    - above services:
      ```
      // This is a valid doc comment for the service
      service : {
        greet : (text) -> (text);
      }
      ```
    - above actor methods:
      ```
      service : {
        // This is a valid doc comment for greet
        greet : (text) -> (text);
      }
      ```
    - above type declarations:
      ```
      // This is a valid doc comment for type A
      type A = record {
        my_field : text;
      };
      ```
    - above record and variant fields:
      ```
      type A = record {
        // This is a valid doc comment for my_field
        my_field : text;
      };

      type B = record {
        // This is a valid doc comment for nat element
        nat;
        text;
      }

      type C = variant {
        // This is a valid doc comment for my_variant_field
        my_variant_field : nat;
      };
      ```

### candid_derive

* Keeps argument names for Rust functions.

### didc

* Breaking changes:
  + The `didc test` subcommand has been removed.

## 2025-05-15

### Candid 0.10.14

* Add a series of decoder functions which provide convenience for ic-cdk macros usage.

## 2025-01-22

### Candid 0.10.13

* Add `ArgumentEncoder::encode_ref`, `utils::{write_args, encode_args}` that don't consume the value when encoding.

## 2025-01-15

### Candid 0.10.12

* Implement `CandidType` for `std::marker::PhantomData`.

## 2024-12-10

### Candid 0.10.11

* Add `IDLBuilder.try_reserve_value_serializer_capacity()` to reserve capacity before serializing a large amount of data.

## 2024-05-03

### Candid 0.10.10

* Add `candid::MotokoResult` type. Use `motoko_result.into_result()` to convert the value into Rust result, and `rust_result.into()` to get Motoko result.

### candid_parser 0.2.0-beta

* Breaking changes:
  + Rewrite `configs` and `random` modules, adapting TOML format as the parser. `configs` module is no longer under a feature flag, and no longer depend on dhall.
  + Rewrite Rust bindgen to use the new `configs` module. Use `emit_bindgen` to generate type bindings, and use `output_handlebar` to provide a handlebar template for the generated module. `compile` function provides a default template. The generated file without config is exactly the same as before.
* Non-breaking changes:
  + `utils::check_rust_type` function to check if a Rust type implements the provided candid type.

## 2024-04-11

### Candid 0.10.5 -- 0.10.9

* Switch `HashMap` to `BTreeMap` in serialization and `T::ty()`. This leads to around 20% perf improvement for serializing complicated types.
* Disable memoization for unrolled types in serialization to save cycle cost. In some cases, type table can get slightly larger, but it's worth the trade off.
* Fix bug in `text_size`
* Fix decoding cost calculation overflow
* Fix length check in decoding principal type
* Implement `CandidType` for `serde_bytes::ByteArray`
* Add `pretty::candid::pp_init_args` function to pretty print init args

## 2024-02-27

### Candid 0.10.4

* Support `#[serde(rename = "")]` with arbitrary string.
* Fix a performance bug in the type table parsing.
* Allow setting decoding quota for deserialization with the following new functions: `candid::decode_args_with_config`, `candid::utils::decode_args_with_config_debug`, `candid::decode_one_with_config`, `candid::Decode!([config]; &bytes, T)`, `candid::Decode!(@Debug [config]; &bytes, T)`, `IDLArgs::from_bytes_with_types_with_config` and `IDLArgs::from_bytes_with_config`. The original decoding method remains to be non-metered.

### candid_parser 0.1.4

* Fix Typescript binding for init args.

## 2024-01-30

### Candid 0.10.3

* Fix parser when converting `vec { number }` into `blob` type.

### candid_parser 0.1.3

* Add Typescript binding for init args.

### Candid UI

* Fix HTTP header.
* Fix agent routing when running in remote environments.

## 2024-01-03

### Candid 0.10.2

* Fix display `IDLValue::Blob` to allow "\n\t" in ascii characters.

### candid_parser 0.1.2

* Add an "assist" feature. Given a type, construct Candid value in the terminal with interactive dialogue.

### didc 0.3.6

* Add `didc assist` command.
* Fix `didc decode --format blob`.

## 2023-12-15

### Candid 0.10.1

* Add `candid::types::value::try_from_candid_type` to convert Rust type to `IDLValue`.
* Display `IDLValue::Blob` in ascii character only when the whole blob are ascii characters.

### candid_parser 0.1.1

* Add `import service` in parser to allow merging services.

### ic_principal 0.1.1

* Export `PRINCIPAL_MAX_LENGTH` as a public constant.
* Make all dependencies optional.

### Candid UI

* Add II integration with URL parameter `ii` and `origin`.

## 2023-11-16 (Rust 0.10.0)

### Breaking changes

* The original `candid` crate is split into three crates:
  * `candid`: mainly for Candid data (de-)serialization.
    + `candid::bindings::candid` moves to `candid::pretty::candid`. `candid::pretty` moves to `candid::pretty::utils`. These modules are only available under feature flag `printer` (enabled by default).
    + `candid::{Int, Nat}` is only available under feature flag `bignum` (enabled by default). If this feature is not enabled, you can use `i128/u128` for `int/nat` type.
    + Remove operator for `i32` and `Nat`.
    + Add `IDLValue::Blob(Vec<u8>)` enum for efficient handling of blob value.
    + `candid::types::number::pp_num_str` moves to `candid::utils::pp_num_str`.
    + `candid::types::value` module is only availble under feature flag `value`.
    + `mute_warning` feature flag is removed, use `candid::types::subtype_with_config` instead.
  * `candid_parser`: used to be the `parser` and `bindings` module in `candid` crate.
    + Remove `FromStr` trait for `IDLArgs` and `IDLValue`. Use `parse_idl_args` and `parse_idl_value` respectively instead.
    + `TypeEnv.ast_to_type` becomes `candid_parser::typing::ast_to_type`.
    + `bindings::rust::Config` uses builder pattern.
    + `candid` is re-exported in `candid_parser::candid`.
    + `candid::*` is re-exported in `candid_parser`.
  * `ic_principal`: only for `Principal` and `PrincipalError`.

### Non-breaking changes

* Add `candid::types::subtype_with_config` to control the error reporting level of special opt rule.
* Add `Type.is_blob(env)` method to check if a type is a blob type.
* Fix TS binding for `variant {}`.

## Rust 0.9.9 -- 0.9.11

* Set different config values for `full_error_message` and `zero_sized_values` for Wasm and non-Wasm target.
* Fix subtyping error message for empty type.
* Remove name duplication check in `candid_method` to avoid errors on certain IDEs.
* Improvements in Candid UI
  + Add II button, thanks to @Web3NL.
  + Support streaming download of profiling data.

## 2023-09-27

### Rust 0.9.8

* Implement `CandidType` for `std::cmp::Reverse`.
* Rust codegen: add `pub` for struct fields.
* Fix `merge_init_types` and `instantiate_candid` when the main actor refers to a variable.

### Candid UI

* Draw flamegraph for canister upgrade
* Upstream fix from `merge_init_types`

## Rust 0.9.7

* Add `utils::merge_init_args` to parse and merge `candid:args` metadata, and add the same endpoint in Candid UI.
* Add `record!` and `variant!` macro to generate record and variant type AST.
* Allow trailing comma in `func!` macro.
* Add `minize_error_message` to `IDLDeserialize::Config`.

## 2023-09-05 (Rust 0.9.6)

* Improve Rust binding generation: 1) Fix generated code for agent; 2) Generated names conform to Rust convention: Pascal case for type names and enum tags; snake case for function names.
* Fix a bug when deriving empty struct/tuple enum tag, e.g., `#[derive(CandidType)] enum T { A{}, B() }`.
* Add `IDLDeserialize::new_with_config` to control deserializer behavior. For now, you can only bound the size of zero sized values.

## 2023-07-25 (Rust 0.9.2--0.9.5)

* Fix error message for `subtype::equal` to report the correct missing label.
* Recover subtype error from custom deserializer. This fixes some custom types for not applying special opt rule.
* Fix Candid UI to support composite query.
* Internally, move away from `BigInt::try_into` to allow more build targets, e.g. WASI and iOS.
* Spec change: allow `record {} <: record {null}`.
* Fix length counting of zero sized values.
* Remove `arc_type` feature.

## 2023-07-11

### Rust (0.9.1)

* `utils::service_equal` to check if two service are structurally equal under variable renaming.
* `utils::instantiate_candid` to generate metadata from did file: separate init args, flatten imports. For now, comments in the original did file is not preserved.
* `impl From<Func/Service>` trait for `define_function/define_service` macros.
* Make `bindings::candid::pp_args` a public method.
* Bump dependencies, notably `pretty`, `logos` and `syn`.

### Candid UI

* Bump agent-js to fix the new response code change
* Bump candid to 0.9

### didc

* Add a strict mode for `didc check` which checks for structural equality instead of backward compatibility.

## 2023-06-30 (Rust 0.9.0)

### Breaking changes:

* Deserializer only checks subtyping for reference types, fully conforming to Candid spec 1.4. You can now decode `opt variant` even if the variant tags are not the same, allowing upgrading variant types without breaking the client code.
* The old `candid::Type` is now `candid::TypeInner`, and `Type` is a newtype of `Rc<TypeInner>`. This change significantly improves deserialization performance (25% -- 50% improvements)
* `candid::parser` module is only available under feature flag `"parser"`. This significantly cuts down compilation time and Wasm binary size
* Disable the use of `candid::Func` and `candid::Service` to avoid footguns. Use `define_function!` and `define_service!` macro instead
* `candid::parser::typing::TypeEnv` moved to `candid::types::TypeEnv`. Use of `candid::TypeEnv` is not affected
* `candid::parser::types::FuncMode` moved to `candid::types::FuncMode`
* `candid::parser::value` moved to `candid::types::value`
* `candid::parser::pretty` moved to `candid::bindings::candid::value`
* Deprecate `ToDoc` trait for pretty printing `IDLProg`, use `candid::bindings::candid` module instead
* Deprecate `candid::codegen`, use `candid::bindings` instead
* In `candid::bindings::rust`, there is a `Config` struct to control how Rust bindings are generated

### Non-breaking changes:

* Macros for constructing type AST nodes: `service!`, `func!` and `field!`
* Support future types
* Bound recursion depth in deserialization for non-Wasm target (Wasm canister doesn't have a specified C ABI, and runs in a sandbox. It's okay to stack overflow)
* Limit the size of vec null/reversed in deserialization
* `Nat` serialization for JSON and CBOR
* Support custom candid path for `export_service!`
* Support `composite_query` function annotation

## 2022-11-17 (Rust 0.8.3 -- 0.8.4)

* Bug fix in TS bindings
* Pretty print numbers

## 2022-10-06 (Rust 0.8.2)

* Downgrade `serde_dhall` for license issue.

## 2022-10-04 (Rust 0.8.1)

* Fix: missing impl serde traits for `Principal`

## 2022-09-27 (Rust 0.8.0)

* Move `Principal` into this crate, no more re-export `ic-types`

## 2022-09-22 (Rust 0.7.17)

* Bump `ic-types` to `0.5` (fixing `lookup_path` for hash trees)

## 2022-08-09 (Rust 0.7.16)

* Implement `CandidType` for `Rc` and `Arc`
* Fix TS binding for TypedArray
* Fix float tokenizer
* Derive `Serialize` for `Int` and `Nat`

## 2022-07-13

### Rust (0.7.15)

* Fix parser: underscore for hexnum; semicolon at the EOF
* Fix semicolon in Rust binding
* Derive `Copy`, `Eq`, `Default` for `Reserved`
* Bump `ic-types` to `0.4`

### Candid UI

* Fetch did file from canister metadata
* Deprecate `localhost/_/candid` endpoint
* Fetch name section from metadata (instrumented code)
* Bug fix for encoding `vec nat8` types
* Disable profiler for query methods

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
