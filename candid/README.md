# Candid library in Rust

## Code structure

- `src/types`, provides Candid type conversion and serialization.
  * trait `CandidType`, converts a Rust type to Candid type `types::Type`. The implementation for user-defined data types can be derived from `candid_derive` crate.
  * trait `Serializer`, serializes a Rust value to Candid binary format; we do not use serde for serialization because serde is not designed to work with types, especially variant types.
- `src/parser`, provides parser for Candid type and value.
  * `str.parse::<IDLProg>()` parses the Candid signature file to Candid AST.
  * `str.parse::<IDLArgs>()` parses the Candid value in text format to a struct `IDLArg` that can be used for serialization and deserialization between Candid and an abstract value `IDLValue` in Rust.
- `src/`, provides serialization and deserialization between Candid and native Rust values.
