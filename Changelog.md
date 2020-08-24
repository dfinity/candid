
# Changelog

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

* Publish `didc` and `candiff` binary as asserts in the release
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
