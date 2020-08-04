# Candid

![](https://github.com/dfinity/candid/workflows/Rust/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/candid.svg)](https://crates.io/crates/candid)
[![Documentation](https://docs.rs/candid/badge.svg)](https://docs.rs/candid)

This directory hosts the following crates:

- `candid`, a serialization/deserialization library for Candid. You can seamlessly convert between Rust values and Candid in both binary and text format.
- `candid_derive`, an internal crate to convert Rust data types to Candid types. This crate should be considered as an implementation detail, and not be used directly, only via the `candid` crate.
