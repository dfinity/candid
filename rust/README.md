# Candid

![](https://github.com/dfinity/candid/workflows/Rust/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/candid.svg)](https://crates.io/crates/candid)
[![Documentation](https://docs.rs/candid/badge.svg)](https://docs.rs/candid)

This directory hosts the following crates:

- `candid`, a serialization/deserialization library for Candid. You can seamlessly convert between Rust values and Candid in both binary and text format. If you are developing canisters on the Internet Computer, this should be the only crate you need.
- `candid_parser`, parser and binding generator for Candid. You will need this crate if you are developing tools for processing Candid data and types.
- `ic_principal`, Principal types used on the Internet Computer. The `candid` crate exports the types defined here. 
- `candid_derive`, an internal crate to convert Rust data types to Candid types. This crate should be considered as an implementation detail, and not be used directly, only via the `candid` crate.

