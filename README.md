# Candid

![](https://github.com/dfinity/candid/workflows/Rust/badge.svg)

[Candid](IDL.md) is an interface description language (IDL) for specifying the signature of an actor. It is used to interact with all canisters running on the Internet Computer.

This respository hosts the following crates:

- `candid`, providing the parser for Candid types `candid::IDLProg` and values `candid::IDLArgs`; integrating Candid value with `serde`, allowing to serialize and deserialize Rust data structures to and from Candid.
- `candid_derive`, an internal crate similar to `serde_derive` to convert Rust data types to Candid types. This crate should be considered as an implementation detail, and not be used directly, only via the `candid` crate.

# Contribution

The Internet Computer is a new technology stack that is unhackable, fast, scales to billions of users around the world, and supports a new kind of autonomous software that promises to reverse Big Tech’s monopolization of the internet. It allows developers to take on the monopolization of the internet, and return the internet back to its free and open roots. We're committed to connecting those who believe the same through our events, content, and discussions.

See our [CONTRIBUTING](.github/CONTRIBUTING.md) and [CODE OF CONDUCT](.github/CODE_OF_CONDUCT.md) to get started.
