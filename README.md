# Candid

![](https://github.com/dfinity/candid/workflows/Rust/badge.svg)

[Candid](IDL.ms) is an interface description language (IDL) for interacting with _canisters_ (also known as _services_ or _actors_) running on the Internet Computer.

There are three common ways that you might find yourself needing to work with Candid in Rust.
 - As a typed Rust data strcuture. When you write canisters or frontend in Rust, you want to have a seamless way of converting data between Rust and Candid.
 - As an untyped Candid value. When you write generic tools for the Internet Computer without knowing the type of the Candid data.
 - As text data. When you get the data from CLI or read from a file, you can use the provided parser to send/receive messages.

Candid crate provides efficient, flexible and safe ways of converting data between each of these representations.

This respository hosts the following crates:

- `candid`, a serialization/deserialization library for Candid.
- `candid_derive`, an internal crate to convert Rust data types to Candid types. This crate should be considered as an implementation detail, and not be used directly, only via the `candid` crate.

# Contribution

The Internet Computer is a new technology stack that is unhackable, fast, scales to billions of users around the world, and supports a new kind of autonomous software that promises to reverse Big Tech’s monopolization of the internet. It allows developers to take on the monopolization of the internet, and return the internet back to its free and open roots. We're committed to connecting those who believe the same through our events, content, and discussions.

See our [CONTRIBUTING](.github/CONTRIBUTING.md) and [CODE OF CONDUCT](.github/CODE_OF_CONDUCT.md) to get started.
