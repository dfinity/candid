# Candid

![](https://github.com/dfinity/candid/workflows/Rust/badge.svg)


[Candid](spec/Candid.md) is an interface description language (IDL) for interacting with _canisters_ (also known as _services_ or _actors_) running on the Internet Computer. It provides a language-independent description of canister interfaces and
the data they exchange, with type safety and extensibility.

## Specifications

The [spec](spec/) directory contains Candid specifications, including the language specification and soundness proof.

## Implementations

Candid supports several different programming languages. 
This repository contains some of the implementations developed by DFINITY.

* [Rust](rust/): A serialization library based on Serde, and a compiler for generating bindings for other languages.
* Motoko: Compiler support for importing/export Candid files.
* JavaScript: As part of the [JavaScript User Library](https://www.npmjs.com/package/@dfinity/agent), we provide a library for serialization of native JavaScript values, and a visitor class for extending Candid for building generic tools such as UI and random testing.

A list of community maintained Candid libraries:

* [Haskell](https://github.com/nomeata/haskell-candid)
* [Elm](https://github.com/chenyan2002/ic-elm/)
* [Kotlin](https://github.com/seniorjoinu/candid-kt)

## Tools

Coming soon

## Contribution

The Internet Computer is a new technology stack that is unhackable, fast, scales to billions of users around the world, and supports a new kind of autonomous software that promises to reverse Big Tech’s monopolization of the internet. It allows developers to take on the monopolization of the internet, and return the internet back to its free and open roots. We're committed to connecting those who believe the same through our events, content, and discussions.

See our [CONTRIBUTING](.github/CONTRIBUTING.md) and [CODE OF CONDUCT](.github/CODE_OF_CONDUCT.md) to get started.
