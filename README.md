# Candid

![](https://github.com/dfinity/candid/workflows/Rust/badge.svg)


Candid is an interface description language (IDL) for interacting with _canisters_ (also known as _services_ or _actors_) running on the Internet Computer. It provides a language-independent description of canister interfaces and
the data they exchange, with type safety and extensibility.

## Documentation

* The [spec](spec/) directory contains Candid specifications, including the [Candid language specification](spec/Candid.md) and a soundness proof.
* The [official manual](https://sdk.dfinity.org/docs/candid-guide/candid-intro.html) is hosted by dfinity; see [./docs](docs/) for the source code.

## Implementations

Candid supports several different programming languages.
This repository contains some of the implementations developed by DFINITY.

* [Rust](rust/): A serialization library based on Serde, and a compiler for generating bindings for other languages.
* [Motoko](https://github.com/dfinity/motoko): Compiler support for importing/export Candid files. Also see the [Motoko-Candid type mapping specificatoin](https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md).
* [JavaScript](https://github.com/dfinity/agent-js/tree/main/packages/candid): We provide a library for serialization of native JavaScript values, and a visitor class for extending Candid for building generic tools such as UI and random testing.

A list of community maintained Candid libraries:

* [Haskell](https://github.com/nomeata/haskell-candid)
* [Elm](https://github.com/chenyan2002/ic-elm/)
* [Kotlin](https://github.com/seniorjoinu/candid-kt)
* [AssemblyScript](https://github.com/rckprtr/cdk-as/tree/master/packages/cdk/assembly/candid)
* [Java](https://github.com/ic4j/ic4j-candid)

## Tools

* [didc](tools/didc): Candid CLI. Download [prebuilt binary](https://github.com/dfinity/candid/releases).
* [candiff](tools/candiff): Diff Candid values structurally
* [ui](tools/ui): Candid UI canister. See deployed [canister](https://a4gq6-oaaaa-aaaab-qaa4q-cai.raw.ic0.app/) on the IC
* [ic-repl](https://github.com/chenyan2002/ic-repl): A REPL environment to communicate with canisters using Candid

## Tests

We provide a [test suite](test/) to check Candid implementations for compliance.

## Release

To make a release in this repo:

* Update `Changelog.md` and merge the PR into master.
* `git tag 2020-04-01 -m "2020-04-01"`
* `git push origin 2020-04-01`

The tag is always today's date. As the repo contains several targets, it is hard to give a version to the tag.

## Contribution

See our [CONTRIBUTING](.github/CONTRIBUTING.md) and [CODE OF CONDUCT](.github/CODE_OF_CONDUCT.md) to get started.
