//! Nothing: this package exists for its tests. `tests/vectors.rs` reads
//! `conformance/vectors/` once, strictly, and asks every crate in this workspace the
//! vectors it can answer. `tests/differential.rs` holds `candid_binary` to the Lean
//! model's exact answers on random messages.
