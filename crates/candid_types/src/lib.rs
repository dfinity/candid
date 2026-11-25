//! Candid's type language, represented flatly, and subtyping
//! (`lean/Spec/Types.md`, Sections 3 and 5).
//!
//! A transcription of `lean/Candid/Types.lean`, `Hash.lean` and `Subtype.lean`; the
//! identifiers are shared with them, so the two read alike.
//!
//! **Nothing here is recursive except the table.** A table entry is a [`Composite`]; its
//! children are [`Slot`]s; and a slot is a primitive or a [`TypeRef`] -- never an inline
//! composite. That is the binary format's own shape (`lean/Spec/Binary.md`, Section 5.1),
//! and it is what bounds every recursion over types: the type graph is the table.
//!
//! A table is built or parsed as a [`RawTypeTable`] and checked once, by
//! [`RawTypeTable::check`], into a [`TypeTable`]: from then on every reference in it
//! resolves. A slot handed in beside a table is checked on its own, into a [`Root`].
//! [`is_subtype`] compares two roots, each in its own table.
//!
//! No global state, no serde, no binary format. `no_std`.

#![no_std]

extern crate alloc;

mod composite;
mod hash;
mod slot;
mod subtype;
mod table;

pub use composite::{Annotation, Composite};
pub use hash::{FieldId, hash_field_name};
pub use slot::{ParsePrimitiveError, Primitive, Slot, TypeRef};
pub use subtype::{is_subtype, is_subtype_within};
pub use table::{Malformation, MalformedTable, RawTypeTable, Root, TypeTable};
