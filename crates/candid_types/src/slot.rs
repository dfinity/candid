//! Primitives, references and slots. Mirrors `lean/Candid/Types.lean`.

use core::fmt;

/// An index into a [`TypeTable`](crate::TypeTable) or [`RawTypeTable`](crate::RawTypeTable).
///
/// Lean's is a `Nat`. A `usize` loses nothing, since a table cannot hold more entries
/// than there are addresses.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeRef(usize);

impl TypeRef {
    /// The reference to the entry at `index`.
    pub const fn new(index: usize) -> Self {
        TypeRef(index)
    }

    /// The index of the entry this refers to.
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Debug for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeRef({})", self.0)
    }
}

impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A primitive type (`lean/Spec/Types.md`, Section 3.1) -- which includes `principal`.
/// The reference types, `func` and `service`, are [`Composite`](crate::Composite)s.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[allow(missing_docs)] // Each variant is the primitive of the same name.
pub enum Primitive {
    Null,
    Bool,
    Nat,
    Int,
    Nat8,
    Nat16,
    Nat32,
    Nat64,
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
    Text,
    Reserved,
    Empty,
    Principal,
}

impl Primitive {
    /// Every primitive, in declaration order.
    pub const ALL: [Primitive; 18] = [
        Primitive::Null,
        Primitive::Bool,
        Primitive::Nat,
        Primitive::Int,
        Primitive::Nat8,
        Primitive::Nat16,
        Primitive::Nat32,
        Primitive::Nat64,
        Primitive::Int8,
        Primitive::Int16,
        Primitive::Int32,
        Primitive::Int64,
        Primitive::Float32,
        Primitive::Float64,
        Primitive::Text,
        Primitive::Reserved,
        Primitive::Empty,
        Primitive::Principal,
    ];

    /// The keyword that names it in Candid syntax.
    pub const fn name(self) -> &'static str {
        match self {
            Primitive::Null => "null",
            Primitive::Bool => "bool",
            Primitive::Nat => "nat",
            Primitive::Int => "int",
            Primitive::Nat8 => "nat8",
            Primitive::Nat16 => "nat16",
            Primitive::Nat32 => "nat32",
            Primitive::Nat64 => "nat64",
            Primitive::Int8 => "int8",
            Primitive::Int16 => "int16",
            Primitive::Int32 => "int32",
            Primitive::Int64 => "int64",
            Primitive::Float32 => "float32",
            Primitive::Float64 => "float64",
            Primitive::Text => "text",
            Primitive::Reserved => "reserved",
            Primitive::Empty => "empty",
            Primitive::Principal => "principal",
        }
    }

    /// The primitive a keyword names, if it names one.
    pub fn from_name(name: &str) -> Option<Primitive> {
        Primitive::ALL.into_iter().find(|p| p.name() == name)
    }
}

impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A type reference, as the binary format writes it (`lean/Spec/Binary.md`, Section 5.1):
/// a primitive, or a reference into the accompanying table.
///
/// This is a leaf. Composites live in the table and only in the table, so the whole
/// type graph is the table.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Slot {
    /// A primitive type.
    Primitive(Primitive),
    /// The composite type at this entry of the table.
    Ref(TypeRef),
}

impl From<Primitive> for Slot {
    fn from(p: Primitive) -> Self {
        Slot::Primitive(p)
    }
}

impl From<TypeRef> for Slot {
    fn from(r: TypeRef) -> Self {
        Slot::Ref(r)
    }
}

/// Abbreviations for the primitives, so examples read like Candid rather than like an
/// AST.
#[allow(missing_docs)] // Each is the primitive of the same name.
impl Slot {
    pub const NULL: Slot = Slot::Primitive(Primitive::Null);
    pub const BOOL: Slot = Slot::Primitive(Primitive::Bool);
    pub const NAT: Slot = Slot::Primitive(Primitive::Nat);
    pub const INT: Slot = Slot::Primitive(Primitive::Int);
    pub const NAT8: Slot = Slot::Primitive(Primitive::Nat8);
    pub const NAT16: Slot = Slot::Primitive(Primitive::Nat16);
    pub const NAT32: Slot = Slot::Primitive(Primitive::Nat32);
    pub const NAT64: Slot = Slot::Primitive(Primitive::Nat64);
    pub const INT8: Slot = Slot::Primitive(Primitive::Int8);
    pub const INT16: Slot = Slot::Primitive(Primitive::Int16);
    pub const INT32: Slot = Slot::Primitive(Primitive::Int32);
    pub const INT64: Slot = Slot::Primitive(Primitive::Int64);
    pub const FLOAT32: Slot = Slot::Primitive(Primitive::Float32);
    pub const FLOAT64: Slot = Slot::Primitive(Primitive::Float64);
    pub const TEXT: Slot = Slot::Primitive(Primitive::Text);
    pub const RESERVED: Slot = Slot::Primitive(Primitive::Reserved);
    pub const EMPTY: Slot = Slot::Primitive(Primitive::Empty);
    pub const PRINCIPAL: Slot = Slot::Primitive(Primitive::Principal);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_round_trip() {
        for p in Primitive::ALL {
            assert_eq!(Primitive::from_name(p.name()), Some(p));
        }
        assert_eq!(Primitive::from_name("vec"), None);
    }
}
