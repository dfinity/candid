//! Composites: what a table entry is. Mirrors `lean/Candid/Types.lean`.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::hash::{FieldId, hash_field_name};
use crate::slot::Slot;

/// A function annotation (`lean/Spec/Types.md`, Section 3.2). Annotations are part of a
/// function's type, not decoration.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Annotation {
    /// `query`
    Query,
    /// `oneway`
    Oneway,
    /// `composite_query`
    CompositeQuery,
}

impl Annotation {
    /// A mode says how a function is called: an update call if it has none. A function
    /// has at most one (`lean/Spec/Types.md`, Section 3.2). Every annotation defined so far
    /// is a mode; one added later need not be.
    pub const fn is_mode(self) -> bool {
        match self {
            Annotation::Query | Annotation::Oneway | Annotation::CompositeQuery => true,
        }
    }

    /// The keyword that names it in Candid syntax.
    pub const fn name(self) -> &'static str {
        match self {
            Annotation::Query => "query",
            Annotation::Oneway => "oneway",
            Annotation::CompositeQuery => "composite_query",
        }
    }
}

impl fmt::Display for Annotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A composite type: what a table entry is (`lean/Spec/Binary.md`, Section 5.2).
///
/// Not a recursive type. Its children are [`Slot`]s, so a composite is one flat node.
///
/// `==` is structural: two entries are equal when they are written alike, which says
/// nothing about whether the types they denote are equal -- that depends on the tables
/// their references index into.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Composite {
    /// `opt t`
    Opt(Slot),
    /// `vec t`
    Vec(Slot),
    /// `record { ... }`, its fields in no particular order.
    Record(Vec<(FieldId, Slot)>),
    /// `variant { ... }`, its alternatives in no particular order.
    Variant(Vec<(FieldId, Slot)>),
    /// `func (parameters) -> (results) annotations`
    Func {
        /// The parameter types.
        parameters: Vec<Slot>,
        /// The result types.
        results: Vec<Slot>,
        /// The annotations, in no particular order.
        annotations: Vec<Annotation>,
    },
    /// `service { ... }`: each method's name and type, in no particular order.
    Service(Vec<(String, Slot)>),
    /// A *future type* (`lean/Spec/Types.md`, Section 3.2; `lean/Spec/Binary.md`,
    /// Section 5.2): an opcode below `-24`, which this version of Candid does not
    /// define, and the bytes that came with it. Only a decoder makes one.
    Future {
        /// The opcode, below `-24`.
        ///
        /// Lean's is unbounded. An `i64` is this implementation's choice, since Candid
        /// will never define that many types; a decoder rejects an opcode below `-2^63`
        /// as a resource limit (`lean/Spec/Binary.md`, Section 9).
        opcode: i64,
        /// The bytes that followed it.
        data: Vec<u8>,
    },
}

impl Composite {
    /// A record from named fields, hashing the names.
    pub fn record_of<'a>(fields: impl IntoIterator<Item = (&'a str, Slot)>) -> Composite {
        Composite::Record(hashed(fields))
    }

    /// A variant from named alternatives, hashing the names.
    pub fn variant_of<'a>(alts: impl IntoIterator<Item = (&'a str, Slot)>) -> Composite {
        Composite::Variant(hashed(alts))
    }

    /// The slots a composite holds, in no particular order: what has to resolve.
    pub fn slots(&self) -> impl Iterator<Item = Slot> + '_ {
        // Each composite fills at most two of these; the rest stay empty.
        type Parts<'a> = (
            &'a [Slot],
            &'a [Slot],
            &'a [(FieldId, Slot)],
            &'a [(String, Slot)],
        );
        let (front, back, labelled, methods): Parts<'_> = match self {
            Composite::Opt(t) | Composite::Vec(t) => (core::slice::from_ref(t), &[], &[], &[]),
            Composite::Record(fs) | Composite::Variant(fs) => (&[], &[], fs, &[]),
            Composite::Func {
                parameters,
                results,
                ..
            } => (parameters, results, &[], &[]),
            Composite::Service(ms) => (&[], &[], &[], ms),
            Composite::Future { .. } => (&[], &[], &[], &[]),
        };
        front
            .iter()
            .chain(back)
            .copied()
            .chain(labelled.iter().map(|(_, s)| *s))
            .chain(methods.iter().map(|(_, s)| *s))
    }
}

fn hashed<'a>(named: impl IntoIterator<Item = (&'a str, Slot)>) -> Vec<(FieldId, Slot)> {
    named
        .into_iter()
        .map(|(name, t)| (hash_field_name(name), t))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slot::TypeRef;
    use alloc::vec;

    #[test]
    fn slots_of_each_composite() {
        let r = Slot::Ref(TypeRef::new(0));
        let func = Composite::Func {
            parameters: vec![Slot::NAT, r],
            results: vec![Slot::TEXT],
            annotations: vec![Annotation::Query],
        };
        assert_eq!(func.slots().collect::<Vec<_>>(), [Slot::NAT, r, Slot::TEXT]);
        assert_eq!(Composite::Opt(r).slots().collect::<Vec<_>>(), [r]);
        let record = Composite::record_of([("a", Slot::NAT), ("b", r)]);
        assert_eq!(record.slots().collect::<Vec<_>>(), [Slot::NAT, r]);
        let service = Composite::Service(vec![("m".into(), r)]);
        assert_eq!(service.slots().collect::<Vec<_>>(), [r]);
        let future = Composite::Future {
            opcode: -25,
            data: vec![1, 2],
        };
        assert_eq!(future.slots().count(), 0);
    }
}
