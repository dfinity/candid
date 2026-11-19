//! The type table, its well-formedness check, and roots. Mirrors `lean/Candid/Types.lean`.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::composite::{Annotation, Composite};
use crate::hash::FieldId;
use crate::slot::{Slot, TypeRef};

/// A type table as it is parsed or built: [`TypeRef`] -> [`Composite`], not yet checked.
///
/// Nothing but [`RawTypeTable::check`] should consume one; see [`TypeTable`].
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct RawTypeTable {
    entries: Vec<Composite>,
}

impl RawTypeTable {
    /// The empty table, for types that contain no references.
    pub const fn new() -> Self {
        RawTypeTable {
            entries: Vec::new(),
        }
    }

    /// The table with these entries, the first at index 0.
    pub fn from_entries(entries: Vec<Composite>) -> Self {
        RawTypeTable { entries }
    }

    /// How many entries it has.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether it has no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The entry a reference names, if there is one.
    pub fn lookup(&self, r: TypeRef) -> Option<&Composite> {
        self.entries.get(r.index())
    }

    /// The entries, the first at index 0.
    pub fn entries(&self) -> &[Composite] {
        &self.entries
    }

    /// Add an entry, and return the slot that names it.
    ///
    /// This appends: it does not look for an equal entry to share. Building a table does
    /// not check it either.
    pub fn intern(&mut self, c: Composite) -> Slot {
        let r = TypeRef::new(self.entries.len());
        self.entries.push(c);
        Slot::Ref(r)
    }

    /// Check the table once, so that nothing downstream has to: every reference resolves,
    /// no record, variant or service repeats a label, a function's annotations are
    /// allowed, and every method's type is a function.
    ///
    /// On failure, names the first malformed entry and one thing wrong with it.
    pub fn check(self) -> Result<TypeTable, MalformedTable> {
        for (index, entry) in self.entries.iter().enumerate() {
            if let Err(malformation) = self.check_entry(entry) {
                return Err(MalformedTable {
                    entry: TypeRef::new(index),
                    malformation,
                });
            }
        }
        Ok(TypeTable { raw: self })
    }

    /// `Composite.wellFormed` and `RawTypeTable.methodsDenoteFuncs`, in that order.
    fn check_entry(&self, entry: &Composite) -> Result<(), Malformation> {
        labels_ok(entry)?;
        annotations_ok(entry)?;
        arity_ok(entry)?;
        opcode_ok(entry)?;
        // `Slot.wellFormed`: a primitive always is.
        let dangling = entry.slots().find_map(|s| match s {
            Slot::Ref(r) if r.index() >= self.len() => Some(r),
            _ => None,
        });
        if let Some(r) = dangling {
            return Err(Malformation::DanglingReference(r));
        }
        self.methods_denote_funcs(entry)
    }

    /// Every method has a function type (`lean/Spec/Types.md`, Section 3.5, rule 2). The
    /// only rule here that looks through the table.
    fn methods_denote_funcs(&self, entry: &Composite) -> Result<(), Malformation> {
        let Composite::Service(methods) = entry else {
            return Ok(());
        };
        for (name, slot) in methods {
            let is_func = match slot {
                Slot::Ref(r) => matches!(self.lookup(*r), Some(Composite::Func { .. })),
                Slot::Primitive(_) => false,
            };
            if !is_func {
                return Err(Malformation::MethodNotFunction(name.clone()));
            }
        }
        Ok(())
    }
}

impl From<Vec<Composite>> for RawTypeTable {
    fn from(entries: Vec<Composite>) -> Self {
        RawTypeTable::from_entries(entries)
    }
}

/// Labels must not repeat: the spec makes a hash collision between field names in one
/// record *disallowed* rather than resolved, so duplicate ids make a type malformed
/// rather than ambiguous.
fn labels_ok(entry: &Composite) -> Result<(), Malformation> {
    match entry {
        Composite::Record(fs) | Composite::Variant(fs) => {
            match first_duplicate(fs.iter().map(|(id, _)| *id)) {
                Some(id) => Err(Malformation::DuplicateField(id)),
                None => Ok(()),
            }
        }
        Composite::Service(ms) => match first_duplicate(ms.iter().map(|(name, _)| name)) {
            Some(name) => Err(Malformation::DuplicateMethod(name.clone())),
            None => Ok(()),
        },
        Composite::Opt(_)
        | Composite::Vec(_)
        | Composite::Func { .. }
        | Composite::Future { .. } => Ok(()),
    }
}

/// No annotation repeats, a function has at most one mode, and a `oneway` function has no
/// results (`lean/Spec/Types.md`, Section 3.5, rules 3 and 4).
fn annotations_ok(entry: &Composite) -> Result<(), Malformation> {
    let Composite::Func {
        results,
        annotations,
        ..
    } = entry
    else {
        return Ok(());
    };
    if let Some(a) = first_duplicate(annotations.iter().copied()) {
        return Err(Malformation::RepeatedAnnotation(a));
    }
    if annotations.iter().filter(|a| a.is_mode()).count() > 1 {
        return Err(Malformation::MultipleModes);
    }
    if annotations.contains(&Annotation::Oneway) && !results.is_empty() {
        return Err(Malformation::OnewayWithResults);
    }
    Ok(())
}

/// Parameter and result lists are shorter than 2^32 (`lean/Spec/Types.md`, Section 3.5,
/// rule 5).
fn arity_ok(entry: &Composite) -> Result<(), Malformation> {
    let Composite::Func {
        parameters,
        results,
        ..
    } = entry
    else {
        return Ok(());
    };
    if u32::try_from(parameters.len()).is_err() {
        return Err(Malformation::TooManyParameters);
    }
    if u32::try_from(results.len()).is_err() {
        return Err(Malformation::TooManyResults);
    }
    Ok(())
}

/// A future type's opcode is one the spec leaves to the future: below `-24`.
fn opcode_ok(entry: &Composite) -> Result<(), Malformation> {
    match entry {
        Composite::Future { opcode, .. } if *opcode >= -24 => {
            Err(Malformation::NotFutureOpcode(*opcode))
        }
        _ => Ok(()),
    }
}

/// Some item that occurs more than once, if any does.
///
/// Lean's `noDups` is quadratic, which is fine for a model and not for a table that
/// arrived on the wire with a hundred thousand fields in one record. Sorting gives the
/// same answer.
fn first_duplicate<T: Ord>(items: impl Iterator<Item = T>) -> Option<T> {
    let mut items: Vec<T> = items.collect();
    items.sort_unstable();
    let mut items = items.into_iter();
    let mut prev = items.next()?;
    for item in items {
        if item == prev {
            return Some(item);
        }
        prev = item;
    }
    None
}

/// Why [`RawTypeTable::check`] rejected a table: an entry, and one thing wrong with it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MalformedTable {
    entry: TypeRef,
    malformation: Malformation,
}

impl MalformedTable {
    /// The malformed entry.
    pub fn entry(&self) -> TypeRef {
        self.entry
    }

    /// What is wrong with it.
    pub fn malformation(&self) -> &Malformation {
        &self.malformation
    }
}

impl fmt::Display for MalformedTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "type table entry {}: {}", self.entry, self.malformation)
    }
}

impl core::error::Error for MalformedTable {}

/// One way a table entry can be malformed.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Malformation {
    /// A reference past the end of the table.
    DanglingReference(TypeRef),
    /// A record or variant with two fields of this id.
    DuplicateField(FieldId),
    /// A service with two methods of this name.
    DuplicateMethod(String),
    /// A function with this annotation twice.
    RepeatedAnnotation(Annotation),
    /// A function with more than one mode.
    MultipleModes,
    /// A `oneway` function with results.
    OnewayWithResults,
    /// A function with 2^32 parameters or more.
    TooManyParameters,
    /// A function with 2^32 results or more.
    TooManyResults,
    /// A future type whose opcode is not below `-24`.
    NotFutureOpcode(i64),
    /// A service method, of this name, whose type is not a function.
    MethodNotFunction(String),
}

impl fmt::Display for Malformation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Malformation::DanglingReference(r) => write!(f, "reference {r} does not resolve"),
            Malformation::DuplicateField(id) => write!(f, "field id {id} occurs twice"),
            Malformation::DuplicateMethod(name) => write!(f, "method {name:?} occurs twice"),
            Malformation::RepeatedAnnotation(a) => write!(f, "annotation {a} occurs twice"),
            Malformation::MultipleModes => f.write_str("function has more than one mode"),
            Malformation::OnewayWithResults => f.write_str("oneway function has results"),
            Malformation::TooManyParameters => f.write_str("function has 2^32 parameters or more"),
            Malformation::TooManyResults => f.write_str("function has 2^32 results or more"),
            Malformation::NotFutureOpcode(op) => {
                write!(f, "opcode {op} is not a future type's")
            }
            Malformation::MethodNotFunction(name) => {
                write!(f, "method {name:?} is not a function")
            }
        }
    }
}

/// A well-formed type table: every reference in it resolves.
///
/// Well-formedness is a prerequisite of everything downstream -- subtyping, decoding,
/// encoding -- so it is a property of the type, not a check each operation repeats on
/// the parts it happens to reach. [`RawTypeTable::check`] is the only way to get one.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TypeTable {
    raw: RawTypeTable,
}

impl TypeTable {
    /// How many entries it has.
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    /// Whether it has no entries.
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// The entry a reference names, if there is one.
    pub fn lookup(&self, r: TypeRef) -> Option<&Composite> {
        self.raw.lookup(r)
    }

    /// The entries, the first at index 0.
    pub fn entries(&self) -> &[Composite] {
        self.raw.entries()
    }

    /// The table, unchecked again.
    pub fn as_raw(&self) -> &RawTypeTable {
        &self.raw
    }

    /// The table, unchecked again.
    pub fn into_raw(self) -> RawTypeTable {
        self.raw
    }

    /// Is this slot a type in this table at all? A primitive always is; a reference is
    /// one exactly when it resolves.
    pub fn resolves(&self, s: Slot) -> bool {
        match s {
            Slot::Primitive(_) => true,
            Slot::Ref(r) => r.index() < self.len(),
        }
    }

    /// The slot as a type in this table, if it resolves.
    ///
    /// A well-formed table says nothing about a slot handed in beside it, so a root is
    /// checked on its own -- one bounds check.
    pub fn root(&self, s: Slot) -> Option<Root<'_>> {
        self.resolves(s).then_some(Root {
            table: self,
            slot: s,
        })
    }
}

/// A slot known to resolve in its table: a type.
///
/// In Lean the table is in the root's type (`t.Root`), so a slot of one table cannot be
/// passed where a slot of another is expected. Rust has no dependent types; this is a
/// view borrowing its table, which keeps the two together instead. One table has many
/// roots -- a message's arguments, a service's methods.
#[derive(Clone, Copy, Debug)]
pub struct Root<'a> {
    table: &'a TypeTable,
    slot: Slot,
}

impl<'a> Root<'a> {
    /// The table it resolves in.
    pub fn table(&self) -> &'a TypeTable {
        self.table
    }

    /// The slot.
    pub fn slot(&self) -> Slot {
        self.slot
    }

    /// The entry it names, or `None` for a primitive.
    pub fn composite(&self) -> Option<&'a Composite> {
        match self.slot {
            Slot::Primitive(_) => None,
            Slot::Ref(r) => self.table.lookup(r),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn func(parameters: Vec<Slot>, results: Vec<Slot>, annotations: Vec<Annotation>) -> Composite {
        Composite::Func {
            parameters,
            results,
            annotations,
        }
    }

    fn rejected(entries: Vec<Composite>) -> Malformation {
        RawTypeTable::from(entries)
            .check()
            .expect_err("table should be malformed")
            .malformation
    }

    #[test]
    fn recursion_is_well_formed() {
        let mut raw = RawTypeTable::new();
        let list = raw.intern(Composite::Opt(Slot::Ref(TypeRef::new(1))));
        raw.intern(Composite::record_of([("head", Slot::NAT), ("tail", list)]));
        let table = raw.check().unwrap();
        let root = table.root(list).unwrap();
        assert_eq!(root.composite(), table.lookup(TypeRef::new(0)));
    }

    #[test]
    fn dangling_reference() {
        let r = TypeRef::new(1);
        assert_eq!(
            rejected(vec![Composite::Vec(Slot::Ref(r))]),
            Malformation::DanglingReference(r)
        );
    }

    #[test]
    fn root_is_checked_on_its_own() {
        let table = RawTypeTable::new().check().unwrap();
        assert!(table.root(Slot::PRINCIPAL).is_some());
        assert!(table.root(Slot::Ref(TypeRef::new(0))).is_none());
    }

    #[test]
    fn duplicate_labels() {
        let id = FieldId::new(7);
        assert_eq!(
            rejected(vec![Composite::Variant(vec![
                (id, Slot::NAT),
                (id, Slot::TEXT)
            ])]),
            Malformation::DuplicateField(id)
        );
        let f = Slot::Ref(TypeRef::new(0));
        assert_eq!(
            rejected(vec![
                func(vec![], vec![], vec![]),
                Composite::Service(vec![("m".into(), f), ("m".into(), f)]),
            ]),
            Malformation::DuplicateMethod("m".into())
        );
    }

    #[test]
    fn annotations() {
        use Annotation::*;
        assert_eq!(
            rejected(vec![func(vec![], vec![], vec![Query, Query])]),
            Malformation::RepeatedAnnotation(Query)
        );
        assert_eq!(
            rejected(vec![func(vec![], vec![], vec![Query, CompositeQuery])]),
            Malformation::MultipleModes
        );
        assert_eq!(
            rejected(vec![func(vec![], vec![Slot::NAT], vec![Oneway])]),
            Malformation::OnewayWithResults
        );
        assert!(
            RawTypeTable::from(vec![func(vec![], vec![Slot::NAT], vec![Query])])
                .check()
                .is_ok()
        );
    }

    #[test]
    fn methods_denote_functions() {
        assert_eq!(
            rejected(vec![Composite::Service(vec![("m".into(), Slot::NAT)])]),
            Malformation::MethodNotFunction("m".into())
        );
        assert_eq!(
            rejected(vec![
                Composite::Vec(Slot::NAT),
                Composite::Service(vec![("m".into(), Slot::Ref(TypeRef::new(0)))]),
            ]),
            Malformation::MethodNotFunction("m".into())
        );
    }

    #[test]
    fn future_opcodes() {
        let future = |opcode| Composite::Future {
            opcode,
            data: vec![],
        };
        assert!(RawTypeTable::from(vec![future(-25)]).check().is_ok());
        assert_eq!(
            rejected(vec![future(-24)]),
            Malformation::NotFutureOpcode(-24)
        );
    }

    #[test]
    fn the_first_malformed_entry_is_named() {
        let err = RawTypeTable::from(vec![
            Composite::Opt(Slot::NAT),
            Composite::Vec(Slot::Ref(TypeRef::new(9))),
        ])
        .check()
        .unwrap_err();
        assert_eq!(err.entry(), TypeRef::new(1));
    }
}
