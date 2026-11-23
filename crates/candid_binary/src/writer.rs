//! Writing values: `M` of `lean/Spec/Binary.md`, Section 6, and `TypeTable.encodeValue`
//! of `lean/Candid/Wire.lean`.
//!
//! A [`ValueWriter`] is one value of a message, at its type. Whoever holds it says which
//! value it is, by calling the method for its shape; the writer checks that a value of
//! that shape has the type, which is `TypeTable.hasType` of `lean/Candid/Value.lean`, and
//! writes its bytes. A record, vector or `opt` hands out a writer for each value inside
//! it, so a value is written from the outside in, with no value type in between.
//!
//! **Every value is finished.** A writer that is dropped, or whose method fails, leaves its
//! value unwritten and the message without it. Each writer knows how many values were
//! owed when it was made, and each value written pays one; so the writer of the enclosing
//! value -- and the [`Encoder`](crate::Encoder) at the top -- sees an unpaid one at its
//! next call, and refuses with [`EncodeError::Unfinished`]. A message is finished only if
//! every value in it was.

use alloc::vec::Vec;

use candid_types::{Composite, FieldId, Primitive, Slot, TypeTable};

use crate::error::EncodeError;
use crate::leb128;

/// The most bytes a principal has (`lean/Spec/Types.md`, Section 3.1).
const MAX_PRINCIPAL_LENGTH: usize = 29;

/// How a value is written into a message.
///
/// A type implements it by calling, on the writer it is given, the method for the value it
/// is: [`ValueWriter::nat`], [`ValueWriter::record`] and so on. The writer checks the value
/// against the type the message gives it.
pub trait Encode {
    /// Write this value.
    fn encode(&self, writer: ValueWriter<'_>) -> Result<(), EncodeError>;
}

impl<T: Encode + ?Sized> Encode for &T {
    fn encode(&self, writer: ValueWriter<'_>) -> Result<(), EncodeError> {
        (**self).encode(writer)
    }
}

impl<T: Encode + ?Sized> Encode for alloc::boxed::Box<T> {
    fn encode(&self, writer: ValueWriter<'_>) -> Result<(), EncodeError> {
        (**self).encode(writer)
    }
}

/// Where values are written: the bytes, and how many values are owed -- handed out as a
/// writer and not yet written.
#[derive(Clone, Debug, Default)]
pub(crate) struct Sink {
    pub(crate) out: Vec<u8>,
    pub(crate) owed: usize,
}

impl Sink {
    /// Check that every value handed out since `level` was owed has been written.
    fn settled(&self, level: usize) -> Result<(), EncodeError> {
        if self.owed == level {
            Ok(())
        } else {
            Err(EncodeError::Unfinished)
        }
    }

    /// A value has been written.
    fn paid(&mut self) -> Result<(), EncodeError> {
        self.owed = self.owed.saturating_sub(1);
        Ok(())
    }
}

/// One value of a message, at its type: call the method for the value it is.
///
/// Each method consumes the writer. A scalar's writes the value; a composite's writes what
/// comes before its parts and gives back a writer for them. A method for a value that does
/// not have the type fails with [`EncodeError::NotOfType`], and writes nothing.
#[derive(Debug)]
pub struct ValueWriter<'w> {
    sink: &'w mut Sink,
    table: &'w TypeTable,
    slot: Slot,
}

impl<'w> ValueWriter<'w> {
    /// A writer for a value at `slot`, which resolves in `table`, whose value is owed.
    pub(crate) fn new(sink: &'w mut Sink, table: &'w TypeTable, slot: Slot) -> Self {
        ValueWriter { sink, table, slot }
    }

    /// The type this value is written at.
    pub fn slot(&self) -> Slot {
        self.slot
    }

    /// The table [`ValueWriter::slot`] resolves in.
    pub fn table(&self) -> &'w TypeTable {
        self.table
    }

    fn not_of_type(&self, value: &'static str) -> EncodeError {
        EncodeError::NotOfType {
            slot: self.slot,
            value,
        }
    }

    /// The entry the type names, if it is a composite.
    fn composite(&self) -> Option<&'w Composite> {
        match self.slot {
            Slot::Ref(r) => self.table.lookup(r),
            Slot::Primitive(_) => None,
        }
    }

    /// Write a primitive value's bytes, if the type is that primitive.
    fn primitive(self, p: Primitive, bytes: &[u8]) -> Result<(), EncodeError> {
        if self.slot != Slot::Primitive(p) {
            return Err(self.not_of_type(p.name()));
        }
        self.sink.out.extend_from_slice(bytes);
        self.sink.paid()
    }

    /// `null`: the value of `null` and of `reserved`, an absent `opt`, and the value of a
    /// future type, written as one with no bytes and no references.
    pub fn null(self) -> Result<(), EncodeError> {
        let bytes: &[u8] = match (self.slot, self.composite()) {
            (Slot::Primitive(Primitive::Null | Primitive::Reserved), _) => &[],
            (_, Some(Composite::Opt(_))) => &[0],
            (_, Some(Composite::Future { .. })) => &[0, 0],
            _ => return Err(self.not_of_type("null")),
        };
        self.sink.out.extend_from_slice(bytes);
        self.sink.paid()
    }

    /// A `bool`.
    pub fn bool(self, b: bool) -> Result<(), EncodeError> {
        self.primitive(Primitive::Bool, &[u8::from(b)])
    }

    /// A `nat`, given by its base-256 digits, least significant first: any number of
    /// bytes, written in the shortest LEB128.
    pub fn nat(self, le_bytes: &[u8]) -> Result<(), EncodeError> {
        if self.slot != Slot::NAT {
            return Err(self.not_of_type("nat"));
        }
        leb128::write_unsigned_bytes(&mut self.sink.out, le_bytes);
        self.sink.paid()
    }

    /// An `int`, given in two's complement, least significant byte first: any number of
    /// bytes, the top bit of the last the sign, written in the shortest SLEB128.
    pub fn int(self, le_bytes: &[u8]) -> Result<(), EncodeError> {
        if self.slot != Slot::INT {
            return Err(self.not_of_type("int"));
        }
        leb128::write_signed_bytes(&mut self.sink.out, le_bytes);
        self.sink.paid()
    }

    /// A `nat8`.
    pub fn nat8(self, n: u8) -> Result<(), EncodeError> {
        self.primitive(Primitive::Nat8, &[n])
    }

    /// A `nat16`.
    pub fn nat16(self, n: u16) -> Result<(), EncodeError> {
        self.primitive(Primitive::Nat16, &n.to_le_bytes())
    }

    /// A `nat32`.
    pub fn nat32(self, n: u32) -> Result<(), EncodeError> {
        self.primitive(Primitive::Nat32, &n.to_le_bytes())
    }

    /// A `nat64`.
    pub fn nat64(self, n: u64) -> Result<(), EncodeError> {
        self.primitive(Primitive::Nat64, &n.to_le_bytes())
    }

    /// An `int8`.
    pub fn int8(self, i: i8) -> Result<(), EncodeError> {
        self.primitive(Primitive::Int8, &i.to_le_bytes())
    }

    /// An `int16`.
    pub fn int16(self, i: i16) -> Result<(), EncodeError> {
        self.primitive(Primitive::Int16, &i.to_le_bytes())
    }

    /// An `int32`.
    pub fn int32(self, i: i32) -> Result<(), EncodeError> {
        self.primitive(Primitive::Int32, &i.to_le_bytes())
    }

    /// An `int64`.
    pub fn int64(self, i: i64) -> Result<(), EncodeError> {
        self.primitive(Primitive::Int64, &i.to_le_bytes())
    }

    /// A `float32`, bit for bit: a NaN keeps its payload.
    pub fn float32(self, f: f32) -> Result<(), EncodeError> {
        self.primitive(Primitive::Float32, &f.to_bits().to_le_bytes())
    }

    /// A `float64`, bit for bit: a NaN keeps its payload.
    pub fn float64(self, f: f64) -> Result<(), EncodeError> {
        self.primitive(Primitive::Float64, &f.to_bits().to_le_bytes())
    }

    /// A `text`.
    pub fn text(self, s: &str) -> Result<(), EncodeError> {
        if self.slot != Slot::TEXT {
            return Err(self.not_of_type("text"));
        }
        write_bytes(&mut self.sink.out, s.as_bytes());
        self.sink.paid()
    }

    /// A `principal`, given by its bytes: at most 29 of them.
    pub fn principal(self, id: &[u8]) -> Result<(), EncodeError> {
        if self.slot != Slot::PRINCIPAL {
            return Err(self.not_of_type("principal"));
        }
        write_id(&mut self.sink.out, id)?;
        self.sink.paid()
    }

    /// An `opt` with a value: the writer for that value.
    ///
    /// The absent one is [`ValueWriter::null`].
    pub fn opt(self) -> Result<ValueWriter<'w>, EncodeError> {
        let Some(&Composite::Opt(inner)) = self.composite() else {
            return Err(self.not_of_type("opt"));
        };
        self.sink.out.push(1);
        // The value inside pays for the `opt`: it is written when that is.
        Ok(ValueWriter::new(self.sink, self.table, inner))
    }

    /// A `vec` of `len` values: the writer for them.
    pub fn vec(self, len: usize) -> Result<VecWriter<'w>, EncodeError> {
        let Some(&Composite::Vec(element)) = self.composite() else {
            return Err(self.not_of_type("vec"));
        };
        leb128::write_unsigned(&mut self.sink.out, len as u64);
        Ok(VecWriter {
            level: self.sink.owed,
            sink: self.sink,
            table: self.table,
            element,
            len,
            written: 0,
        })
    }

    /// A `vec nat8`, all at once: the bytes [`ValueWriter::vec`] and a
    /// [`ValueWriter::nat8`] for each would write. So no bytes is the empty vector, which
    /// has every vector type.
    pub fn blob(self, bytes: &[u8]) -> Result<(), EncodeError> {
        let accepted = match self.composite() {
            Some(&Composite::Vec(element)) => bytes.is_empty() || element == Slot::NAT8,
            _ => false,
        };
        if !accepted {
            return Err(self.not_of_type("blob"));
        }
        write_bytes(&mut self.sink.out, bytes);
        self.sink.paid()
    }

    /// A `record`: the writer for its fields, which come in the type's order.
    pub fn record(self) -> Result<RecordWriter<'w>, EncodeError> {
        let Some(Composite::Record(fields)) = self.composite() else {
            return Err(self.not_of_type("record"));
        };
        Ok(RecordWriter {
            level: self.sink.owed,
            sink: self.sink,
            table: self.table,
            fields,
            next: 0,
        })
    }

    /// A `variant`, at the alternative `id`: the writer for its value.
    pub fn variant(self, id: FieldId) -> Result<ValueWriter<'w>, EncodeError> {
        let Some(Composite::Variant(alternatives)) = self.composite() else {
            return Err(self.not_of_type("variant"));
        };
        // A table keeps the alternatives in ascending id, the order the index counts in.
        let Ok(index) = alternatives.binary_search_by_key(&id, |&(f, _)| f) else {
            return Err(EncodeError::NoSuchAlternative { id });
        };
        leb128::write_unsigned(&mut self.sink.out, index as u64);
        let inner = alternatives[index].1;
        Ok(ValueWriter::new(self.sink, self.table, inner))
    }

    /// A `service` reference, given by its principal's bytes.
    pub fn service(self, id: &[u8]) -> Result<(), EncodeError> {
        let Some(Composite::Service(_)) = self.composite() else {
            return Err(self.not_of_type("service"));
        };
        write_id(&mut self.sink.out, id)?;
        self.sink.paid()
    }

    /// A `func` reference: its service's principal's bytes, and the method's name.
    pub fn func(self, service: &[u8], method: &str) -> Result<(), EncodeError> {
        let Some(Composite::Func { .. }) = self.composite() else {
            return Err(self.not_of_type("func"));
        };
        // Check the principal before writing anything.
        let mut bytes = Vec::new();
        write_id(&mut bytes, service)?;
        self.sink.out.push(1);
        self.sink.out.extend_from_slice(&bytes);
        write_bytes(&mut self.sink.out, method.as_bytes());
        self.sink.paid()
    }
}

/// A length, then the bytes.
fn write_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    leb128::write_unsigned(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

/// `M(id(v*) : principal)`: a transparent reference, then its bytes.
fn write_id(out: &mut Vec<u8>, id: &[u8]) -> Result<(), EncodeError> {
    if id.len() > MAX_PRINCIPAL_LENGTH {
        return Err(EncodeError::PrincipalTooLong { len: id.len() });
    }
    out.push(1);
    write_bytes(out, id);
    Ok(())
}

/// The values of a `vec`, as many as it was given: a writer for each in turn, then
/// [`VecWriter::finish`].
#[derive(Debug)]
pub struct VecWriter<'w> {
    sink: &'w mut Sink,
    table: &'w TypeTable,
    element: Slot,
    /// How many values were owed when the vector was begun, its own among them.
    level: usize,
    len: usize,
    written: usize,
}

impl VecWriter<'_> {
    /// The writer for the next value.
    pub fn element(&mut self) -> Result<ValueWriter<'_>, EncodeError> {
        self.sink.settled(self.level)?;
        if self.written == self.len {
            return Err(EncodeError::ElementCount {
                len: self.len,
                written: self.written + 1,
            });
        }
        self.written += 1;
        self.sink.owed += 1;
        Ok(ValueWriter::new(self.sink, self.table, self.element))
    }

    /// The vector is written, once each of its values is.
    pub fn finish(self) -> Result<(), EncodeError> {
        self.sink.settled(self.level)?;
        if self.written != self.len {
            return Err(EncodeError::ElementCount {
                len: self.len,
                written: self.written,
            });
        }
        self.sink.paid()
    }
}

/// The fields of a `record`, in the type's order -- ascending id: a writer for each in
/// turn, then [`RecordWriter::finish`].
#[derive(Debug)]
pub struct RecordWriter<'w> {
    sink: &'w mut Sink,
    table: &'w TypeTable,
    /// The type's fields, in ascending id.
    fields: &'w [(FieldId, Slot)],
    /// How many values were owed when the record was begun, its own among them.
    level: usize,
    /// How many fields have been handed out.
    next: usize,
}

impl RecordWriter<'_> {
    /// The id of the field to write next, or `None` once every field has a writer.
    pub fn next_field(&self) -> Option<FieldId> {
        self.fields.get(self.next).map(|&(id, _)| id)
    }

    /// The writer for field `id`, which must be the next: [`RecordWriter::next_field`].
    pub fn field(&mut self, id: FieldId) -> Result<ValueWriter<'_>, EncodeError> {
        self.sink.settled(self.level)?;
        let expected = self.next_field();
        let Some(&(_, slot)) = self.fields.get(self.next).filter(|_| expected == Some(id)) else {
            return Err(EncodeError::UnexpectedField { id, expected });
        };
        self.next += 1;
        self.sink.owed += 1;
        Ok(ValueWriter::new(self.sink, self.table, slot))
    }

    /// The record is written, once each of its fields is.
    pub fn finish(self) -> Result<(), EncodeError> {
        self.sink.settled(self.level)?;
        if let Some(id) = self.next_field() {
            return Err(EncodeError::MissingField { id });
        }
        self.sink.paid()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Encoder, Header};
    use alloc::vec;
    use alloc::vec::Vec;
    use candid_types::{RawTypeTable, TypeRef};

    fn header(entries: Vec<Composite>, types: Vec<Slot>) -> Header {
        Header::new(RawTypeTable::from(entries).check().unwrap(), types).unwrap()
    }

    fn r(i: usize) -> Slot {
        Slot::Ref(TypeRef::new(i))
    }

    /// The values' bytes, after the header, of a message with one argument.
    fn one(
        entries: Vec<Composite>,
        t: Slot,
        write: impl FnOnce(ValueWriter<'_>) -> Result<(), EncodeError>,
    ) -> Result<Vec<u8>, EncodeError> {
        let h = header(entries, vec![t]);
        let mut empty = Vec::new();
        h.encode(&mut empty);
        let mut e = Encoder::new(h);
        write(e.argument()?)?;
        Ok(e.finish()?[empty.len()..].to_vec())
    }

    #[test]
    fn scalars() {
        assert_eq!(
            one(vec![], Slot::NAT, |w| w.nat(&[0x2c, 0x01, 0, 0])),
            Ok(vec![0xac, 0x02])
        );
        assert_eq!(
            one(vec![], Slot::INT, |w| w.int(&[0x7f, 0xff])),
            Ok(vec![0xff, 0x7e])
        );
        assert_eq!(
            one(vec![], Slot::INT16, |w| w.int16(-2)),
            Ok(vec![0xfe, 0xff])
        );
        assert_eq!(one(vec![], Slot::BOOL, |w| w.bool(true)), Ok(vec![1]));
        assert_eq!(
            one(vec![], Slot::TEXT, |w| w.text("hi")),
            Ok(vec![2, b'h', b'i'])
        );
        let nan = f32::from_bits(0x7fc0_0001);
        assert_eq!(
            one(vec![], Slot::FLOAT32, |w| w.float32(nan)),
            Ok(vec![1, 0, 0xc0, 0x7f])
        );
        assert_eq!(
            one(vec![], Slot::PRINCIPAL, |w| w.principal(&[4])),
            Ok(vec![1, 1, 4])
        );
    }

    #[test]
    fn null_at_each_type_that_has_it() {
        let entries = vec![
            Composite::Opt(Slot::NAT),
            Composite::Future {
                opcode: -30,
                data: vec![],
            },
        ];
        assert_eq!(one(entries.clone(), Slot::NULL, |w| w.null()), Ok(vec![]));
        assert_eq!(
            one(entries.clone(), Slot::RESERVED, |w| w.null()),
            Ok(vec![])
        );
        assert_eq!(one(entries.clone(), r(0), |w| w.null()), Ok(vec![0]));
        assert_eq!(one(entries.clone(), r(1), |w| w.null()), Ok(vec![0, 0]));
        assert_eq!(
            one(entries, Slot::NAT, |w| w.null()),
            Err(EncodeError::NotOfType {
                slot: Slot::NAT,
                value: "null"
            })
        );
    }

    #[test]
    fn a_value_has_its_type_exactly() {
        // No coercion on the way out: a `nat` is not an `int`, nor `reserved`.
        assert_eq!(
            one(vec![], Slot::INT, |w| w.nat(&[1])),
            Err(EncodeError::NotOfType {
                slot: Slot::INT,
                value: "nat"
            })
        );
        assert!(one(vec![], Slot::RESERVED, |w| w.nat(&[1])).is_err());
        assert!(one(vec![], Slot::EMPTY, |w| w.null()).is_err());
        assert_eq!(
            one(vec![], Slot::PRINCIPAL, |w| w.principal(&[0; 30])),
            Err(EncodeError::PrincipalTooLong { len: 30 })
        );
        // A blob is a `vec nat8` and nothing else -- but the empty one is every vector.
        let entries = vec![Composite::Vec(Slot::NAT16), Composite::Vec(Slot::EMPTY)];
        assert!(one(entries.clone(), r(0), |w| w.blob(&[1])).is_err());
        for t in [r(0), r(1)] {
            let empty_vec = one(entries.clone(), t, |w| w.vec(0)?.finish());
            assert_eq!(one(entries.clone(), t, |w| w.blob(&[])), empty_vec);
            assert_eq!(empty_vec, Ok(vec![0]));
        }
        assert!(one(vec![], Slot::NAT, |w| w.blob(&[])).is_err());
    }

    #[test]
    fn composites() {
        let entries = vec![
            Composite::Opt(r(1)),
            Composite::record_of([("a", Slot::NAT8), ("b", Slot::BOOL)]),
            Composite::Vec(Slot::NAT8),
            Composite::variant_of([("x", Slot::NULL), ("y", Slot::TEXT)]),
        ];
        let Composite::Record(fs) = &entries[1] else {
            unreachable!()
        };
        let mut ids: Vec<FieldId> = fs.iter().map(|f| f.0).collect();
        ids.sort();
        let bytes = one(entries.clone(), r(0), |w| {
            let mut rec = w.opt()?.record()?;
            for &id in &ids {
                let f = rec.field(id)?;
                if f.slot() == Slot::NAT8 {
                    f.nat8(7)?
                } else {
                    f.bool(false)?
                }
            }
            rec.finish()
        });
        let field_bytes: Vec<u8> = ids
            .iter()
            .map(|&id| {
                if id == candid_types::hash_field_name("a") {
                    7
                } else {
                    0
                }
            })
            .collect();
        assert_eq!(bytes, Ok([&[1][..], &field_bytes].concat()));

        let by_elements = one(entries.clone(), r(2), |w| {
            let mut v = w.vec(2)?;
            v.element()?.nat8(1)?;
            v.element()?.nat8(2)?;
            v.finish()
        });
        assert_eq!(by_elements, Ok(vec![2, 1, 2]));
        assert_eq!(one(entries.clone(), r(2), |w| w.blob(&[1, 2])), by_elements);

        let y = candid_types::hash_field_name("y");
        let x = candid_types::hash_field_name("x");
        let y_index = u8::from(y > x);
        assert_eq!(
            one(entries.clone(), r(3), |w| w.variant(y)?.text("")),
            Ok(vec![y_index, 0])
        );
        assert_eq!(
            one(entries, r(3), |w| w.variant(FieldId::new(0)).map(drop)),
            Err(EncodeError::NoSuchAlternative {
                id: FieldId::new(0)
            })
        );
    }

    #[test]
    fn fields_in_order() {
        let entries = vec![Composite::Record(vec![
            (FieldId::new(1), Slot::NULL),
            (FieldId::new(2), Slot::NULL),
        ])];
        let unexpected = one(entries.clone(), r(0), |w| {
            let mut rec = w.record()?;
            rec.field(FieldId::new(2))?.null()?;
            rec.finish()
        });
        assert_eq!(
            unexpected,
            Err(EncodeError::UnexpectedField {
                id: FieldId::new(2),
                expected: Some(FieldId::new(1))
            })
        );
        let missing = one(entries, r(0), |w| {
            let mut rec = w.record()?;
            rec.field(FieldId::new(1))?.null()?;
            rec.finish()
        });
        assert_eq!(
            missing,
            Err(EncodeError::MissingField {
                id: FieldId::new(2)
            })
        );
    }

    #[test]
    fn element_count() {
        let entries = vec![Composite::Vec(Slot::NULL)];
        let short = one(entries.clone(), r(0), |w| {
            let mut v = w.vec(2)?;
            v.element()?.null()?;
            v.finish()
        });
        assert_eq!(short, Err(EncodeError::ElementCount { len: 2, written: 1 }));
        let long = one(entries, r(0), |w| {
            let mut v = w.vec(0)?;
            v.element()?.null()?;
            v.finish()
        });
        assert_eq!(long, Err(EncodeError::ElementCount { len: 0, written: 1 }));
    }

    #[test]
    fn an_unwritten_value_is_noticed() {
        let entries = vec![Composite::Vec(Slot::NAT), Composite::Opt(r(0))];
        // A dropped element writer.
        let dropped = one(entries.clone(), r(0), |w| {
            let mut v = w.vec(1)?;
            let _ = v.element()?;
            v.finish()
        });
        assert_eq!(dropped, Err(EncodeError::Unfinished));
        // A failed element, its error ignored.
        let ignored = one(entries.clone(), r(0), |w| {
            let mut v = w.vec(2)?;
            let _ = v.element()?.text("not a nat");
            v.element()?.nat(&[1])?;
            v.finish()
        });
        assert_eq!(ignored, Err(EncodeError::Unfinished));
        // A nested vector left unfinished, inside an `opt`.
        let nested = one(entries.clone(), r(1), |w| {
            let mut v = w.opt()?.vec(1)?;
            v.element()?.nat(&[1])?;
            Ok(())
        });
        assert_eq!(nested, Err(EncodeError::Unfinished));
        // A dropped argument writer.
        let mut e = Encoder::new(header(entries, vec![Slot::NAT, Slot::NAT]));
        let _ = e.argument().unwrap();
        assert_eq!(e.argument().map(drop), Err(EncodeError::Unfinished));
        assert_eq!(e.finish(), Err(EncodeError::Unfinished));
    }

    #[test]
    fn a_value_writes_through_the_trait() {
        struct Five;
        impl Encode for Five {
            fn encode(&self, writer: ValueWriter<'_>) -> Result<(), EncodeError> {
                writer.nat(&[5])
            }
        }
        // Through `&T`'s impl too.
        let five = &Five;
        assert_eq!(one(vec![], Slot::NAT, |w| five.encode(w)), Ok(vec![5]));
        assert_eq!(
            one(vec![], Slot::NAT, |w| Encode::encode(&five, w)),
            Ok(vec![5])
        );
    }
}
