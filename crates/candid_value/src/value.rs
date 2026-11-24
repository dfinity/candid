//! [`Value`], transcribing `lean/Candid/Value.lean`.

use core::fmt;
use core::hash::{Hash, Hasher};

use candid_binary::{Decode, DecodeError, Encode, EncodeError, ValueReader, ValueWriter};
use candid_types::{Composite, FieldId, Primitive, Slot};
use ic_principal::Principal;

use crate::number::{Int, Nat};

/// Any value of any Candid type.
///
/// A value does not know its type: `5` is the same `Value::Nat8` at every type it has.
/// Where a value can have more than one type, a type says which:
///
/// - **One `null`.** [`Value::Null`] is the value of `null` and of `reserved`, an absent
///   `opt`, and the value of a type from a later version of Candid, which a receiver
///   cannot know more of.
/// - **A blob is a `vec nat8`.** [`Value::Blob`] holds the bytes, rather than a
///   [`Value::Nat8`] each, and is equal to the [`Value::Vec`] of those values.
///
/// Equality is the model's: floats are compared by their bits, and a record's fields are
/// kept in order (see [`Record`]), so two values are equal exactly when they are the same
/// Candid value.
#[derive(Clone, Debug)]
#[allow(missing_docs)] // Each variant is a value of the type of the same name.
pub enum Value {
    Null,
    Bool(bool),
    Nat(Nat),
    Int(Int),
    Nat8(u8),
    Nat16(u16),
    Nat32(u32),
    Nat64(u64),
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Float32(Float32),
    Float64(Float64),
    Text(String),
    /// An `opt` with a value. The absent one is [`Value::Null`].
    Opt(Box<Value>),
    Vec(Vec<Value>),
    /// A `vec nat8`, one byte per value: equal to the [`Value::Vec`] of the same
    /// [`Value::Nat8`]s.
    Blob(Vec<u8>),
    Record(Record),
    /// A `variant`: the alternative's id, and its value.
    Variant(FieldId, Box<Value>),
    Principal(Principal),
    /// A `service` reference: the service's principal.
    Service(Principal),
    /// A `func` reference: its service's principal, and the method's name.
    Func(Principal, String),
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        use Value::*;
        match (self, other) {
            (Null, Null) => true,
            (Bool(a), Bool(b)) => a == b,
            (Nat(a), Nat(b)) => a == b,
            (Int(a), Int(b)) => a == b,
            (Nat8(a), Nat8(b)) => a == b,
            (Nat16(a), Nat16(b)) => a == b,
            (Nat32(a), Nat32(b)) => a == b,
            (Nat64(a), Nat64(b)) => a == b,
            (Int8(a), Int8(b)) => a == b,
            (Int16(a), Int16(b)) => a == b,
            (Int32(a), Int32(b)) => a == b,
            (Int64(a), Int64(b)) => a == b,
            (Float32(a), Float32(b)) => a == b,
            (Float64(a), Float64(b)) => a == b,
            (Text(a), Text(b)) => a == b,
            (Opt(a), Opt(b)) => a == b,
            (Vec(a), Vec(b)) => a == b,
            (Blob(a), Blob(b)) => a == b,
            (Blob(bytes), Vec(values)) | (Vec(values), Blob(bytes)) => {
                bytes.len() == values.len() && bytes.iter().zip(values).all(|(&b, v)| *v == Nat8(b))
            }
            (Record(a), Record(b)) => a == b,
            (Variant(a, v), Variant(b, w)) => a == b && v == w,
            (Principal(a), Principal(b)) => a == b,
            (Service(a), Service(b)) => a == b,
            (Func(a, m), Func(b, n)) => a == b && m == n,
            _ => false,
        }
    }
}

impl Eq for Value {}

/// Agrees with equality: a [`Value::Blob`] hashes as the [`Value::Vec`] it equals.
impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Blob(bytes) => {
                core::mem::discriminant(&Value::Vec(Vec::new())).hash(state);
                bytes.len().hash(state);
                for &b in bytes {
                    Value::Nat8(b).hash(state);
                }
            }
            Value::Vec(values) => {
                core::mem::discriminant(self).hash(state);
                values.len().hash(state);
                for v in values {
                    v.hash(state);
                }
            }
            _ => {
                core::mem::discriminant(self).hash(state);
                match self {
                    Value::Null | Value::Blob(_) | Value::Vec(_) => {}
                    Value::Bool(b) => b.hash(state),
                    Value::Nat(n) => n.hash(state),
                    Value::Int(i) => i.hash(state),
                    Value::Nat8(n) => n.hash(state),
                    Value::Nat16(n) => n.hash(state),
                    Value::Nat32(n) => n.hash(state),
                    Value::Nat64(n) => n.hash(state),
                    Value::Int8(i) => i.hash(state),
                    Value::Int16(i) => i.hash(state),
                    Value::Int32(i) => i.hash(state),
                    Value::Int64(i) => i.hash(state),
                    Value::Float32(f) => f.hash(state),
                    Value::Float64(f) => f.hash(state),
                    Value::Text(s) => s.hash(state),
                    Value::Opt(v) => v.hash(state),
                    Value::Record(r) => r.hash(state),
                    Value::Variant(id, v) => (id, v).hash(state),
                    Value::Principal(p) | Value::Service(p) => p.hash(state),
                    Value::Func(p, m) => (p, m).hash(state),
                }
            }
        }
    }
}

/// Writes the value at the type the writer has: it fails if the value does not have it.
impl Encode for Value {
    fn encode(&self, writer: ValueWriter<'_>) -> Result<(), EncodeError> {
        match self {
            Value::Null => writer.null(),
            Value::Bool(b) => writer.bool(*b),
            Value::Nat(n) => writer.nat(&n.to_le_bytes()),
            Value::Int(i) => writer.int(&i.to_le_bytes()),
            Value::Nat8(n) => writer.nat8(*n),
            Value::Nat16(n) => writer.nat16(*n),
            Value::Nat32(n) => writer.nat32(*n),
            Value::Nat64(n) => writer.nat64(*n),
            Value::Int8(i) => writer.int8(*i),
            Value::Int16(i) => writer.int16(*i),
            Value::Int32(i) => writer.int32(*i),
            Value::Int64(i) => writer.int64(*i),
            Value::Float32(f) => writer.float32(f.get()),
            Value::Float64(f) => writer.float64(f.get()),
            Value::Text(s) => writer.text(s),
            Value::Opt(v) => v.encode(writer.opt()?),
            Value::Vec(values) => {
                let mut elements = writer.vec(values.len())?;
                for v in values {
                    v.encode(elements.element()?)?;
                }
                elements.finish()
            }
            Value::Blob(bytes) => writer.blob(bytes),
            Value::Record(record) => {
                let mut fields = writer.record()?;
                for (id, v) in record.fields() {
                    v.encode(fields.field(*id)?)?;
                }
                fields.finish()
            }
            Value::Variant(id, v) => v.encode(writer.variant(*id)?),
            Value::Principal(p) => writer.principal(p.as_slice()),
            Value::Service(p) => writer.service(p.as_slice()),
            Value::Func(p, method) => writer.func(p.as_slice(), method),
        }
    }
}

/// Reads the value at the receiver's type, following it: so a decoded value has that
/// type. At `vec nat8` it is always a [`Value::Blob`].
impl<'a> Decode<'a> for Value {
    fn try_decode(reader: ValueReader<'_, 'a>) -> Result<Option<Value>, DecodeError> {
        let expected = reader.expected();
        let principal = |id: &[u8]| Principal::from_slice(id);
        Ok(match (expected.slot(), expected.composite()) {
            (Slot::Primitive(p), _) => match p {
                Primitive::Null => reader.null()?.map(|()| Value::Null),
                Primitive::Reserved => reader.reserved()?.map(|()| Value::Null),
                Primitive::Empty => reader.empty()?.map(|never| match never {}),
                Primitive::Bool => reader.bool()?.map(Value::Bool),
                Primitive::Nat => reader
                    .nat()?
                    .map(|n| Value::Nat(Nat::from_le_bytes(&n.to_le_bytes()))),
                Primitive::Int => reader
                    .int()?
                    .map(|i| Value::Int(Int::from_le_bytes(&i.to_le_bytes()))),
                Primitive::Nat8 => reader.nat8()?.map(Value::Nat8),
                Primitive::Nat16 => reader.nat16()?.map(Value::Nat16),
                Primitive::Nat32 => reader.nat32()?.map(Value::Nat32),
                Primitive::Nat64 => reader.nat64()?.map(Value::Nat64),
                Primitive::Int8 => reader.int8()?.map(Value::Int8),
                Primitive::Int16 => reader.int16()?.map(Value::Int16),
                Primitive::Int32 => reader.int32()?.map(Value::Int32),
                Primitive::Int64 => reader.int64()?.map(Value::Int64),
                Primitive::Float32 => reader.float32()?.map(|f| Value::Float32(f.into())),
                Primitive::Float64 => reader.float64()?.map(|f| Value::Float64(f.into())),
                Primitive::Text => reader.text()?.map(|s| Value::Text(s.into())),
                Primitive::Principal => reader
                    .principal()?
                    .map(|id| Value::Principal(principal(id))),
            },
            (_, Some(Composite::Opt(_))) => reader.opt(Value::try_decode)?.map(|v| match v {
                Some(v) => Value::Opt(Box::new(v)),
                None => Value::Null,
            }),
            (_, Some(Composite::Vec(Slot::NAT8))) => {
                reader.blob()?.map(|b| Value::Blob(b.to_vec()))
            }
            (_, Some(Composite::Vec(_))) => reader.vec(Value::try_decode)?.map(Value::Vec),
            (_, Some(Composite::Record(fields))) => reader.record(|r| {
                let mut values = Vec::with_capacity(fields.len());
                for &(id, _) in fields {
                    match r.field(id, Value::try_decode)? {
                        Some(v) => values.push((id, v)),
                        None => return Ok(None),
                    }
                }
                // The receiver's fields are in ascending id, so this is a record already.
                Ok(Some(Value::Record(Record { fields: values })))
            })?,
            (_, Some(Composite::Variant(_))) => reader.variant(|id, r| {
                Ok(Value::try_decode(r)?.map(|v| Value::Variant(id, Box::new(v))))
            })?,
            (_, Some(Composite::Func { .. })) => reader
                .func()?
                .map(|(id, method)| Value::Func(principal(id), method.into())),
            (_, Some(Composite::Service(_))) => {
                reader.service()?.map(|id| Value::Service(principal(id)))
            }
            (_, Some(Composite::Future { .. })) => reader.future()?.map(|()| Value::Null),
            // A reference into the receiver's table resolves.
            (Slot::Ref(_), None) => reader.null()?.map(|()| Value::Null),
        })
    }
}

/// A `record` value: its fields in strictly ascending order of id, which is the order the
/// binary format writes them in. So two records with the same fields are equal as lists.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Record {
    fields: Vec<(FieldId, Value)>,
}

impl Record {
    /// A record of no fields.
    pub fn new() -> Record {
        Record::default()
    }

    /// A record of these fields, in any order, unless two have one id.
    pub fn from_fields(
        fields: impl IntoIterator<Item = (FieldId, Value)>,
    ) -> Result<Record, DuplicateField> {
        let mut fields: Vec<(FieldId, Value)> = fields.into_iter().collect();
        fields.sort_by_key(|&(id, _)| id);
        if let Some(w) = fields.windows(2).find(|w| w[0].0 == w[1].0) {
            return Err(DuplicateField { id: w[0].0 });
        }
        Ok(Record { fields })
    }

    /// The fields, in ascending id.
    pub fn fields(&self) -> &[(FieldId, Value)] {
        &self.fields
    }

    /// The fields, in ascending id.
    pub fn into_fields(self) -> Vec<(FieldId, Value)> {
        self.fields
    }

    /// The value of field `id`, if the record has it.
    pub fn get(&self, id: FieldId) -> Option<&Value> {
        let i = self.fields.binary_search_by_key(&id, |&(f, _)| f).ok()?;
        Some(&self.fields[i].1)
    }

    /// Set field `id` to `value`, giving back the value it had, if it had one.
    pub fn insert(&mut self, id: FieldId, value: Value) -> Option<Value> {
        match self.fields.binary_search_by_key(&id, |&(f, _)| f) {
            Ok(i) => Some(core::mem::replace(&mut self.fields[i].1, value)),
            Err(i) => {
                self.fields.insert(i, (id, value));
                None
            }
        }
    }
}

/// Two fields of one record with the same id.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DuplicateField {
    id: FieldId,
}

impl DuplicateField {
    /// The id.
    pub fn id(&self) -> FieldId {
        self.id
    }
}

impl fmt::Display for DuplicateField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "two fields with id {}", self.id)
    }
}

impl core::error::Error for DuplicateField {}

macro_rules! float {
    ($t:ident, $f:ty, $bits:ty) => {
        /// A float as its IEEE 754 bits, so that equality is bitwise: a NaN equals itself,
        /// and `-0.0` is not `0.0`.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $t($bits);

        impl $t {
            /// The float, bit for bit.
            pub fn new(f: $f) -> $t {
                $t(f.to_bits())
            }

            /// The float.
            pub fn get(self) -> $f {
                <$f>::from_bits(self.0)
            }

            /// The float of these bits.
            pub const fn from_bits(bits: $bits) -> $t {
                $t(bits)
            }

            /// The bits.
            pub const fn to_bits(self) -> $bits {
                self.0
            }
        }

        impl From<$f> for $t {
            fn from(f: $f) -> $t {
                $t::new(f)
            }
        }

        impl From<$t> for $f {
            fn from(f: $t) -> $f {
                f.get()
            }
        }

        /// The float, as Rust prints it.
        impl fmt::Debug for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.get(), f)
            }
        }
    };
}

float!(Float32, f32, u32);
float!(Float64, f64, u64);

#[cfg(test)]
mod tests {
    use super::*;
    use candid_binary::{Encoder, Header};
    use candid_types::{Composite, RawTypeTable, Slot, TypeRef};
    use std::collections::hash_map::DefaultHasher;

    fn hash(v: &Value) -> u64 {
        let mut h = DefaultHasher::new();
        v.hash(&mut h);
        h.finish()
    }

    #[test]
    fn a_blob_is_a_vec_of_nat8() {
        let blob = Value::Blob(vec![1, 2]);
        let vec = Value::Vec(vec![Value::Nat8(1), Value::Nat8(2)]);
        assert_eq!(blob, vec);
        assert_eq!(vec, blob);
        assert_eq!(hash(&blob), hash(&vec));
        assert_ne!(blob, Value::Vec(vec![Value::Nat16(1), Value::Nat16(2)]));
        assert_ne!(blob, Value::Vec(vec![Value::Nat8(1)]));
        assert_eq!(Value::Blob(vec![]), Value::Vec(vec![]));
    }

    #[test]
    fn floats_are_their_bits() {
        let nan = Value::Float64(Float64::new(f64::NAN));
        assert_eq!(nan, nan.clone());
        assert_ne!(Value::Float32(0.0.into()), Value::Float32((-0.0).into()));
        let payload = Float32::from_bits(0x7fc0_0001);
        assert_eq!(Float32::new(payload.get()), payload);
    }

    #[test]
    fn records_are_canonical() {
        let (a, b) = (FieldId::new(1), FieldId::new(2));
        let one = Record::from_fields([(b, Value::Null), (a, Value::Bool(true))]).unwrap();
        let two = Record::from_fields([(a, Value::Bool(true)), (b, Value::Null)]).unwrap();
        assert_eq!(one, two);
        assert_eq!(one.fields()[0].0, a);
        assert_eq!(one.get(a), Some(&Value::Bool(true)));
        assert_eq!(
            Record::from_fields([(a, Value::Null), (a, Value::Null)]),
            Err(DuplicateField { id: a })
        );
        let mut r = Record::new();
        assert_eq!(r.insert(b, Value::Null), None);
        assert_eq!(r.insert(a, Value::Null), None);
        assert_eq!(r.insert(b, Value::Bool(false)), Some(Value::Null));
        assert_eq!(r.fields().iter().map(|f| f.0).collect::<Vec<_>>(), [a, b]);
    }

    fn encode(entries: Vec<Composite>, t: Slot, v: &Value) -> Result<Vec<u8>, EncodeError> {
        let header = Header::new(RawTypeTable::from(entries).check().unwrap(), vec![t]).unwrap();
        let mut e = Encoder::new(header);
        v.encode(e.argument()?)?;
        e.finish()
    }

    #[test]
    fn encoding() {
        let r = |i| Slot::Ref(TypeRef::new(i));
        let entries = vec![
            Composite::Vec(Slot::NAT8),
            Composite::Opt(r(0)),
            Composite::Record(vec![
                (FieldId::new(0), Slot::NAT),
                (FieldId::new(1), Slot::INT),
            ]),
        ];
        // A blob and the vector it equals write the same bytes.
        let blob = encode(
            entries.clone(),
            r(1),
            &Value::Opt(Box::new(Value::Blob(vec![7]))),
        );
        let vec = Value::Opt(Box::new(Value::Vec(vec![Value::Nat8(7)])));
        assert_eq!(blob, encode(entries.clone(), r(1), &vec));
        assert!(blob.unwrap().ends_with(&[1, 1, 7]));
        // Equal values write alike: the empty blob is the empty vector, of any element.
        let nat16s = vec![Composite::Vec(Slot::NAT16)];
        assert_eq!(
            encode(nat16s.clone(), r(0), &Value::Blob(vec![])),
            encode(nat16s, r(0), &Value::Vec(vec![]))
        );

        let record = Value::Record(
            Record::from_fields([
                (FieldId::new(1), Value::Int(Int::from(-1))),
                (FieldId::new(0), Value::Nat(Nat::from(300u16))),
            ])
            .unwrap(),
        );
        assert!(
            encode(entries.clone(), r(2), &record)
                .unwrap()
                .ends_with(&[0xac, 0x02, 0x7f])
        );
        // A record without every field of its type does not have it.
        let short = Value::Record(
            Record::from_fields([(FieldId::new(0), Value::Nat(Nat::default()))]).unwrap(),
        );
        assert_eq!(
            encode(entries, r(2), &short),
            Err(EncodeError::MissingField {
                id: FieldId::new(1)
            })
        );
    }
}
