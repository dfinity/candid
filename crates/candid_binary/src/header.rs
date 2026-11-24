//! The part of a message before its values: the magic number, the type table and the
//! argument types (`lean/Spec/Binary.md`, Sections 4 and 5). Mirrors the "Opcodes",
//! "Encoding" and "Decoding the header" sections of `lean/Candid/Wire.lean`.

use alloc::string::String;
use alloc::vec::Vec;

use candid_types::{
    Annotation, Composite, FieldId, Primitive, RawTypeTable, Slot, TypeRef, TypeTable,
};

use crate::error::{Rejection, UnresolvedArgument};
use crate::leb128::{self, Signed};
use crate::reader::{Read, Reader};

/// The magic number every message starts with.
const MAGIC: [u8; 4] = *b"DIDL";

/// A message's type table and the type of each of its arguments: everything in a
/// message but the values.
///
/// Every argument type resolves in the table, which is well formed. A [`Decoder`] reads
/// one, and an [`Encoder`] writes one.
///
/// [`Decoder`]: crate::Decoder
/// [`Encoder`]: crate::Encoder
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Header {
    table: TypeTable,
    types: Vec<Slot>,
}

impl Header {
    /// A header with these argument types, unless one does not resolve in `table`.
    pub fn new(table: TypeTable, types: Vec<Slot>) -> Result<Header, UnresolvedArgument> {
        match types.iter().position(|&t| !table.resolves(t)) {
            Some(index) => Err(UnresolvedArgument::new(index)),
            None => Ok(Header { table, types }),
        }
    }

    /// The type table.
    pub fn table(&self) -> &TypeTable {
        &self.table
    }

    /// The argument types, in order. Each resolves in [`Header::table`].
    pub fn types(&self) -> &[Slot] {
        &self.types
    }

    /// Read the header at the start of a message, leaving `r` at the first value.
    ///
    /// Rejects what the spec says a decoder must reject in a header, and then a table
    /// that is not well formed and an argument type that does not resolve.
    pub(crate) fn decode(r: &mut Reader<'_>) -> Read<Header> {
        for b in MAGIC {
            let at = r.position();
            if r.byte()? != b {
                return r.fail(at, Rejection::MissingMagicNumber);
            }
        }
        // Where each entry and argument type starts, so that a check made once the header
        // is read can still say where the problem is.
        let (entries, entry_offsets) = list_with_offsets(r, entry)?;
        let (types, type_offsets) = list_with_offsets(r, slot)?;
        let table = match RawTypeTable::from_entries(entries).check() {
            Ok(table) => table,
            Err(e) => {
                let at = entry_offsets[e.entry().index()];
                return r.fail(at, Rejection::MalformedTable(e));
            }
        };
        if let Some(i) = types.iter().position(|&t| !table.resolves(t)) {
            return r.fail(type_offsets[i], Rejection::UnresolvedArgument(i));
        }
        Ok(Header { table, types })
    }

    /// Append the header to `out`: the magic number, the whole table in its order, and
    /// the argument types.
    ///
    /// An encoder chooses its table, and this one writes the table it is given. A
    /// [`TypeTable`] keeps fields in order of id and methods in order of name, which is
    /// the order the spec requires.
    pub(crate) fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&MAGIC);
        let entries = self.table.entries();
        leb128::write_unsigned(out, length(entries.len()));
        for e in entries {
            encode_entry(out, e);
        }
        leb128::write_unsigned(out, length(self.types.len()));
        for &t in &self.types {
            encode_slot(out, t);
        }
    }
}

/// A length, as LEB128 writes it. A `usize` always fits in a `u64` on the targets Rust
/// supports.
fn length(n: usize) -> u64 {
    n as u64
}

/// The opcode of each composite type.
mod opcode {
    pub(super) const OPT: i64 = -18;
    pub(super) const VEC: i64 = -19;
    pub(super) const RECORD: i64 = -20;
    pub(super) const VARIANT: i64 = -21;
    pub(super) const FUNC: i64 = -22;
    pub(super) const SERVICE: i64 = -23;
    /// Opcodes below this are future types.
    pub(super) const PRINCIPAL: i64 = -24;
}

fn primitive_opcode(p: Primitive) -> i64 {
    match p {
        Primitive::Null => -1,
        Primitive::Bool => -2,
        Primitive::Nat => -3,
        Primitive::Int => -4,
        Primitive::Nat8 => -5,
        Primitive::Nat16 => -6,
        Primitive::Nat32 => -7,
        Primitive::Nat64 => -8,
        Primitive::Int8 => -9,
        Primitive::Int16 => -10,
        Primitive::Int32 => -11,
        Primitive::Int64 => -12,
        Primitive::Float32 => -13,
        Primitive::Float64 => -14,
        Primitive::Text => -15,
        Primitive::Reserved => -16,
        Primitive::Empty => -17,
        Primitive::Principal => opcode::PRINCIPAL,
    }
}

fn primitive_of_opcode(op: i64) -> Option<Primitive> {
    Primitive::ALL
        .into_iter()
        .find(|&p| primitive_opcode(p) == op)
}

fn annotation_code(a: Annotation) -> u8 {
    match a {
        Annotation::Query => 1,
        Annotation::Oneway => 2,
        Annotation::CompositeQuery => 3,
    }
}

fn annotation_of_code(b: u8) -> Option<Annotation> {
    [
        Annotation::Query,
        Annotation::Oneway,
        Annotation::CompositeQuery,
    ]
    .into_iter()
    .find(|&a| annotation_code(a) == b)
}

// Decoding.

/// `T*`: a count, then that many items, in order.
fn list<'a, T>(r: &mut Reader<'a>, item: impl Fn(&mut Reader<'a>) -> Read<T>) -> Read<Vec<T>> {
    let n = r.unsigned()?;
    let mut items = Vec::new();
    for _ in 0..n {
        items.push(item(r)?);
    }
    Ok(items)
}

/// `T*`, and the offset each item starts at, in a list of its own so that neither has to
/// be copied out of a list of pairs.
fn list_with_offsets<'a, T>(
    r: &mut Reader<'a>,
    item: impl Fn(&mut Reader<'a>) -> Read<T>,
) -> Read<(Vec<T>, Vec<usize>)> {
    let n = r.unsigned()?;
    let (mut items, mut offsets) = (Vec::new(), Vec::new());
    for _ in 0..n {
        offsets.push(r.position());
        items.push(item(r)?);
    }
    Ok((items, offsets))
}

/// A type reference: a primitive type's opcode, or an index into the table. Whether the
/// index resolves is [`RawTypeTable::check`]'s to say, so one too large for a `usize`
/// is kept as `usize::MAX`, which dangles just the same.
fn slot(r: &mut Reader<'_>) -> Read<Slot> {
    let at = r.position();
    match r.signed()? {
        Signed::Value(op) if op >= 0 => Ok(index(usize::try_from(op).unwrap_or(usize::MAX))),
        Signed::Above => Ok(index(usize::MAX)),
        Signed::Value(op) => match primitive_of_opcode(op) {
            Some(p) => Ok(Slot::Primitive(p)),
            None => r.fail(at, Rejection::NotATypeReference),
        },
        Signed::Below => r.fail(at, Rejection::NotATypeReference),
    }
}

fn index(i: usize) -> Slot {
    Slot::Ref(TypeRef::new(i))
}

/// Fields in strictly ascending order of id, which also rules out a repeated one.
fn fields(r: &mut Reader<'_>) -> Read<Vec<(FieldId, Slot)>> {
    let at = r.position();
    let fs = list(r, |r| {
        let at = r.position();
        let Ok(id) = u32::try_from(r.unsigned()?) else {
            return r.fail(at, Rejection::FieldIdTooLarge);
        };
        Ok((FieldId::new(id), slot(r)?))
    })?;
    if !fs.windows(2).all(|w| w[0].0 < w[1].0) {
        return r.fail(at, Rejection::FieldsOutOfOrder);
    }
    Ok(fs)
}

fn entry(r: &mut Reader<'_>) -> Read<Composite> {
    let at = r.position();
    let op = match r.signed()? {
        Signed::Value(op) => op,
        Signed::Above => return r.fail(at, Rejection::NotAType),
        Signed::Below => return r.fail(at, Rejection::OpcodeOutOfRange),
    };
    Ok(match op {
        opcode::OPT => Composite::Opt(slot(r)?),
        opcode::VEC => Composite::Vec(slot(r)?),
        opcode::RECORD => Composite::Record(fields(r)?),
        opcode::VARIANT => Composite::Variant(fields(r)?),
        opcode::FUNC => {
            let parameters = list(r, slot)?;
            let results = list(r, slot)?;
            let annotations = list(r, |r| {
                let at = r.position();
                let b = r.byte()?;
                match annotation_of_code(b) {
                    Some(a) => Ok(a),
                    None => r.fail(at, Rejection::UnknownAnnotation(b)),
                }
            })?;
            Composite::Func {
                parameters,
                results,
                annotations,
            }
        }
        opcode::SERVICE => {
            let start = r.position();
            let methods = list(r, |r| {
                let name = String::from(r.text()?);
                Ok((name, slot(r)?))
            })?;
            // `str`'s order is that of the UTF-8 bytes, which is the spec's.
            if !methods.windows(2).all(|w| w[0].0 < w[1].0) {
                return r.fail(start, Rejection::MethodsOutOfOrder);
            }
            Composite::Service(methods)
        }
        op => {
            if let Some(p) = primitive_of_opcode(op) {
                return r.fail(at, Rejection::PrimitiveInTable(p));
            }
            if op >= opcode::PRINCIPAL {
                return r.fail(at, Rejection::NotAType);
            }
            Composite::Future {
                opcode: op,
                data: r.blob()?.to_vec(),
            }
        }
    })
}

// Encoding.

/// A type reference: signed, like the opcodes.
fn encode_slot(out: &mut Vec<u8>, s: Slot) {
    match s {
        Slot::Primitive(p) => leb128::write_signed(out, primitive_opcode(p)),
        // A table index fits in an `i64`: the table is in memory.
        Slot::Ref(r) => leb128::write_signed(out, r.index() as i64),
    }
}

fn encode_fields(out: &mut Vec<u8>, fields: &[(FieldId, Slot)]) {
    leb128::write_unsigned(out, length(fields.len()));
    for &(id, s) in fields {
        leb128::write_unsigned(out, u64::from(id.get()));
        encode_slot(out, s);
    }
}

fn encode_slots(out: &mut Vec<u8>, slots: &[Slot]) {
    leb128::write_unsigned(out, length(slots.len()));
    for &s in slots {
        encode_slot(out, s);
    }
}

fn encode_entry(out: &mut Vec<u8>, entry: &Composite) {
    match entry {
        Composite::Opt(s) => {
            leb128::write_signed(out, opcode::OPT);
            encode_slot(out, *s);
        }
        Composite::Vec(s) => {
            leb128::write_signed(out, opcode::VEC);
            encode_slot(out, *s);
        }
        Composite::Record(fs) => {
            leb128::write_signed(out, opcode::RECORD);
            encode_fields(out, fs);
        }
        Composite::Variant(fs) => {
            leb128::write_signed(out, opcode::VARIANT);
            encode_fields(out, fs);
        }
        Composite::Func {
            parameters,
            results,
            annotations,
        } => {
            leb128::write_signed(out, opcode::FUNC);
            encode_slots(out, parameters);
            encode_slots(out, results);
            leb128::write_unsigned(out, length(annotations.len()));
            out.extend(annotations.iter().map(|&a| annotation_code(a)));
        }
        Composite::Service(methods) => {
            leb128::write_signed(out, opcode::SERVICE);
            leb128::write_unsigned(out, length(methods.len()));
            for (name, s) in methods {
                leb128::write_unsigned(out, length(name.len()));
                out.extend_from_slice(name.as_bytes());
                encode_slot(out, *s);
            }
        }
        Composite::Future { opcode, data } => {
            leb128::write_signed(out, *opcode);
            leb128::write_unsigned(out, length(data.len()));
            out.extend_from_slice(data);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn decode(bytes: &[u8]) -> Result<Header, Rejection> {
        Header::decode(&mut Reader::new(bytes)).map_err(|e| e.rejection().clone())
    }

    /// `DIDL`, then `rest`.
    fn message(rest: &[u8]) -> Vec<u8> {
        let mut m = MAGIC.to_vec();
        m.extend_from_slice(rest);
        m
    }

    #[test]
    fn opcodes_are_distinct() {
        for p in Primitive::ALL {
            assert_eq!(primitive_of_opcode(primitive_opcode(p)), Some(p));
        }
        for b in 0..=u8::MAX {
            if let Some(a) = annotation_of_code(b) {
                assert_eq!(annotation_code(a), b);
            }
        }
    }

    #[test]
    fn empty_message() {
        let bytes = message(&[0x00, 0x00]);
        let h = decode(&bytes).unwrap();
        assert!(h.table().is_empty() && h.types().is_empty());
    }

    #[test]
    fn roundtrip() {
        let mut raw = RawTypeTable::new();
        let list = raw.intern(Composite::Opt(Slot::Ref(TypeRef::new(1))));
        raw.intern(Composite::record_of([("tail", list), ("head", Slot::NAT)]));
        raw.intern(Composite::Func {
            parameters: vec![list, Slot::TEXT],
            results: vec![],
            annotations: vec![Annotation::Query],
        });
        raw.intern(Composite::Service(vec![
            ("z".into(), Slot::Ref(TypeRef::new(2))),
            ("a".into(), Slot::Ref(TypeRef::new(2))),
        ]));
        raw.intern(Composite::Future {
            opcode: i64::MIN,
            data: vec![1, 2, 3],
        });
        let header = Header::new(raw.check().unwrap(), vec![list, Slot::INT]).unwrap();
        let mut bytes = header.encode_to_vec();
        bytes.extend_from_slice(&[0xaa, 0xbb]);
        let mut r = Reader::new(&bytes);
        assert_eq!(Header::decode(&mut r).unwrap(), header);
        // The reader is left at the values.
        assert_eq!(r.rest(), [0xaa, 0xbb]);
        // A table is written as it is held: fields in order of id, methods of name.
        let Composite::Service(methods) = &header.table().entries()[3] else {
            panic!("entry 3 is the service");
        };
        assert_eq!(methods[0].0, "a");
    }

    #[test]
    fn an_argument_that_does_not_resolve() {
        let table = TypeTable::default();
        let err = Header::new(table, vec![Slot::NAT, Slot::Ref(TypeRef::new(0))]).unwrap_err();
        assert_eq!(err.index(), 1);
    }

    impl Header {
        fn encode_to_vec(&self) -> Vec<u8> {
            let mut out = Vec::new();
            self.encode(&mut out);
            out
        }
    }

    #[test]
    fn rejections() {
        use Rejection::*;
        let cases: Vec<(Vec<u8>, Rejection)> = vec![
            // The magic number.
            (b"DIDM\x00\x00".to_vec(), MissingMagicNumber),
            (b"DID".to_vec(), EndOfInput),
            // A composite opcode where a type reference belongs.
            (message(&[0x00, 0x01, 0x6e]), NotATypeReference),
            // -25 is no primitive.
            (message(&[0x00, 0x01, 0x67]), NotATypeReference),
            // A primitive in the table.
            (
                message(&[0x01, 0x7d, 0x00]),
                PrimitiveInTable(Primitive::Nat),
            ),
            // An entry opcode of 0.
            (message(&[0x01, 0x00, 0x00]), NotAType),
            // `record { 1 : nat; 0 : nat }`.
            (
                message(&[0x01, 0x6c, 0x02, 0x01, 0x7d, 0x00, 0x7d, 0x00]),
                FieldsOutOfOrder,
            ),
            // A repeated field.
            (
                message(&[0x01, 0x6c, 0x02, 0x00, 0x7d, 0x00, 0x7d, 0x00]),
                FieldsOutOfOrder,
            ),
            // A field id of 2^32.
            (
                message(&[0x01, 0x6c, 0x01, 0x80, 0x80, 0x80, 0x80, 0x10, 0x7d, 0x00]),
                FieldIdTooLarge,
            ),
            // `func () -> () 4`.
            (
                message(&[0x01, 0x6a, 0x00, 0x00, 0x01, 0x04, 0x00]),
                UnknownAnnotation(4),
            ),
            // `service { "b" : 0; "a" : 0 }`, whose methods are out of order.
            (
                message(&[0x01, 0x69, 0x02, 0x01, b'b', 0x00, 0x01, b'a', 0x00, 0x00]),
                MethodsOutOfOrder,
            ),
            // A method name that is not UTF-8.
            (
                message(&[0x01, 0x69, 0x01, 0x01, 0xff, 0x00, 0x00]),
                TextNotUtf8,
            ),
            // An argument that dangles.
            (message(&[0x00, 0x01, 0x00]), UnresolvedArgument(0)),
            // A count larger than the message.
            (message(&[0xff, 0xff, 0xff, 0xff, 0x0f]), EndOfInput),
            // A future type's opcode below -2^63.
            (
                message(&[
                    0x01, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7e, 0x00,
                ]),
                OpcodeOutOfRange,
            ),
        ];
        for (bytes, want) in cases {
            assert_eq!(decode(&bytes).err(), Some(want), "{bytes:02x?}");
        }
    }

    #[test]
    fn checks_after_parsing_point_at_the_offending_bytes() {
        // The argument type `0` at offset 6 dangles; the byte after it is a value.
        let e = Header::decode(&mut Reader::new(&message(&[0x00, 0x01, 0x00, 0xaa]))).unwrap_err();
        assert_eq!(
            (e.position(), e.rejection()),
            (6, &Rejection::UnresolvedArgument(0))
        );
        // Entry 1, `vec 5` at offset 7, dangles; entry 0 is `opt nat` at offset 5.
        let e = Header::decode(&mut Reader::new(&message(&[
            0x02, 0x6e, 0x7d, 0x6d, 0x05, 0x00,
        ])))
        .unwrap_err();
        assert_eq!(e.position(), 7);
        assert!(matches!(e.rejection(), Rejection::MalformedTable(_)));
    }

    #[test]
    fn a_malformed_table_is_rejected() {
        // `vec 1` in a table of one entry.
        let got = decode(&message(&[0x01, 0x6d, 0x01, 0x00])).unwrap_err();
        assert!(matches!(got, Rejection::MalformedTable(_)), "{got:?}");
    }

    #[test]
    fn redundant_continuation_bytes() {
        // `opt nat`, its opcode written `ee 7f`, and the argument 0 written `80 00`.
        let h = decode(&message(&[0x01, 0xee, 0x7f, 0x7d, 0x01, 0x80, 0x00])).unwrap();
        assert_eq!(h.table().entries(), [Composite::Opt(Slot::NAT)]);
        // An index past the end of any table dangles rather than overflowing.
        let mut huge = message(&[0x00, 0x01]);
        huge.extend_from_slice(&[0xff; 12]);
        huge.push(0x00);
        assert_eq!(decode(&huge).unwrap_err(), Rejection::UnresolvedArgument(0));
    }
}
