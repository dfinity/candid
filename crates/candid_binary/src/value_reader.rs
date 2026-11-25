//! Reading values at the receiver's types: coercion (`lean/Spec/Types.md`, Section 6),
//! as `decodeAt` of `lean/Candid/DecodeAt.lean` does it, in one pass.
//!
//! **The receiver drives; the decoder decides.** A [`ValueReader`] is one value of the
//! message, paired with the receiver's type for it. The receiver calls the method for
//! that type -- [`ValueReader::nat`] at `nat`, [`ValueReader::record`] at a record -- and
//! the decoder applies the coercion rule for the sender's type and the receiver's: a
//! `nat` read as an `int`, the fields the receiver does not have skipped, the ones the
//! sender does not have `null` if their type accepts it, the `opt` rules, references
//! checked by subtyping. A receiver never sees the sender's type. One that has no shape
//! of its own, such as a dynamic value, asks [`ValueReader::expected`] and follows it.
//!
//! **Three outcomes.** A value is `Ok(Some(_))`. `Ok(None)` is the spec's *failure*: the
//! value does not coerce, which an enclosing `opt` turns into `null`. `Err` rejects the
//! message: malformed, past a limit, or undefined -- a value at an infinite option.
//!
//! **No rewinding.** Each method reads its value to the end before it returns, whatever
//! it returns: once the outcome is decided, the rest is skipped, read at the sender's
//! types and checked, never gone back over. A record, vector, variant or `opt` hands out
//! its parts through a closure, so its reader is the frame that knows how far through
//! the value it is; a reader the receiver drops unread is skipped by the one that handed
//! it out. Once a part fails, the value has failed: nothing more of it is read at the
//! receiver's types, as `decodeAt` reads nothing more.

use alloc::vec::Vec;
use core::convert::Infallible;

use candid_types::{Composite, FieldId, Primitive, Root, Slot, TypeTable};

use crate::cursor::{Cursor, Pending, Scalar, accepts_null};
use crate::error::{DecodeError, Rejection};
use crate::leb128;
use crate::reader::Read;

/// How a value is read from a message, at the receiver's type.
///
/// `'a` is the message's lifetime, so a receiver can borrow text and blobs from it rather
/// than copy them.
pub trait Decode<'a>: Sized {
    /// Read the value. `Ok(None)` if it does not coerce to `Self` -- the spec's
    /// *failure*, which an enclosing `opt` turns into `null`; `Err` if the message is
    /// rejected.
    fn try_decode(reader: ValueReader<'_, 'a>) -> Result<Option<Self>, DecodeError>;
}

/// A `nat`, as the message has it: read it out at the size the receiver wants.
#[derive(Clone, Copy, Debug)]
pub struct Natural<'a> {
    leb128: &'a [u8],
}

impl Natural<'_> {
    /// Its base-256 digits, least significant first, in as few bytes as there are: 0 is
    /// no bytes.
    pub fn to_le_bytes(&self) -> Vec<u8> {
        leb128::to_le_bytes(self.leb128, false)
    }

    /// As a `u64`, if it fits.
    pub fn to_u64(&self) -> Option<u64> {
        let bytes = self.to_le_bytes();
        let mut wide = [0; 8];
        wide.get_mut(..bytes.len())?.copy_from_slice(&bytes);
        Some(u64::from_le_bytes(wide))
    }

    /// As a `u128`, if it fits.
    pub fn to_u128(&self) -> Option<u128> {
        let bytes = self.to_le_bytes();
        let mut wide = [0; 16];
        wide.get_mut(..bytes.len())?.copy_from_slice(&bytes);
        Some(u128::from_le_bytes(wide))
    }
}

/// An `int`, as the message has it -- or a `nat`, which coerces to `int`: read it out at
/// the size the receiver wants.
#[derive(Clone, Copy, Debug)]
pub struct Integer<'a> {
    leb128: &'a [u8],
    /// SLEB128, or LEB128 for a `nat`.
    signed: bool,
}

impl Integer<'_> {
    /// The number in two's complement, least significant byte first, in as few bytes as
    /// hold it with its sign: 0 is no bytes.
    pub fn to_le_bytes(&self) -> Vec<u8> {
        let mut bytes = leb128::to_le_bytes(self.leb128, self.signed);
        // A natural number whose top bit is set needs a byte more for its sign.
        if !self.signed && bytes.last().is_some_and(|&b| b & 0x80 != 0) {
            bytes.push(0);
        }
        bytes
    }

    /// As an `i64`, if it fits.
    pub fn to_i64(&self) -> Option<i64> {
        let bytes = self.to_le_bytes();
        let negative = bytes.last().is_some_and(|&b| b & 0x80 != 0);
        let mut wide = [if negative { 0xff } else { 0 }; 8];
        wide.get_mut(..bytes.len())?.copy_from_slice(&bytes);
        Some(i64::from_le_bytes(wide))
    }

    /// As an `i128`, if it fits.
    pub fn to_i128(&self) -> Option<i128> {
        let bytes = self.to_le_bytes();
        let negative = bytes.last().is_some_and(|&b| b & 0x80 != 0);
        let mut wide = [if negative { 0xff } else { 0 }; 16];
        wide.get_mut(..bytes.len())?.copy_from_slice(&bytes);
        Some(i128::from_le_bytes(wide))
    }
}

/// One value of a message, at the receiver's type: call the method for that type.
///
/// Each method consumes the reader. Calling one for another type than
/// [`ValueReader::expected`] is a bug in the receiver, and an `Err`
/// ([`Rejection::ReceiverMismatch`]), never a wrong value.
#[derive(Debug)]
pub struct ValueReader<'r, 'a> {
    cursor: &'r mut Cursor<'a>,
    /// The sender's table.
    sender: &'r TypeTable,
    /// The sender's value, or `None` for one the message does not have: an argument past
    /// its last, or a field its record lacks. That is `null` if the receiver's type
    /// accepts it, and a failure if not.
    value: Option<Pending>,
    expected: Root<'r>,
}

type Outcome<T> = Result<Option<T>, DecodeError>;

impl<'r, 'a> ValueReader<'r, 'a> {
    /// A reader of `value`, which is handed out: the one handing it out skips it if the
    /// receiver does not read it. Counted against [`Limits::received`](crate::Limits::received),
    /// whether the message has the value or not.
    pub(crate) fn new(
        cursor: &'r mut Cursor<'a>,
        sender: &'r TypeTable,
        value: Option<Pending>,
        expected: Root<'r>,
    ) -> Read<Self> {
        cursor.receive()?;
        cursor.pending = value;
        Ok(ValueReader {
            cursor,
            sender,
            value,
            expected,
        })
    }

    /// The receiver's type for this value.
    pub fn expected(&self) -> Root<'r> {
        self.expected
    }

    /// The receiver's type, unless the method is for another.
    fn check(&self, fits: bool, method: &'static str) -> Read<()> {
        if fits {
            Ok(())
        } else {
            self.cursor.fail(Rejection::ReceiverMismatch {
                expected: self.expected.slot(),
                method,
            })
        }
    }

    /// The receiver's type's entry, if it is a composite.
    fn composite(&self) -> Option<&'r Composite> {
        self.expected.composite()
    }

    /// A type in the receiver's table, under this one.
    fn child(&self, slot: Slot) -> Read<Root<'r>> {
        match self.expected.table().root(slot) {
            Some(root) => Ok(root),
            // Every reference in a checked table resolves.
            None => self.cursor.fail(Rejection::ReceiverMismatch {
                expected: slot,
                method: "a type that does not resolve",
            }),
        }
    }

    /// Start on the sender's value, if there is one: it is no longer pending.
    fn begin(&mut self) -> Option<Pending> {
        self.cursor.pending = None;
        self.value
    }

    /// Skip the sender's value: it does not coerce, or the receiver's type is `reserved`.
    fn skip(mut self) -> Read<()> {
        match self.begin() {
            Some(p) => self.cursor.skip(self.sender, p),
            None => Ok(()),
        }
    }

    /// The sender's type's entry.
    fn sender_composite(&self, p: Pending) -> Option<&'r Composite> {
        match p.slot {
            Slot::Ref(r) => self.sender.lookup(r),
            Slot::Primitive(_) => None,
        }
    }

    /// A primitive value, at the receiver's primitive type `q`: `coerceScalar` of
    /// `lean/Candid/DecodeAt.lean`.
    fn primitive(mut self, q: Primitive) -> Outcome<Scalar<'a>> {
        self.check(self.expected.slot() == Slot::Primitive(q), q.name())?;
        let Some(p) = self.begin() else {
            let null = matches!(q, Primitive::Null | Primitive::Reserved);
            return Ok(null.then_some(Scalar::Null));
        };
        let sender_service = matches!(self.sender_composite(p), Some(Composite::Service(_)));
        match (p.slot, q) {
            (_, Primitive::Reserved) => {
                self.cursor.skip(self.sender, p)?;
                Ok(Some(Scalar::Null))
            }
            (Slot::Primitive(s), q) if s == q || (s, q) == (Primitive::Nat, Primitive::Int) => {
                self.cursor.charge()?;
                self.cursor.primitive(s).map(Some)
            }
            (Slot::Ref(_), Primitive::Principal) if sender_service => {
                self.cursor.charge()?;
                self.cursor.id().map(|id| Some(Scalar::Principal(id)))
            }
            _ => {
                self.cursor.skip(self.sender, p)?;
                Ok(None)
            }
        }
    }

    fn fixed<const N: usize>(self, q: Primitive) -> Outcome<[u8; N]> {
        Ok(match self.primitive(q)? {
            Some(Scalar::Fixed(bytes)) => bytes.try_into().ok(),
            _ => None,
        })
    }

    /// At `null`.
    pub fn null(self) -> Outcome<()> {
        Ok(self.primitive(Primitive::Null)?.map(drop))
    }

    /// At `reserved`: every value coerces, to `null`.
    pub fn reserved(self) -> Outcome<()> {
        Ok(self.primitive(Primitive::Reserved)?.map(drop))
    }

    /// At `empty`: no value coerces, since `empty` has none.
    pub fn empty(self) -> Outcome<Infallible> {
        self.primitive(Primitive::Empty)?;
        Ok(None)
    }

    /// At `bool`.
    pub fn bool(self) -> Outcome<bool> {
        Ok(match self.primitive(Primitive::Bool)? {
            Some(Scalar::Bool(b)) => Some(b),
            _ => None,
        })
    }

    /// At `nat`.
    pub fn nat(self) -> Outcome<Natural<'a>> {
        Ok(match self.primitive(Primitive::Nat)? {
            Some(Scalar::Nat(leb128)) => Some(Natural { leb128 }),
            _ => None,
        })
    }

    /// At `int`: an `int`, or a `nat`.
    pub fn int(self) -> Outcome<Integer<'a>> {
        Ok(match self.primitive(Primitive::Int)? {
            Some(Scalar::Int(leb128)) => Some(Integer {
                leb128,
                signed: true,
            }),
            Some(Scalar::Nat(leb128)) => Some(Integer {
                leb128,
                signed: false,
            }),
            _ => None,
        })
    }

    /// At `nat8`.
    pub fn nat8(self) -> Outcome<u8> {
        Ok(self.fixed(Primitive::Nat8)?.map(u8::from_le_bytes))
    }

    /// At `nat16`.
    pub fn nat16(self) -> Outcome<u16> {
        Ok(self.fixed(Primitive::Nat16)?.map(u16::from_le_bytes))
    }

    /// At `nat32`.
    pub fn nat32(self) -> Outcome<u32> {
        Ok(self.fixed(Primitive::Nat32)?.map(u32::from_le_bytes))
    }

    /// At `nat64`.
    pub fn nat64(self) -> Outcome<u64> {
        Ok(self.fixed(Primitive::Nat64)?.map(u64::from_le_bytes))
    }

    /// At `int8`.
    pub fn int8(self) -> Outcome<i8> {
        Ok(self.fixed(Primitive::Int8)?.map(i8::from_le_bytes))
    }

    /// At `int16`.
    pub fn int16(self) -> Outcome<i16> {
        Ok(self.fixed(Primitive::Int16)?.map(i16::from_le_bytes))
    }

    /// At `int32`.
    pub fn int32(self) -> Outcome<i32> {
        Ok(self.fixed(Primitive::Int32)?.map(i32::from_le_bytes))
    }

    /// At `int64`.
    pub fn int64(self) -> Outcome<i64> {
        Ok(self.fixed(Primitive::Int64)?.map(i64::from_le_bytes))
    }

    /// At `float32`, bit for bit.
    pub fn float32(self) -> Outcome<f32> {
        Ok(self
            .fixed(Primitive::Float32)?
            .map(|b| f32::from_bits(u32::from_le_bytes(b))))
    }

    /// At `float64`, bit for bit.
    pub fn float64(self) -> Outcome<f64> {
        Ok(self
            .fixed(Primitive::Float64)?
            .map(|b| f64::from_bits(u64::from_le_bytes(b))))
    }

    /// At `text`, borrowed from the message.
    pub fn text(self) -> Outcome<&'a str> {
        Ok(match self.primitive(Primitive::Text)? {
            Some(Scalar::Text(s)) => Some(s),
            _ => None,
        })
    }

    /// At `principal`: a principal, or a service reference, which coerces to its
    /// principal. Its bytes, borrowed from the message.
    pub fn principal(self) -> Outcome<&'a [u8]> {
        Ok(match self.primitive(Primitive::Principal)? {
            Some(Scalar::Principal(id)) => Some(id),
            _ => None,
        })
    }

    /// At a `service`: a reference to one whose type is a subtype of the receiver's. Its
    /// principal's bytes.
    pub fn service(mut self) -> Outcome<&'a [u8]> {
        self.check(
            matches!(self.composite(), Some(Composite::Service(_))),
            "service",
        )?;
        match self.value {
            Some(p) if matches!(self.sender_composite(p), Some(Composite::Service(_))) => {
                self.begin();
                self.cursor.charge()?;
                let id = self.cursor.id()?;
                Ok(self.reference_coerces(p)?.then_some(id))
            }
            _ => self.skip().map(|()| None),
        }
    }

    /// At a `func`: a reference to one whose type is a subtype of the receiver's. Its
    /// service's principal's bytes, and the method's name.
    pub fn func(mut self) -> Outcome<(&'a [u8], &'a str)> {
        self.check(
            matches!(self.composite(), Some(Composite::Func { .. })),
            "func",
        )?;
        match self.value {
            Some(p) if matches!(self.sender_composite(p), Some(Composite::Func { .. })) => {
                self.begin();
                self.cursor.charge()?;
                let reference = self.cursor.func()?;
                Ok(self.reference_coerces(p)?.then_some(reference))
            }
            _ => self.skip().map(|()| None),
        }
    }

    fn reference_coerces(&mut self, p: Pending) -> Read<bool> {
        match self.sender.root(p.slot) {
            Some(t) => self.cursor.coerces(t, self.expected),
            None => Ok(false),
        }
    }

    /// At a type from a later version of Candid: a value of that same type, which is
    /// skipped, since nothing more of it can be known.
    pub fn future(self) -> Outcome<()> {
        let Some(Composite::Future { opcode, data }) = self.composite() else {
            return Err(self.mismatch("future"));
        };
        let same = self.value.is_some_and(|p| {
            matches!(self.sender_composite(p),
                Some(Composite::Future { opcode: o, data: d }) if o == opcode && d == data)
        });
        self.skip()?;
        Ok(same.then_some(()))
    }

    fn mismatch(&self, method: &'static str) -> DecodeError {
        match self.check(false, method) {
            Err(e) => e,
            Ok(()) => DecodeError::new(self.cursor.position(), Rejection::EndOfInput),
        }
    }

    /// At an `opt`: `None` for `null`, or the value under it, which `inner` reads at the
    /// receiver's type under the `opt`. If that fails, the `opt` is `null`: never a
    /// failure.
    pub fn opt<T>(
        mut self,
        inner: impl FnOnce(ValueReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<Option<T>> {
        let Some(&Composite::Opt(u)) = self.composite() else {
            return Err(self.mismatch("opt"));
        };
        let u = self.child(u)?;
        let Some(p) = self.value else {
            return Ok(Some(None));
        };
        if accepts_null(self.sender, p.slot) {
            self.begin();
            let Some(&Composite::Opt(t)) = self.sender_composite(p) else {
                // `null` or `reserved`: `null` at any option.
                self.cursor.skip(self.sender, p)?;
                return Ok(Some(None));
            };
            self.cursor.charge()?;
            if !self.cursor.opt_tag()? {
                return Ok(Some(None));
            }
            let value = Some(Pending { slot: t, stall: 0 });
            let v = self.part(value, u, inner)?;
            Ok(self.recover(v))
        } else {
            // The sender's value has no `null`: it is the value under the option, if it
            // coerces to the receiver's type there -- the same value, read one option
            // deeper. At an infinite option that question has no answer: the value is
            // skipped, and is undefined, which no enclosing `opt` recovers from.
            if self.cursor.is_infinite_option(u) {
                self.begin();
                let at = self.cursor.position();
                self.cursor.skip(self.sender, p)?;
                self.cursor.undefined.get_or_insert(at);
                return Ok(None);
            }
            let v = self.part(Some(p), u, inner)?;
            Ok(self.recover(v))
        }
    }

    /// The value under an `opt`, or `null` if it failed -- unless it is undefined, which
    /// stays a failure: `Outcome.recover` of `lean/Candid/DecodeAt.lean`.
    fn recover<T>(&self, v: Option<T>) -> Option<Option<T>> {
        match (v, self.cursor.undefined) {
            (_, Some(_)) => None,
            (v, None) => Some(v),
        }
    }

    /// Read a part of this value, `value` at the receiver's `u`, with `read`, one level
    /// deeper: and skip it if `read` does not.
    fn part<T>(
        &mut self,
        value: Option<Pending>,
        u: Root<'r>,
        read: impl FnOnce(ValueReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<T> {
        self.cursor.enter()?;
        let v = read(ValueReader::new(self.cursor, self.sender, value, u)?)?;
        self.cursor.settle(self.sender)?;
        self.cursor.leave();
        Ok(v)
    }

    /// At a `vec`: each value, read by `element` at the receiver's element type, in
    /// order. If one fails, the vector does.
    pub fn vec<T>(
        mut self,
        mut element: impl FnMut(ValueReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<Vec<T>> {
        let Some(&Composite::Vec(u)) = self.composite() else {
            return Err(self.mismatch("vec"));
        };
        let u = self.child(u)?;
        let Some(p) = self.value else {
            return Ok(None);
        };
        let Some(&Composite::Vec(t)) = self.sender_composite(p) else {
            return self.skip().map(|()| None);
        };
        self.begin();
        self.cursor.charge()?;
        let n = self.cursor.reader.unsigned()?;
        // Nothing is reserved for `n`, which the sender chose: the values arrive, or the
        // bytes or the count run out first.
        let mut values = Vec::new();
        for i in 0..n {
            let value = Some(Pending { slot: t, stall: 0 });
            match self.part(value, u, &mut element)? {
                Some(v) => values.push(v),
                None => {
                    self.cursor.skip_elements(self.sender, t, n - i - 1)?;
                    return Ok(None);
                }
            }
        }
        Ok(Some(values))
    }

    /// At `vec nat8`, all at once, borrowed from the message: what [`ValueReader::vec`]
    /// and [`ValueReader::nat8`] for each would read.
    pub fn blob(mut self) -> Outcome<&'a [u8]> {
        self.check(
            self.composite() == Some(&Composite::Vec(Slot::NAT8)),
            "blob",
        )?;
        let Some(p) = self.value else {
            return Ok(None);
        };
        let Some(&Composite::Vec(t)) = self.sender_composite(p) else {
            return self.skip().map(|()| None);
        };
        self.begin();
        self.cursor.charge()?;
        let n = self.cursor.reader.unsigned()?;
        // Each element would be read one level deeper.
        if n > 0 {
            self.cursor.enter()?;
            self.cursor.leave();
        }
        if t == Slot::NAT8 {
            return self.cursor.bytes_counted(n).map(Some);
        }
        // Another element type: the empty vector coerces, and no other. The first element
        // would be handed out, and fail.
        if n > 0 {
            self.cursor.receive()?;
        }
        self.cursor.skip_elements(self.sender, t, n)?;
        Ok((n == 0).then_some(&[]))
    }

    /// At a `variant`: the alternative's id, and its value, which `alternative` reads at
    /// the receiver's type for it. An alternative the receiver's type does not have
    /// fails.
    pub fn variant<T>(
        mut self,
        alternative: impl FnOnce(FieldId, ValueReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<T> {
        let Some(Composite::Variant(expected)) = self.composite() else {
            return Err(self.mismatch("variant"));
        };
        let Some(p) = self.value else {
            return Ok(None);
        };
        let Some(Composite::Variant(alternatives)) = self.sender_composite(p) else {
            return self.skip().map(|()| None);
        };
        self.begin();
        self.cursor.charge()?;
        let (id, t) = self.cursor.alternative(alternatives)?;
        let value = Pending { slot: t, stall: 0 };
        match expected.binary_search_by_key(&id, |&(f, _)| f) {
            Ok(k) => {
                let u = self.child(expected[k].1)?;
                self.part(Some(value), u, |r| alternative(id, r))
            }
            Err(_) => {
                self.cursor.skip_part(self.sender, value)?;
                Ok(None)
            }
        }
    }

    /// At a `record`: its fields, which `fields` reads through a [`RecordReader`], in
    /// ascending order of id. If one fails, the record does.
    pub fn record<T>(
        mut self,
        fields: impl FnOnce(&mut RecordReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<T> {
        let Some(Composite::Record(expected)) = self.composite() else {
            return Err(self.mismatch("record"));
        };
        let Some(p) = self.value else {
            return Ok(None);
        };
        let Some(Composite::Record(sent)) = self.sender_composite(p) else {
            return self.skip().map(|()| None);
        };
        self.begin();
        self.cursor.charge()?;
        self.cursor.record_stall(self.sender, p.stall)?;
        let mut record = RecordReader {
            start: self.cursor.position(),
            cursor: &mut *self.cursor,
            sender: self.sender,
            receiver: self.expected.table(),
            sent,
            expected,
            next_sent: 0,
            next_expected: 0,
            stall: p.stall + 1,
            failed: false,
        };
        let value = fields(&mut record)?;
        // A record the receiver gives up on has failed, as one whose field fails has:
        // nothing more of it is read at the receiver's types.
        if value.is_none() {
            record.failed = true;
        }
        record.finish()?;
        let failed = record.failed;
        Ok(if failed { None } else { value })
    }
}

/// The fields of a record being read: ask for each of the receiver's, in ascending id,
/// with [`RecordReader::field`].
///
/// The sender's fields come in ascending id too, so the two are walked together: a
/// sender's field the receiver does not have is skipped, and a receiver's field the
/// sender does not have is read as a value the message lacks -- `null` if its type
/// accepts it, a failure if not. A field the receiver does not ask for is still read at
/// its type, and its outcome counts: the receiver's type decides the record, not which
/// fields the receiver keeps.
#[derive(Debug)]
pub struct RecordReader<'r, 'a> {
    cursor: &'r mut Cursor<'a>,
    sender: &'r TypeTable,
    receiver: &'r TypeTable,
    /// The sender's fields, in ascending id.
    sent: &'r [(FieldId, Slot)],
    /// The receiver's fields, in ascending id.
    expected: &'r [(FieldId, Slot)],
    next_sent: usize,
    next_expected: usize,
    /// The stall of the last sender's field, and where it started.
    stall: usize,
    start: usize,
    /// Whether a field has failed, which decides the record.
    failed: bool,
}

impl<'a> RecordReader<'_, 'a> {
    /// The next of the receiver's fields not asked for yet, if any is left. `None` once a
    /// field has failed, which decides the record: there is nothing more to ask for.
    pub fn next_field(&self) -> Option<FieldId> {
        if self.failed {
            return None;
        }
        self.expected.get(self.next_expected).map(|&(id, _)| id)
    }

    /// Field `id`, read by `read` at the receiver's type for it. Fields are asked for in
    /// ascending id; one skipped over is read anyway, and dropped.
    ///
    /// `Ok(None)` once a field has failed, which decides the record: nothing more of it is
    /// read at the receiver's types.
    pub fn field<T>(
        &mut self,
        id: FieldId,
        read: impl FnOnce(ValueReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<T> {
        let Some(k) = self.expected[self.next_expected..]
            .iter()
            .position(|&(f, _)| f == id)
        else {
            return self.cursor.fail(Rejection::FieldNotExpected(id));
        };
        for _ in 0..k {
            if self.failed {
                break;
            }
            self.next(Discard::try_decode)?;
        }
        if self.failed {
            return Ok(None);
        }
        self.next(read)
    }

    /// The receiver's next field, read by `read`.
    fn next<T>(&mut self, read: impl FnOnce(ValueReader<'_, 'a>) -> Outcome<T>) -> Outcome<T> {
        let Some(&(id, u)) = self.expected.get(self.next_expected) else {
            return Ok(None);
        };
        self.next_expected += 1;
        while let Some(&(sent, t)) = self.sent.get(self.next_sent) {
            if sent >= id {
                break;
            }
            self.skip_sent(t)?;
        }
        let value = match self.sent.get(self.next_sent) {
            Some(&(sent, t)) if sent == id => {
                self.next_sent += 1;
                Some(Pending {
                    slot: t,
                    stall: self.sent_stall(),
                })
            }
            _ => None,
        };
        let Some(u) = self.receiver.root(u) else {
            return self.cursor.fail(Rejection::ReceiverMismatch {
                expected: u,
                method: "a type that does not resolve",
            });
        };
        self.cursor.enter()?;
        let v = read(ValueReader::new(self.cursor, self.sender, value, u)?)?;
        self.cursor.settle(self.sender)?;
        self.cursor.leave();
        if v.is_none() {
            self.failed = true;
        }
        Ok(v)
    }

    /// The stall of the sender's next field: the last one's, if it started here too.
    fn sent_stall(&mut self) -> usize {
        let here = self.cursor.position();
        if here != self.start {
            self.stall = 0;
        }
        self.start = here;
        self.stall
    }

    /// Skip the sender's next field.
    fn skip_sent(&mut self, slot: Slot) -> Read<()> {
        self.next_sent += 1;
        let stall = self.sent_stall();
        self.cursor.skip_part(self.sender, Pending { slot, stall })
    }

    /// The rest of the record: the receiver's fields not asked for, unless one has failed,
    /// then the sender's fields left.
    fn finish(&mut self) -> Read<()> {
        while !self.failed && self.next_expected < self.expected.len() {
            self.next(Discard::try_decode)?;
        }
        while let Some(&(_, t)) = self.sent.get(self.next_sent) {
            self.skip_sent(t)?;
        }
        Ok(())
    }
}

/// A receiver that follows the receiver's type and keeps nothing: for a field the
/// receiver did not ask for, whose outcome still counts.
pub(crate) struct Discard;

impl<'a> Decode<'a> for Discard {
    fn try_decode(reader: ValueReader<'_, 'a>) -> Outcome<Self> {
        fn kept<T>(o: Option<T>) -> Option<Discard> {
            o.map(|_| Discard)
        }
        let expected = reader.expected();
        Ok(match (expected.slot(), expected.composite()) {
            (Slot::Primitive(p), _) => match p {
                Primitive::Null => kept(reader.null()?),
                Primitive::Bool => kept(reader.bool()?),
                Primitive::Nat => kept(reader.nat()?),
                Primitive::Int => kept(reader.int()?),
                Primitive::Nat8 => kept(reader.nat8()?),
                Primitive::Nat16 => kept(reader.nat16()?),
                Primitive::Nat32 => kept(reader.nat32()?),
                Primitive::Nat64 => kept(reader.nat64()?),
                Primitive::Int8 => kept(reader.int8()?),
                Primitive::Int16 => kept(reader.int16()?),
                Primitive::Int32 => kept(reader.int32()?),
                Primitive::Int64 => kept(reader.int64()?),
                Primitive::Float32 => kept(reader.float32()?),
                Primitive::Float64 => kept(reader.float64()?),
                Primitive::Text => kept(reader.text()?),
                Primitive::Reserved => kept(reader.reserved()?),
                Primitive::Empty => kept(reader.empty()?),
                Primitive::Principal => kept(reader.principal()?),
            },
            (_, Some(Composite::Opt(_))) => kept(reader.opt(Discard::try_decode)?),
            (_, Some(Composite::Vec(Slot::NAT8))) => kept(reader.blob()?),
            (_, Some(Composite::Vec(_))) => kept(reader.vec(Discard::try_decode)?),
            (_, Some(Composite::Record(fields))) => reader.record(|r| {
                for &(id, _) in fields {
                    if r.field(id, Discard::try_decode)?.is_none() {
                        return Ok(None);
                    }
                }
                Ok(Some(Discard))
            })?,
            (_, Some(Composite::Variant(_))) => reader.variant(|_, r| Discard::try_decode(r))?,
            (_, Some(Composite::Func { .. })) => kept(reader.func()?),
            (_, Some(Composite::Service(_))) => kept(reader.service()?),
            (_, Some(Composite::Future { .. })) => kept(reader.future()?),
            (Slot::Ref(_), None) => kept(reader.null()?),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Decoder, Encoder, Header, Limits};
    use alloc::vec;
    use candid_types::{RawTypeTable, TypeRef};

    fn r(i: usize) -> Slot {
        Slot::Ref(TypeRef::new(i))
    }

    fn table(entries: Vec<Composite>) -> TypeTable {
        RawTypeTable::from(entries).check().unwrap()
    }

    /// A message of one value at `t`, written by `write`.
    fn message(
        entries: Vec<Composite>,
        t: Slot,
        write: impl FnOnce(crate::ValueWriter<'_>) -> Result<(), crate::EncodeError>,
    ) -> Vec<u8> {
        let mut e = Encoder::new(Header::new(table(entries), vec![t]).unwrap());
        write(e.argument().unwrap()).unwrap();
        e.finish().unwrap()
    }

    /// Read `bytes`' one argument at `u` in `receiver` with `read`, then finish.
    fn read<'a, T>(
        bytes: &'a [u8],
        receiver: &TypeTable,
        u: Slot,
        limits: Limits,
        read: impl FnOnce(ValueReader<'_, 'a>) -> Outcome<T>,
    ) -> Outcome<T> {
        let mut d = Decoder::with_limits(bytes, limits)?;
        let v = d.argument_with(receiver.root(u).unwrap(), read)?;
        d.finish()?;
        Ok(v)
    }

    #[test]
    fn borrowed_from_the_message() {
        let bytes = message(vec![], Slot::TEXT, |w| w.text("hello"));
        let none = TypeTable::default();
        let s = read(&bytes, &none, Slot::TEXT, Limits::default(), |r| r.text());
        assert_eq!(s, Ok(Some("hello")));
        let blobs = vec![Composite::Vec(Slot::NAT8)];
        let bytes = message(blobs.clone(), r(0), |w| w.blob(&[1, 2, 3]));
        let b = read(&bytes, &table(blobs), r(0), Limits::default(), |r| r.blob());
        assert_eq!(b, Ok(Some(&[1u8, 2, 3][..])));
    }

    #[test]
    fn a_blob_reads_as_its_elements_would() {
        let blobs = vec![Composite::Vec(Slot::NAT8)];
        let bytes = message(blobs.clone(), r(0), |w| w.blob(&[7, 8]));
        let t = table(blobs);
        let each = read(&bytes, &t, r(0), Limits::default(), |r| r.vec(|e| e.nat8()));
        assert_eq!(each, Ok(Some(vec![7, 8])));
        // Each byte counts as a value, as each element would: three in all.
        let mut limits = Limits {
            values: 2,
            ..Limits::default()
        };
        let e = read(&bytes, &t, r(0), limits, |r| r.blob()).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::TooManyValues);
        limits.values = 3;
        assert!(read(&bytes, &t, r(0), limits, |r| r.blob()).is_ok());
    }

    #[test]
    fn a_blob_fails_where_its_elements_would() {
        let blobs = vec![Composite::Vec(Slot::NAT8)];
        let bytes = message(blobs.clone(), r(0), |w| w.blob(&[7, 8]));
        let t = table(blobs);
        let both = |bytes: &[u8], limits: Limits| {
            let blob = read(bytes, &t, r(0), limits, |r| r.blob()).map(|b| b.map(<[u8]>::to_vec));
            let each = read(bytes, &t, r(0), limits, |r| r.vec(|e| e.nat8()));
            assert_eq!(blob, each);
            blob.unwrap_err()
        };
        // The count runs out at the second byte: the vector and the first are counted.
        let limits = Limits {
            values: 2,
            ..Limits::default()
        };
        let e = both(&bytes, limits);
        assert_eq!(
            (e.position(), e.rejection()),
            (bytes.len() - 1, &Rejection::TooManyValues)
        );
        // The bytes run out at the second byte.
        let cut = &bytes[..bytes.len() - 1];
        let e = both(cut, Limits::default());
        assert_eq!(
            (e.position(), e.rejection()),
            (cut.len(), &Rejection::EndOfInput)
        );
        // Both at once: the count, which comes first.
        let e = both(cut, limits);
        assert_eq!(e.rejection(), &Rejection::TooManyValues);
        // Each element would be one level deeper.
        let flat = Limits {
            depth: 0,
            ..Limits::default()
        };
        assert_eq!(both(&bytes, flat).rejection(), &Rejection::TooDeep);
        // Each element would be handed to the receiver: the vector and the first are.
        let handed = Limits {
            received: 2,
            ..Limits::default()
        };
        let e = both(&bytes, handed);
        assert_eq!(
            (e.position(), e.rejection()),
            (bytes.len() - 1, &Rejection::TooManyReceived)
        );
        // Handed out, then counted: the first of the two to run out is the answer.
        let e = both(
            &bytes,
            Limits {
                values: 2,
                ..handed
            },
        );
        assert_eq!(e.rejection(), &Rejection::TooManyReceived);
        // Elements of another type: the first is handed out, and fails.
        let ints = vec![Composite::Vec(Slot::INT8)];
        let bytes = message(ints, r(0), |w| {
            let mut v = w.vec(2)?;
            v.element()?.int8(1)?;
            v.element()?.int8(2)?;
            v.finish()
        });
        let t = table(vec![Composite::Vec(Slot::NAT8)]);
        for (received, want) in [(1, Err(Rejection::TooManyReceived)), (2, Ok(None))] {
            let limits = Limits {
                received,
                ..Limits::default()
            };
            let blob = read(&bytes, &t, r(0), limits, |r| r.blob()).map(|b| b.map(<[u8]>::to_vec));
            let each = read(&bytes, &t, r(0), limits, |r| r.vec(|e| e.nat8()));
            assert_eq!(blob, each);
            assert_eq!(blob.map_err(|e| e.rejection().clone()), want);
        }
        let empty = message(vec![Composite::Vec(Slot::NAT8)], r(0), |w| w.blob(&[]));
        let blob = read(&empty, &t, r(0), flat, |r| r.blob());
        assert_eq!(blob, Ok(Some(&[][..])));
    }

    /// A `nat`, then `extra`, read at `type R = opt R`.
    fn at_infinite_option(extra: &[u8], limits: Limits) -> Outcome<Option<()>> {
        let mut bytes = message(vec![], Slot::NAT, |w| w.nat(&[5]));
        bytes.extend_from_slice(extra);
        let receiver = table(vec![Composite::Opt(r(0))]);
        read(&bytes, &receiver, r(0), limits, |r| r.opt(|_| Ok(Some(()))))
    }

    #[test]
    fn an_infinite_option_is_the_answer_last() {
        let e = at_infinite_option(&[], Limits::default()).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::InfiniteOption);
        // An error in the message's bytes is the answer instead.
        let e = at_infinite_option(&[0], Limits::default()).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::BytesAfterValues);
        let none = Limits {
            values: 0,
            ..Limits::default()
        };
        let e = at_infinite_option(&[], none).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::TooManyValues);
    }

    #[test]
    fn an_infinite_option_is_not_null_under_an_opt() {
        // `opt vec R`, with `type R = opt R`, and `vec {5}` sent: the element is undefined,
        // and so the vector is, which the outer `opt` does not make `null`.
        let nats = vec![Composite::Vec(Slot::NAT)];
        let bytes = message(nats, r(0), |w| {
            let mut v = w.vec(1)?;
            v.element()?.nat(&[5])?;
            v.finish()
        });
        let receiver = table(vec![
            Composite::Opt(r(0)),
            Composite::Opt(r(2)),
            Composite::Vec(r(0)),
        ]);
        let mut seen = None;
        let got = read(&bytes, &receiver, r(1), Limits::default(), |r| {
            let v = r.opt(|v| v.vec(|e| e.opt(|_| Ok(Some(())))));
            seen = Some(v.clone());
            v
        });
        assert_eq!(got.unwrap_err().rejection(), &Rejection::InfiniteOption);
        // What the receiver saw: a failure, not `null`.
        assert_eq!(seen, Some(Ok(None)));
    }

    #[test]
    fn a_record_is_one_level_deep() {
        let entries = vec![Composite::Record(vec![(FieldId::new(0), Slot::NAT8)])];
        let bytes = message(entries.clone(), r(0), |w| {
            let mut rec = w.record()?;
            rec.field(FieldId::new(0))?.nat8(1)?;
            rec.finish()
        });
        let t = table(entries);
        let at = |depth| {
            let limits = Limits {
                depth,
                ..Limits::default()
            };
            read(&bytes, &t, r(0), limits, |r| {
                r.record(|rec| rec.field(FieldId::new(0), |r| r.nat8()))
            })
        };
        assert_eq!(at(1), Ok(Some(1)));
        assert_eq!(at(0).unwrap_err().rejection(), &Rejection::TooDeep);
        // An empty record has no level below it.
        let empty = vec![Composite::Record(vec![])];
        let bytes = message(empty.clone(), r(0), |w| w.record()?.finish());
        let flat = Limits {
            depth: 0,
            ..Limits::default()
        };
        let got = read(&bytes, &table(empty), r(0), flat, |r| {
            r.record(|_| Ok(Some(())))
        });
        assert_eq!(got, Ok(Some(())));
    }

    #[test]
    fn a_record_the_receiver_gives_up_on_has_failed() {
        // `opt record {0 : nat; 1 : R}`, with `type R = opt R`, and `{0 = 1; 1 = 5}` sent.
        // The receiver gives up before field 1, which is not read at `R`: the record
        // fails, and the `opt` is `null`.
        let sent = vec![Composite::Record(vec![
            (FieldId::new(0), Slot::NAT),
            (FieldId::new(1), Slot::NAT),
        ])];
        let bytes = message(sent, r(0), |w| {
            let mut rec = w.record()?;
            rec.field(FieldId::new(0))?.nat(&[1])?;
            rec.field(FieldId::new(1))?.nat(&[5])?;
            rec.finish()
        });
        let receiver = table(vec![
            Composite::Opt(r(0)),
            Composite::Record(vec![(FieldId::new(0), Slot::NAT), (FieldId::new(1), r(0))]),
            Composite::Opt(r(1)),
        ]);
        let got = read(&bytes, &receiver, r(2), Limits::default(), |r| {
            r.opt(|v| v.record(|_| Ok(None::<()>)))
        });
        assert_eq!(got, Ok(Some(None)));
    }

    #[test]
    fn a_principal_is_rejected_by_its_length() {
        // Flag 1 and a length of 30, then nothing: too long, whatever follows.
        let bytes = [b'D', b'I', b'D', b'L', 0x00, 0x01, 0x68, 0x01, 0x1e];
        let none = TypeTable::default();
        let e = read(&bytes, &none, Slot::PRINCIPAL, Limits::default(), |r| {
            r.principal()
        });
        let e = e.unwrap_err();
        assert_eq!(
            (e.position(), e.rejection()),
            (8, &Rejection::PrincipalTooLong)
        );
        // A length of 29 is read on, and runs out of bytes.
        let mut short = bytes;
        short[8] = 0x1d;
        let e = read(&short, &none, Slot::PRINCIPAL, Limits::default(), |r| {
            r.principal()
        });
        let e = e.unwrap_err();
        assert_eq!((e.position(), e.rejection()), (9, &Rejection::EndOfInput));
    }

    #[test]
    fn no_field_is_next_once_one_has_failed() {
        // A receiver that asks for fields while there are any, and ignores failures: the
        // first failure ends the record, rather than offering the same field forever.
        let (bytes, entries) = three_nats();
        let mut receiver = entries.clone();
        receiver[0] = Composite::Record(vec![
            (FieldId::new(1), Slot::TEXT),
            (FieldId::new(2), Slot::NAT),
            (FieldId::new(3), Slot::NAT),
        ]);
        let mut asked = 0;
        let got = read(&bytes, &table(receiver), r(0), Limits::default(), |r| {
            r.record(|rec| {
                while let Some(id) = rec.next_field() {
                    asked += 1;
                    let _ = rec.field(id, Discard::try_decode)?;
                }
                Ok(Some(()))
            })
        });
        assert_eq!((got, asked), (Ok(None), 1));
    }

    #[test]
    fn a_receiver_calls_the_method_for_its_type() {
        let bytes = message(vec![], Slot::NAT, |w| w.nat(&[5]));
        let none = TypeTable::default();
        let e = read(&bytes, &none, Slot::NAT, Limits::default(), |r| r.text()).unwrap_err();
        assert_eq!(
            e.rejection(),
            &Rejection::ReceiverMismatch {
                expected: Slot::NAT,
                method: "text"
            }
        );
        // `int` reads a `nat` too, which coerces.
        let i = read(&bytes, &none, Slot::INT, Limits::default(), |r| r.int());
        assert_eq!(i.unwrap().and_then(|i| i.to_i64()), Some(5));
        // A `nat` does not coerce to `text`: a failure, not an error.
        let s = read(&bytes, &none, Slot::TEXT, Limits::default(), |r| r.text());
        assert_eq!(s, Ok(None));
    }

    /// `record {1 : nat; 2 : nat; 3 : nat}`, sent as `{1 = 1; 2 = 2; 3 = 3}`.
    fn three_nats() -> (Vec<u8>, Vec<Composite>) {
        let entries = vec![Composite::Record(vec![
            (FieldId::new(1), Slot::NAT),
            (FieldId::new(2), Slot::NAT),
            (FieldId::new(3), Slot::NAT),
        ])];
        let bytes = message(entries.clone(), r(0), |w| {
            let mut rec = w.record()?;
            for i in 1..=3 {
                rec.field(FieldId::new(i))?.nat(&[i as u8])?;
            }
            rec.finish()
        });
        (bytes, entries)
    }

    #[test]
    fn fields_in_ascending_order() {
        let (bytes, entries) = three_nats();
        let t = table(entries);
        let got = read(&bytes, &t, r(0), Limits::default(), |r| {
            r.record(|rec| {
                // Field 1 is skipped over, and read anyway.
                let c = rec.field(FieldId::new(3), |r| r.nat())?;
                Ok(c.and_then(|n| n.to_u64()))
            })
        });
        assert_eq!(got, Ok(Some(3)));
        let e = read(&bytes, &t, r(0), Limits::default(), |r| {
            r.record(|rec| {
                rec.field(FieldId::new(2), |r| r.nat())?;
                rec.field(FieldId::new(1), |r| r.nat())
            })
        })
        .unwrap_err();
        assert_eq!(e.rejection(), &Rejection::FieldNotExpected(FieldId::new(1)));
    }

    #[test]
    fn a_field_not_asked_for_still_decides_the_record() {
        let (bytes, _) = three_nats();
        // The receiver's field 2 is `text`: a `nat` does not coerce to it. The record
        // fails though the receiver asks only for field 3 -- and so does the `opt`
        // around it, to `null`.
        let receiver = table(vec![
            Composite::Record(vec![
                (FieldId::new(2), Slot::TEXT),
                (FieldId::new(3), Slot::NAT),
            ]),
            Composite::Opt(r(0)),
        ]);
        let got = read(&bytes, &receiver, r(1), Limits::default(), |r| {
            r.opt(|r| r.record(|rec| rec.field(FieldId::new(3), |r| r.nat())))
        });
        assert!(matches!(got, Ok(Some(None))));
        // Not asking for any field changes nothing.
        let got = read(&bytes, &receiver, r(1), Limits::default(), |r| {
            r.opt(|r| r.record(|_| Ok(Some(()))))
        });
        assert_eq!(got, Ok(Some(None)));
    }

    #[test]
    fn a_value_the_receiver_drops_is_skipped() {
        let (bytes, entries) = three_nats();
        let t = table(entries);
        let got = read(&bytes, &t, r(0), Limits::default(), |_| Ok(Some(())));
        assert_eq!(got, Ok(Some(())));
        let got = read(&bytes, &t, r(0), Limits::default(), |r| {
            r.record(|rec| rec.field(FieldId::new(1), |_| Ok(Some(()))))
        });
        assert_eq!(got, Ok(Some(())));
    }

    #[test]
    fn depth_is_limited() {
        // `type R = opt R`, `null` seven options deep.
        let entries = vec![Composite::Opt(r(0))];
        let bytes = message(entries.clone(), r(0), |w| {
            let mut w = w;
            for _ in 0..7 {
                w = w.opt()?;
            }
            w.null()
        });
        fn depth(r: ValueReader<'_, '_>) -> Outcome<usize> {
            Ok(r.opt(depth)?.map(|d| d.map_or(0, |d| d + 1)))
        }
        let t = table(entries);
        let mut limits = Limits {
            depth: 7,
            ..Limits::default()
        };
        assert_eq!(read(&bytes, &t, r(0), limits, depth), Ok(Some(7)));
        limits.depth = 6;
        let e = read(&bytes, &t, r(0), limits, depth).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::TooDeep);
        assert!(e.rejection().is_resource_limit());
    }

    /// The least depth at which `decode` gets past a message's values: below it,
    /// `TooDeep`.
    fn least_depth(decode: impl Fn(Limits) -> Result<(), DecodeError>) -> usize {
        let with = |depth| Limits {
            depth: depth as usize,
            ..Limits::default()
        };
        least(with, Rejection::TooDeep, decode) as usize
    }

    #[test]
    fn a_skipped_value_is_as_deep_as_a_read_one() {
        // `type R = opt R`, seven options deep: its deepest value is seven levels below it,
        // wherever it is, read or skipped.
        let deep = [1, 1, 1, 1, 1, 1, 1, 0];
        let with = |header: &[u8], before: &[u8]| -> Vec<u8> {
            [b"DIDL", header, before, &deep[..]].concat()
        };
        let decoded = |r: Outcome<()>| r.map(drop);
        let opt_r = Composite::Opt(r(0));

        // Read by the receiver.
        let bytes = with(&[1, 0x6e, 0, 1, 0], &[]);
        let t = table(vec![opt_r.clone()]);
        let depth = |r: ValueReader<'_, '_>| -> Outcome<()> {
            fn depth(r: ValueReader<'_, '_>) -> Outcome<()> {
                Ok(r.opt(depth)?.map(drop))
            }
            depth(r)
        };
        assert_eq!(
            least_depth(|l| decoded(read(&bytes, &t, r(0), l, depth))),
            7
        );
        // An argument the receiver does not expect.
        let skipped = |l| Decoder::with_limits(&bytes, l)?.finish();
        assert_eq!(least_depth(skipped), 7);
        // An argument at `reserved`.
        let none = TypeTable::default();
        let reserved = |l| decoded(read(&bytes, &none, Slot::RESERVED, l, |r| r.reserved()));
        assert_eq!(least_depth(reserved), 7);

        // A field the receiver's record does not have: one level down.
        let bytes = with(&[2, 0x6e, 0, 0x6c, 1, 0, 0, 1, 1], &[]);
        let t = table(vec![Composite::Record(vec![])]);
        let unknown = |l| decoded(read(&bytes, &t, r(0), l, |r| r.record(|_| Ok(Some(())))));
        assert_eq!(least_depth(unknown), 8);
        // A field the receiver drops unread.
        let t = table(vec![Composite::Record(vec![(FieldId::new(0), Slot::NULL)])]);
        let dropped = |l| {
            decoded(read(&bytes, &t, r(0), l, |r| {
                r.record(|f| f.field(FieldId::new(0), |_| Ok(Some(()))))
            }))
        };
        assert_eq!(least_depth(dropped), 8);

        // An alternative the receiver's variant does not have: one level down.
        let bytes = with(&[2, 0x6e, 0, 0x6b, 1, 0, 0, 1, 1], &[0]);
        let t = table(vec![Composite::Variant(vec![(
            FieldId::new(1),
            Slot::NULL,
        )])]);
        let unknown = |l| decoded(read(&bytes, &t, r(0), l, |r| r.variant(|_, r| r.null())));
        assert_eq!(least_depth(unknown), 8);

        // The elements after one that fails: an element is one level down, and the deep
        // one is under an alternative, one more. The first element, alternative 0, fails.
        let bytes = with(
            &[3, 0x6e, 0, 0x6b, 2, 0, 0x7f, 1, 0, 0x6d, 1, 1, 2],
            &[2, 0, 1],
        );
        let t = table(vec![
            Composite::Vec(r(1)),
            Composite::Variant(vec![(FieldId::new(2), Slot::NULL)]),
        ]);
        let rest = |l| {
            decoded(read(&bytes, &t, r(0), l, |r| {
                r.vec(|r| r.variant(|_, r| r.null())).map(|v| v.map(drop))
            }))
        };
        assert_eq!(least_depth(rest), 9);
    }

    /// The least `limit` for which `decode` succeeds, given limits from `with`: below
    /// it, the rejection `over`.
    fn least(
        with: impl Fn(u64) -> Limits,
        over: Rejection,
        decode: impl Fn(Limits) -> Result<(), DecodeError>,
    ) -> u64 {
        let least = (1..10_000)
            .find(|&n| decode(with(n)).is_ok())
            .expect("decodes within 10,000");
        assert_eq!(decode(with(least - 1)).unwrap_err().rejection(), &over);
        least
    }

    fn received(n: u64) -> Limits {
        Limits {
            received: n,
            ..Limits::default()
        }
    }

    #[test]
    fn values_handed_to_the_receiver_are_counted() {
        let decoded = |r: Outcome<Discard>| r.map(drop);
        let least_received = |bytes: &[u8], t: &TypeTable, u: Slot| {
            least(received, Rejection::TooManyReceived, |l| {
                decoded(read(bytes, t, u, l, Discard::try_decode))
            })
        };
        // Ten empty records, read as records of three `opt nat`s the sender does not
        // have: the argument, ten elements, thirty fields, in two values of the message.
        let bytes = [b"DIDL".as_slice(), &[2, 0x6c, 0, 0x6d, 0, 1, 1, 10]].concat();
        let fields = (0..3).map(|i| (FieldId::new(i), r(2))).collect();
        let t = table(vec![
            Composite::Record(fields),
            Composite::Vec(r(0)),
            Composite::Opt(Slot::NAT),
        ]);
        assert_eq!(least_received(&bytes, &t, r(1)), 41);
        // A `nat` read as `opt opt nat`: an `opt` around it is a value the message lacks.
        let bytes = [b"DIDL".as_slice(), &[0, 1, 0x7d, 5]].concat();
        let t = table(vec![Composite::Opt(r(1)), Composite::Opt(Slot::NAT)]);
        assert_eq!(least_received(&bytes, &t, r(0)), 3);
        // An argument past the sender's last.
        let bytes = [b"DIDL".as_slice(), &[0, 0]].concat();
        assert_eq!(least_received(&bytes, &t, r(1)), 1);
    }

    #[test]
    fn reference_checks_are_counted_once_for_each_pair() {
        // References of `func (V) -> ()`, where `V` is a cycle of three
        // `variant { 0: next; 1: null }`, read at `func (P) -> ()`, with `P` the same in
        // one entry. The message's table has those four entries and `extra`, at most one.
        let message = |extra: &[u8], types: &[u8], values: &[u8], references: u8| {
            let mut m = b"DIDL".to_vec();
            m.push(4 + u8::from(!extra.is_empty()));
            m.extend([0x6b, 2, 0, 1, 1, 0x7f, 0x6b, 2, 0, 2, 1, 0x7f]);
            m.extend([0x6b, 2, 0, 0, 1, 0x7f, 0x6a, 1, 0, 0, 0]);
            m.extend(extra);
            m.extend(types);
            m.extend(values);
            for _ in 0..references {
                m.extend([1, 1, 1, 0x2a, 1, b'f']);
            }
            m
        };
        let t = table(vec![
            Composite::Variant(vec![(FieldId::new(0), r(0)), (FieldId::new(1), Slot::NULL)]),
            Composite::Func {
                parameters: vec![r(0)],
                results: vec![],
                annotations: vec![],
            },
            Composite::Vec(r(1)),
        ]);
        let steps = |bytes: &[u8], arguments: Slot, count: usize| {
            let with = |steps| Limits {
                subtype_steps: steps,
                ..Limits::default()
            };
            least(with, Rejection::TooManySubtypeSteps, |l| {
                let mut d = Decoder::with_limits(bytes, l)?;
                for _ in 0..count {
                    d.argument_with(t.root(arguments).unwrap(), Discard::try_decode)?;
                }
                d.finish()
            })
        };
        // A vector of `n` references: one argument, one check.
        let vector = |n| message(&[0x6d, 3], &[1, 4], &[n], n);
        let one = steps(&vector(1), r(2), 1);
        assert!(one > 3, "{one} steps for a cycle of three");
        assert_eq!(steps(&vector(4), r(2), 1), one);
        // Two arguments, each a reference: the answers are kept for one receiver's table,
        // and so for one argument, but the steps are the message's.
        let two = message(&[], &[2, 3, 3], &[], 2);
        assert_eq!(steps(&two, r(1), 2), 2 * one);
    }

    #[test]
    fn values_are_counted_where_they_are_skipped() {
        // `vec null` of a million, as an argument the receiver does not expect.
        let entries = vec![Composite::Vec(Slot::NULL)];
        let bytes = message(entries, r(0), |w| {
            let mut v = w.vec(1_000_000)?;
            for _ in 0..1_000_000 {
                v.element()?.null()?;
            }
            v.finish()
        });
        let mut limits = Limits {
            values: 1_000_000,
            ..Limits::default()
        };
        let e = Decoder::with_limits(&bytes, limits)
            .unwrap()
            .finish()
            .unwrap_err();
        assert_eq!(e.rejection(), &Rejection::TooManyValues);
        limits.values = 1_000_001;
        assert_eq!(
            Decoder::with_limits(&bytes, limits).unwrap().finish(),
            Ok(())
        );
    }

    #[test]
    fn after_a_failed_argument_nothing_more_is_read() {
        let mut e =
            Encoder::new(Header::new(TypeTable::default(), vec![Slot::NAT, Slot::NAT]).unwrap());
        e.argument().unwrap().nat(&[1]).unwrap();
        e.argument().unwrap().nat(&[2]).unwrap();
        let bytes = e.finish().unwrap();
        let none = TypeTable::default();
        let mut d = Decoder::new(&bytes).unwrap();
        let text = none.root(Slot::TEXT).unwrap();
        let nat = none.root(Slot::NAT).unwrap();
        assert_eq!(d.argument_with(text, |r| r.text()), Ok(None));
        let second = d.argument_with(nat, |r| Ok(r.nat()?.and_then(|n| n.to_u64())));
        assert_eq!(second, Ok(None));
        assert_eq!(d.finish(), Ok(()));
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let mut bytes = message(vec![], Slot::NAT, |w| w.nat(&[1]));
        bytes.push(0);
        let e = Decoder::new(&bytes).unwrap().finish().unwrap_err();
        assert_eq!(
            (e.position(), e.rejection()),
            (bytes.len() - 1, &Rejection::BytesAfterValues)
        );
    }
}
