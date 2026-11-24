//! Where a decoder is in a message's values, and what it has spent: the position, the
//! values counted against [`Limits::values`], and the receiver's depth. Reads values at
//! the sender's types alone: a scalar, to hand to a receiver, and any value, to skip it.
//!
//! Skipping is `decodeValue` of `lean/Candid/Wire.lean` with the value thrown away, and
//! counts and rejects exactly as it does, so that a value the receiver drops costs what
//! one it keeps does and is checked as well. It is a loop over a stack of what is left to
//! read, not a recursion: how deep a skipped value nests is the sender's choice.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use candid_types::{Composite, FieldId, Primitive, Root, Slot, TypeTable, is_subtype};

use crate::decoder::Limits;
use crate::error::Rejection;
use crate::reader::{Read, Reader};

/// The most bytes a principal has (`lean/Spec/Types.md`, Section 3.1).
const MAX_PRINCIPAL_LENGTH: u64 = 29;

/// A value of the message not read yet: its type in the sender's table, and how many
/// records on the way to it started where it does (`lean/Candid/Wire.lean`,
/// "Termination").
#[derive(Clone, Copy, Debug)]
pub(crate) struct Pending {
    pub(crate) slot: Slot,
    pub(crate) stall: usize,
}

/// A scalar value, as read at the sender's type.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Scalar<'a> {
    /// `null` or `reserved`, which take no bytes.
    Null,
    Bool(bool),
    /// The bytes of a LEB128 `nat`.
    Nat(&'a [u8]),
    /// The bytes of an SLEB128 `int`.
    Int(&'a [u8]),
    /// A fixed-width number's bytes, least significant first.
    Fixed(&'a [u8]),
    Text(&'a str),
    /// A principal's bytes.
    Principal(&'a [u8]),
}

/// What is left to skip.
enum Work<'t> {
    Value(Pending),
    /// This many more elements of this type.
    Elements(Slot, u64),
    /// These fields of a record, the next with this stall unless bytes were read since
    /// `start`.
    Fields {
        fields: &'t [(FieldId, Slot)],
        stall: usize,
        start: usize,
    },
}

#[derive(Debug)]
pub(crate) struct Cursor<'a> {
    pub(crate) reader: Reader<'a>,
    limits: Limits,
    /// Values counted so far.
    used: u64,
    /// How deep the receiver is.
    depth: usize,
    /// The value handed to a receiver that it has not started on. Whoever handed it out
    /// skips it if the receiver never does.
    pub(crate) pending: Option<Pending>,
    /// Subtype answers for references, by sender's entry and receiver's entry. Only for
    /// one receiver's table at a time: cleared for each argument.
    subtypes: BTreeMap<(usize, usize), bool>,
    /// Where a value at an infinite option was, once one has been: its coercion is
    /// undefined (`lean/Spec/Types.md`, Section 6.1), and so is the message's. The message
    /// is still read to its end first, as `decodeAt` reads it, so that an error in its
    /// bytes or a limit it runs into is the answer instead.
    pub(crate) undefined: Option<usize>,
}

impl<'a> Cursor<'a> {
    pub(crate) fn new(reader: Reader<'a>, limits: Limits) -> Self {
        Cursor {
            reader,
            limits,
            used: 0,
            depth: 0,
            pending: None,
            subtypes: BTreeMap::new(),
            undefined: None,
        }
    }

    pub(crate) fn position(&self) -> usize {
        self.reader.position()
    }

    pub(crate) fn fail<T>(&self, rejection: Rejection) -> Read<T> {
        self.reader.fail(self.position(), rejection)
    }

    /// A new receiver's table: forget the subtype answers about the last one.
    pub(crate) fn new_receiver(&mut self) {
        self.subtypes.clear();
    }

    /// Count one value against the limit, as `charge` in `lean/Candid/Wire.lean`.
    pub(crate) fn charge(&mut self) -> Read<()> {
        if self.used >= self.limits.values {
            return self.fail(Rejection::TooManyValues);
        }
        self.used += 1;
        Ok(())
    }

    /// One level deeper in the receiver.
    pub(crate) fn enter(&mut self) -> Read<()> {
        if self.depth >= self.limits.depth {
            return self.fail(Rejection::TooDeep);
        }
        self.depth += 1;
        Ok(())
    }

    pub(crate) fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    /// Skip the value handed out, if the receiver did not start on it.
    pub(crate) fn settle(&mut self, table: &TypeTable) -> Read<()> {
        match self.pending.take() {
            Some(p) => self.skip(table, p),
            None => Ok(()),
        }
    }

    /// Read a primitive value of type `p`, which has been counted.
    pub(crate) fn primitive(&mut self, p: Primitive) -> Read<Scalar<'a>> {
        let r = &mut self.reader;
        let fixed = |r: &mut Reader<'a>, n: u64| r.bytes(n).map(Scalar::Fixed);
        match p {
            Primitive::Null | Primitive::Reserved => Ok(Scalar::Null),
            Primitive::Empty => self.fail(Rejection::ValueOfEmpty),
            Primitive::Bool => {
                let at = r.position();
                match r.byte()? {
                    0 => Ok(Scalar::Bool(false)),
                    1 => Ok(Scalar::Bool(true)),
                    b => r.fail(at, Rejection::NotABool(b)),
                }
            }
            Primitive::Nat => r.leb128_bytes().map(Scalar::Nat),
            Primitive::Int => r.leb128_bytes().map(Scalar::Int),
            Primitive::Nat8 | Primitive::Int8 => fixed(r, 1),
            Primitive::Nat16 | Primitive::Int16 => fixed(r, 2),
            Primitive::Nat32 | Primitive::Int32 | Primitive::Float32 => fixed(r, 4),
            Primitive::Nat64 | Primitive::Int64 | Primitive::Float64 => fixed(r, 8),
            Primitive::Text => r.text().map(Scalar::Text),
            Primitive::Principal => self.id().map(Scalar::Principal),
        }
    }

    /// `M(id(v*))`: flag 1, then at most 29 bytes.
    pub(crate) fn id(&mut self) -> Read<&'a [u8]> {
        self.reference_flag()?;
        let at = self.position();
        let n = self.reader.unsigned()?;
        if n > MAX_PRINCIPAL_LENGTH {
            return self.reader.fail(at, Rejection::PrincipalTooLong);
        }
        self.reader.bytes(n)
    }

    /// A function reference: flag 1, the service's principal, the method's name.
    pub(crate) fn func(&mut self) -> Read<(&'a [u8], &'a str)> {
        self.reference_flag()?;
        let id = self.id()?;
        Ok((id, self.reader.text()?))
    }

    fn reference_flag(&mut self) -> Read<()> {
        let at = self.position();
        match self.reader.byte()? {
            1 => Ok(()),
            0 => self.reader.fail(at, Rejection::OpaqueReference),
            b => self.reader.fail(at, Rejection::NotAReferenceFlag(b)),
        }
    }

    /// An `opt` tag: whether a value follows.
    pub(crate) fn opt_tag(&mut self) -> Read<bool> {
        let at = self.position();
        match self.reader.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            b => self.reader.fail(at, Rejection::NotAnOptTag(b)),
        }
    }

    /// A variant's alternative: its id and type, from its index.
    pub(crate) fn alternative(
        &mut self,
        alternatives: &[(FieldId, Slot)],
    ) -> Read<(FieldId, Slot)> {
        let at = self.position();
        let i = self.reader.unsigned()?;
        match usize::try_from(i).ok().and_then(|i| alternatives.get(i)) {
            Some(&a) => Ok(a),
            None => self.reader.fail(at, Rejection::VariantIndexOutOfRange),
        }
    }

    /// The check of a record's value (`lean/Candid/Wire.lean`, "Termination"): a record
    /// entered where as many records as the table has entries started already has no
    /// value.
    pub(crate) fn record_stall(&self, table: &TypeTable, stall: usize) -> Read<()> {
        if stall < table.len() {
            Ok(())
        } else {
            self.fail(Rejection::RecordWithoutValue)
        }
    }

    /// `n` bytes, the elements of a `vec nat8`, each counted.
    ///
    /// The one step the elements one by one would take, and the same rejection at the
    /// same byte: each element is counted, then read, so the elements before the count or
    /// the bytes run out are read, and the next one fails at the byte after them.
    pub(crate) fn bytes_counted(&mut self, n: u64) -> Read<&'a [u8]> {
        let room = self.limits.values - self.used;
        let left = self.reader.rest().len() as u64;
        let whole = n.min(room).min(left);
        let bytes = self.reader.bytes(whole)?;
        self.used += whole;
        if whole == n {
            return Ok(bytes);
        }
        // The next element: its count runs out, or else its byte does.
        self.charge()?;
        self.fail(Rejection::EndOfInput)
    }

    /// Whether a reference of the sender's type `t` coerces to the receiver's `u`: whether
    /// `t` is a subtype of `u`. Asked once for each pair of entries.
    pub(crate) fn coerces(&mut self, t: Root<'_>, u: Root<'_>) -> bool {
        let (Slot::Ref(a), Slot::Ref(b)) = (t.slot(), u.slot()) else {
            return is_subtype(t, u);
        };
        *self
            .subtypes
            .entry((a.index(), b.index()))
            .or_insert_with(|| is_subtype(t, u))
    }

    /// Skip a value: read it at the sender's type, count it and everything in it, and
    /// throw it away.
    pub(crate) fn skip(&mut self, table: &TypeTable, value: Pending) -> Read<()> {
        self.skip_all(table, &mut Vec::from([Work::Value(value)]))
    }

    /// `n` more elements of type `slot`.
    pub(crate) fn skip_elements(&mut self, table: &TypeTable, slot: Slot, n: u64) -> Read<()> {
        let mut work = Vec::from([Work::Elements(slot, n)]);
        self.skip_all(table, &mut work)
    }

    fn skip_all<'t>(&mut self, table: &'t TypeTable, work: &mut Vec<Work<'t>>) -> Read<()> {
        while let Some(w) = work.pop() {
            match w {
                Work::Value(p) => self.skip_one(table, p, work)?,
                Work::Elements(slot, n) => {
                    if n > 0 {
                        work.push(Work::Elements(slot, n - 1));
                        work.push(Work::Value(Pending { slot, stall: 0 }));
                    }
                }
                Work::Fields {
                    fields,
                    stall,
                    start,
                } => {
                    if let [(_, slot), rest @ ..] = fields {
                        let here = self.position();
                        let stall = if here == start { stall } else { 0 };
                        work.push(Work::Fields {
                            fields: rest,
                            stall,
                            start: here,
                        });
                        work.push(Work::Value(Pending { slot: *slot, stall }));
                    }
                }
            }
        }
        Ok(())
    }

    /// One value: count it, read what comes before its parts, and leave its parts on
    /// `work`.
    fn skip_one<'t>(
        &mut self,
        table: &'t TypeTable,
        p: Pending,
        work: &mut Vec<Work<'t>>,
    ) -> Read<()> {
        self.charge()?;
        let r = match p.slot {
            Slot::Primitive(q) => return self.primitive(q).map(drop),
            Slot::Ref(r) => r,
        };
        match table.lookup(r) {
            Some(Composite::Opt(inner)) => {
                if self.opt_tag()? {
                    work.push(Work::Value(Pending {
                        slot: *inner,
                        stall: 0,
                    }));
                }
            }
            Some(Composite::Vec(inner)) => {
                let n = self.reader.unsigned()?;
                work.push(Work::Elements(*inner, n));
            }
            Some(Composite::Record(fields)) => {
                self.record_stall(table, p.stall)?;
                work.push(Work::Fields {
                    fields,
                    stall: p.stall + 1,
                    start: self.position(),
                });
            }
            Some(Composite::Variant(alternatives)) => {
                let (_, inner) = self.alternative(alternatives)?;
                work.push(Work::Value(Pending {
                    slot: inner,
                    stall: 0,
                }));
            }
            Some(Composite::Service(_)) => {
                self.id()?;
            }
            Some(Composite::Func { .. }) => {
                self.func()?;
            }
            Some(Composite::Future { .. }) => {
                // Two lengths, then that many bytes; the references are not in the message.
                let m = self.reader.unsigned()?;
                self.reader.unsigned()?;
                self.reader.bytes(m)?;
            }
            // A table's every reference resolves, and a header's argument types do.
            None => {}
        }
        Ok(())
    }
}

/// `null <: t`: `null`, `reserved` and the options (`TypeTable.acceptsNull`).
pub(crate) fn accepts_null(table: &TypeTable, slot: Slot) -> bool {
    match slot {
        Slot::Primitive(p) => matches!(p, Primitive::Null | Primitive::Reserved),
        Slot::Ref(r) => matches!(table.lookup(r), Some(Composite::Opt(_))),
    }
}

/// Whether `slot` is an infinite option, such as `type R = opt R`: a chain of options that
/// does not end (`optLayers` in `lean/Candid/Coerce.lean`). A chain that ends visits each
/// entry at most once.
pub(crate) fn is_infinite_option(table: &TypeTable, mut slot: Slot) -> bool {
    for _ in 0..=table.len() {
        match slot {
            Slot::Ref(r) => match table.lookup(r) {
                Some(Composite::Opt(inner)) => slot = *inner,
                _ => return false,
            },
            Slot::Primitive(_) => return false,
        }
    }
    true
}
