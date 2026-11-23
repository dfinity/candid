//! Why a message is rejected.

use core::fmt;

use candid_types::{FieldId, MalformedTable, Primitive, Slot};

/// Why a message was rejected, and where: the offset of the byte the problem starts at.
///
/// The conformance vectors say only *that* a message is rejected; the reason and the
/// position are for people.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DecodeError {
    position: usize,
    rejection: Rejection,
}

impl DecodeError {
    pub(crate) fn new(position: usize, rejection: Rejection) -> Self {
        DecodeError {
            position,
            rejection,
        }
    }

    /// The offset in the message where the problem starts.
    pub fn position(&self) -> usize {
        self.position
    }

    /// What the problem is.
    pub fn rejection(&self) -> &Rejection {
        &self.rejection
    }
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "at byte {}: {}", self.position, self.rejection)
    }
}

impl core::error::Error for DecodeError {}

/// One reason a message is rejected (`lean/Spec/Binary.md`).
///
/// All are rejections the spec requires, except the resource limits it allows (Section
/// 9), which [`Rejection::is_resource_limit`] tells apart.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Rejection {
    /// The message ends before what is being read does.
    EndOfInput,
    /// The message does not start with `DIDL`.
    MissingMagicNumber,
    /// A type reference that is neither a primitive type's opcode nor a table index:
    /// a composite type, say, which belongs in the table (Section 5.1).
    NotATypeReference,
    /// A table entry whose opcode is not a composite type's (Section 5.2).
    NotAType,
    /// A table entry that is a primitive type, which belongs in a type reference.
    PrimitiveInTable(Primitive),
    /// A field id of 2^32 or more.
    FieldIdTooLarge,
    /// Record or variant fields not in strictly ascending order of id.
    FieldsOutOfOrder,
    /// Service methods not in strictly ascending order of name.
    MethodsOutOfOrder,
    /// A function annotation byte that is not one of the three.
    UnknownAnnotation(u8),
    /// Text that is not UTF-8.
    TextNotUtf8,
    /// A type table that is not well formed.
    MalformedTable(MalformedTable),
    /// An argument type, the one at this index, that does not resolve in the table.
    UnresolvedArgument(usize),
    /// A future type whose opcode is below `-2^63`.
    ///
    /// A resource limit: Candid will not define that many types, so this implementation
    /// keeps an opcode in an `i64`, where the Lean model's is unbounded.
    OpcodeOutOfRange,
    /// A header longer than [`Limits::header_bytes`](crate::Limits::header_bytes).
    ///
    /// A resource limit: a header takes some tens of times its length in memory once
    /// read, and the sender chooses its length.
    HeaderTooLarge,
}

impl Rejection {
    /// Whether this is a resource limit (`lean/Spec/Binary.md`, Section 9): a message
    /// this decoder will not read, rather than one that is not valid.
    pub fn is_resource_limit(&self) -> bool {
        matches!(
            self,
            Rejection::OpcodeOutOfRange | Rejection::HeaderTooLarge
        )
    }
}

impl fmt::Display for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rejection::EndOfInput => f.write_str("the message ends too soon"),
            Rejection::MissingMagicNumber => {
                f.write_str("not a Candid message: it does not start with DIDL")
            }
            Rejection::NotATypeReference => {
                f.write_str("neither a primitive type nor a table index where a type belongs")
            }
            Rejection::NotAType => f.write_str("a table entry that is not a composite type"),
            Rejection::PrimitiveInTable(p) => write!(f, "primitive type {p} in the type table"),
            Rejection::FieldIdTooLarge => f.write_str("a field id that does not fit in 32 bits"),
            Rejection::FieldsOutOfOrder => f.write_str("fields not in strictly ascending id order"),
            Rejection::MethodsOutOfOrder => {
                f.write_str("methods not in strictly ascending name order")
            }
            Rejection::UnknownAnnotation(b) => write!(f, "unknown function annotation {b}"),
            Rejection::TextNotUtf8 => f.write_str("text that is not UTF-8"),
            Rejection::MalformedTable(e) => write!(f, "the type table is not well formed: {e}"),
            Rejection::UnresolvedArgument(i) => {
                write!(f, "the type of argument {i} does not resolve")
            }
            Rejection::OpcodeOutOfRange => {
                f.write_str("a future type's opcode is below -2^63, past this decoder's limit")
            }
            Rejection::HeaderTooLarge => f.write_str("the header is longer than the limit"),
        }
    }
}

/// An argument type, the one at [`UnresolvedArgument::index`], that does not resolve in
/// the table it was given with.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct UnresolvedArgument {
    index: usize,
}

impl UnresolvedArgument {
    pub(crate) fn new(index: usize) -> Self {
        UnresolvedArgument { index }
    }

    /// Which argument.
    pub fn index(&self) -> usize {
        self.index
    }
}

impl fmt::Display for UnresolvedArgument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "the type of argument {} does not resolve", self.index)
    }
}

impl core::error::Error for UnresolvedArgument {}

/// Why a message could not be written: a value that does not have its type, or one that
/// was not written at all.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum EncodeError {
    /// Fewer values were written than the header has arguments.
    MissingArguments {
        /// How many arguments the header has.
        expected: usize,
        /// How many values were written.
        written: usize,
    },
    /// A value was asked for past the header's last argument.
    TooManyArguments {
        /// How many arguments the header has.
        expected: usize,
    },
    /// A value was begun and not finished: its writer was dropped, or failed and the
    /// failure was ignored. The message is missing that value, and cannot be finished.
    Unfinished,
    /// A value that does not have its type: the `value` named, at `slot`.
    NotOfType {
        /// The type the value was written at.
        slot: Slot,
        /// What was written: the Candid word for it, such as `nat` or `record`.
        value: &'static str,
    },
    /// A principal, or a reference's, of more than 29 bytes.
    PrincipalTooLong {
        /// How many bytes it has.
        len: usize,
    },
    /// A record field that is not the next in the type's order, or not the type's at all.
    UnexpectedField {
        /// The field written.
        id: FieldId,
        /// The field that comes next, or `None` if every field has been written.
        expected: Option<FieldId>,
    },
    /// A record finished without this field, and any after it.
    MissingField {
        /// The first field not written.
        id: FieldId,
    },
    /// A variant written at an alternative its type does not have.
    NoSuchAlternative {
        /// The alternative.
        id: FieldId,
    },
    /// A vector given more or fewer values than its length.
    ElementCount {
        /// The length it was begun with.
        len: usize,
        /// How many values it was given.
        written: usize,
    },
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeError::MissingArguments { expected, written } => write!(
                f,
                "the header has {expected} arguments, and {written} values were written"
            ),
            EncodeError::TooManyArguments { expected } => {
                write!(f, "a value past the header's {expected} arguments")
            }
            EncodeError::Unfinished => f.write_str("a value was begun and not finished"),
            EncodeError::NotOfType { slot, value } => {
                write!(f, "a {value} value where the type is {slot:?}")
            }
            EncodeError::PrincipalTooLong { len } => {
                write!(f, "a principal of {len} bytes, more than 29")
            }
            EncodeError::UnexpectedField {
                id,
                expected: Some(next),
            } => {
                write!(f, "field {id} written where field {next} comes next")
            }
            EncodeError::UnexpectedField { id, expected: None } => {
                write!(f, "field {id} written after the record's last field")
            }
            EncodeError::MissingField { id } => write!(f, "a record without its field {id}"),
            EncodeError::NoSuchAlternative { id } => {
                write!(f, "the variant has no alternative {id}")
            }
            EncodeError::ElementCount { len, written } => {
                write!(f, "a vector of length {len} given {written} values")
            }
        }
    }
}

impl core::error::Error for EncodeError {}
