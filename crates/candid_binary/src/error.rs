//! Why a message is rejected.

use core::fmt;

use candid_types::{MalformedTable, Primitive};

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

/// Why a message could not be finished.
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
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeError::MissingArguments { expected, written } => write!(
                f,
                "the header has {expected} arguments, and {written} values were written"
            ),
        }
    }
}

impl core::error::Error for EncodeError {}
