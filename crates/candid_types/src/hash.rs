//! Field identifiers and the field-id hash. Mirrors `lean/Candid/Hash.lean`.

use core::fmt;

/// A record or variant field identifier: a 32-bit number.
///
/// In the textual syntax it may be written literally or as a name that hashes to it, and
/// the two are indistinguishable at the type level -- `record { 24860 : nat }` and
/// `record { ok : nat }` are the same type. So types key fields on `FieldId` and leave
/// names to the syntax layer: two fields are equal exactly when their ids are.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldId(u32);

impl FieldId {
    /// The field with this id.
    pub const fn new(id: u32) -> Self {
        FieldId(id)
    }

    /// The id as a number.
    pub const fn get(self) -> u32 {
        self.0
    }
}

impl From<u32> for FieldId {
    fn from(id: u32) -> Self {
        FieldId(id)
    }
}

impl From<FieldId> for u32 {
    fn from(id: FieldId) -> Self {
        id.0
    }
}

impl fmt::Debug for FieldId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FieldId({})", self.0)
    }
}

impl fmt::Display for FieldId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// The field-id hash (`lean/Spec/Types.md`, Section 3.3). For a name whose UTF-8
/// encoding is the bytes `b₀ … bₖ`:
///
/// ```text
/// hash(b₀ … bₖ) = (b₀·223^k + b₁·223^(k−1) + … + bₖ·223^0) mod 2³²
/// ```
///
/// Evaluated in Horner form over the UTF-8 *bytes* of the name -- not its characters,
/// which differ for any name outside ASCII.
///
/// A record with two fields of equal id is malformed rather than ambiguous; checking
/// that is [`RawTypeTable::check`](crate::RawTypeTable::check)'s job, not the hash's.
pub const fn hash_field_name(name: &str) -> FieldId {
    let bytes = name.as_bytes();
    let mut acc: u32 = 0;
    let mut i = 0;
    while i < bytes.len() {
        acc = acc.wrapping_mul(223).wrapping_add(bytes[i] as u32);
        i += 1;
    }
    FieldId(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_hashes() {
        assert_eq!(hash_field_name("").get(), 0);
        assert_eq!(hash_field_name("Ok").get(), 17724);
        assert_eq!(hash_field_name("Err").get(), 3456837);
        // Two UTF-8 bytes, not one character.
        assert_eq!(hash_field_name("é").get(), 0xc3 * 223 + 0xa9);
    }

    #[test]
    fn wraps_modulo_2_32() {
        // Long enough to overflow many times over; must not panic in a debug build.
        let name = "a_rather_long_field_name_that_overflows_u32";
        let expected = name
            .bytes()
            .fold(0u64, |acc, b| (acc * 223 + u64::from(b)) % (1 << 32));
        assert_eq!(u64::from(hash_field_name(name).get()), expected);
    }
}
