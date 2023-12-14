#[cfg(feature = "arbitrary")]
use arbitrary::{Arbitrary, Result as ArbitraryResult, Unstructured};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "self_authenticating")]
use sha2::{Digest, Sha224};
#[cfg(feature = "convert")]
use std::convert::TryFrom;
#[cfg(feature = "convert")]
use std::fmt::Write;
#[cfg(feature = "convert")]
use thiserror::Error;

/// An error happened while encoding, decoding or serializing a [`Principal`].
#[derive(Error, Clone, Debug, Eq, PartialEq)]
#[cfg(feature = "convert")]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum PrincipalError {
    #[error("Bytes is longer than 29 bytes.")]
    BytesTooLong(),

    #[error("Text must be in valid Base32 encoding.")]
    InvalidBase32(),

    #[error("Text is too short.")]
    TextTooShort(),

    #[error("Text is too long.")]
    TextTooLong(),

    #[error("CRC32 check sequence doesn't match with calculated from Principal bytes.")]
    CheckSequenceNotMatch(),

    #[error(r#"Text should be separated by - (dash) every 5 characters: expected "{0}""#)]
    AbnormalGrouped(Principal),
}

/// Generic ID on Internet Computer.
///
/// Principals are generic identifiers for canisters, users
/// and possibly other concepts in the future.
/// As far as most uses of the IC are concerned they are
/// opaque binary blobs with a length between 0 and 29 bytes,
/// and there is intentionally no mechanism to tell canister ids and user ids apart.
///
/// Note a principal is not necessarily tied with a public key-pair,
/// yet we need at least a key-pair of a related principal to sign
/// requests.
///
/// A Principal can be serialized to a byte array ([`Vec<u8>`]) or a text
/// representation, but the inner structure of the byte representation
/// is kept private.
///
/// Example of using a Principal object:
/// ```
/// # #[cfg(feature = "convert")] {
/// use ic_principal::Principal;
///
/// let text = "aaaaa-aa";  // The management canister ID.
/// let principal = Principal::from_text(text).expect("Could not decode the principal.");
/// assert_eq!(principal.as_slice(), &[]);
/// assert_eq!(principal.to_text(), text);
///
/// # }
/// ```
///
/// Serialization is enabled with the "serde" feature. It supports serializing
/// to a byte bufer for non-human readable serializer, and a string version for human
/// readable serializers.
///
/// ```
/// # #[cfg(all(feature = "convert", feature = "serde"))] {
/// use ic_principal::Principal;
/// use serde::{Deserialize, Serialize};
/// use std::str::FromStr;
///
/// #[derive(Serialize)]
/// struct Data {
///     id: Principal,
/// }
///
/// let id = Principal::from_str("2chl6-4hpzw-vqaaa-aaaaa-c").unwrap();
///
/// // JSON is human readable, so this will serialize to a textual
/// // representation of the Principal.
/// assert_eq!(
///     serde_json::to_string(&Data { id: id.clone() }).unwrap(),
///     r#"{"id":"2chl6-4hpzw-vqaaa-aaaaa-c"}"#
/// );
///
/// // CBOR is not human readable, so will serialize to bytes.
/// assert_eq!(
///     serde_cbor::to_vec(&Data { id: id.clone() }).unwrap(),
///     &[161, 98, 105, 100, 73, 239, 205, 171, 0, 0, 0, 0, 0, 1],
/// );
/// # }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Principal {
    /// Length.
    len: u8,

    /// The content buffer. When returning slices this should always be sized according to
    /// `len`.
    bytes: [u8; Self::MAX_LENGTH_IN_BYTES],
}

impl Principal {
    pub const MAX_LENGTH_IN_BYTES: usize = 29;
    #[allow(dead_code)]
    const CRC_LENGTH_IN_BYTES: usize = 4;

    #[allow(dead_code)]
    const SELF_AUTHENTICATING_TAG: u8 = 2;
    const ANONYMOUS_TAG: u8 = 4;

    /// Construct a [`Principal`] of the IC management canister
    pub const fn management_canister() -> Self {
        Self {
            len: 0,
            bytes: [0; Self::MAX_LENGTH_IN_BYTES],
        }
    }

    /// Construct a self-authenticating ID from public key
    #[cfg(feature = "self_authenticating")]
    pub fn self_authenticating<P: AsRef<[u8]>>(public_key: P) -> Self {
        let public_key = public_key.as_ref();
        let hash = Sha224::digest(public_key);
        let mut bytes = [0; Self::MAX_LENGTH_IN_BYTES];
        bytes[..Self::MAX_LENGTH_IN_BYTES - 1].copy_from_slice(hash.as_slice());
        bytes[Self::MAX_LENGTH_IN_BYTES - 1] = Self::SELF_AUTHENTICATING_TAG;

        Self {
            len: Self::MAX_LENGTH_IN_BYTES as u8,
            bytes,
        }
    }

    /// Construct an anonymous ID.
    pub const fn anonymous() -> Self {
        let mut bytes = [0; Self::MAX_LENGTH_IN_BYTES];
        bytes[0] = Self::ANONYMOUS_TAG;
        Self { len: 1, bytes }
    }

    /// Returns `None` if the slice exceeds the max length.
    const fn from_slice_core(slice: &[u8]) -> Option<Self> {
        match slice.len() {
            len @ 0..=Self::MAX_LENGTH_IN_BYTES => {
                let mut bytes = [0; Self::MAX_LENGTH_IN_BYTES];
                let mut i = 0;
                while i < len {
                    bytes[i] = slice[i];
                    i += 1;
                }
                Some(Self {
                    len: len as u8,
                    bytes,
                })
            }
            _ => None,
        }
    }

    /// Construct a [`Principal`] from a slice of bytes.
    ///
    /// # Panics
    ///
    /// Panics if the slice is longer than 29 bytes.
    pub const fn from_slice(slice: &[u8]) -> Self {
        match Self::from_slice_core(slice) {
            Some(principal) => principal,
            _ => panic!("slice length exceeds capacity"),
        }
    }

    /// Construct a [`Principal`] from a slice of bytes.
    #[cfg(feature = "convert")]
    pub const fn try_from_slice(slice: &[u8]) -> Result<Self, PrincipalError> {
        match Self::from_slice_core(slice) {
            Some(principal) => Ok(principal),
            None => Err(PrincipalError::BytesTooLong()),
        }
    }

    /// Parse a [`Principal`] from text representation.
    #[cfg(feature = "convert")]
    pub fn from_text<S: AsRef<str>>(text: S) -> Result<Self, PrincipalError> {
        // Strategy: Parse very liberally, then pretty-print and compare output
        // This is both simpler and yields better error messages

        let mut s = text.as_ref().to_string();
        s.make_ascii_uppercase();
        s.retain(|c| c != '-');
        match data_encoding::BASE32_NOPAD.decode(s.as_bytes()) {
            Ok(bytes) => {
                if bytes.len() < Self::CRC_LENGTH_IN_BYTES {
                    return Err(PrincipalError::TextTooShort());
                }

                let crc_bytes = &bytes[..Self::CRC_LENGTH_IN_BYTES];
                let data_bytes = &bytes[Self::CRC_LENGTH_IN_BYTES..];
                if data_bytes.len() > Self::MAX_LENGTH_IN_BYTES {
                    return Err(PrincipalError::TextTooLong());
                }

                if crc32fast::hash(data_bytes).to_be_bytes() != crc_bytes {
                    return Err(PrincipalError::CheckSequenceNotMatch());
                }

                // Already checked data_bytes.len() <= MAX_LENGTH_IN_BYTES
                // safe to unwrap here
                let result = Self::try_from_slice(data_bytes).unwrap();
                let expected = format!("{result}");

                // In the Spec:
                // The textual representation is conventionally printed with lower case letters,
                // but parsed case-insensitively.
                if text.as_ref().to_ascii_lowercase() != expected {
                    return Err(PrincipalError::AbnormalGrouped(result));
                }
                Ok(result)
            }
            _ => Err(PrincipalError::InvalidBase32()),
        }
    }

    /// Convert [`Principal`] to text representation.
    #[cfg(feature = "convert")]
    pub fn to_text(&self) -> String {
        format!("{self}")
    }

    /// Return the [`Principal`]'s underlying slice of bytes.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.bytes[..self.len as usize]
    }
}

#[cfg(feature = "convert")]
impl std::fmt::Display for Principal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let blob: &[u8] = self.as_slice();

        // calc checksum
        let checksum = crc32fast::hash(blob);

        // combine blobs
        let mut bytes = vec![];
        bytes.extend_from_slice(&checksum.to_be_bytes());
        bytes.extend_from_slice(blob);

        // base32
        let mut s = data_encoding::BASE32_NOPAD.encode(&bytes);
        s.make_ascii_lowercase();

        // write out string with dashes
        let mut s = s.as_str();
        while s.len() > 5 {
            f.write_str(&s[..5])?;
            f.write_char('-')?;
            s = &s[5..];
        }
        f.write_str(s)
    }
}

#[cfg(feature = "convert")]
impl std::str::FromStr for Principal {
    type Err = PrincipalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Principal::from_text(s)
    }
}

#[cfg(feature = "convert")]
impl TryFrom<&str> for Principal {
    type Error = PrincipalError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Principal::from_text(s)
    }
}

#[cfg(feature = "convert")]
impl TryFrom<Vec<u8>> for Principal {
    type Error = PrincipalError;

    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        Self::try_from(bytes.as_slice())
    }
}

#[cfg(feature = "convert")]
impl TryFrom<&Vec<u8>> for Principal {
    type Error = PrincipalError;

    fn try_from(bytes: &Vec<u8>) -> Result<Self, Self::Error> {
        Self::try_from(bytes.as_slice())
    }
}

#[cfg(feature = "convert")]
impl TryFrom<&[u8]> for Principal {
    type Error = PrincipalError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Self::try_from_slice(bytes)
    }
}

impl AsRef<[u8]> for Principal {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

// Serialization
#[cfg(feature = "serde")]
impl serde::Serialize for Principal {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            self.to_text().serialize(serializer)
        } else {
            serializer.serialize_bytes(self.as_slice())
        }
    }
}

// Deserialization
#[cfg(feature = "serde")]
mod deserialize {
    use super::Principal;
    use std::convert::TryFrom;

    // Simple visitor for deserialization from bytes. We don't support other number types
    // as there's no need for it.
    pub(super) struct PrincipalVisitor;

    impl<'de> serde::de::Visitor<'de> for PrincipalVisitor {
        type Value = super::Principal;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("bytes or string")
        }

        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Principal::from_text(v).map_err(E::custom)
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Principal::try_from(value).map_err(E::custom)
        }
        /// This visitor should only be used by the Candid crate.
        fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if v.is_empty() || v[0] != 2u8 {
                Err(E::custom("Not called by Candid"))
            } else {
                Principal::try_from(&v[1..]).map_err(E::custom)
            }
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Principal {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Principal, D::Error> {
        use serde::de::Error;
        if deserializer.is_human_readable() {
            deserializer
                .deserialize_str(deserialize::PrincipalVisitor)
                .map_err(D::Error::custom)
        } else {
            deserializer
                .deserialize_bytes(deserialize::PrincipalVisitor)
                .map_err(D::Error::custom)
        }
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> Arbitrary<'a> for Principal {
    fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
        let principal = match u8::arbitrary(u)? {
            u8::MAX => Principal::management_canister(),
            254u8 => Principal::anonymous(),
            _ => {
                let length: usize = u.int_in_range(1..=Principal::MAX_LENGTH_IN_BYTES)?;
                let mut result: Vec<u8> = Vec::with_capacity(length);
                for _ in 0..length {
                    result.push(u8::arbitrary(u)?);
                }
                // non-anonymous principal cannot have type ANONYMOUS
                // adapt by changing the last byte.
                let last = result.last_mut().unwrap();
                if *last == 4_u8 {
                    *last = u8::MAX;
                }
                Principal::try_from(&result[..]).unwrap()
            }
        };
        Ok(principal)
    }
}
