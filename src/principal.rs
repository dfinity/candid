#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha224};
use std::convert::TryFrom;
use std::fmt::Write;
use thiserror::Error;

// TODO: remove (blocked by rust-lang/rust#85194)
const ASSERT: [(); 1] = [()];
macro_rules! const_panic {
    ($($arg:tt)*) => {
        #[allow(unconditional_panic)]
        let _ = $crate::principal::ASSERT[1];
    };
}

/// An error happened while encoding, decoding or serializing a principal.
#[derive(Error, Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum PrincipalError {
    #[error("Buffer is too long.")]
    BufferTooLong(),

    #[error(r#"Invalid textual format: expected "{0}""#)]
    AbnormalTextualFormat(Principal),

    #[error("Text must be a base 32 string.")]
    InvalidTextualFormatNotBase32(),

    #[error("Text cannot be converted to a Principal; too small.")]
    TextTooSmall(),
}

/// A class of principal. Because this should not be exposed it
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
enum PrincipalClass {
    OpaqueId = 1,
    SelfAuthenticating = 2,
    DerivedId = 3,
    Anonymous = 4,
    Unassigned,
}

impl Into<u8> for PrincipalClass {
    fn into(self) -> u8 {
        match self {
            PrincipalClass::Unassigned => 0,
            PrincipalClass::OpaqueId => 1,
            PrincipalClass::SelfAuthenticating => 2,
            PrincipalClass::DerivedId => 3,
            PrincipalClass::Anonymous => 4,
        }
    }
}

impl TryFrom<u8> for PrincipalClass {
    type Error = PrincipalError;

    fn try_from(byte: u8) -> Result<Self, Self::Error> {
        match byte {
            1 => Ok(PrincipalClass::OpaqueId),
            2 => Ok(PrincipalClass::SelfAuthenticating),
            3 => Ok(PrincipalClass::DerivedId),
            4 => Ok(PrincipalClass::Anonymous),
            _ => Ok(PrincipalClass::Unassigned),
        }
    }
}

/// A principal describes the security context of an identity, namely
/// any identity that can be authenticated along with a specific
/// role. In the case of the Internet Computer this maps currently to
/// the identities that can be authenticated by a canister. For example,
/// a canister ID is a Principal. So is a user.
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
/// use ic_types::Principal;
///
/// let text = "aaaaa-aa";  // The management canister ID.
/// let principal = Principal::from_text(text).expect("Could not decode the principal.");
/// assert_eq!(principal.as_slice(), &[]);
/// assert_eq!(principal.to_text(), text);
/// ```
///
/// Serialization is enabled with the "serde" feature. It supports serializing
/// to a byte bufer for non-human readable serializer, and a string version for human
/// readable serializers.
///
/// ```
/// use ic_types::Principal;
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
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Principal(PrincipalInner);

impl Principal {
    const CRC_LENGTH_IN_BYTES: usize = 4;

    /// An empty principal that marks the system canister.
    pub const fn management_canister() -> Self {
        Self(PrincipalInner::new())
    }

    /// Right now we are enforcing a Twisted Edwards Curve 25519 point
    /// as the public key.
    pub fn self_authenticating<P: AsRef<[u8]>>(public_key: P) -> Self {
        let public_key = public_key.as_ref();
        let hash = Sha224::digest(public_key);
        let mut inner = PrincipalInner::from_slice(hash.as_slice());
        // Now add a suffix denoting the identifier as representing a
        // self-authenticating principal.
        inner.push(PrincipalClass::SelfAuthenticating as u8);

        Self(inner)
    }

    /// An anonymous Principal.
    pub const fn anonymous() -> Self {
        Self(PrincipalInner::from_slice(&[
            PrincipalClass::Anonymous as u8
        ]))
    }

    /// Attempt to decode a slice into a Principal.
    ///
    /// # Panics
    ///
    /// Panics if the bytes can't be interpreted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ic_types::Principal;
    /// const FOO: Principal = Principal::from_slice(&[0; 29]);    // normal length
    /// const MGMT: Principal = Principal::from_slice(&[]);        // management
    /// const OPQ: Principal = Principal::from_slice(&[4,3,2,1]);  // opaque id
    /// ```
    ///
    /// ```compile_fail
    /// # use ic_types::Principal;
    /// const BAR: Principal = Principal::from_slice(&[0; 32]); // Fails, too long
    /// ```
    ///
    /// ```compile_fail
    /// # use ic_types::Principal;
    /// // Fails, ends in 0x04 (anonymous), but has a prefix
    /// const BAZ: Principal = Principal::from_slice(&[1,2,3,4]);
    /// ```
    pub const fn from_slice(bytes: &[u8]) -> Self {
        if let Ok(v) = Self::try_from_slice(bytes) {
            v
        } else {
            // TODO: replace with panic (blocked by rust-lang/rust#85194)
            const_panic!("slice length exceeded capacity");
            //panic!("slice length exceeds capacity")
            Self::management_canister()
        }
    }

    /// Attempt to decode a slice into a Principal.
    pub const fn try_from_slice(bytes: &[u8]) -> Result<Self, PrincipalError> {
        const ANONYMOUS: u8 = PrincipalClass::Anonymous as u8;
        match bytes {
            [] => Ok(Principal::management_canister()),
            [ANONYMOUS] => Ok(Principal::anonymous()),
            [.., ANONYMOUS] => Err(PrincipalError::BufferTooLong()),
            bytes @ [..] => match PrincipalInner::try_from_slice(bytes) {
                None => Err(PrincipalError::BufferTooLong()),
                Some(v) => Ok(Principal(v)),
            },
        }
    }

    /// Parse the text format for canister IDs (e.g., `jkies-sibbb-ap6`).
    ///
    /// The text format follows the public spec (see Textual IDs section).
    pub fn from_text<S: AsRef<str>>(text: S) -> Result<Self, PrincipalError> {
        // Strategy: Parse very liberally, then pretty-print and compare output
        // This is both simpler and yields better error messages

        let mut s = text.as_ref().to_string();
        s.make_ascii_lowercase();
        s.retain(|c| c != '-');
        match base32::decode(base32::Alphabet::RFC4648 { padding: false }, &s) {
            Some(mut bytes) => {
                if bytes.len() < Principal::CRC_LENGTH_IN_BYTES {
                    return Err(PrincipalError::TextTooSmall());
                }
                let result = Self::try_from(bytes.split_off(Principal::CRC_LENGTH_IN_BYTES))?;
                let expected = format!("{}", result);

                if text.as_ref() != expected {
                    return Err(PrincipalError::AbnormalTextualFormat(result));
                }
                Ok(result)
            }
            None => Err(PrincipalError::InvalidTextualFormatNotBase32()),
        }
    }

    /// Returns this Principal's text representation. The text representation is described
    /// in the spec.
    pub fn to_text(&self) -> String {
        format!("{}", self)
    }

    /// Returns this Principal's bytes.
    pub fn as_slice(&self) -> &[u8] {
        self.as_ref()
    }
}

impl std::fmt::Display for Principal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let blob: &[u8] = self.0.as_ref();

        // calc checksum
        let mut hasher = crc32fast::Hasher::new();
        hasher.update(blob);
        let checksum = hasher.finalize();

        // combine blobs
        let mut bytes = vec![];
        bytes.extend_from_slice(&checksum.to_be_bytes());
        bytes.extend_from_slice(blob);

        // base32
        let mut s = base32::encode(base32::Alphabet::RFC4648 { padding: false }, &bytes);
        s.make_ascii_lowercase();

        // write out string with dashes
        let mut s = s.as_str();
        while s.len() > 5 {
            f.write_str(&s[..5])?;
            f.write_char('-')?;
            s = &s[5..];
        }
        f.write_str(&s)
    }
}

impl std::str::FromStr for Principal {
    type Err = PrincipalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Principal::from_text(s)
    }
}

impl TryFrom<&str> for Principal {
    type Error = PrincipalError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Principal::from_text(s)
    }
}

/// Vector TryFrom. The slice and array version of this trait are defined below.
impl TryFrom<Vec<u8>> for Principal {
    type Error = PrincipalError;

    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        Self::try_from(bytes.as_slice())
    }
}

impl TryFrom<&Vec<u8>> for Principal {
    type Error = PrincipalError;

    fn try_from(bytes: &Vec<u8>) -> Result<Self, Self::Error> {
        Self::try_from(bytes.as_slice())
    }
}

/// Implement try_from for a generic sized slice.
impl TryFrom<&[u8]> for Principal {
    type Error = PrincipalError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Self::try_from_slice(bytes)
    }
}

impl AsRef<[u8]> for Principal {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

// Serialization
#[cfg(feature = "serde")]
impl serde::Serialize for Principal {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            self.to_text().serialize(serializer)
        } else {
            serializer.serialize_bytes(self.0.as_ref())
        }
    }
}

// Deserialization
#[cfg(feature = "serde")]
mod deserialize {
    use super::Principal;
    use std::convert::TryFrom;

    /// Simple visitor for deserialization from bytes. We don't support other number types
    /// as there's no need for it.
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
        deserializer
            .deserialize_bytes(deserialize::PrincipalVisitor)
            .map_err(D::Error::custom)
    }
}

mod inner {
    use sha2::{digest::generic_array::typenum::Unsigned, Digest, Sha224};

    /// Inner structure of a Principal. This is not meant to be public as the different classes
    /// of principals are not public.
    ///
    /// This is a length (1 byte) and 29 bytes. The length can be 0, but won't ever be longer
    /// than 29. The current interface spec says that principals cannot be longer than 29 bytes.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(packed)]
    pub struct PrincipalInner {
        /// Length.
        len: u8,

        /// The content buffer. When returning slices this should always be sized according to
        /// `len`.
        bytes: [u8; Self::MAX_LENGTH_IN_BYTES],
    }

    impl PrincipalInner {
        const HASH_LEN_IN_BYTES: usize = <<Sha224 as Digest>::OutputSize as Unsigned>::USIZE; // 28
        const MAX_LENGTH_IN_BYTES: usize = Self::HASH_LEN_IN_BYTES + 1; // 29

        pub const fn new() -> Self {
            PrincipalInner {
                len: 0,
                bytes: [0; Self::MAX_LENGTH_IN_BYTES],
            }
        }

        /// Panics if the length is over `MAX_LENGTH_IN_BYTES`
        pub const fn from_slice(slice: &[u8]) -> Self {
            if let Some(v) = Self::try_from_slice(slice) {
                v
            } else {
                // TODO: replace with panic (blocked by rust-lang/rust#85194)
                const_panic!("slice length exceeded capacity");
                Self::new()
                //panic!("slice length exceeds capacity")
            }
        }

        /// Returns none if the slice length is over `MAX_LENGTH_IN_BYTES`
        pub const fn try_from_slice(slice: &[u8]) -> Option<Self> {
            let len = slice.len();
            const MAX_LENGTH_IN_BYTES: usize = PrincipalInner::MAX_LENGTH_IN_BYTES;
            if len > MAX_LENGTH_IN_BYTES {
                None
            } else {
                // for-loops in const fn are not supported
                const fn assign_recursive(
                    mut v: [u8; MAX_LENGTH_IN_BYTES],
                    slice: &[u8],
                    index: usize,
                ) -> [u8; MAX_LENGTH_IN_BYTES] {
                    if index == 0 {
                        v
                    } else {
                        let index = index - 1;
                        v[index] = slice[index];
                        assign_recursive(v, slice, index)
                    }
                }
                let bytes = assign_recursive([0; MAX_LENGTH_IN_BYTES], slice, len);
                //bytes.copy_from_slice(slice);
                Some(PrincipalInner {
                    bytes,
                    len: len as u8,
                })
            }
        }

        #[inline]
        pub fn as_slice(&self) -> &[u8] {
            &self.bytes[..self.len as usize]
        }

        pub fn push(&mut self, val: u8) {
            if self.len >= Self::MAX_LENGTH_IN_BYTES as u8 {
                panic!("capacity overflow");
            } else {
                self.bytes[self.len as usize] = val;
                self.len += 1;
            }
        }
    }

    impl AsRef<[u8]> for PrincipalInner {
        fn as_ref(&self) -> &[u8] {
            self.as_slice()
        }
    }
}
use inner::PrincipalInner;

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    #[should_panic]
    fn inner_fails() {
        let _ = inner::PrincipalInner::from_slice(&[0; 32]);
    }

    #[test]
    fn inner() {
        let _ = inner::PrincipalInner::from_slice(&[0; 29]);
        let _ = inner::PrincipalInner::from_slice(&[0; 0]);
        let _ = inner::PrincipalInner::from_slice(&[0; 4]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serializes() {
        let seed = [
            0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22,
            0x11, 0x00, 0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44,
            0x33, 0x22, 0x11, 0x00,
        ];
        let principal: Principal = Principal::self_authenticating(&seed);
        assert_eq!(
            serde_cbor::from_slice::<Principal>(
                serde_cbor::to_vec(&principal)
                    .expect("Failed to serialize")
                    .as_slice()
            )
            .unwrap(),
            principal
        );
    }

    #[test]
    fn parse_management_canister_ok() {
        assert_eq!(
            Principal::from_str("aaaaa-aa").unwrap(),
            Principal::management_canister(),
        );
    }

    #[test]
    fn parse_text_bad_format() {
        assert_eq!(
            Principal::from_str("aaaaa-aA").unwrap_err().to_string(),
            r#"Invalid textual format: expected "aaaaa-aa""#,
        );
    }

    #[test]
    fn parse_management_canister_to_text_ok() {
        assert_eq!(Principal::from_str("aaaaa-aa").unwrap().as_slice(), &[]);
    }

    #[test]
    fn create_managment_cid_from_empty_blob_ok() {
        assert_eq!(Principal::management_canister().to_text(), "aaaaa-aa");
    }

    #[test]
    fn create_managment_cid_from_text_ok() {
        assert_eq!(
            Principal::from_str("aaaaa-aa").unwrap().to_text(),
            "aaaaa-aa",
        );
    }

    #[test]
    fn display_canister_id() {
        assert_eq!(
            Principal::try_from(vec![0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1])
                .unwrap()
                .to_text(),
            "2chl6-4hpzw-vqaaa-aaaaa-c",
        );
    }

    #[test]
    fn display_canister_id_from_bytes_as_bytes() {
        assert_eq!(
            Principal::try_from(vec![0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1])
                .unwrap()
                .as_slice(),
            &[0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1],
        );
    }

    #[test]
    fn display_canister_id_from_blob_as_bytes() {
        assert_eq!(
            Principal::try_from(vec![0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1])
                .unwrap()
                .as_slice(),
            &[0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1],
        );
    }

    #[test]
    fn display_canister_id_from_text_as_bytes() {
        assert_eq!(
            Principal::from_str("2chl6-4hpzw-vqaaa-aaaaa-c")
                .unwrap()
                .as_slice(),
            &[0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1],
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn check_serialize_deserialize() {
        let id = Principal::from_str("2chl6-4hpzw-vqaaa-aaaaa-c").unwrap();

        // Use cbor serialization.
        let vec = serde_cbor::to_vec(&id).unwrap();
        let value = serde_cbor::from_slice(vec.as_slice()).unwrap();

        assert_eq!(id, value);
    }

    #[test]
    fn text_form() {
        let cid = Principal::try_from(vec![1, 8, 64, 255]).unwrap();
        let text = cid.to_text();
        let cid2 = Principal::from_str(&text).unwrap();
        assert_eq!(cid, cid2);
        assert_eq!(text, "jkies-sibbb-ap6");
    }
}
