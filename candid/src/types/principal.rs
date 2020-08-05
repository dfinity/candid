use super::{CandidType, Serializer, Type, TypeId};
use crate::Error;
use serde::de::{Deserialize, Visitor};
use std::fmt;
use std::fmt::Write as FmtWrite;

#[derive(PartialEq, Debug, Clone)]
pub struct Principal(pub Vec<u8>);

// TODO this whole implementation should be replaced with the real ic-types crate
impl Principal {
    pub fn from_text<S: std::string::ToString + AsRef<[u8]>>(text: S) -> crate::Result<Self> {
        let mut s = text.to_string();
        s.make_ascii_lowercase();
        s.retain(|c| c != '-');
        match base32::decode(base32::Alphabet::RFC4648 { padding: false }, &s) {
            Some(mut bytes) => {
                if bytes.len() < 4 {
                    return Err(Error::msg("Principal too short."));
                }
                let result = Principal::from_bytes(bytes.split_off(4));
                let expected = format!("{}", result);

                if text.to_string() != expected {
                    let fmt = format!(
                        "Wrong format. Got {}, expected {}",
                        text.to_string(),
                        expected
                    );
                    return Err(Error::msg(fmt));
                }
                Ok(result)
            }
            None => Err(Error::msg("Principal not base32.")),
        }
    }
    pub fn from_bytes<S: AsRef<[u8]>>(bytes: S) -> Principal {
        Principal(bytes.as_ref().to_vec())
    }
    pub fn to_text(&self) -> String {
        let blob = &self.0;
        // calc checksum
        let mut hasher = crc32fast::Hasher::new();
        hasher.update(&blob);
        let checksum = hasher.finalize();

        // combine blobs
        let mut bytes = vec![];
        bytes.extend(&(checksum.to_be_bytes().to_vec()));
        bytes.extend_from_slice(&blob);

        // base32
        let mut s = base32::encode(base32::Alphabet::RFC4648 { padding: false }, &bytes);
        s.make_ascii_lowercase();

        let mut string_format = String::new();
        // write out string with dashes
        while s.len() > 5 {
            // to bad split_off does not work the other way
            let rest = s.split_off(5);
            write!(&mut string_format, "{}-", s).unwrap();
            s = rest;
        }
        write!(string_format, "{}", s).unwrap();
        string_format
    }
}

impl fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_text())
    }
}

impl CandidType for Principal {
    fn id() -> TypeId {
        TypeId::of::<Principal>()
    }
    fn _ty() -> Type {
        Type::Principal
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_principal(&self.0)
    }
}

impl<'de> Deserialize<'de> for Principal {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct PrincipalVisitor;
        impl<'de> Visitor<'de> for PrincipalVisitor {
            type Value = Principal;
            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("Principal value")
            }
            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E> {
                Ok(Principal(v[1..].to_vec()))
            }
        }
        deserializer.deserialize_any(PrincipalVisitor)
    }
}
