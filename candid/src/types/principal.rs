use super::{CandidType, Serializer, Type, TypeId};
use crate::Error;
use crc8::Crc8;
use serde::de::{Deserialize, Visitor};
use std::fmt;

#[derive(PartialEq, Debug, Clone)]
pub struct Principal(pub Vec<u8>);

// TODO this whole implementation should be replaced with the real ic-types crate
impl Principal {
    pub fn from_text<S: AsRef<[u8]>>(text: S) -> crate::Result<Self> {
        let (_text_prefix, text_rest) = text.as_ref().split_at(3);
        match hex::decode(text_rest).unwrap().as_slice().split_last() {
            None => Err(Error::msg("Cannot parse principal")),
            Some((last, buf)) => {
                let mut crc8 = Crc8::create_msb(0x07);
                let checksum: u8 = crc8.calc(buf, buf.len() as i32, 0);
                if *last == checksum {
                    Ok(Principal(buf.to_vec()))
                } else {
                    Err(Error::msg("Bad checksum"))
                }
            }
        }
    }
    pub fn from_bytes<S: AsRef<[u8]>>(bytes: S) -> Principal {
        Principal(bytes.as_ref().to_vec())
    }
    pub fn to_text(&self) -> String {
        let mut crc8 = Crc8::create_msb(0x07);
        let checksum: u8 = crc8.calc(&self.0, self.0.len() as i32, 0);
        let mut buf = self.0.clone();
        buf.push(checksum);
        format!("ic:{}", hex::encode_upper(buf))
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
