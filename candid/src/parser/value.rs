use crate::types::{Field, Type};
use crate::Nat;
use num_bigint::BigUint;
use serde::de;
use serde::de::{Deserialize, Visitor};
use std::fmt;
use std::ops::Deref;

#[derive(Debug, PartialEq, Clone)]
pub enum IDLValue {
    Bool(bool),
    Null,
    Text(String),
    Int(i64),
    Nat(u64),
    None,
    Opt(Box<IDLValue>),
    Vec(Vec<IDLValue>),
    Record(Vec<IDLField>),
    Variant(Box<IDLField>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct IDLField {
    pub id: u32,
    pub val: IDLValue,
}

#[derive(Debug, PartialEq, Clone)]
pub struct IDLArgs {
    pub args: Vec<IDLValue>,
}

impl IDLArgs {
    pub fn new(args: &[IDLValue]) -> Self {
        IDLArgs {
            args: args.to_owned(),
        }
    }
    pub fn to_bytes(&self) -> crate::Result<Vec<u8>> {
        let mut idl = crate::ser::IDLBuilder::new();
        for v in self.args.iter() {
            idl.value_arg(v)?;
        }
        idl.serialize_to_vec()
    }
    pub fn from_bytes(bytes: &[u8]) -> crate::Result<Self> {
        let mut de = crate::de::IDLDeserialize::new(bytes)?;
        let mut args = Vec::new();
        while !de.is_done() {
            let v = de.get_value::<IDLValue>()?;
            args.push(v);
        }
        de.done()?;
        Ok(IDLArgs { args })
    }
}

impl std::str::FromStr for IDLArgs {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        let lexer = super::lexer::Lexer::new(str);
        Ok(super::grammar::ArgsParser::new().parse(lexer)?)
    }
}

impl fmt::Display for IDLArgs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let len = self.args.len();
        for i in 0..len {
            write!(f, "{}", self.args[i])?;
            if i < len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

impl fmt::Display for IDLValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            IDLValue::Null => write!(f, "null"),
            IDLValue::Bool(b) => write!(f, "{}", b),
            IDLValue::Int(i) => {
                if i >= 0 {
                    write!(f, "+{}", i)
                } else {
                    write!(f, "{}", i)
                }
            }
            IDLValue::Nat(n) => write!(f, "{}", n),
            IDLValue::Text(ref s) => write!(f, "\"{}\"", s),
            IDLValue::None => write!(f, "none"),
            IDLValue::Opt(ref v) => write!(f, "opt {}", v),
            IDLValue::Vec(ref vec) => {
                write!(f, "vec {{ ")?;
                for e in vec.iter() {
                    write!(f, "{}; ", e)?;
                }
                write!(f, "}}")
            }
            IDLValue::Record(ref fs) => {
                write!(f, "record {{ ")?;
                for e in fs.iter() {
                    write!(f, "{}; ", e)?;
                }
                write!(f, "}}")
            }
            IDLValue::Variant(ref v) => write!(f, "variant {{ {} }}", v),
        }
    }
}

impl fmt::Display for IDLField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.id, self.val)
    }
}

impl crate::CandidType for IDLValue {
    fn ty() -> Type {
        unreachable!();
    }
    fn id() -> crate::types::TypeId {
        unreachable!();
    }
    fn _ty() -> Type {
        unreachable!();
    }
    fn value_ty(&self) -> Type {
        match *self {
            IDLValue::Null => Type::Null,
            IDLValue::Bool(_) => Type::Bool,
            IDLValue::Int(_) => Type::Int,
            IDLValue::Nat(_) => Type::Nat,
            IDLValue::Text(_) => Type::Text,
            IDLValue::None => Type::Opt(Box::new(Type::Null)),
            IDLValue::Opt(ref v) => {
                let t = v.deref().value_ty();
                Type::Opt(Box::new(t))
            }
            IDLValue::Vec(ref vec) => {
                let t = if vec.is_empty() {
                    Type::Null
                } else {
                    vec[0].value_ty()
                };
                Type::Vec(Box::new(t))
            }
            IDLValue::Record(ref vec) => {
                let fs: Vec<_> = vec
                    .iter()
                    .map(|IDLField { id, val }| Field {
                        id: id.to_string(),
                        hash: *id,
                        ty: val.value_ty(),
                    })
                    .collect();
                Type::Record(fs)
            }
            IDLValue::Variant(ref v) => {
                let f = Field {
                    id: v.id.to_string(),
                    hash: v.id,
                    ty: v.val.value_ty(),
                };
                Type::Variant(vec![f])
            }
        }
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: crate::types::Serializer,
    {
        use crate::types::Compound;
        match *self {
            IDLValue::Null => serializer.serialize_null(()),
            IDLValue::Bool(b) => serializer.serialize_bool(b),
            IDLValue::Int(i) => serializer.serialize_int(&i.to_string()),
            IDLValue::Nat(n) => serializer.serialize_nat(&n.to_string()),
            IDLValue::Text(ref s) => serializer.serialize_text(s),
            IDLValue::None => serializer.serialize_option::<Option<String>>(None),
            IDLValue::Opt(ref v) => serializer.serialize_option(Some(v.deref())),
            IDLValue::Vec(ref vec) => {
                let mut ser = serializer.serialize_vec(vec.len())?;
                for e in vec.iter() {
                    ser.serialize_element(&e)?;
                }
                Ok(())
            }
            IDLValue::Record(ref vec) => {
                let mut ser = serializer.serialize_struct()?;
                for f in vec.iter() {
                    ser.serialize_element(&f.val)?;
                }
                Ok(())
            }
            IDLValue::Variant(ref v) => {
                let mut ser = serializer.serialize_variant(0)?;
                ser.serialize_element(&v.val)?;
                Ok(())
            }
        }
    }
}

impl<'de> Deserialize<'de> for IDLValue {
    fn deserialize<D>(deserializer: D) -> Result<IDLValue, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct IDLValueVisitor;

        impl<'de> Visitor<'de> for IDLValueVisitor {
            type Value = IDLValue;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("any valid IDL value")
            }
            fn visit_bool<E>(self, value: bool) -> Result<IDLValue, E> {
                Ok(IDLValue::Bool(value))
            }
            fn visit_i64<E>(self, value: i64) -> Result<IDLValue, E> {
                Ok(IDLValue::Int(value))
            }
            fn visit_u64<E>(self, value: u64) -> Result<IDLValue, E> {
                Ok(IDLValue::Nat(value))
            }
            // Deserialize biguint
            fn visit_bytes<E>(self, value: &[u8]) -> Result<IDLValue, E> {
                let v = BigUint::from_bytes_le(value);
                let num = v.to_str_radix(10).parse::<u64>().unwrap();
                Ok(IDLValue::Nat(num))
            }
            fn visit_string<E>(self, value: String) -> Result<IDLValue, E> {
                Ok(IDLValue::Text(value))
            }
            fn visit_str<E>(self, value: &str) -> Result<IDLValue, E>
            where
                E: serde::de::Error,
            {
                self.visit_string(String::from(value))
            }
            fn visit_none<E>(self) -> Result<IDLValue, E> {
                Ok(IDLValue::None)
            }
            fn visit_some<D>(self, deserializer: D) -> Result<IDLValue, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let v = Deserialize::deserialize(deserializer)?;
                Ok(IDLValue::Opt(Box::new(v)))
            }
            fn visit_unit<E>(self) -> Result<IDLValue, E> {
                Ok(IDLValue::Null)
            }
            fn visit_seq<V>(self, mut visitor: V) -> Result<IDLValue, V::Error>
            where
                V: de::SeqAccess<'de>,
            {
                let mut vec = Vec::new();
                while let Some(elem) = visitor.next_element()? {
                    vec.push(elem);
                }
                Ok(IDLValue::Vec(vec))
            }
            fn visit_map<V>(self, mut visitor: V) -> Result<IDLValue, V::Error>
            where
                V: de::MapAccess<'de>,
            {
                let mut vec = Vec::new();
                while let Some((key, value)) = visitor.next_entry()? {
                    if let IDLValue::Nat(hash) = key {
                        let f = IDLField {
                            id: hash as u32,
                            val: value,
                        };
                        vec.push(f);
                    } else {
                        unreachable!()
                    }
                }
                Ok(IDLValue::Record(vec))
            }
            fn visit_enum<V>(self, data: V) -> Result<IDLValue, V::Error>
            where
                V: de::EnumAccess<'de>,
            {
                use serde::de::VariantAccess;
                let (variant, visitor) = data.variant::<IDLValue>()?;
                if let IDLValue::Text(v) = variant {
                    let v: Vec<_> = v.split(',').collect();
                    assert_eq!(v.len(), 2);
                    let id = v[0].parse::<u32>().unwrap();
                    let val = match v[1] {
                        "unit" => {
                            visitor.unit_variant()?;
                            IDLValue::Null
                        }
                        "struct" => visitor.struct_variant(&[], self)?,
                        "newtype" => visitor.newtype_variant()?,
                        _ => unreachable!(),
                    };
                    let f = IDLField { id, val };
                    Ok(IDLValue::Variant(Box::new(f)))
                } else {
                    unreachable!()
                }
            }
        }

        deserializer.deserialize_any(IDLValueVisitor)
    }
}
