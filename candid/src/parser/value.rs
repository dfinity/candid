use super::lexer::error;
use crate::types::{Field, Type};
use crate::{Error, Result};
use crate::{Int, Nat};
use serde::de;
use serde::de::{Deserialize, Visitor};
use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;

#[derive(Debug, PartialEq, Clone)]
pub enum IDLValue {
    Bool(bool),
    Null,
    Text(String),
    Number(String), // Undetermined number type
    Opt(Box<IDLValue>),
    Vec(Vec<IDLValue>),
    Record(Vec<IDLField>),
    Variant(Box<IDLField>),
    // The following values can only be generated with type annotation
    None,
    Int(Int),
    Nat(Nat),
    Nat8(u8),
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
    pub fn annotate_types<'a>(&'a mut self, types: &[Type]) -> Result<&'a mut Self> {
        if types.len() > self.args.len() {
            return Err(Error::msg("length mismatch for types and values"));
        }
        for (i, t) in types.iter().enumerate() {
            let v = self.args[i].annotate_type(t)?;
            self.args[i] = v;
        }
        Ok(self)
    }
    pub fn annotate_type<'a>(&'a mut self, idx: usize, t: &Type) -> Result<&'a mut Self> {
        if idx >= self.args.len() {
            return Err(Error::msg("index out of bounds"));
        }
        let v = self.args[idx].annotate_type(t)?;
        self.args[idx] = v;
        Ok(self)
    }
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let mut idl = crate::ser::IDLBuilder::new();
        for v in self.args.iter() {
            idl.value_arg(v)?;
        }
        idl.serialize_to_vec()
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
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
    type Err = Error;
    fn from_str(str: &str) -> std::result::Result<Self, Self::Err> {
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
            IDLValue::Number(ref str) => write!(f, "{}", str),
            IDLValue::Int(ref i) => write!(f, "{}", i),
            IDLValue::Nat(ref n) => write!(f, "{}", n),
            IDLValue::Nat8(n) => write!(f, "{}", n),
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

impl IDLValue {
    pub fn annotate_type(&self, t: &Type) -> Result<Self> {
        Ok(match (self, t) {
            (IDLValue::Null, Type::Null) => IDLValue::Null,
            (IDLValue::Null, Type::Opt(_)) => IDLValue::None,
            (IDLValue::Bool(b), Type::Bool) => IDLValue::Bool(*b),
            (IDLValue::Number(str), t) => match t {
                Type::Int => IDLValue::Int(str.parse::<Int>()?),
                Type::Nat => IDLValue::Nat(str.parse::<Nat>()?),
                Type::Nat8 => IDLValue::Nat8(str.parse::<u8>().map_err(error)?),
                _ => return Err(Error::msg("not a number type")),
            },
            (IDLValue::Int(i), Type::Int) => IDLValue::Int(i.clone()),
            (IDLValue::Nat(n), Type::Nat) => IDLValue::Nat(n.clone()),
            (IDLValue::Nat8(n), Type::Nat8) => IDLValue::Nat8(*n),
            (IDLValue::Text(s), Type::Text) => IDLValue::Text(s.to_owned()),
            (IDLValue::None, Type::Opt(_)) => IDLValue::None,
            (IDLValue::Opt(v), Type::Opt(ty)) => {
                let v = v.annotate_type(ty)?;
                IDLValue::Opt(Box::new(v))
            }
            (IDLValue::Vec(vec), Type::Vec(ty)) => {
                let mut res = Vec::new();
                for e in vec.iter() {
                    let v = e.annotate_type(ty)?;
                    res.push(v);
                }
                IDLValue::Vec(res)
            }
            (IDLValue::Record(vec), Type::Record(fs)) => {
                let fs: HashMap<_, _> =
                    fs.iter().map(|Field { hash, ty, .. }| (hash, ty)).collect();
                let mut res = Vec::new();
                for e in vec.iter() {
                    let ty = fs
                        .get(&e.id)
                        .ok_or_else(|| Error::msg("field is not found"))?;
                    let v = e.val.annotate_type(ty)?;
                    res.push(IDLField { id: e.id, val: v });
                }
                IDLValue::Record(res)
            }
            (IDLValue::Variant(v), Type::Variant(fs)) => {
                let fs: HashMap<_, _> =
                    fs.iter().map(|Field { hash, ty, .. }| (hash, ty)).collect();
                let ty = fs
                    .get(&v.id)
                    .ok_or_else(|| Error::msg("field is not found"))?;
                let val = v.val.annotate_type(ty)?;
                let field = IDLField { id: v.id, val };
                IDLValue::Variant(Box::new(field))
            }
            _ => return Err(Error::msg("type mismatch")),
        })
    }
    // This will only be called when the type is not provided
    pub fn value_ty(&self) -> Type {
        match *self {
            IDLValue::Null => Type::Null,
            IDLValue::Bool(_) => Type::Bool,
            IDLValue::Number(_) => Type::Int,
            IDLValue::Int(_) => Type::Int,
            IDLValue::Nat(_) => Type::Nat,
            IDLValue::Nat8(_) => Type::Nat8,
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
    fn idl_serialize<S>(&self, serializer: S) -> std::result::Result<(), S::Error>
    where
        S: crate::types::Serializer,
    {
        use crate::types::Compound;
        match *self {
            IDLValue::Null => serializer.serialize_null(()),
            IDLValue::Bool(b) => serializer.serialize_bool(b),
            IDLValue::Number(ref str) => {
                let v = str.parse::<Int>().expect("cannot parse int");
                serializer.serialize_int(&v)
            }
            IDLValue::Int(ref i) => serializer.serialize_int(i),
            IDLValue::Nat(ref n) => serializer.serialize_nat(n),
            IDLValue::Nat8(n) => serializer.serialize_nat8(n),
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

type DResult<E> = std::result::Result<IDLValue, E>;

impl<'de> Deserialize<'de> for IDLValue {
    fn deserialize<D>(deserializer: D) -> DResult<D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct IDLValueVisitor;

        impl<'de> Visitor<'de> for IDLValueVisitor {
            type Value = IDLValue;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("any valid IDL value")
            }
            fn visit_bool<E>(self, value: bool) -> DResult<E> {
                Ok(IDLValue::Bool(value))
            }
            /*
            fn visit_i64<E>(self, value: i64) -> DResult<E> {
                Ok(IDLValue::Int(value))
            }*/
            fn visit_u8<E>(self, value: u8) -> DResult<E> {
                Ok(IDLValue::Nat8(value))
            }
            // Deserialize bignum
            fn visit_bytes<E: de::Error>(self, value: &[u8]) -> DResult<E> {
                let (tag, bytes) = value.split_at(1);
                match tag[0] {
                    0u8 => {
                        let v = Int(num_bigint::BigInt::from_signed_bytes_le(bytes));
                        //let num = v.to_str_radix(10).parse::<i64>().unwrap();
                        Ok(IDLValue::Int(v))
                    }
                    1u8 => {
                        let v = Nat(num_bigint::BigUint::from_bytes_le(bytes));
                        //let num = v.to_str_radix(10).parse::<u64>().unwrap();
                        Ok(IDLValue::Nat(v))
                    }
                    _ => Err(de::Error::custom("unknown tag in visit_bytes")),
                }
            }
            fn visit_string<E>(self, value: String) -> DResult<E> {
                Ok(IDLValue::Text(value))
            }
            fn visit_str<E>(self, value: &str) -> DResult<E>
            where
                E: serde::de::Error,
            {
                self.visit_string(String::from(value))
            }
            fn visit_none<E>(self) -> DResult<E> {
                Ok(IDLValue::None)
            }
            fn visit_some<D>(self, deserializer: D) -> DResult<D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let v = Deserialize::deserialize(deserializer)?;
                Ok(IDLValue::Opt(Box::new(v)))
            }
            fn visit_unit<E>(self) -> DResult<E> {
                Ok(IDLValue::Null)
            }
            fn visit_seq<V>(self, mut visitor: V) -> DResult<V::Error>
            where
                V: de::SeqAccess<'de>,
            {
                let mut vec = Vec::new();
                while let Some(elem) = visitor.next_element()? {
                    vec.push(elem);
                }
                Ok(IDLValue::Vec(vec))
            }
            fn visit_map<V>(self, mut visitor: V) -> DResult<V::Error>
            where
                V: de::MapAccess<'de>,
            {
                let mut vec = Vec::new();
                while let Some((key, value)) = visitor.next_entry()? {
                    if let IDLValue::Nat(hash) = key {
                        use num_traits::cast::ToPrimitive;
                        let f = IDLField {
                            id: hash.0.to_u32().unwrap(), //.ok_or(Error::msg("field hash out of range"))?,
                            val: value,
                        };
                        vec.push(f);
                    } else {
                        unreachable!()
                    }
                }
                Ok(IDLValue::Record(vec))
            }
            fn visit_enum<V>(self, data: V) -> DResult<V::Error>
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
