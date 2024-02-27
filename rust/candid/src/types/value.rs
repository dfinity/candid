use crate::types::number::{Int, Nat};
use crate::types::{Field, Label, Type, TypeEnv, TypeInner};
use crate::{CandidType, DecoderConfig, Error, Result};
use serde::de;
use serde::de::{Deserialize, Visitor};
use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;

#[derive(PartialEq, Clone)]
pub enum IDLValue {
    Bool(bool),
    Null,
    Text(String),
    Number(String), // Undetermined number type
    Float64(f64),
    Opt(Box<IDLValue>),
    Vec(Vec<IDLValue>),
    Record(Vec<IDLField>),
    Variant(VariantValue),
    Blob(Vec<u8>),
    Principal(crate::Principal),
    Service(crate::Principal),
    Func(crate::Principal, String),
    // The following values can only be generated with type annotation
    None,
    Int(Int),
    Nat(Nat),
    Nat8(u8),
    Nat16(u16),
    Nat32(u32),
    Nat64(u64),
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Float32(f32),
    Reserved,
}

#[derive(Clone)]
pub struct VariantValue(pub Box<IDLField>, pub u64); // u64 represents the index from the type, defaults to 0 when parsing, only used for serialization
impl PartialEq for VariantValue {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(PartialEq, Clone)]
pub struct IDLField {
    pub id: Label,
    pub val: IDLValue,
}

#[derive(PartialEq, Clone)]
pub struct IDLArgs {
    pub args: Vec<IDLValue>,
}

impl IDLArgs {
    pub fn new(args: &[IDLValue]) -> Self {
        IDLArgs {
            args: args.to_owned(),
        }
    }
    pub fn annotate_types(self, from_parser: bool, env: &TypeEnv, types: &[Type]) -> Result<Self> {
        let mut args = Vec::new();
        for (v, ty) in self.args.iter().zip(types.iter()) {
            let v = v.annotate_type(from_parser, env, ty)?;
            args.push(v);
        }
        for ty in types[self.args.len()..].iter() {
            let v = match env.trace_type(ty)?.as_ref() {
                TypeInner::Null => IDLValue::Null,
                TypeInner::Reserved => IDLValue::Reserved,
                TypeInner::Opt(_) => IDLValue::None,
                _ => return Err(Error::msg(format!("Omitted values cannot be of type {ty}"))),
            };
            args.push(v);
        }
        Ok(IDLArgs { args })
    }
    pub fn get_types(&self) -> Vec<Type> {
        self.args.iter().map(|v| v.value_ty()).collect()
    }
    /// Encode IDLArgs with the given types. Note that this is not equivalent to
    /// `idl_args.annotate_types(true, env, types).to_bytes()` for recursive types.
    pub fn to_bytes_with_types(&self, env: &TypeEnv, types: &[Type]) -> Result<Vec<u8>> {
        if types.len() > self.args.len() {
            return Err(Error::msg("wrong number of argument values"));
        }
        let mut idl = crate::ser::IDLBuilder::new();
        let empty_env = TypeEnv::new();
        for (i, (v, ty)) in self.args.iter().zip(types.iter()).enumerate() {
            if i == 0 {
                // env gets merged into the builder state, we only need to pass in env once.
                idl.value_arg_with_type(v, env, ty)?;
            } else {
                idl.value_arg_with_type(v, &empty_env, ty)?;
            }
        }
        idl.serialize_to_vec()
    }
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let mut idl = crate::ser::IDLBuilder::new();
        for v in self.args.iter() {
            idl.value_arg(v)?;
        }
        idl.serialize_to_vec()
    }
    pub fn from_bytes_with_types(bytes: &[u8], env: &TypeEnv, types: &[Type]) -> Result<Self> {
        let mut de = crate::de::IDLDeserialize::new(bytes)?;
        let mut args = Vec::new();
        for ty in types.iter() {
            let v = de.get_value_with_type(env, ty)?;
            args.push(v);
        }
        de.done()?;
        Ok(IDLArgs { args })
    }
    pub fn from_bytes_with_types_with_config(
        bytes: &[u8],
        env: &TypeEnv,
        types: &[Type],
        config: &DecoderConfig,
    ) -> Result<Self> {
        let mut de = crate::de::IDLDeserialize::new_with_config(bytes, config)?;
        let mut args = Vec::new();
        for ty in types.iter() {
            let v = de.get_value_with_type(env, ty)?;
            args.push(v);
        }
        de.done()?;
        Ok(IDLArgs { args })
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
    pub fn from_bytes_with_config(bytes: &[u8], config: &DecoderConfig) -> Result<Self> {
        let mut de = crate::de::IDLDeserialize::new_with_config(bytes, config)?;
        let mut args = Vec::new();
        while !de.is_done() {
            let v = de.get_value::<IDLValue>()?;
            args.push(v);
        }
        de.done()?;
        Ok(IDLArgs { args })
    }
}

impl IDLValue {
    /// Anotate `IDLValue` with the given type, allowing subtyping. If `IDLValue` is parsed from
    /// string, we need to set `from_parser` to true to enable converting numbers to the expected
    /// types, and disable the opt rules.
    pub fn annotate_type(&self, from_parser: bool, env: &TypeEnv, t: &Type) -> Result<Self> {
        Ok(match (self, t.as_ref()) {
            (_, TypeInner::Var(id)) => {
                let ty = env.rec_find_type(id)?;
                self.annotate_type(from_parser, env, ty)?
            }
            (_, TypeInner::Knot(ref id)) => {
                let ty = crate::types::internal::find_type(id).unwrap();
                self.annotate_type(from_parser, env, &ty)?
            }
            (_, TypeInner::Reserved) => IDLValue::Reserved,
            (IDLValue::Float64(n), TypeInner::Float32) if from_parser => {
                IDLValue::Float32(*n as f32)
            }
            (IDLValue::Null, TypeInner::Null) => IDLValue::Null,
            (IDLValue::Bool(b), TypeInner::Bool) => IDLValue::Bool(*b),
            (IDLValue::Nat(n), TypeInner::Nat) => IDLValue::Nat(n.clone()),
            (IDLValue::Int(i), TypeInner::Int) => IDLValue::Int(i.clone()),
            (IDLValue::Nat(n), TypeInner::Int) => IDLValue::Int(n.clone().into()),
            (IDLValue::Nat8(n), TypeInner::Nat8) => IDLValue::Nat8(*n),
            (IDLValue::Nat16(n), TypeInner::Nat16) => IDLValue::Nat16(*n),
            (IDLValue::Nat32(n), TypeInner::Nat32) => IDLValue::Nat32(*n),
            (IDLValue::Nat64(n), TypeInner::Nat64) => IDLValue::Nat64(*n),
            (IDLValue::Int8(n), TypeInner::Int8) => IDLValue::Int8(*n),
            (IDLValue::Int16(n), TypeInner::Int16) => IDLValue::Int16(*n),
            (IDLValue::Int32(n), TypeInner::Int32) => IDLValue::Int32(*n),
            (IDLValue::Int64(n), TypeInner::Int64) => IDLValue::Int64(*n),
            (IDLValue::Float64(n), TypeInner::Float64) => IDLValue::Float64(*n),
            (IDLValue::Float32(n), TypeInner::Float32) => IDLValue::Float32(*n),
            (IDLValue::Text(s), TypeInner::Text) => IDLValue::Text(s.to_owned()),
            // opt parsing. NB: Always succeeds!
            (IDLValue::Null, TypeInner::Opt(_)) => IDLValue::None,
            (IDLValue::Reserved, TypeInner::Opt(_)) => IDLValue::None,
            (IDLValue::None, TypeInner::Opt(_)) => IDLValue::None,
            (IDLValue::Opt(v), TypeInner::Opt(ty)) if from_parser => {
                IDLValue::Opt(Box::new(v.annotate_type(from_parser, env, ty)?))
            }
            // liberal decoding of optionals
            (IDLValue::Opt(v), TypeInner::Opt(ty)) if !from_parser => v
                .annotate_type(from_parser, env, ty)
                .map(|v| IDLValue::Opt(Box::new(v)))
                .unwrap_or(IDLValue::None),
            // try consituent type
            (v, TypeInner::Opt(ty))
                if !from_parser
                    && !matches!(
                        env.trace_type(ty)?.as_ref(),
                        TypeInner::Null | TypeInner::Reserved | TypeInner::Opt(_)
                    ) =>
            {
                v.annotate_type(from_parser, env, ty)
                    .map(|v| IDLValue::Opt(Box::new(v)))
                    .unwrap_or(IDLValue::None)
            }
            // fallback
            (_, TypeInner::Opt(_)) if !from_parser => IDLValue::None,
            (IDLValue::Blob(blob), ty) if ty.is_blob(env) => IDLValue::Blob(blob.to_vec()),
            (IDLValue::Vec(vec), ty) if ty.is_blob(env) => {
                let mut blob = Vec::with_capacity(vec.len());
                for e in vec.iter() {
                    match e {
                        IDLValue::Nat8(n) => blob.push(*n),
                        IDLValue::Number(n) => blob.push(n.parse::<u8>()?),
                        _ => {
                            return Err(Error::msg(format!(
                                "type mismatch: {e} cannot be of type nat8"
                            )))
                        }
                    }
                }
                IDLValue::Blob(blob)
            }
            (IDLValue::Vec(vec), TypeInner::Vec(ty)) => {
                let mut res = Vec::with_capacity(vec.len());
                for e in vec.iter() {
                    let v = e.annotate_type(from_parser, env, ty)?;
                    res.push(v);
                }
                IDLValue::Vec(res)
            }
            (IDLValue::Record(vec), TypeInner::Record(fs)) => {
                let fields: HashMap<_, _> =
                    vec.iter().map(|IDLField { id, val }| (id, val)).collect();
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    let val = fields
                        .get(id.as_ref())
                        .cloned()
                        .or_else(|| match env.trace_type(ty).unwrap().as_ref() {
                            TypeInner::Opt(_) => Some(&IDLValue::None),
                            TypeInner::Reserved => Some(&IDLValue::Reserved),
                            _ => None,
                        })
                        .ok_or_else(|| Error::msg(format!("record field {id} not found")))?;
                    let val = val.annotate_type(from_parser, env, ty)?;
                    res.push(IDLField {
                        id: id.as_ref().clone(),
                        val,
                    });
                }
                IDLValue::Record(res)
            }
            (IDLValue::Variant(v), TypeInner::Variant(fs)) => {
                for (i, f) in fs.iter().enumerate() {
                    if v.0.id == *f.id {
                        let val = v.0.val.annotate_type(from_parser, env, &f.ty)?;
                        let field = IDLField {
                            id: f.id.as_ref().clone(),
                            val,
                        };
                        return Ok(IDLValue::Variant(VariantValue(Box::new(field), i as u64)));
                    }
                }
                return Err(Error::msg(format!("variant field {} not found", v.0.id)));
            }
            (IDLValue::Principal(id), TypeInner::Principal) => IDLValue::Principal(*id),
            (IDLValue::Service(_), TypeInner::Service(_)) => self.clone(),
            (IDLValue::Func(_, _), TypeInner::Func(_)) => self.clone(),
            (IDLValue::Number(str), _) if from_parser => match t.as_ref() {
                TypeInner::Int => IDLValue::Int(str.parse::<Int>()?),
                TypeInner::Nat => IDLValue::Nat(str.parse::<Nat>()?),
                TypeInner::Nat8 => IDLValue::Nat8(str.parse::<u8>()?),
                TypeInner::Nat16 => IDLValue::Nat16(str.parse::<u16>()?),
                TypeInner::Nat32 => IDLValue::Nat32(str.parse::<u32>()?),
                TypeInner::Nat64 => IDLValue::Nat64(str.parse::<u64>()?),
                TypeInner::Int8 => IDLValue::Int8(str.parse::<i8>()?),
                TypeInner::Int16 => IDLValue::Int16(str.parse::<i16>()?),
                TypeInner::Int32 => IDLValue::Int32(str.parse::<i32>()?),
                TypeInner::Int64 => IDLValue::Int64(str.parse::<i64>()?),
                _ => {
                    return Err(Error::msg(format!(
                        "type mismatch: {self} can not be of type {t}"
                    )))
                }
            },
            _ => {
                return Err(Error::msg(format!(
                    "type mismatch: {self} cannot be of type {t}"
                )))
            }
        })
    }
    // This will only be called when the type is not provided
    pub fn value_ty(&self) -> Type {
        match *self {
            IDLValue::Null => TypeInner::Null,
            IDLValue::Bool(_) => TypeInner::Bool,
            IDLValue::Number(_) => TypeInner::Int, // Number defaults to Int
            IDLValue::Int(_) => TypeInner::Int,
            IDLValue::Nat(_) => TypeInner::Nat,
            IDLValue::Nat8(_) => TypeInner::Nat8,
            IDLValue::Nat16(_) => TypeInner::Nat16,
            IDLValue::Nat32(_) => TypeInner::Nat32,
            IDLValue::Nat64(_) => TypeInner::Nat64,
            IDLValue::Int8(_) => TypeInner::Int8,
            IDLValue::Int16(_) => TypeInner::Int16,
            IDLValue::Int32(_) => TypeInner::Int32,
            IDLValue::Int64(_) => TypeInner::Int64,
            IDLValue::Float32(_) => TypeInner::Float32,
            IDLValue::Float64(_) => TypeInner::Float64,
            IDLValue::Text(_) => TypeInner::Text,
            IDLValue::None => TypeInner::Opt(TypeInner::Empty.into()),
            IDLValue::Reserved => TypeInner::Reserved,
            IDLValue::Opt(ref v) => {
                let t = v.deref().value_ty();
                TypeInner::Opt(t)
            }
            IDLValue::Blob(_) => TypeInner::Vec(TypeInner::Nat8.into()),
            IDLValue::Vec(ref vec) => {
                let t = if vec.is_empty() {
                    TypeInner::Empty.into()
                } else {
                    vec[0].value_ty()
                };
                TypeInner::Vec(t)
            }
            IDLValue::Record(ref vec) => {
                let fs: Vec<_> = vec
                    .iter()
                    .map(|IDLField { id, val }| Field {
                        id: id.clone().into(),
                        ty: val.value_ty(),
                    })
                    .collect();
                TypeInner::Record(fs)
            }
            IDLValue::Variant(ref v) => {
                let f = Field {
                    id: v.0.id.clone().into(),
                    ty: v.0.val.value_ty(),
                };
                TypeInner::Variant(vec![f])
            }
            IDLValue::Principal(_) => TypeInner::Principal,
            IDLValue::Service(_) => TypeInner::Service(Vec::new()),
            IDLValue::Func(_, _) => {
                let f = crate::types::Function {
                    modes: Vec::new(),
                    args: Vec::new(),
                    rets: Vec::new(),
                };
                TypeInner::Func(f)
            }
        }
        .into()
    }

    /// Converts data that implements [`CandidType`] into an [`IDLValue`].
    ///
    /// # Example: Convert data to candid text format
    /// ```
    /// # use candid::{CandidType, IDLValue};
    /// #[derive(CandidType)]
    /// struct MyStruct {
    ///    a: u8,
    ///   b: String,
    /// }
    /// let my_struct = MyStruct { a: 42, b: "hello".to_string() };
    /// let idl_value = IDLValue::try_from_candid_type(&my_struct).unwrap();
    /// let expected_text = "record { a = 42 : nat8; b = \"hello\" }";
    /// let actual_text = idl_value.to_string();
    /// assert_eq!(expected_text, actual_text);
    /// ```
    pub fn try_from_candid_type<T>(data: &T) -> Result<Self>
    where
        T: CandidType,
    {
        use crate::Encode;
        let blob = Encode!(data)?;
        let args = IDLArgs::from_bytes_with_types(&blob, &TypeEnv::default(), &[T::ty()])?;
        Ok(args.args[0].clone())
    }
}

impl crate::CandidType for IDLValue {
    fn ty() -> Type {
        TypeInner::Unknown.into()
    }
    fn id() -> crate::types::TypeId {
        unreachable!();
    }
    fn _ty() -> Type {
        TypeInner::Unknown.into()
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
                let v = str.parse::<Int>().map_err(serde::ser::Error::custom)?;
                serializer.serialize_int(&v)
            }
            IDLValue::Int(ref i) => serializer.serialize_int(i),
            IDLValue::Nat(ref n) => serializer.serialize_nat(n),
            IDLValue::Nat8(n) => serializer.serialize_nat8(n),
            IDLValue::Nat16(n) => serializer.serialize_nat16(n),
            IDLValue::Nat32(n) => serializer.serialize_nat32(n),
            IDLValue::Nat64(n) => serializer.serialize_nat64(n),
            IDLValue::Int8(n) => serializer.serialize_int8(n),
            IDLValue::Int16(n) => serializer.serialize_int16(n),
            IDLValue::Int32(n) => serializer.serialize_int32(n),
            IDLValue::Int64(n) => serializer.serialize_int64(n),
            IDLValue::Float32(f) => serializer.serialize_float32(f),
            IDLValue::Float64(f) => serializer.serialize_float64(f),
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
            IDLValue::Blob(ref blob) => serializer.serialize_blob(blob),
            IDLValue::Record(ref vec) => {
                let mut ser = serializer.serialize_struct()?;
                for f in vec.iter() {
                    ser.serialize_element(&f.val)?;
                }
                Ok(())
            }
            IDLValue::Variant(ref v) => {
                let mut ser = serializer.serialize_variant(v.1)?;
                ser.serialize_element(&v.0.val)?;
                Ok(())
            }
            IDLValue::Principal(ref id) => serializer.serialize_principal(id.as_slice()),
            IDLValue::Service(ref id) => serializer.serialize_principal(id.as_slice()),
            IDLValue::Func(ref id, ref meth) => serializer.serialize_function(id.as_slice(), meth),
            IDLValue::Reserved => serializer.serialize_null(()),
        }
    }
}

type DResult<E> = std::result::Result<IDLValue, E>;

macro_rules! visit_prim {
    ($name:ident, $ty:ty) => {
        paste::item! {
            fn [<visit_ $ty>]<E>(self, value: $ty) -> DResult<E> {
                Ok(IDLValue::$name(value))
            }
        }
    };
}

/// A [`Visitor`] to extract [`IDLValue`]s.
#[derive(Copy, Clone)]
pub struct IDLValueVisitor;

impl<'de> Visitor<'de> for IDLValueVisitor {
    type Value = IDLValue;
    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("any valid Candid value")
    }
    visit_prim!(Bool, bool);
    visit_prim!(Nat8, u8);
    visit_prim!(Nat16, u16);
    visit_prim!(Nat32, u32);
    visit_prim!(Nat64, u64);
    visit_prim!(Int8, i8);
    visit_prim!(Int16, i16);
    visit_prim!(Int32, i32);
    visit_prim!(Int64, i64);
    visit_prim!(Float32, f32);
    visit_prim!(Float64, f64);
    // Deserialize Candid specific types: Bignumber, principal, reversed, service, function, blob
    fn visit_byte_buf<E: de::Error>(self, value: Vec<u8>) -> DResult<E> {
        let (tag, mut bytes) = value.split_at(1);
        match tag[0] {
            0u8 => {
                let v = Int(num_bigint::BigInt::from_signed_bytes_le(bytes));
                Ok(IDLValue::Int(v))
            }
            1u8 => {
                let v = Nat(num_bigint::BigUint::from_bytes_le(bytes));
                Ok(IDLValue::Nat(v))
            }
            2u8 => {
                let v = crate::Principal::try_from(bytes).map_err(E::custom)?;
                Ok(IDLValue::Principal(v))
            }
            3u8 => Ok(IDLValue::Reserved),
            4u8 => {
                let v = crate::Principal::try_from(bytes).map_err(E::custom)?;
                Ok(IDLValue::Service(v))
            }
            5u8 => {
                use std::io::Read;
                let len = leb128::read::unsigned(&mut bytes).map_err(E::custom)? as usize;
                let mut buf = vec![0; len];
                bytes.read_exact(&mut buf).map_err(E::custom)?;
                let meth = String::from_utf8(buf).map_err(E::custom)?;
                let id = crate::Principal::try_from(bytes).map_err(E::custom)?;
                Ok(IDLValue::Func(id, meth))
            }
            6u8 => Ok(IDLValue::Blob(bytes.to_vec())),
            _ => Err(de::Error::custom("unknown tag in visit_byte_buf")),
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
            let id = match key {
                IDLValue::Nat32(hash) => Label::Id(hash),
                IDLValue::Text(name) if name == "_" => continue,
                IDLValue::Text(name) => Label::Named(name),
                _ => unreachable!(),
            };
            let f = IDLField { id, val: value };
            vec.push(f);
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
            let (id, style) = match v.as_slice() {
                [name, "name", style] => (Label::Named(name.to_string()), style),
                [hash, "id", style] => (Label::Id(hash.parse::<u32>().unwrap()), style),
                _ => unreachable!(),
            };
            let val = match *style {
                "unit" => {
                    visitor.unit_variant()?;
                    IDLValue::Null
                }
                "struct" => visitor.struct_variant(&[], self)?,
                "newtype" => visitor.newtype_variant()?,
                _ => unreachable!(),
            };
            let f = IDLField { id, val };
            // Deserialized variant always has 0 index to ensure untyped
            // serialization is correct.
            Ok(IDLValue::Variant(VariantValue(Box::new(f), 0)))
        } else {
            unreachable!()
        }
    }
}

impl<'de> Deserialize<'de> for IDLValue {
    fn deserialize<D>(deserializer: D) -> DResult<D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(IDLValueVisitor)
    }
}
