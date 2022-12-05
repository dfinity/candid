//! Deserialize Candid binary format to Rust data structures

use super::{
    error::{Error, Result},
    parser::typing::TypeEnv,
    types::{Field, Label, Type},
    CandidType, Int, Nat,
};
use crate::{
    binary_parser::{BoolValue, Header, Len, PrincipalBytes},
    types::subtype::{subtype, Gamma},
};
use anyhow::{anyhow, Context};
use binread::BinRead;
use byteorder::{LittleEndian, ReadBytesExt};
use serde::de::{self, Visitor};
use std::fmt::Write;
use std::{collections::VecDeque, io::Cursor, mem::replace};

/// Use this struct to deserialize a sequence of Rust values (heterogeneous) from IDL binary message.
pub struct IDLDeserialize<'de> {
    de: Deserializer<'de>,
}
impl<'de> IDLDeserialize<'de> {
    /// Create a new deserializer with IDL binary message.
    pub fn new(bytes: &'de [u8]) -> Result<Self> {
        let de = Deserializer::from_bytes(bytes)
            .with_context(|| format!("Cannot parse header {}", &hex::encode(bytes)))?;
        Ok(IDLDeserialize { de })
    }
    /// Deserialize one value from deserializer.
    pub fn get_value<T>(&mut self) -> Result<T>
    where
        T: de::Deserialize<'de> + CandidType,
    {
        self.de.is_untyped = false;
        self.deserialize_with_type(T::ty())
    }
    pub fn get_value_with_type(
        &mut self,
        env: &TypeEnv,
        expected_type: &Type,
    ) -> Result<crate::parser::value::IDLValue> {
        self.de.table.merge(env)?;
        self.de.is_untyped = true;
        self.deserialize_with_type(expected_type.clone())
    }
    fn deserialize_with_type<T>(&mut self, expected_type: Type) -> Result<T>
    where
        T: de::Deserialize<'de> + CandidType,
    {
        let expected_type = self.de.table.trace_type(&expected_type)?;
        if self.de.types.is_empty() {
            if matches!(expected_type, Type::Opt(_) | Type::Reserved) {
                self.de.expect_type = expected_type;
                self.de.wire_type = Type::Reserved;
                return T::deserialize(&mut self.de);
            } else {
                return Err(Error::msg(format!(
                    "No more values on the wire, the expected type {} is not opt or reserved",
                    expected_type
                )));
            }
        }

        let (ind, ty) = self.de.types.pop_front().unwrap();
        self.de.expect_type = if matches!(expected_type, Type::Unknown) {
            self.de.is_untyped = true;
            ty.clone()
        } else {
            expected_type.clone()
        };
        self.de.wire_type = ty.clone();

        let v = T::deserialize(&mut self.de)
            .with_context(|| self.de.dump_state())
            .with_context(|| {
                format!(
                    "Fail to decode argument {} from {} to {}",
                    ind, ty, expected_type
                )
            })?;
        Ok(v)
    }
    /// Check if we finish deserializing all values.
    pub fn is_done(&self) -> bool {
        self.de.types.is_empty()
    }
    /// Return error if there are unprocessed bytes in the input.
    pub fn done(mut self) -> Result<()> {
        while !self.is_done() {
            self.get_value::<crate::Reserved>()?;
        }
        let ind = self.de.input.position() as usize;
        let rest = &self.de.input.get_ref()[ind..];
        if !rest.is_empty() {
            return Err(anyhow!(self.de.dump_state()))
                .context("Trailing value after finishing deserialization")?;
        }
        Ok(())
    }
}

macro_rules! assert {
    ( false ) => {{
        return Err(Error::msg(format!(
            "Internal error at {}:{}. Please file a bug.",
            file!(),
            line!()
        )));
    }};
    ( $pred:expr ) => {{
        if !$pred {
            return Err(Error::msg(format!(
                "Internal error at {}:{}. Please file a bug.",
                file!(),
                line!()
            )));
        }
    }};
}

macro_rules! check {
    ( false ) => {{
        return Err(Error::Subtype(format!(
            "Type mismatch at {}:{}",
            file!(),
            line!()
        )));
    }};
    ($exp:expr, $msg:expr) => {{
        if !$exp {
            return Err(Error::Subtype($msg.to_string()));
        }
    }};
}

struct Deserializer<'de> {
    input: Cursor<&'de [u8]>,
    table: TypeEnv,
    types: VecDeque<(usize, Type)>,
    wire_type: Type,
    expect_type: Type,
    // Memo table for subtyping relation
    gamma: Gamma,
    // field_name tells deserialize_identifier which field name to process.
    // This field should always be set by set_field_name function.
    field_name: Option<Label>,
    // Indicates whether to deserialize with IDLValue.
    // It only affects the field id generation in enum type.
    is_untyped: bool,
}

impl<'de> Deserializer<'de> {
    fn from_bytes(bytes: &'de [u8]) -> Result<Self> {
        let mut reader = Cursor::new(bytes);
        let header = Header::read(&mut reader)?;
        let (env, types) = header.to_types()?;
        Ok(Deserializer {
            input: reader,
            table: env,
            types: types.into_iter().enumerate().collect(),
            wire_type: Type::Unknown,
            expect_type: Type::Unknown,
            gamma: Gamma::default(),
            field_name: None,
            is_untyped: false,
        })
    }
    fn dump_state(&self) -> String {
        let hex = hex::encode(self.input.get_ref());
        let pos = self.input.position() as usize * 2;
        let (before, after) = hex.split_at(pos);
        let mut res = format!("input: {}_{}\n", before, after);
        if !self.table.0.is_empty() {
            write!(&mut res, "table: {}", self.table).unwrap();
        }
        write!(
            &mut res,
            "wire_type: {}, expect_type: {}",
            self.wire_type, self.expect_type
        )
        .unwrap();
        if let Some(field) = &self.field_name {
            write!(&mut res, ", field_name: {:?}", field).unwrap();
        }
        res
    }
    fn borrow_bytes(&mut self, len: usize) -> Result<&'de [u8]> {
        let pos = self.input.position() as usize;
        let slice = self.input.get_ref();
        if len > slice.len() || pos + len > slice.len() {
            return Err(Error::msg(format!("Cannot read {} bytes", len)));
        }
        let end = pos + len;
        let res = &slice[pos..end];
        self.input.set_position(end as u64);
        Ok(res)
    }
    fn check_subtype(&mut self) -> Result<()> {
        subtype(
            &mut self.gamma,
            &self.table,
            &self.wire_type,
            &self.expect_type,
        )
        .with_context(|| {
            format!(
                "{} is not a subtype of {}",
                self.wire_type, self.expect_type,
            )
        })
        .map_err(Error::subtype)?;
        Ok(())
    }
    fn unroll_type(&mut self) -> Result<()> {
        if matches!(self.expect_type, Type::Var(_) | Type::Knot(_)) {
            self.expect_type = self.table.trace_type(&self.expect_type)?;
        }
        if matches!(self.wire_type, Type::Var(_) | Type::Knot(_)) {
            self.wire_type = self.table.trace_type(&self.wire_type)?;
        }
        Ok(())
    }
    // Should always call set_field_name to set the field_name. After deserialize_identifier
    // processed the field_name, field_name will be reset to None.
    fn set_field_name(&mut self, field: Label) {
        if self.field_name.is_some() {
            unreachable!();
        }
        self.field_name = Some(field);
    }
    // Customize deserailization methods
    // Several deserialize functions will call visit_byte_buf.
    // We reserve the first byte to be a tag to distinguish between different callers:
    // int(0), nat(1), principal(2), reserved(3), service(4), function(5)
    // This is necessary for deserializing IDLValue because
    // it has only one visitor and we need a way to know who called the visitor.
    fn deserialize_int<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use std::convert::TryInto;
        self.unroll_type()?;
        assert!(self.expect_type == Type::Int);
        let mut bytes = vec![0u8];
        let int = match &self.wire_type {
            Type::Int => Int::decode(&mut self.input).map_err(Error::msg)?,
            Type::Nat => Int(Nat::decode(&mut self.input)
                .map_err(Error::msg)?
                .0
                .try_into()
                .map_err(Error::msg)?),
            t => {
                return Err(Error::subtype(format!(
                    "{} cannot be deserialized to int",
                    t
                )))
            }
        };
        bytes.extend_from_slice(&int.0.to_signed_bytes_le());
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_nat<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Nat && self.wire_type == Type::Nat,
            "nat"
        );
        let mut bytes = vec![1u8];
        let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
        bytes.extend_from_slice(&nat.0.to_bytes_le());
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_principal<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Principal && self.wire_type == Type::Principal,
            "principal"
        );
        let mut bytes = vec![2u8];
        let id = PrincipalBytes::read(&mut self.input)?.inner;
        bytes.extend_from_slice(&id);
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_reserved<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let bytes = vec![3u8];
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_service<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        self.check_subtype()?;
        let mut bytes = vec![4u8];
        let id = PrincipalBytes::read(&mut self.input)?.inner;
        bytes.extend_from_slice(&id);
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_function<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        self.check_subtype()?;
        if !BoolValue::read(&mut self.input)?.0 {
            return Err(Error::msg("Opaque reference not supported"));
        }
        let mut bytes = vec![5u8];
        let id = PrincipalBytes::read(&mut self.input)?.inner;
        let len = Len::read(&mut self.input)?.0;
        let meth = self.borrow_bytes(len)?;
        // TODO find a better way
        leb128::write::unsigned(&mut bytes, len as u64)?;
        bytes.extend_from_slice(meth);
        bytes.extend_from_slice(&id);
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_empty<'a, V>(&'a mut self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::subtype("Cannot decode empty type"))
    }
    fn deserialize_future<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let len = Len::read(&mut self.input)?.0 as u64;
        Len::read(&mut self.input)?;
        let pos = self.input.position();
        self.input.set_position(pos + len);
        visitor.visit_unit()
    }
    unsafe fn recoverable_visit_some<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use de::Deserializer;
        let v = std::ptr::read(&visitor);
        let self_ptr = std::ptr::read(&self);
        match v.visit_some(self_ptr) {
            Ok(v) => Ok(v),
            Err(Error::Subtype(_)) => {
                self.deserialize_ignored_any(serde::de::IgnoredAny)?;
                visitor.visit_none()
            }
            Err(e) => Err(e),
        }
    }
}

macro_rules! primitive_impl {
    ($ty:ident, $type:expr, $($value:tt)*) => {
        paste::item! {
            fn [<deserialize_ $ty>]<V>(self, visitor: V) -> Result<V::Value>
            where V: Visitor<'de> {
                self.unroll_type()?;
                check!(self.expect_type == $type && self.wire_type == $type, stringify!($type));
                let val = self.input.$($value)*().map_err(|_| Error::msg(format!("Cannot read {} value", stringify!($type))))?;
                visitor.[<visit_ $ty>](val)
            }
        }
    };
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if self.field_name.is_some() {
            return self.deserialize_identifier(visitor);
        }
        self.unroll_type()?;
        match &self.expect_type {
            Type::Int => self.deserialize_int(visitor),
            Type::Nat => self.deserialize_nat(visitor),
            Type::Nat8 => self.deserialize_u8(visitor),
            Type::Nat16 => self.deserialize_u16(visitor),
            Type::Nat32 => self.deserialize_u32(visitor),
            Type::Nat64 => self.deserialize_u64(visitor),
            Type::Int8 => self.deserialize_i8(visitor),
            Type::Int16 => self.deserialize_i16(visitor),
            Type::Int32 => self.deserialize_i32(visitor),
            Type::Int64 => self.deserialize_i64(visitor),
            Type::Float32 => self.deserialize_f32(visitor),
            Type::Float64 => self.deserialize_f64(visitor),
            Type::Bool => self.deserialize_bool(visitor),
            Type::Text => self.deserialize_string(visitor),
            Type::Null => self.deserialize_unit(visitor),
            Type::Reserved => {
                if self.wire_type != Type::Reserved {
                    self.deserialize_ignored_any(serde::de::IgnoredAny)?;
                }
                self.deserialize_reserved(visitor)
            }
            Type::Empty => self.deserialize_empty(visitor),
            Type::Principal => self.deserialize_principal(visitor),
            // construct types
            Type::Opt(_) => self.deserialize_option(visitor),
            Type::Vec(_) => self.deserialize_seq(visitor),
            Type::Record(_) => self.deserialize_struct("_", &[], visitor),
            Type::Variant(_) => self.deserialize_enum("_", &[], visitor),
            Type::Service(_) => self.deserialize_service(visitor),
            Type::Func(_) => self.deserialize_function(visitor),
            Type::Future => self.deserialize_future(visitor),
            _ => assert!(false),
        }
    }
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let is_untyped = replace(&mut self.is_untyped, true);
        self.expect_type = self.wire_type.clone();
        let v = self.deserialize_any(visitor);
        self.is_untyped = is_untyped;
        v
    }

    primitive_impl!(i8, Type::Int8, read_i8);
    primitive_impl!(i16, Type::Int16, read_i16::<LittleEndian>);
    primitive_impl!(i32, Type::Int32, read_i32::<LittleEndian>);
    primitive_impl!(i64, Type::Int64, read_i64::<LittleEndian>);
    primitive_impl!(u8, Type::Nat8, read_u8);
    primitive_impl!(u16, Type::Nat16, read_u16::<LittleEndian>);
    primitive_impl!(u32, Type::Nat32, read_u32::<LittleEndian>);
    primitive_impl!(u64, Type::Nat64, read_u64::<LittleEndian>);
    primitive_impl!(f32, Type::Float32, read_f32::<LittleEndian>);
    primitive_impl!(f64, Type::Float64, read_f64::<LittleEndian>);

    fn is_human_readable(&self) -> bool {
        false
    }
    fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use std::convert::TryInto;
        self.unroll_type()?;
        assert!(self.expect_type == Type::Int);
        let value: i128 = match &self.wire_type {
            Type::Int => {
                let int = Int::decode(&mut self.input).map_err(Error::msg)?;
                int.0.try_into().map_err(Error::msg)?
            }
            Type::Nat => {
                let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
                nat.0.try_into().map_err(Error::msg)?
            }
            t => {
                return Err(Error::subtype(format!(
                    "{} cannot be deserialized to int",
                    t
                )))
            }
        };
        visitor.visit_i128(value)
    }
    fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use std::convert::TryInto;
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Nat && self.wire_type == Type::Nat,
            "nat"
        );
        let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
        let value: u128 = nat.0.try_into().map_err(Error::msg)?;
        visitor.visit_u128(value)
    }
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Null && self.wire_type == Type::Null,
            "unit"
        );
        visitor.visit_unit()
    }
    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Bool && self.wire_type == Type::Bool,
            "bool"
        );
        let res = BoolValue::read(&mut self.input)?;
        visitor.visit_bool(res.0)
    }
    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Text && self.wire_type == Type::Text,
            "text"
        );
        let len = Len::read(&mut self.input)?.0;
        let bytes = self.borrow_bytes(len)?.to_owned();
        let value = String::from_utf8(bytes).map_err(Error::msg)?;
        visitor.visit_string(value)
    }
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Text && self.wire_type == Type::Text,
            "text"
        );
        let len = Len::read(&mut self.input)?.0;
        let slice = self.borrow_bytes(len)?;
        let value: &str = std::str::from_utf8(slice).map_err(Error::msg)?;
        visitor.visit_borrowed_str(value)
    }
    fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }
    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }
    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        match (&self.wire_type, &self.expect_type) {
            (Type::Null, Type::Opt(_)) | (Type::Reserved, Type::Opt(_)) => visitor.visit_none(),
            (Type::Opt(t1), Type::Opt(t2)) => {
                self.wire_type = *t1.clone();
                self.expect_type = *t2.clone();
                if BoolValue::read(&mut self.input)?.0 {
                    unsafe { self.recoverable_visit_some(visitor) }
                } else {
                    visitor.visit_none()
                }
            }
            (_, Type::Opt(t2)) => {
                self.expect_type = self.table.trace_type(t2)?;
                if !matches!(self.expect_type, Type::Null | Type::Reserved | Type::Opt(_)) {
                    unsafe { self.recoverable_visit_some(visitor) }
                } else {
                    self.deserialize_ignored_any(serde::de::IgnoredAny)?;
                    visitor.visit_none()
                }
            }
            (_, _) => check!(false),
        }
    }
    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Vec(ref e), Type::Vec(ref w)) => {
                let expect = *e.clone();
                let wire = *w.clone();
                let len = Len::read(&mut self.input)?.0;
                visitor.visit_seq(Compound::new(self, Style::Vector { len, expect, wire }))
            }
            (Type::Record(e), Type::Record(w)) => {
                let expect = e.clone().into();
                let wire = w.clone().into();
                check!(self.expect_type.is_tuple(), "seq_tuple");
                if !self.wire_type.is_tuple() {
                    return Err(Error::subtype(format!(
                        "{} is not a tuple type",
                        self.wire_type
                    )));
                }
                let value =
                    visitor.visit_seq(Compound::new(self, Style::Struct { expect, wire }))?;
                Ok(value)
            }
            _ => check!(false),
        }
    }
    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.unroll_type()?;
        check!(
            self.expect_type == Type::Vec(Box::new(Type::Nat8))
                && self.wire_type == Type::Vec(Box::new(Type::Nat8)),
            "vec nat8"
        );
        let len = Len::read(&mut self.input)?.0;
        let bytes = self.borrow_bytes(len)?.to_owned();
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.unroll_type()?;
        match &self.expect_type {
            Type::Principal => self.deserialize_principal(visitor),
            Type::Vec(t) if **t == Type::Nat8 => {
                let len = Len::read(&mut self.input)?.0;
                let slice = self.borrow_bytes(len)?;
                visitor.visit_borrowed_bytes(slice)
            }
            _ => Err(Error::subtype("bytes only takes principal or vec nat8")),
        }
    }
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Vec(ref e), Type::Vec(ref w)) => {
                let e = self.table.trace_type(e)?;
                let w = self.table.trace_type(w)?;
                match (e, w) {
                    (Type::Record(ref e), Type::Record(ref w)) => match (&e[..], &w[..]) {
                        (
                            [Field {
                                id: Label::Id(0),
                                ty: ek,
                            }, Field {
                                id: Label::Id(1),
                                ty: ev,
                            }],
                            [Field {
                                id: Label::Id(0),
                                ty: wk,
                            }, Field {
                                id: Label::Id(1),
                                ty: wv,
                            }],
                        ) => {
                            let expect = (ek.clone(), ev.clone());
                            let wire = (wk.clone(), wv.clone());
                            let len = Len::read(&mut self.input)?.0;
                            visitor.visit_map(Compound::new(self, Style::Map { len, expect, wire }))
                        }
                        _ => Err(Error::subtype("expect a key-value pair")),
                    },
                    _ => Err(Error::subtype("expect a key-value pair")),
                }
            }
            _ => check!(false),
        }
    }
    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }
    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }
    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Record(e), Type::Record(w)) => {
                let expect = e.clone().into();
                let wire = w.clone().into();
                let value =
                    visitor.visit_map(Compound::new(self, Style::Struct { expect, wire }))?;
                Ok(value)
            }
            _ => check!(false),
        }
    }
    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Variant(e), Type::Variant(w)) => {
                let old_pos = self.input.position();
                let index = Len::read(&mut self.input)?.0;
                let len = w.len();
                if index >= len {
                    return Err(Error::msg(format!(
                        "Variant index {} larger than length {}",
                        index, len
                    )));
                }
                let wire = w[index].clone();
                let expect = match e.iter().find(|f| f.id == wire.id) {
                    Some(v) => v.clone(),
                    None => {
                        self.input.set_position(old_pos);
                        return Err(Error::subtype(format!("Unknown variant field {}", wire.id)));
                    }
                };
                visitor.visit_enum(Compound::new(self, Style::Enum { expect, wire }))
            }
            _ => check!(false),
        }
    }
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.field_name.take() {
            Some(Label::Named(name)) => visitor.visit_string(name),
            Some(Label::Id(hash)) | Some(Label::Unnamed(hash)) => visitor.visit_u32(hash),
            None => assert!(false),
        }
    }

    serde::forward_to_deserialize_any! {
        char
    }
}

#[derive(Debug)]
enum Style {
    Vector {
        len: usize,
        expect: Type,
        wire: Type,
    },
    Struct {
        expect: VecDeque<Field>,
        wire: VecDeque<Field>,
    },
    Enum {
        expect: Field,
        wire: Field,
    },
    Map {
        len: usize,
        expect: (Type, Type),
        wire: (Type, Type),
    },
}

struct Compound<'a, 'de> {
    de: &'a mut Deserializer<'de>,
    style: Style,
}

impl<'a, 'de> Compound<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>, style: Style) -> Self {
        Compound { de, style }
    }
}

impl<'de, 'a> de::SeqAccess<'de> for Compound<'a, 'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: de::DeserializeSeed<'de>,
    {
        match self.style {
            Style::Vector {
                ref mut len,
                ref expect,
                ref wire,
            } => {
                if *len == 0 {
                    return Ok(None);
                }
                *len -= 1;
                self.de.expect_type = expect.clone();
                self.de.wire_type = wire.clone();
                seed.deserialize(&mut *self.de).map(Some)
            }
            Style::Struct {
                ref mut expect,
                ref mut wire,
            } => {
                if expect.is_empty() && wire.is_empty() {
                    return Ok(None);
                }
                self.de.expect_type = expect.pop_front().map(|f| f.ty).unwrap_or(Type::Reserved);
                self.de.wire_type = wire.pop_front().map(|f| f.ty).unwrap_or(Type::Reserved);
                seed.deserialize(&mut *self.de).map(Some)
            }
            _ => Err(Error::subtype("expect vector or tuple")),
        }
    }
}

impl<'de, 'a> de::MapAccess<'de> for Compound<'a, 'de> {
    type Error = Error;
    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: de::DeserializeSeed<'de>,
    {
        match self.style {
            Style::Struct {
                ref mut expect,
                ref mut wire,
            } => {
                match (expect.front(), wire.front()) {
                    (Some(e), Some(w)) => {
                        use std::cmp::Ordering;
                        match e.id.get_id().cmp(&w.id.get_id()) {
                            Ordering::Equal => {
                                self.de.set_field_name(e.id.clone());
                                self.de.expect_type = expect.pop_front().unwrap().ty;
                                self.de.wire_type = wire.pop_front().unwrap().ty;
                            }
                            Ordering::Less => {
                                // by subtyping rules, expect_type can only be opt, reserved or null.
                                let field = e.id.clone();
                                self.de.set_field_name(field.clone());
                                let expect = expect.pop_front().unwrap().ty;
                                self.de.expect_type = self.de.table.trace_type(&expect)?;
                                check!(
                                    matches!(
                                        self.de.expect_type,
                                        Type::Opt(_) | Type::Reserved | Type::Null
                                    ),
                                    format!("field {} is not optional field", field)
                                );
                                self.de.wire_type = Type::Reserved;
                            }
                            Ordering::Greater => {
                                self.de.set_field_name(Label::Named("_".to_owned()));
                                self.de.wire_type = wire.pop_front().unwrap().ty;
                                self.de.expect_type = Type::Reserved;
                            }
                        }
                    }
                    (None, Some(_)) => {
                        self.de.set_field_name(Label::Named("_".to_owned()));
                        self.de.wire_type = wire.pop_front().unwrap().ty;
                        self.de.expect_type = Type::Reserved;
                    }
                    (Some(e), None) => {
                        self.de.set_field_name(e.id.clone());
                        self.de.expect_type = expect.pop_front().unwrap().ty;
                        self.de.wire_type = Type::Reserved;
                    }
                    (None, None) => return Ok(None),
                }
                seed.deserialize(&mut *self.de).map(Some)
            }
            Style::Map {
                ref mut len,
                ref expect,
                ref wire,
            } => {
                // This only comes from deserialize_map
                if *len == 0 {
                    return Ok(None);
                }
                self.de.expect_type = expect.0.clone();
                self.de.wire_type = wire.0.clone();
                *len -= 1;
                seed.deserialize(&mut *self.de).map(Some)
            }
            _ => Err(Error::msg("expect struct or map")),
        }
    }
    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        match &self.style {
            Style::Map { expect, wire, .. } => {
                self.de.expect_type = expect.1.clone();
                self.de.wire_type = wire.1.clone();
                seed.deserialize(&mut *self.de)
            }
            _ => seed.deserialize(&mut *self.de),
        }
    }
}

impl<'de, 'a> de::EnumAccess<'de> for Compound<'a, 'de> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: de::DeserializeSeed<'de>,
    {
        match &self.style {
            Style::Enum { expect, wire } => {
                self.de.expect_type = expect.ty.clone();
                self.de.wire_type = wire.ty.clone();
                let (mut label, label_type) = match &expect.id {
                    Label::Named(name) => (name.clone(), "name"),
                    Label::Id(hash) | Label::Unnamed(hash) => (hash.to_string(), "id"),
                };
                if self.de.is_untyped {
                    let accessor = match &expect.ty {
                        Type::Null => "unit",
                        Type::Record(_) => "struct",
                        _ => "newtype",
                    };
                    write!(&mut label, ",{},{}", label_type, accessor).map_err(Error::msg)?;
                }
                self.de.set_field_name(Label::Named(label));
                let field = seed.deserialize(&mut *self.de)?;
                Ok((field, self))
            }
            _ => Err(Error::subtype("expect enum")),
        }
    }
}

impl<'de, 'a> de::VariantAccess<'de> for Compound<'a, 'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        check!(
            self.de.expect_type == Type::Null && self.de.wire_type == Type::Null,
            "unit_variant"
        );
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: de::DeserializeSeed<'de>,
    {
        seed.deserialize(self.de)
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        de::Deserializer::deserialize_tuple(self.de, len, visitor)
    }

    fn struct_variant<V>(self, fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        de::Deserializer::deserialize_struct(self.de, "_", fields, visitor)
    }
}
