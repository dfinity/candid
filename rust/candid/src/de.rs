//! Deserialize Candid binary format to Rust data structures

use super::error::{Error, Result};
use super::{
    parser::typing::TypeEnv,
    types::{Field, Label, Type},
    CandidType, Int, Nat,
};
use crate::binary_parser::{BoolValue, Bytes, Header, Len};
use crate::types::subtype::{subtype, Gamma};
use anyhow::{anyhow, Context};
use binread::BinRead;
use byteorder::{LittleEndian, ReadBytesExt};
use serde::de::{self, Visitor};
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::io::{Cursor, Read};

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
        let (ind, ty) = self
            .de
            .types
            .pop_front()
            .context("No more values to deserialize")?;
        let expected_type = T::ty();
        self.de.expect_type = if matches!(expected_type, Type::Unknown) {
            ty.clone()
        } else {
            expected_type
        };
        self.de.wire_type = ty.clone();
        self.de.check_subtype()?;

        let v = T::deserialize(&mut self.de)
            .with_context(|| self.de.dump_state())
            .with_context(|| {
                format!("Fail to decode argument {} from {} to {}", ind, ty, T::ty())
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
    // The record nesting depth should be bounded by the length of table to avoid infinite loop.
    record_nesting_depth: usize,
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
            record_nesting_depth: 0,
        })
    }
    fn dump_state(&self) -> String {
        let hex = hex::encode(self.input.get_ref());
        let pos = self.input.position() as usize * 2;
        let (before, after) = hex.split_at(pos);
        let mut res = format!("input: {}_{}\n", before, after);
        if !self.table.0.is_empty() {
            res += &format!("table: {}", self.table);
        }
        res += &format!(
            "wire_type: {}, expect_type: {}",
            self.wire_type, self.expect_type
        );
        if let Some(field) = &self.field_name {
            res += &format!(", field_name: {:?}", field);
        }
        res
    }
    fn check_subtype(&mut self) -> Result<()> {
        if !subtype(
            &mut self.gamma,
            &self.table,
            &self.wire_type,
            &self.table,
            &self.expect_type,
        ) {
            Err(Error::msg(format!(
                "{} is not subtype of {}",
                self.wire_type, self.expect_type,
            )))
        } else {
            Ok(())
        }
    }
    fn unroll_type(&mut self) -> Result<()> {
        self.expect_type = self.table.trace_type(&self.expect_type)?;
        self.wire_type = self.table.trace_type(&self.wire_type)?;
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
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Int);
        let mut bytes = Vec::new();
        match &self.wire_type {
            Type::Int => {
                bytes.push(0u8);
                let int = Int::decode(&mut self.input).map_err(Error::msg)?;
                bytes.extend_from_slice(&int.0.to_signed_bytes_le());
            }
            Type::Nat => {
                bytes.push(1u8);
                let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
                bytes.extend_from_slice(&nat.0.to_bytes_le());
            }
            // We already did subtype checking before deserialize, so this is unreachable code
            _ => assert!(false),
        }
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_nat<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Nat && self.wire_type == Type::Nat);
        let mut bytes = vec![1u8];
        let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
        bytes.extend_from_slice(&nat.0.to_bytes_le());
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_reserved<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Reserved);
        let bytes = vec![3u8];
        visitor.visit_byte_buf(bytes)
    }
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
        let t = self.table.trace_type(&self.expect_type)?;
        // TODO needed?
        if !matches!(t, Type::Record(_)) {
            self.record_nesting_depth = 0;
        }
        match t {
            Type::Int => self.deserialize_int(visitor),
            Type::Nat => self.deserialize_nat(visitor),
            /*Type::Nat8 => self.deserialize_u8(visitor),
            Type::Nat16 => self.deserialize_u16(visitor),
            Type::Nat32 => self.deserialize_u32(visitor),
            Type::Nat64 => self.deserialize_u64(visitor),
            Type::Int8 => self.deserialize_i8(visitor),
            Type::Int16 => self.deserialize_i16(visitor),
            Type::Int32 => self.deserialize_i32(visitor),
            Type::Int64 => self.deserialize_i64(visitor),
            Type::Float32 => self.deserialize_f32(visitor),
            Type::Float64 => self.deserialize_f64(visitor),*/
            Type::Bool => self.deserialize_bool(visitor),
            Type::Text => self.deserialize_string(visitor),
            Type::Null => self.deserialize_unit(visitor),
            Type::Reserved => self.deserialize_reserved(visitor),
            //Type::Empty => self.deserialize_empty(visitor),
            // construct types
            Type::Opt(_) => self.deserialize_option(visitor),
            Type::Vec(_) => self.deserialize_seq(visitor),
            Type::Record(_) => self.deserialize_struct("_", &[], visitor),
            Type::Variant(_) => self.deserialize_enum("_", &[], visitor),
            _ => assert!(false),
        }
    }
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.expect_type = self.wire_type.clone();
        self.deserialize_any(visitor)
    }
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Null && self.wire_type == Type::Null);
        visitor.visit_unit()
    }
    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Bool && self.wire_type == Type::Bool);
        let res = BoolValue::read(&mut self.input)?;
        visitor.visit_bool(res.0)
    }
    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Text && self.wire_type == Type::Text);
        let bytes = Bytes::read(&mut self.input)?;
        let value = String::from_utf8(bytes.inner).map_err(Error::msg)?;
        visitor.visit_string(value)
    }
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self.expect_type == Type::Text && self.wire_type == Type::Text);
        let len = Len::read(&mut self.input)?.0 as usize;
        let pos = self.input.position() as usize;
        let end = pos + len;
        let slice = &self.input.get_ref()[pos..end];
        self.input.set_position(end as u64);
        let value: &str = std::str::from_utf8(slice).map_err(Error::msg)?;
        visitor.visit_borrowed_str(value)
    }
    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.unroll_type()?;
        match self.expect_type {
            Type::Opt(ref t) => self.expect_type = *t.clone(),
            _ => assert!(false),
        }
        match self.wire_type {
            Type::Null | Type::Reserved => visitor.visit_none(),
            Type::Opt(ref t) => {
                self.wire_type = *t.clone();
                if BoolValue::read(&mut self.input)?.0 {
                    if self.check_subtype().is_ok() {
                        visitor.visit_some(self)
                    } else {
                        visitor.visit_none()
                    }
                } else {
                    visitor.visit_none()
                }
            }
            _ => {
                if self.check_subtype().is_ok() {
                    visitor.visit_some(self)
                } else {
                    visitor.visit_none()
                }
            }
        }
    }
    fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Vec(ref e), Type::Vec(ref w)) => {
                self.expect_type = *e.clone();
                self.wire_type = *w.clone();
                let len = Len::read(&mut self.input)?.0;
                visitor.visit_seq(Compound::new(&mut self, Style::Vector { len }))
            }
            _ => assert!(false),
        }
    }
    fn deserialize_struct<V>(
        mut self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let old_nesting = self.record_nesting_depth;
        self.record_nesting_depth += 1;
        if self.record_nesting_depth > self.table.0.len() {
            return Err(Error::msg("There is an infinite loop in the record definition, the type is isomorphic to an empty type"));
        }
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Record(e), Type::Record(w)) => {
                let expect = e.clone().into();
                let wire = w.clone().into();
                let value =
                    visitor.visit_map(Compound::new(&mut self, Style::Struct { expect, wire }))?;
                self.record_nesting_depth = old_nesting;
                Ok(value)
            }
            _ => assert!(false),
        }
    }
    fn deserialize_enum<V>(
        mut self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.unroll_type()?;
        match (&self.expect_type, &self.wire_type) {
            (Type::Variant(e), Type::Variant(w)) => {
                let index = usize::try_from(Len::read(&mut self.input)?.0).map_err(Error::msg)?;
                let len = w.len();
                if index >= len {
                    return Err(Error::msg(format!(
                        "Variant index {} larger than length {}",
                        index, len
                    )));
                }
                let wire = w[index].clone();
                let expect = e
                    .iter()
                    .find(|&f| f.id == wire.id)
                    .ok_or_else(|| Error::msg(format!("Unknown variant field {}", wire.id)))?
                    .clone();
                visitor.visit_enum(Compound::new(&mut self, Style::Enum { expect, wire }))
            }
            _ => assert!(false),
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
        u8
        u16
        u32
        u64
        i8
        i16
        i32
        i64
        f32
        f64
        char
        bytes
        byte_buf
        unit_struct
        newtype_struct
        tuple_struct
        tuple
        map
    }
}

#[derive(Debug)]
enum Style {
    Tuple {
        len: u32,
        index: u32,
    },
    Vector {
        len: u64, // non-vector length can only be u32, because field ids is u32.
    },
    Struct {
        expect: VecDeque<Field>,
        wire: VecDeque<Field>,
    },
    Enum {
        expect: Field,
        wire: Field,
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
            Style::Vector { ref mut len } => {
                if *len == 0 {
                    return Ok(None);
                }
                *len -= 1;
                seed.deserialize(&mut *self.de).map(Some)
            }
            _ => Err(Error::msg("expect vector")),
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
                        if e.id.get_id() == w.id.get_id() {
                            self.de.set_field_name(e.id.clone());
                            self.de.expect_type = expect.pop_front().unwrap().ty;
                            self.de.wire_type = wire.pop_front().unwrap().ty;
                        } else if e.id.get_id() < w.id.get_id() {
                            // by subtyping rules, expect_type can only be opt, reserved or null.
                            self.de.set_field_name(e.id.clone());
                            self.de.expect_type = expect.pop_front().unwrap().ty;
                            self.de.wire_type = Type::Reserved;
                        } else {
                            self.de.set_field_name(Label::Named("_".to_owned()));
                            self.de.wire_type = expect.pop_front().unwrap().ty;
                            self.de.expect_type = Type::Reserved;
                        }
                    }
                    (None, Some(_)) => {
                        self.de.set_field_name(Label::Named("_".to_owned()));
                        self.de.wire_type = expect.pop_front().unwrap().ty;
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
            /*
            Style::Map { ref mut len, .. } => {
                // This only comes from deserialize_map
                if *len == 0 {
                    return Ok(None);
                }
                self.de.table.check_type(Opcode::Record)?;
                assert_eq!(2, self.de.table.pop_current_type()?.get_u32()?);
                assert_eq!(0, self.de.table.pop_current_type()?.get_u32()?);
                *len -= 1;
                seed.deserialize(&mut *self.de).map(Some)
            }*/
            _ => Err(Error::msg("expect struct or map")),
        }
    }
    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        seed.deserialize(&mut *self.de)
        /*
        match self.style {
            Style::Map { ref ty, .. } => {
                assert_eq!(1, self.de.table.pop_current_type()?.get_u32()?);
                let res = seed.deserialize(&mut *self.de);
                self.de.table.current_type.push_front(ty.clone());
                res
            }
            _ => seed.deserialize(&mut *self.de),
        }*/
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
                let label = match &expect.id {
                    Label::Named(name) => name.clone(),
                    Label::Id(hash) | Label::Unnamed(hash) => {
                        let accessor = match &expect.ty {
                            Type::Null => "unit",
                            Type::Record(_) => "struct",
                            _ => "newtype",
                        };
                        format!("{},{}", hash, accessor)
                    }
                };
                self.de.set_field_name(Label::Named(label));
                let field = seed.deserialize(&mut *self.de)?;
                Ok((field, self))
            }
            _ => Err(Error::msg("expect enum")),
        }
    }
}

impl<'de, 'a> de::VariantAccess<'de> for Compound<'a, 'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        assert!(self.de.expect_type == Type::Null && self.de.wire_type == Type::Null);
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
        /*
        if fields.is_empty() {
            de::Deserializer::deserialize_any(self.de, visitor)
        } else {
            de::Deserializer::deserialize_struct(self.de, "_", fields, visitor)
        }*/
    }
}
