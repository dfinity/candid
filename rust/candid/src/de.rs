//! Deserialize Candid binary format to Rust data structures

use super::error::{pretty_read, Error, Result};
use super::{idl_hash, parser::typing::TypeEnv, types::Type, CandidType, Int, Nat};
use crate::binary_parser::Header;
use crate::types::subtype::{subtype, Gamma};
use anyhow::{anyhow, Context};
use binread::BinRead;
use byteorder::{LittleEndian, ReadBytesExt};
use serde::de::{self, Deserialize, Visitor};
use std::collections::{BTreeMap, VecDeque};
use std::convert::TryFrom;
use std::io::Cursor;

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
        if !subtype(
            &mut self.de.gamma,
            &self.de.table,
            &ty,
            &self.de.table,
            &self.de.expect_type,
        ) {
            return Err(Error::msg(format!(
                "Fail to decode argument {}, because {} is not subtype of {}",
                ind,
                ty,
                T::ty()
            )));
        }

        let v = T::deserialize(&mut self.de)
            .with_context(|| self.de.dump_state())
            .with_context(|| {
                format!("Fail to decode argument {} from {} to {}", ind, ty, T::ty())
            })?;
        Ok(v)
        /*if self.de.table.current_type.is_empty() && self.de.field_name.is_none() {
            Ok(v)
        } else {
            Err(Error::msg("Trailing type after deserializing a value"))
                .map_err(|e| self.de.dump_error_state(e))
        }*/
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
    ( $self:ident, false ) => {{
        return Err(anyhow!($self.dump_state())).context("Internal error")?;
    }};
    ( $self:ident, $pred:expr ) => {{
        if !$pred {
            return Err(anyhow!($self.dump_state())).context("Internal error")?;
        }
    }};
}

struct Deserializer<'de> {
    input: Cursor<&'de [u8]>,
    table: TypeEnv,
    types: VecDeque<(usize, Type)>,
    wire_type: Type,
    expect_type: Type,
    gamma: Gamma,
    record_nesting_depth: usize,
}

impl<'de> Deserializer<'de> {
    fn from_bytes(bytes: &'de [u8]) -> Result<Self> {
        let mut reader = Cursor::new(bytes);
        let header: Header = pretty_read(&mut reader)?;
        let (env, types) = header.to_types()?;
        Ok(Deserializer {
            input: reader,
            table: env,
            types: types.into_iter().enumerate().collect(),
            wire_type: Type::Unknown,
            expect_type: Type::Unknown,
            gamma: Gamma::default(),
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
        res
    }
    fn deserialize_int<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        assert!(self, self.expect_type == Type::Int);
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
            _ => assert!(self, false),
        }
        visitor.visit_byte_buf(bytes)
    }
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let t = self.table.trace_type(&self.expect_type)?;
        match t {
            Type::Bool => self.deserialize_bool(visitor),
            Type::Int => self.deserialize_int(visitor),
            Type::Vec(_) => self.deserialize_seq(visitor),
            _ => assert!(self, false),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        #[derive(BinRead)]
        struct BoolValue(
            #[br(try_map = |x:u8| match x { 0u8 => Ok(false), | 1u8 => Ok(true), | _ => Err("Not a boolean") } )]
             bool,
        );
        self.record_nesting_depth = 0;
        assert!(self, self.expect_type == Type::Bool);
        let res: BoolValue = pretty_read(&mut self.input)?;
        visitor.visit_bool(res.0)
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
        str
        string
        unit
        option
        bytes
        byte_buf
        unit_struct
        newtype_struct
        tuple_struct
        struct
        identifier
        tuple
        enum
        seq
        map
        ignored_any
    }
}
