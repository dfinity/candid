//! Deserialize Candid binary format to Rust data structures

use super::error::{Error, Result};
use super::types::internal::Opcode;
use super::{idl_hash, Nat};
use byteorder::{LittleEndian, ReadBytesExt};
use leb128::read::{signed as sleb128_decode, unsigned as leb128_decode};
use serde::de::{self, Visitor};
use std::collections::{BTreeMap, VecDeque};
use std::convert::TryFrom;
use std::io::Read;

const MAGIC_NUMBER: &[u8; 4] = b"DIDL";

/// Use this struct to deserialize a sequence of Rust values (heterogeneous) from IDL binary message.
pub struct IDLDeserialize<'de> {
    de: Deserializer<'de>,
}

impl<'de> IDLDeserialize<'de> {
    /// Create a new deserializer with IDL binary message.
    pub fn new(bytes: &'de [u8]) -> Result<Self> {
        let mut de = Deserializer::from_bytes(bytes);
        de.parse_table().map_err(|e| de.dump_error_state(e))?;
        Ok(IDLDeserialize { de })
    }
    /// Deserialize one value from deserializer.
    pub fn get_value<T>(&mut self) -> Result<T>
    where
        T: de::Deserialize<'de>,
    {
        let ty = self
            .de
            .types
            .pop_front()
            .ok_or_else(|| Error::msg("No more values to deserialize"))?;
        self.de.current_type.push_back(ty);

        let v = T::deserialize(&mut self.de).map_err(|e| self.de.dump_error_state(e))?;
        if self.de.current_type.is_empty() && self.de.field_name.is_none() {
            Ok(v)
        } else {
            Err(Error::msg("Trailing type after deserializing a value"))
                .map_err(|e| self.de.dump_error_state(e))
        }
    }
    /// Check if we finish deserializing all values.
    pub fn is_done(&self) -> bool {
        self.de.types.is_empty()
    }
    /// Return error if there are unprocessed bytes in the input.
    pub fn done(self) -> Result<()> {
        if !self.de.types.is_empty() {
            return Err(Error::msg(format!(
                "{} more values need to be deserialized",
                self.de.types.len()
            )));
        }
        if !self.de.input.is_empty() {
            return Err(Error::msg("Trailing value after finishing deserialization"))
                .map_err(|e| self.de.dump_error_state(e));
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
enum RawValue {
    I(i64),
    U(u64),
}
impl RawValue {
    fn get_i64(&self) -> Result<i64> {
        match *self {
            RawValue::I(i) => Ok(i),
            _ => Err(Error::msg(format!("get_i64 fail: {:?}", *self))),
        }
    }
    fn get_u64(&self) -> Result<u64> {
        match *self {
            RawValue::U(u) => Ok(u),
            _ => Err(Error::msg(format!("get_u64 fail: {:?}", *self))),
        }
    }
}

#[derive(Debug)]
enum FieldLabel {
    Named(&'static str),
    Id(u32),
    Variant(String),
    Skip,
}

struct Deserializer<'de> {
    input: &'de [u8],
    // Raw value of the type description table
    table: Vec<Vec<RawValue>>,
    // Value types for deserialization
    types: VecDeque<RawValue>,
    // The front of current_type queue always points to the type of the value we are deserailizing.
    // The type info is cloned from table. Someone more familiar with Rust should see if we can
    // rewrite this to avoid copying.
    current_type: VecDeque<RawValue>,
    // field_name tells deserialize_identifier which field name to process.
    // This field should always be set by set_field_name function.
    field_name: Option<FieldLabel>,
}

impl<'de> Deserializer<'de> {
    fn from_bytes(input: &'de [u8]) -> Self {
        Deserializer {
            input,
            table: Vec::new(),
            types: VecDeque::new(),
            current_type: VecDeque::new(),
            field_name: None,
        }
    }

    fn dump_error_state(&self, e: Error) -> Error {
        let mut str = format!("Trailing type: {:?}\n", self.current_type);
        str.push_str(&format!("Trailing value: {:02x?}\n", self.input));
        if self.field_name.is_some() {
            str.push_str(&format!("Trailing field_name: {:?}\n", self.field_name));
        }
        str.push_str(&format!("Type table: {:?}\n", self.table));
        str.push_str(&format!("Remaining value types: {:?}", self.types));
        e.with_states(str)
    }

    fn leb128_read(&mut self) -> Result<u64> {
        leb128_decode(&mut self.input).map_err(Error::msg)
    }
    fn sleb128_read(&mut self) -> Result<i64> {
        sleb128_decode(&mut self.input).map_err(Error::msg)
    }
    fn parse_byte(&mut self) -> Result<u8> {
        let mut buf = [0u8; 1];
        self.input.read_exact(&mut buf)?;
        Ok(buf[0])
    }
    fn parse_bytes(&mut self, len: usize) -> Result<Vec<u8>> {
        let mut buf = Vec::new();
        buf.resize(len, 0);
        self.input.read_exact(&mut buf)?;
        Ok(buf)
    }
    fn parse_string(&mut self, len: usize) -> Result<String> {
        let buf = self.parse_bytes(len)?;
        String::from_utf8(buf).map_err(Error::msg)
    }
    fn parse_magic(&mut self) -> Result<()> {
        let mut buf = [0u8; 4];
        match self.input.read(&mut buf) {
            Ok(4) if buf == *MAGIC_NUMBER => Ok(()),
            _ => Err(Error::msg(format!("wrong magic number {:?}", buf))),
        }
    }
    // Parse magic number, type table, and type seq from input.
    fn parse_table(&mut self) -> Result<()> {
        self.parse_magic()?;
        let len = self.leb128_read()?;
        for _i in 0..len {
            let mut buf = Vec::new();
            let ty = self.sleb128_read()?;
            buf.push(RawValue::I(ty));
            match Opcode::try_from(ty) {
                Ok(Opcode::Opt) | Ok(Opcode::Vec) => {
                    buf.push(RawValue::I(self.sleb128_read()?));
                }
                Ok(Opcode::Record) | Ok(Opcode::Variant) => {
                    let obj_len = self.leb128_read()?;
                    buf.push(RawValue::U(obj_len));
                    for _ in 0..obj_len {
                        buf.push(RawValue::U(self.leb128_read()?));
                        buf.push(RawValue::I(self.sleb128_read()?));
                    }
                }
                _ => {
                    return Err(Error::msg(format!(
                        "Unsupported op_code {} in type table",
                        ty
                    )))
                }
            };
            self.table.push(buf);
        }
        let len = self.leb128_read()?;
        for _i in 0..len {
            let ty = self.sleb128_read()?;
            self.types.push_back(RawValue::I(ty));
        }
        Ok(())
    }
    fn pop_current_type(&mut self) -> Result<RawValue> {
        self.current_type
            .pop_front()
            .ok_or_else(|| Error::msg("empty current_type"))
    }
    fn peek_current_type(&self) -> Result<&RawValue> {
        self.current_type
            .front()
            .ok_or_else(|| Error::msg("empty current_type"))
    }
    fn rawvalue_to_opcode(&self, v: &RawValue) -> Result<Opcode> {
        let mut op = v.get_i64()?;
        if op >= 0 && op < self.table.len() as i64 {
            op = self.table[op as usize][0].get_i64()?;
        }
        Opcode::try_from(op).map_err(|_| Error::msg(format!("Unknown opcode {}", op)))
    }
    // Pop type opcode from the front of current_type.
    // If the opcode is an index (>= 0), we push the corresponding entry from table,
    // to current_type queue, and pop the opcode from the front.
    fn parse_type(&mut self) -> Result<Opcode> {
        let mut op = self.pop_current_type()?.get_i64()?;
        if op >= 0 && op < self.table.len() as i64 {
            let ty = &self.table[op as usize];
            for x in ty.iter().rev() {
                self.current_type.push_front(x.clone());
            }
            op = self.pop_current_type()?.get_i64()?;
        }
        let r = Opcode::try_from(op).map_err(|_| Error::msg(format!("Unknown opcode {}", op)))?;
        Ok(r)
    }
    // Same logic as parse_type, but not poping the current_type queue.
    fn peek_type(&self) -> Result<Opcode> {
        let op = self.peek_current_type()?;
        self.rawvalue_to_opcode(op)
    }
    // Check if current_type matches the provided type
    fn check_type(&mut self, expected: Opcode) -> Result<()> {
        let wire_type = self.parse_type()?;
        if wire_type != expected {
            return Err(Error::msg(format!(
                "Type mismatch. Type on the wire: {:?}; Provided type: {:?}",
                wire_type, expected
            )));
        }
        Ok(())
    }
    // Should always call set_field_name to set the field_name. After deserialize_identifier
    // processed the field_name, field_name will be reset to None.
    fn set_field_name(&mut self, field: FieldLabel) {
        if self.field_name.is_some() {
            panic!(format!("field_name already taken {:?}", self.field_name));
        }
        self.field_name = Some(field);
    }
    // Customize deserailization methods
    fn deserialize_int<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Int)?;
        visitor.visit_i64(self.sleb128_read()?)
    }
    fn deserialize_nat<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Nat)?;
        //visitor.visit_u64(self.leb128_read()?)
        let v = Nat::decode(&mut self.input)
            .map_err(Error::msg)
            .map_err(Error::msg)?;
        let value = v.0.to_str_radix(10).parse::<u64>().unwrap();
        visitor.visit_u64(value)
    }
}

macro_rules! primitive_impl {
    ($ty:ident, $opcode:expr, $value:expr) => {
        paste::item! {
            fn [<deserialize_ $ty>]<V>(self, visitor: V) -> Result<V::Value>
            where V: Visitor<'de> {
                self.check_type($opcode)?;
                visitor.[<visit_ $ty>]($value)
            }
        }
    };
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;

    // Skipping unused field types
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if self.field_name.is_some() {
            return self.deserialize_identifier(visitor);
        }
        let t = self.peek_type()?;
        match t {
            Opcode::Int => self.deserialize_int(visitor),
            Opcode::Nat => self.deserialize_nat(visitor),
            Opcode::Nat8 => self.deserialize_u8(visitor),
            Opcode::Nat16 => self.deserialize_u16(visitor),
            Opcode::Nat32 => self.deserialize_u32(visitor),
            Opcode::Nat64 => self.deserialize_u64(visitor),
            Opcode::Int8 => self.deserialize_i8(visitor),
            Opcode::Int16 => self.deserialize_i16(visitor),
            Opcode::Int32 => self.deserialize_i32(visitor),
            Opcode::Int64 => self.deserialize_i64(visitor),
            Opcode::Float32 => self.deserialize_f32(visitor),
            Opcode::Float64 => self.deserialize_f64(visitor),
            Opcode::Bool => self.deserialize_bool(visitor),
            Opcode::Text => self.deserialize_string(visitor),
            Opcode::Null => self.deserialize_unit(visitor),
            Opcode::Vec => self.deserialize_seq(visitor),
            Opcode::Opt => self.deserialize_option(visitor),
            Opcode::Record => self.deserialize_struct("_", &[], visitor),
            Opcode::Variant => self.deserialize_enum("_", &[], visitor),
        }
    }

    // Used for deserializing to IDLValue
    fn deserialize_any<V>(mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if self.field_name.is_some() {
            return self.deserialize_identifier(visitor);
        }
        let t = self.peek_type()?;
        match t {
            Opcode::Int => self.deserialize_int(visitor),
            Opcode::Nat => self.deserialize_nat(visitor),
            Opcode::Nat8 => self.deserialize_u8(visitor),
            Opcode::Nat16 => self.deserialize_u16(visitor),
            Opcode::Nat32 => self.deserialize_u32(visitor),
            Opcode::Nat64 => self.deserialize_u64(visitor),
            Opcode::Int8 => self.deserialize_i8(visitor),
            Opcode::Int16 => self.deserialize_i16(visitor),
            Opcode::Int32 => self.deserialize_i32(visitor),
            Opcode::Int64 => self.deserialize_i64(visitor),
            Opcode::Float32 => self.deserialize_f32(visitor),
            Opcode::Float64 => self.deserialize_f64(visitor),
            Opcode::Bool => self.deserialize_bool(visitor),
            Opcode::Text => self.deserialize_string(visitor),
            Opcode::Null => self.deserialize_unit(visitor),
            Opcode::Vec => self.deserialize_seq(visitor),
            Opcode::Opt => self.deserialize_option(visitor),
            Opcode::Record => {
                self.check_type(Opcode::Record)?;
                let len = self.pop_current_type()?.get_u64()? as u32;
                let mut fs = BTreeMap::new();
                for i in 0..len {
                    let hash = self.current_type[2 * i as usize].get_u64()? as u32;
                    if fs.insert(hash, None) != None {
                        return Err(Error::msg(format!("hash collision {}", hash)));
                    }
                }
                visitor.visit_map(Compound::new(&mut self, Style::Struct { len, fs }))
            }
            Opcode::Variant => {
                self.check_type(Opcode::Variant)?;
                let len = self.pop_current_type()?.get_u64()? as u32;
                let mut fs = BTreeMap::new();
                for i in 0..len {
                    let hash = self.current_type[2 * i as usize].get_u64()? as u32;
                    if fs.insert(hash, None) != None {
                        return Err(Error::msg(format!("hash collision {}", hash)));
                    }
                }
                visitor.visit_enum(Compound::new(&mut self, Style::Enum { len, fs }))
            }
        }
    }

    primitive_impl!(i8, Opcode::Int8, self.input.read_i8()?);
    primitive_impl!(i16, Opcode::Int16, self.input.read_i16::<LittleEndian>()?);
    primitive_impl!(i32, Opcode::Int32, self.input.read_i32::<LittleEndian>()?);
    primitive_impl!(i64, Opcode::Int64, self.input.read_i64::<LittleEndian>()?);
    primitive_impl!(u8, Opcode::Nat8, self.input.read_u8()?);
    primitive_impl!(u16, Opcode::Nat16, self.input.read_u16::<LittleEndian>()?);
    primitive_impl!(u32, Opcode::Nat32, self.input.read_u32::<LittleEndian>()?);
    primitive_impl!(u64, Opcode::Nat64, self.input.read_u64::<LittleEndian>()?);
    primitive_impl!(bool, Opcode::Bool, self.parse_byte()? == 1u8);

    primitive_impl!(f32, Opcode::Float32, self.input.read_f32::<LittleEndian>()?);
    primitive_impl!(f64, Opcode::Float64, self.input.read_f64::<LittleEndian>()?);

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Text)?;
        let len = self.leb128_read()? as usize;
        let value = self.parse_string(len)?;
        visitor.visit_string(value)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Text)?;
        let len = self.leb128_read()? as usize;
        let value: Result<&str> =
            std::str::from_utf8(&self.input[0..len]).map_err(de::Error::custom);
        self.input = &self.input[len..];
        visitor.visit_borrowed_str(value?)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Opt)?;
        let bit = self.parse_byte()?;
        if bit == 0u8 {
            // Skip the type T of Option<T>
            self.pop_current_type()?;
            visitor.visit_none()
        } else {
            visitor.visit_some(self)
        }
    }
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Null)?;
        visitor.visit_unit()
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
    fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.parse_type()? {
            Opcode::Vec => {
                let len = self.leb128_read()? as u32;
                let value = visitor.visit_seq(Compound::new(&mut self, Style::Vector { len }));
                // Skip the type T of Vec<T>.
                self.pop_current_type()?;
                value
            }
            Opcode::Record => {
                let len = self.pop_current_type()?.get_u64()? as u32;
                visitor.visit_seq(Compound::new(&mut self, Style::Tuple { len, index: 0 }))
            }
            _ => Err(Error::msg("seq only takes vector or tuple")),
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
        mut self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Record)?;
        let len = self.pop_current_type()?.get_u64()? as u32;
        let mut fs = BTreeMap::new();
        for s in fields.iter() {
            if fs.insert(idl_hash(s), Some(*s)) != None {
                return Err(Error::msg(format!("hash collision {}", s)));
            }
        }
        let value = visitor.visit_map(Compound::new(&mut self, Style::Struct { len, fs }))?;
        Ok(value)
    }

    fn deserialize_enum<V>(
        mut self,
        _name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.check_type(Opcode::Variant)?;
        let len = self.pop_current_type()?.get_u64()? as u32;
        let mut fs = BTreeMap::new();
        for s in variants.iter() {
            if fs.insert(idl_hash(s), Some(*s)) != None {
                return Err(Error::msg(format!("hash collision {}", s)));
            }
        }
        let value = visitor.visit_enum(Compound::new(&mut self, Style::Enum { len, fs }))?;
        Ok(value)
    }
    /// Deserialize identifier.
    /// # Panics
    /// *Will Panic* when identifier name is None.
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        // N.B. Here we want to panic as it indicates a logical error.
        let label = self.field_name.as_ref().unwrap();
        let v = match label {
            FieldLabel::Named(name) => visitor.visit_str(name),
            FieldLabel::Id(hash) => visitor.visit_u32(*hash),
            FieldLabel::Variant(variant) => visitor.visit_str(variant),
            FieldLabel::Skip => visitor.visit_str("_"),
        };
        self.field_name = None;
        v
    }

    serde::forward_to_deserialize_any! {
        char bytes byte_buf map
    }
}

#[derive(Debug)]
enum Style {
    Tuple {
        len: u32,
        index: u32,
    },
    Vector {
        len: u32,
    },
    Struct {
        len: u32,
        fs: BTreeMap<u32, Option<&'static str>>,
    },
    Enum {
        len: u32,
        fs: BTreeMap<u32, Option<&'static str>>,
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
            Style::Tuple {
                ref len,
                ref mut index,
            } => {
                if *index == *len {
                    return Ok(None);
                }
                let t_idx = self.de.pop_current_type()?.get_u64()? as u32;
                if t_idx != *index {
                    return Err(Error::msg(format!(
                        "Expect vector index {}, but get {}",
                        index, t_idx
                    )));
                }
                *index += 1;
                seed.deserialize(&mut *self.de).map(Some)
            }
            Style::Vector { ref mut len } => {
                if *len == 0 {
                    return Ok(None);
                }
                let ty = self.de.peek_current_type()?.clone();
                self.de.current_type.push_front(ty);
                *len -= 1;
                seed.deserialize(&mut *self.de).map(Some)
            }
            _ => Err(Error::msg("expect vector or tuple")),
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
                ref mut len,
                ref fs,
            } => {
                if *len == 0 {
                    return Ok(None);
                }
                *len -= 1;
                let hash = self.de.pop_current_type()?.get_u64()? as u32;
                match fs.get(&hash) {
                    Some(None) => self.de.set_field_name(FieldLabel::Id(hash)),
                    Some(Some(field)) => self.de.set_field_name(FieldLabel::Named(field)),
                    None => {
                        // This triggers seed.deserialize to call deserialize_ignore_any
                        // to skip both type and value of this unknown field.
                        self.de.set_field_name(FieldLabel::Skip);
                    }
                }
                seed.deserialize(&mut *self.de).map(Some)
            }
            _ => Err(Error::msg("expect struct")),
        }
    }
    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        seed.deserialize(&mut *self.de)
    }
}

impl<'de, 'a> de::EnumAccess<'de> for Compound<'a, 'de> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: de::DeserializeSeed<'de>,
    {
        match self.style {
            Style::Enum { len, ref fs } => {
                let index = self.de.leb128_read()? as u32;
                if index >= len {
                    return Err(Error::msg(format!(
                        "variant index {} larger than length {}",
                        index, len
                    )));
                }
                let mut index_ty = None;
                for i in 0..len {
                    let hash = self.de.pop_current_type()?.get_u64()? as u32;
                    let ty = self.de.pop_current_type()?;
                    if i == index {
                        match fs.get(&hash) {
                            Some(None) => {
                                let opcode = self.de.rawvalue_to_opcode(&ty)?;
                                let accessor = match opcode {
                                    Opcode::Null => "unit",
                                    Opcode::Record => "struct",
                                    _ => "newtype",
                                };
                                self.de.set_field_name(FieldLabel::Variant(format!(
                                    "{},{}",
                                    hash, accessor
                                )));
                            }
                            Some(Some(field)) => {
                                self.de.set_field_name(FieldLabel::Named(field));
                            }
                            None => {
                                if !fs.is_empty() {
                                    return Err(Error::msg(format!(
                                        "Unknown variant hash {}",
                                        hash
                                    )));
                                } else {
                                    // Actual enum won't have empty fs. This can only be generated
                                    // from deserialize_ignored_any
                                    self.de.set_field_name(FieldLabel::Skip);
                                }
                            }
                        }
                        index_ty = Some(ty);
                    }
                }
                // Okay to unwrap, as index_ty always has a value here.
                self.de.current_type.push_front(index_ty.unwrap());
                let val = seed.deserialize(&mut *self.de)?;
                Ok((val, self))
            }
            _ => Err(Error::msg("expect enum")),
        }
    }
}

impl<'de, 'a> de::VariantAccess<'de> for Compound<'a, 'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        self.de.check_type(Opcode::Null)?;
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: de::DeserializeSeed<'de>,
    {
        seed.deserialize(self.de)
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        de::Deserializer::deserialize_seq(self.de, visitor)
    }

    fn struct_variant<V>(self, fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if fields.is_empty() {
            de::Deserializer::deserialize_any(self.de, visitor)
        } else {
            de::Deserializer::deserialize_struct(self.de, "_", fields, visitor)
        }
    }
}
