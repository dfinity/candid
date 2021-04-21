//! Deserialize Candid binary format to Rust data structures

use super::error::{Error, Result};
use super::types::internal::Opcode;
use super::{idl_hash, Int, Nat};
use byteorder::{LittleEndian, ReadBytesExt};
use leb128::read::{signed as sleb128_decode, unsigned as leb128_decode};
use serde::de::{self, Deserialize, Visitor};
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
        let de = Deserializer::from_bytes(bytes)?;
        Ok(IDLDeserialize { de })
    }
    /// Deserialize one value from deserializer.
    pub fn get_value<T>(&mut self) -> Result<T>
    where
        T: de::Deserialize<'de>,
    {
        let ty = self
            .de
            .table
            .types
            .pop_front()
            .ok_or_else(|| Error::msg("No more values to deserialize"))?;
        self.de.table.current_type.push_back(ty);

        let v = T::deserialize(&mut self.de).map_err(|e| self.de.dump_error_state(e))?;
        if self.de.table.current_type.is_empty() && self.de.field_name.is_none() {
            Ok(v)
        } else {
            Err(Error::msg("Trailing type after deserializing a value"))
                .map_err(|e| self.de.dump_error_state(e))
        }
    }
    /// Check if we finish deserializing all values.
    pub fn is_done(&self) -> bool {
        self.de.table.types.is_empty()
    }
    /// Return error if there are unprocessed bytes in the input.
    pub fn done(mut self) -> Result<()> {
        while !self.is_done() {
            self.get_value::<crate::Reserved>()?;
        }
        if !self.de.input.0.is_empty() {
            return Err(Error::msg("Trailing value after finishing deserialization"))
                .map_err(|e| self.de.dump_error_state(e));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RawValue {
    I(i64),
    U(u32),
}
impl RawValue {
    fn get_i64(&self) -> Result<i64> {
        match *self {
            RawValue::I(i) => Ok(i),
            _ => Err(Error::msg(format!("get_i64 fail: {:?}", *self))),
        }
    }
    fn get_u32(&self) -> Result<u32> {
        match *self {
            RawValue::U(u) => Ok(u),
            _ => Err(Error::msg(format!("get_u32 fail: {:?}", *self))),
        }
    }
}

struct Bytes<'a>(&'a [u8]);
impl<'a> Bytes<'a> {
    fn from(input: &'a [u8]) -> Self {
        Bytes(input)
    }
    fn leb128_read(&mut self) -> Result<u64> {
        leb128_decode(&mut self.0).map_err(Error::msg)
    }
    fn sleb128_read(&mut self) -> Result<i64> {
        sleb128_decode(&mut self.0).map_err(Error::msg)
    }
    fn parse_byte(&mut self) -> Result<u8> {
        let mut buf = [0u8; 1];
        self.0.read_exact(&mut buf)?;
        Ok(buf[0])
    }
    fn parse_bytes(&mut self, len: usize) -> Result<Vec<u8>> {
        if self.0.len() < len {
            return Err(Error::msg("unexpected end of message"));
        }
        let mut buf = vec![0; len];
        self.0.read_exact(&mut buf)?;
        Ok(buf)
    }
    fn parse_string(&mut self, len: usize) -> Result<String> {
        let buf = self.parse_bytes(len)?;
        String::from_utf8(buf).map_err(Error::msg)
    }
    fn parse_magic(&mut self) -> Result<()> {
        let mut buf = [0u8; 4];
        match self.0.read(&mut buf) {
            Ok(4) if buf == *MAGIC_NUMBER => Ok(()),
            _ => Err(Error::msg(format!("wrong magic number {:?}", buf))),
        }
    }
}

struct TypeTable {
    // Raw value of the type description table
    table: Vec<Vec<RawValue>>,
    // Value types for deserialization
    types: VecDeque<RawValue>,
    // The front of current_type queue always points to the type of the value we are deserailizing.
    // The type info is cloned from table. Someone more familiar with Rust should see if we can
    // rewrite this to avoid copying.
    current_type: VecDeque<RawValue>,
}
impl TypeTable {
    // Parse the type table and return the remaining bytes
    fn from_bytes(input: &[u8]) -> Result<(Self, &[u8])> {
        let mut bytes = Bytes::from(input);
        let mut table: Vec<Vec<RawValue>> = Vec::new();
        let mut types = VecDeque::new();

        bytes.parse_magic()?;
        let len = bytes.leb128_read()? as usize;
        let mut expect_func = std::collections::HashSet::new();
        for i in 0..len {
            let mut buf = Vec::new();
            let ty = bytes.sleb128_read()?;
            buf.push(RawValue::I(ty));
            if expect_func.contains(&i) && ty != -22 {
                return Err(Error::msg(format!(
                    "Expect function opcode, but got {}",
                    ty
                )));
            }
            match Opcode::try_from(ty) {
                Ok(Opcode::Opt) | Ok(Opcode::Vec) => {
                    let ty = bytes.sleb128_read()?;
                    validate_type_range(ty, len)?;
                    buf.push(RawValue::I(ty));
                }
                Ok(Opcode::Record) | Ok(Opcode::Variant) => {
                    let obj_len = u32::try_from(bytes.leb128_read()?)
                        .map_err(|_| Error::msg(Error::msg("length out of u32")))?;
                    buf.push(RawValue::U(obj_len));
                    let mut prev_hash = None;
                    for _ in 0..obj_len {
                        let hash = u32::try_from(bytes.leb128_read()?)
                            .map_err(|_| Error::msg(Error::msg("field hash out of u32")))?;
                        if let Some(prev_hash) = prev_hash {
                            if prev_hash >= hash {
                                return Err(Error::msg("field id collision or not sorted"));
                            }
                        }
                        prev_hash = Some(hash);
                        buf.push(RawValue::U(hash));
                        let ty = bytes.sleb128_read()?;
                        validate_type_range(ty, len)?;
                        buf.push(RawValue::I(ty));
                    }
                }
                Ok(Opcode::Service) => {
                    let obj_len = u32::try_from(bytes.leb128_read()?)
                        .map_err(|_| Error::msg(Error::msg("length out of u32")))?;
                    // Push one element to the table to ensure it's a non-primitive type
                    buf.push(RawValue::U(obj_len));
                    let mut prev = None;
                    for _ in 0..obj_len {
                        let mlen = bytes.leb128_read()? as usize;
                        let meth = bytes.parse_string(mlen)?;
                        if let Some(prev) = prev {
                            if prev >= meth {
                                return Err(Error::msg("method name collision or not sorted"));
                            }
                        }
                        prev = Some(meth);
                        let ty = bytes.sleb128_read()?;
                        validate_type_range(ty, len)?;
                        // Check for method type
                        if ty >= 0 {
                            let idx = ty as usize;
                            if idx < table.len() && table[idx][0] != RawValue::I(-22) {
                                return Err(Error::msg("not a function type"));
                            } else {
                                expect_func.insert(idx);
                            }
                        } else {
                            return Err(Error::msg("not a function type"));
                        }
                    }
                }
                Ok(Opcode::Func) => {
                    let arg_len = bytes.leb128_read()?;
                    // Push one element to the table to ensure it's a non-primitive type
                    buf.push(RawValue::U(arg_len as u32));
                    for _ in 0..arg_len {
                        let ty = bytes.sleb128_read()?;
                        validate_type_range(ty, len)?;
                    }
                    let ret_len = bytes.leb128_read()?;
                    for _ in 0..ret_len {
                        let ty = bytes.sleb128_read()?;
                        validate_type_range(ty, len)?;
                    }
                    let ann_len = bytes.leb128_read()?;
                    for _ in 0..ann_len {
                        let ann = bytes.parse_byte()?;
                        if ann > 2u8 {
                            return Err(Error::msg("Unknown function annotation"));
                        }
                    }
                }
                _ => {
                    return Err(Error::msg(format!(
                        "Unsupported op_code {} in type table",
                        ty
                    )))
                }
            };
            table.push(buf);
        }
        let len = bytes.leb128_read()?;
        for _i in 0..len {
            let ty = bytes.sleb128_read()?;
            validate_type_range(ty, table.len())?;
            types.push_back(RawValue::I(ty));
        }
        Ok((
            TypeTable {
                table,
                types,
                current_type: VecDeque::new(),
            },
            bytes.0,
        ))
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
                "Type mismatch. Type on the wire: {:?}; Expected type: {:?}",
                wire_type, expected
            )));
        }
        Ok(())
    }
}
fn is_primitive_type(ty: i64) -> bool {
    ty < 0 && (ty >= -17 || ty == -24)
}
fn validate_type_range(ty: i64, len: usize) -> Result<()> {
    if ty >= 0 && (ty as usize) < len || is_primitive_type(ty) {
        Ok(())
    } else {
        Err(Error::msg(format!("unknown type {}", ty)))
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
    input: Bytes<'de>,
    table: TypeTable,
    // field_name tells deserialize_identifier which field name to process.
    // This field should always be set by set_field_name function.
    field_name: Option<FieldLabel>,
    // The record nesting depth should be bounded by the length of table to avoid infinite loop.
    record_nesting_depth: usize,
}

impl<'de> Deserializer<'de> {
    fn from_bytes(input: &'de [u8]) -> Result<Self> {
        let (table, input) = TypeTable::from_bytes(input)?;
        Ok(Deserializer {
            input: Bytes::from(input),
            table,
            field_name: None,
            record_nesting_depth: 0,
        })
    }

    fn dump_error_state(&self, e: Error) -> Error {
        let mut str = format!("Trailing type: {:?}\n", self.table.current_type);
        str.push_str(&format!("Trailing value: {:02x?}\n", self.input.0));
        if self.field_name.is_some() {
            str.push_str(&format!("Trailing field_name: {:?}\n", self.field_name));
        }
        str.push_str(&format!("Type table: {:?}\n", self.table.table));
        str.push_str(&format!("Remaining value types: {:?}", self.table.types));
        e.with_states(str)
    }

    // Should always call set_field_name to set the field_name. After deserialize_identifier
    // processed the field_name, field_name will be reset to None.
    fn set_field_name(&mut self, field: FieldLabel) {
        if self.field_name.is_some() {
            panic!("field_name already taken");
        }
        self.field_name = Some(field);
    }
    // Customize deserailization methods
    // Several deserialize functions will call visit_byte_buf.
    // We reserve the first byte to be a tag to distinguish between different callers:
    // int(0), nat(1), principal(2), reserved(3)
    // This is necessary for deserializing IDLValue because
    // it has only one visitor and we need a way to know who called the visitor.
    fn deserialize_int<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Int)?;
        let v = Int::decode(&mut self.input.0).map_err(Error::msg)?;
        let bytes = v.0.to_signed_bytes_le();
        let mut tagged = vec![0u8];
        tagged.extend_from_slice(&bytes);
        visitor.visit_byte_buf(tagged)
    }
    fn deserialize_nat<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Nat)?;
        let v = Nat::decode(&mut self.input.0).map_err(Error::msg)?;
        let bytes = v.0.to_bytes_le();
        let mut tagged = vec![1u8];
        tagged.extend_from_slice(&bytes);
        visitor.visit_byte_buf(tagged)
    }
    fn decode_principal(&mut self) -> Result<Vec<u8>> {
        let bit = self.input.parse_byte()?;
        if bit != 1u8 {
            return Err(Error::msg("Opaque reference not supported"));
        }
        let len = self.input.leb128_read()? as usize;
        self.input.parse_bytes(len)
    }
    fn deserialize_principal<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Principal)?;
        let vec = self.decode_principal()?;
        let mut tagged = vec![2u8];
        tagged.extend_from_slice(&vec);
        visitor.visit_byte_buf(tagged)
    }
    fn deserialize_service<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Service)?;
        self.table.pop_current_type()?;
        let vec = self.decode_principal()?;
        let mut tagged = vec![4u8];
        tagged.extend_from_slice(&vec);
        visitor.visit_byte_buf(tagged)
    }
    fn deserialize_function<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Func)?;
        self.table.pop_current_type()?;
        let bit = self.input.parse_byte()?;
        if bit != 1u8 {
            return Err(Error::msg("Opaque reference not supported"));
        }
        let vec = self.decode_principal()?;
        let len = self.input.leb128_read()? as usize;
        let meth = self.input.parse_bytes(len)?;
        let mut tagged = vec![5u8];
        // TODO: find a better way
        leb128::write::unsigned(&mut tagged, len as u64)?;
        tagged.extend_from_slice(&meth);
        tagged.extend_from_slice(&vec);
        visitor.visit_byte_buf(tagged)
    }
    fn deserialize_reserved<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Reserved)?;
        let tagged = vec![3u8];
        visitor.visit_byte_buf(tagged)
    }
    fn deserialize_empty<'a, V>(&'a mut self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::msg("Cannot decode empty type"))
    }
}

macro_rules! primitive_impl {
    ($ty:ident, $opcode:expr, $($value:tt)*) => {
        paste::item! {
            fn [<deserialize_ $ty>]<V>(self, visitor: V) -> Result<V::Value>
            where V: Visitor<'de> {
                self.record_nesting_depth = 0;
                self.table.check_type($opcode)?;
                let value = (self.input.0).$($value)*().map_err(|_| Error::msg(format!("cannot read {} value", stringify!($opcode))))?;
                visitor.[<visit_ $ty>](value)
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
        let t = self.table.peek_type()?;
        if t != Opcode::Record {
            self.record_nesting_depth = 0;
        }
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
            Opcode::Reserved => self.deserialize_reserved(visitor),
            Opcode::Empty => self.deserialize_empty(visitor),
            Opcode::Vec => self.deserialize_seq(visitor),
            Opcode::Opt => self.deserialize_option(visitor),
            Opcode::Record => self.deserialize_struct("_", &[], visitor),
            Opcode::Variant => self.deserialize_enum("_", &[], visitor),
            Opcode::Principal => self.deserialize_principal(visitor),
            Opcode::Service => self.deserialize_service(visitor),
            Opcode::Func => self.deserialize_function(visitor),
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
        let t = self.table.peek_type()?;
        if t != Opcode::Record {
            self.record_nesting_depth = 0;
        }
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
            Opcode::Reserved => self.deserialize_reserved(visitor),
            Opcode::Empty => self.deserialize_empty(visitor),
            Opcode::Vec => self.deserialize_seq(visitor),
            Opcode::Opt => self.deserialize_option(visitor),
            Opcode::Record => {
                let old_nesting = self.record_nesting_depth;
                self.record_nesting_depth += 1;
                if self.record_nesting_depth > self.table.table.len() {
                    return Err(Error::msg("There is an infinite loop in the record definition, the type is isomorphic to an empty type"));
                }
                self.table.check_type(Opcode::Record)?;
                let len = self.table.pop_current_type()?.get_u32()?;
                let mut fs = BTreeMap::new();
                for i in 0..len {
                    let hash = self.table.current_type[2 * i as usize].get_u32()?;
                    if fs.insert(hash, None) != None {
                        return Err(Error::msg(format!("hash collision {}", hash)));
                    }
                }
                let res = visitor.visit_map(Compound::new(&mut self, Style::Struct { len, fs }));
                self.record_nesting_depth = old_nesting;
                res
            }
            Opcode::Variant => {
                self.record_nesting_depth = 0;
                self.table.check_type(Opcode::Variant)?;
                let len = self.table.pop_current_type()?.get_u32()?;
                let mut fs = BTreeMap::new();
                for i in 0..len {
                    let hash = self.table.current_type[2 * i as usize].get_u32()?;
                    if fs.insert(hash, None) != None {
                        return Err(Error::msg(format!("hash collision {}", hash)));
                    }
                }
                visitor.visit_enum(Compound::new(&mut self, Style::Enum { len, fs }))
            }
            Opcode::Principal => self.deserialize_principal(visitor),
            Opcode::Service => self.deserialize_service(visitor),
            Opcode::Func => self.deserialize_function(visitor),
        }
    }

    primitive_impl!(i8, Opcode::Int8, read_i8);
    primitive_impl!(i16, Opcode::Int16, read_i16::<LittleEndian>);
    primitive_impl!(i32, Opcode::Int32, read_i32::<LittleEndian>);
    primitive_impl!(i64, Opcode::Int64, read_i64::<LittleEndian>);
    primitive_impl!(u8, Opcode::Nat8, read_u8);
    primitive_impl!(u16, Opcode::Nat16, read_u16::<LittleEndian>);
    primitive_impl!(u32, Opcode::Nat32, read_u32::<LittleEndian>);
    primitive_impl!(u64, Opcode::Nat64, read_u64::<LittleEndian>);
    primitive_impl!(f32, Opcode::Float32, read_f32::<LittleEndian>);
    primitive_impl!(f64, Opcode::Float64, read_f64::<LittleEndian>);

    fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use std::convert::TryInto;
        self.record_nesting_depth = 0;
        let value: i128 = match self.table.parse_type()? {
            Opcode::Int => {
                let v = Int::decode(&mut self.input.0).map_err(Error::msg)?;
                v.0.try_into().map_err(Error::msg)?
            }
            Opcode::Nat => {
                let v = Nat::decode(&mut self.input.0).map_err(Error::msg)?;
                v.0.try_into().map_err(Error::msg)?
            }
            t => {
                return Err(Error::msg(format!(
                    "Type mismatch. Type on the wire: {:?}; Expected type: int",
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
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Nat)?;
        let v = Nat::decode(&mut self.input.0).map_err(Error::msg)?;
        let value: u128 = v.0.try_into().map_err(Error::msg)?;
        visitor.visit_u128(value)
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Bool)?;
        let byte = self.input.parse_byte()?;
        if byte > 1u8 {
            return Err(de::Error::custom("not a boolean value"));
        }
        let value = byte == 1u8;
        visitor.visit_bool(value)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Text)?;
        let len = self.input.leb128_read()? as usize;
        let value = self.input.parse_string(len)?;
        visitor.visit_string(value)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Text)?;
        let len = self.input.leb128_read()? as usize;
        let value: Result<&str> =
            std::str::from_utf8(&self.input.0[0..len]).map_err(de::Error::custom);
        self.input.0 = &self.input.0[len..];
        visitor.visit_borrowed_str(value?)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        match self.table.peek_type()? {
            Opcode::Opt => {
                self.table.parse_type()?;
                match self.input.parse_byte()? {
                    0 => {
                        // Skip the type T of Option<T>
                        self.table.pop_current_type()?;
                        visitor.visit_none()
                    }
                    // TODO handle subtyping failure
                    1 => visitor.visit_some(self),
                    _ => Err(de::Error::custom("not an option tag")),
                }
            }
            Opcode::Null | Opcode::Reserved => {
                self.table.parse_type()?;
                visitor.visit_none()
            }
            _ => visitor.visit_some(self),
        }
    }
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Null)?;
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
    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Vec)?;
        self.table.check_type(Opcode::Nat8)?;
        let len = self.input.leb128_read()?;
        let bytes = self.input.parse_bytes(len as usize)?;
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.record_nesting_depth = 0;
        match self.table.peek_type()? {
            Opcode::Principal => self.deserialize_principal(visitor),
            Opcode::Vec => {
                self.table.check_type(Opcode::Vec)?;
                self.table.check_type(Opcode::Nat8)?;
                let len = self.input.leb128_read()? as usize;
                let bytes: &[u8] = &self.input.0[0..len];
                self.input.0 = &self.input.0[len..];
                visitor.visit_borrowed_bytes(bytes)
            }
            _ => Err(Error::msg("bytes only takes principal or vec nat8")),
        }
    }
    fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        match self.table.parse_type()? {
            Opcode::Vec => {
                let len = self.input.leb128_read()?;
                let value = visitor.visit_seq(Compound::new(&mut self, Style::Vector { len }));
                // Skip the type T of Vec<T>.
                self.table.pop_current_type()?;
                value
            }
            Opcode::Record => {
                let len = self.table.pop_current_type()?.get_u32()?;
                visitor.visit_seq(Compound::new(&mut self, Style::Tuple { len, index: 0 }))
            }
            _ => Err(Error::msg("seq only takes vector or tuple")),
        }
    }
    fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Vec)?;
        let len = self.input.leb128_read()?;
        let ty = self.table.peek_current_type()?.clone();
        let value = visitor.visit_map(Compound::new(&mut self, Style::Map { len, ty }));
        self.table.pop_current_type()?;
        value
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
        let old_nesting = self.record_nesting_depth;
        self.record_nesting_depth += 1;
        if self.record_nesting_depth > self.table.table.len() {
            return Err(Error::msg("There is an infinite loop in the record definition, the type is isomorphic to an empty type"));
        }
        self.table.check_type(Opcode::Record)?;
        let len = self.table.pop_current_type()?.get_u32()?;
        let mut fs = BTreeMap::new();
        for s in fields.iter() {
            if fs.insert(idl_hash(s), Some(*s)) != None {
                return Err(Error::msg(format!("hash collision {}", s)));
            }
        }
        let value = visitor.visit_map(Compound::new(&mut self, Style::Struct { len, fs }))?;
        self.record_nesting_depth = old_nesting;
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
        self.record_nesting_depth = 0;
        self.table.check_type(Opcode::Variant)?;
        let len = self.table.pop_current_type()?.get_u32()?;
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
        char
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
        len: u32,
        fs: BTreeMap<u32, Option<&'static str>>,
    },
    Enum {
        len: u32,
        fs: BTreeMap<u32, Option<&'static str>>,
    },
    Map {
        len: u64,
        ty: RawValue,
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
                let t_idx = self.de.table.pop_current_type()?.get_u32()?;
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
                let ty = self.de.table.peek_current_type()?.clone();
                self.de.table.current_type.push_front(ty);
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
                let hash = self.de.table.pop_current_type()?.get_u32()?;
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
            }
            _ => Err(Error::msg("expect struct or map")),
        }
    }
    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        match self.style {
            Style::Map { ref ty, .. } => {
                assert_eq!(1, self.de.table.pop_current_type()?.get_u32()?);
                let res = seed.deserialize(&mut *self.de);
                self.de.table.current_type.push_front(ty.clone());
                res
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
        match self.style {
            Style::Enum { len, ref fs } => {
                let index = u32::try_from(self.de.input.leb128_read()?)
                    .map_err(|_| Error::msg("variant index out of u32"))?;
                if index >= len {
                    return Err(Error::msg(format!(
                        "variant index {} larger than length {}",
                        index, len
                    )));
                }
                let mut index_ty = None;
                for i in 0..len {
                    let hash = self.de.table.pop_current_type()?.get_u32()?;
                    let ty = self.de.table.pop_current_type()?;
                    if i == index {
                        match fs.get(&hash) {
                            Some(None) => {
                                let opcode = self.de.table.rawvalue_to_opcode(&ty)?;
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
                self.de.table.current_type.push_front(index_ty.unwrap());
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
        self.de.table.check_type(Opcode::Null)?;
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

/// Allow decoding of any sized argument.
pub trait ArgumentDecoder<'a>: Sized {
    /// Decodes a value of type [Self], modifying the deserializer (values are consumed).
    fn decode(de: &mut IDLDeserialize<'a>) -> Result<Self>;
}

/// Decode an empty tuple.
impl<'a> ArgumentDecoder<'a> for () {
    fn decode(_de: &mut IDLDeserialize<'a>) -> Result<()> {
        Ok(())
    }
}

// Create implementation of [ArgumentDecoder] for up to 16 value tuples.
macro_rules! decode_impl {
    ( $($id: ident : $typename: ident),* ) => {
        impl<'a, $( $typename ),*> ArgumentDecoder<'a> for ($($typename,)*)
        where
            $( $typename: Deserialize<'a> ),*
        {
            fn decode(de: &mut IDLDeserialize<'a>) -> Result<Self> {
                $(
                let $id: $typename = de.get_value()?;
                )*

                Ok(($( $id, )*))
            }
        }
    }
}

decode_impl!(a: A);
decode_impl!(a: A, b: B);
decode_impl!(a: A, b: B, c: C);
decode_impl!(a: A, b: B, c: C, d: D);
decode_impl!(a: A, b: B, c: C, d: D, e: E);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
decode_impl!(
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
    k: K
);
decode_impl!(
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
    k: K,
    l: L
);
decode_impl!(
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
    k: K,
    l: L,
    m: M
);
decode_impl!(
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
    k: K,
    l: L,
    m: M,
    n: N
);
decode_impl!(
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
    k: K,
    l: L,
    m: M,
    n: N,
    o: O
);
decode_impl!(
    a: A,
    b: B,
    c: C,
    d: D,
    e: E,
    f: F,
    g: G,
    h: H,
    i: I,
    j: J,
    k: K,
    l: L,
    m: M,
    n: N,
    o: O,
    p: P
);

/// Decode a series of arguments, represented as a tuple. There is a maximum of 16 arguments
/// supported.
///
/// Example:
///
/// ```
/// # use candid::Encode;
/// # use candid::de::decode_args;
/// let golden1 = 123u64;
/// let golden2 = "456";
/// let bytes = Encode!(&golden1, &golden2).unwrap();
/// let (value1, value2): (u64, String) = decode_args(&bytes).unwrap();
///
/// assert_eq!(golden1, value1);
/// assert_eq!(golden2, value2);
/// ```
pub fn decode_args<'a, Tuple>(bytes: &'a [u8]) -> Result<Tuple>
where
    Tuple: ArgumentDecoder<'a>,
{
    let mut de = IDLDeserialize::new(bytes)?;
    let res = ArgumentDecoder::decode(&mut de)?;
    de.done()?;
    Ok(res)
}

/// Decode a single argument.
///
/// Example:
///
/// ```
/// # use candid::Encode;
/// # use candid::de::decode_one;
/// let golden1 = 123u64;
/// let bytes = Encode!(&golden1).unwrap();
/// let value1: u64 = decode_one(&bytes).unwrap();
///
/// assert_eq!(golden1, value1);
/// ```
pub fn decode_one<'a, T>(bytes: &'a [u8]) -> Result<T>
where
    T: Deserialize<'a>,
{
    let (res,) = decode_args(bytes)?;
    Ok(res)
}
