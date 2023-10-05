//! Deserialize Candid binary format to Rust data structures

use super::{
    error::{Error, Result},
    types::internal::{text_size, type_of, TypeId},
    types::{Field, Label, SharedLabel, Type, TypeEnv, TypeInner},
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

const MAX_TYPE_LEN: i32 = 500;

/// Use this struct to deserialize a sequence of Rust values (heterogeneous) from IDL binary message.
pub struct IDLDeserialize<'de> {
    de: Deserializer<'de>,
}
impl<'de> IDLDeserialize<'de> {
    /// Create a new deserializer with IDL binary message.
    pub fn new(bytes: &'de [u8]) -> Result<Self> {
        let de = Deserializer::from_bytes(bytes).with_context(|| {
            if bytes.len() <= 500 {
                format!("Cannot parse header {}", &hex::encode(bytes))
            } else {
                "Cannot parse header".to_string()
            }
        })?;
        Ok(IDLDeserialize { de })
    }
    /// Create a new deserializer with IDL binary message. The config is used to adjust some parameters in the deserializer.
    pub fn new_with_config(bytes: &'de [u8], config: Config) -> Result<Self> {
        let mut de = Deserializer::from_bytes(bytes).with_context(|| {
            if config.full_error_message || bytes.len() <= 500 {
                format!("Cannot parse header {}", &hex::encode(bytes))
            } else {
                "Cannot parse header".to_string()
            }
        })?;
        de.zero_sized_values = config.zero_sized_values;
        de.full_error_message = config.full_error_message;
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
    ) -> Result<crate::types::value::IDLValue> {
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
            if matches!(
                expected_type.as_ref(),
                TypeInner::Opt(_) | TypeInner::Reserved | TypeInner::Null
            ) {
                self.de.expect_type = expected_type;
                self.de.wire_type = TypeInner::Reserved.into();
                return T::deserialize(&mut self.de);
            } else if self.de.full_error_message || text_size(&expected_type, MAX_TYPE_LEN).is_ok()
            {
                return Err(Error::msg(format!(
                    "No more values on the wire, the expected type {expected_type} is not opt, null, or reserved"
                )));
            } else {
                return Err(Error::msg("No more values on the wire"));
            }
        }

        let (ind, ty) = self.de.types.pop_front().unwrap();
        self.de.expect_type = if matches!(expected_type.as_ref(), TypeInner::Unknown) {
            self.de.is_untyped = true;
            ty.clone()
        } else {
            expected_type.clone()
        };
        self.de.wire_type = ty.clone();

        let mut v = T::deserialize(&mut self.de).with_context(|| {
            if self.de.full_error_message
                || (text_size(&ty, MAX_TYPE_LEN).is_ok()
                    && text_size(&expected_type, MAX_TYPE_LEN).is_ok())
            {
                format!("Fail to decode argument {ind} from {ty} to {expected_type}")
            } else {
                format!("Fail to decode argument {ind}")
            }
        });
        if self.de.full_error_message {
            v = v.with_context(|| self.de.dump_state());
        }
        Ok(v?)
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
            if !self.de.full_error_message {
                return Err(Error::msg("Trailing value after finishing deserialization"));
            } else {
                return Err(anyhow!(self.de.dump_state()))
                    .context("Trailing value after finishing deserialization")?;
            }
        }
        Ok(())
    }
}

pub struct Config {
    pub zero_sized_values: usize,
    pub full_error_message: bool,
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
#[cfg(not(target_arch = "wasm32"))]
macro_rules! check_recursion {
    ($this:ident $($body:tt)*) => {
        $this.recursion_depth += 1;
        match stacker::remaining_stack() {
            Some(size) if size < 32768 => return Err(Error::msg(format!("Recursion limit exceeded at depth {}", $this.recursion_depth))),
            None if $this.recursion_depth > 512 => return Err(Error::msg(format!("Recursion limit exceeded at depth {}. Cannot detect stack size, use a conservative bound", $this.recursion_depth))),
            _ => (),
        }
        let __ret = { $this $($body)* };
        $this.recursion_depth -= 1;
        __ret
    };
}
// No need to check recursion depth for wasm32, because canisters are running in a sandbox
#[cfg(target_arch = "wasm32")]
macro_rules! check_recursion {
    ($this:ident $($body:tt)*) => {
        $this $($body)*
    };
}

#[derive(Clone)]
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
    field_name: Option<SharedLabel>,
    // Indicates whether to deserialize with IDLValue.
    // It only affects the field id generation in enum type.
    is_untyped: bool,
    zero_sized_values: usize,
    full_error_message: bool,
    #[cfg(not(target_arch = "wasm32"))]
    recursion_depth: u16,
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
            wire_type: TypeInner::Unknown.into(),
            expect_type: TypeInner::Unknown.into(),
            gamma: Gamma::default(),
            field_name: None,
            is_untyped: false,
            #[cfg(not(target_arch = "wasm32"))]
            zero_sized_values: 2_000_000,
            #[cfg(target_arch = "wasm32")]
            zero_sized_values: 0,
            #[cfg(not(target_arch = "wasm32"))]
            full_error_message: true,
            #[cfg(target_arch = "wasm32")]
            full_error_message: false,
            #[cfg(not(target_arch = "wasm32"))]
            recursion_depth: 0,
        })
    }
    fn dump_state(&self) -> String {
        let hex = hex::encode(self.input.get_ref());
        let pos = self.input.position() as usize * 2;
        let (before, after) = hex.split_at(pos);
        let mut res = format!("input: {before}_{after}\n");
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
            write!(&mut res, ", field_name: {field:?}").unwrap();
        }
        res
    }
    fn borrow_bytes(&mut self, len: usize) -> Result<&'de [u8]> {
        let pos = self.input.position() as usize;
        let slice = self.input.get_ref();
        if len > slice.len() || pos + len > slice.len() {
            return Err(Error::msg(format!("Cannot read {len} bytes")));
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
            if self.full_error_message
                || (text_size(&self.wire_type, MAX_TYPE_LEN).is_ok()
                    && text_size(&self.expect_type, MAX_TYPE_LEN).is_ok())
            {
                format!(
                    "{} is not a subtype of {}",
                    self.wire_type, self.expect_type,
                )
            } else {
                "subtype mismatch".to_string()
            }
        })
        .map_err(Error::subtype)?;
        Ok(())
    }
    fn unroll_type(&mut self) -> Result<()> {
        if matches!(
            self.expect_type.as_ref(),
            TypeInner::Var(_) | TypeInner::Knot(_)
        ) {
            self.expect_type = self.table.trace_type(&self.expect_type)?;
        }
        if matches!(
            self.wire_type.as_ref(),
            TypeInner::Var(_) | TypeInner::Knot(_)
        ) {
            self.wire_type = self.table.trace_type(&self.wire_type)?;
        }
        Ok(())
    }
    fn is_zero_sized_type(&self, t: &Type) -> bool {
        match t.as_ref() {
            TypeInner::Null | TypeInner::Reserved => true,
            TypeInner::Record(fs) => fs.iter().all(|f| {
                let t = self.table.trace_type(&f.ty).unwrap();
                // recursive records have been replaced with empty already, it's safe to call without memoization.
                self.is_zero_sized_type(&t)
            }),
            _ => false,
        }
    }
    // Should always call set_field_name to set the field_name. After deserialize_identifier
    // processed the field_name, field_name will be reset to None.
    fn set_field_name(&mut self, field: SharedLabel) {
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
        self.unroll_type()?;
        assert!(*self.expect_type == TypeInner::Int);
        let mut bytes = vec![0u8];
        let int = match self.wire_type.as_ref() {
            TypeInner::Int => Int::decode(&mut self.input).map_err(Error::msg)?,
            TypeInner::Nat => Int(Nat::decode(&mut self.input)
                .map_err(Error::msg)?
                .0
                .try_into()
                .map_err(Error::msg)?),
            t => return Err(Error::subtype(format!("{t} cannot be deserialized to int"))),
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
            *self.expect_type == TypeInner::Nat && *self.wire_type == TypeInner::Nat,
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
            *self.expect_type == TypeInner::Principal && *self.wire_type == TypeInner::Principal,
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
        let slice_len = self.input.get_ref().len() as u64;
        let pos = self.input.position();
        if len > slice_len || pos + len > slice_len {
            return Err(Error::msg(format!("Cannot read {len} bytes")));
        }
        self.input.set_position(pos + len);
        visitor.visit_unit()
    }
    fn recoverable_visit_some<'a, V>(&'a mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use de::Deserializer;
        let tid = type_of(&visitor);
        if tid != TypeId::of::<crate::types::value::IDLValueVisitor>() // derive Copy
            && tid != TypeId::of::<de::IgnoredAny>() // derive Copy
        // OptionVisitor doesn't derive Copy, but has only PhantomData.
        // OptionVisitor is private and we cannot get TypeId of OptionVisitor<T>,
        // we also cannot downcast V to concrete type, because of 'de
        // The only option left seems to be type_name, but it is not guaranteed to be stable, so there is risk here.
            && !tid.name.starts_with("serde::de::impls::OptionVisitor<")
        {
            panic!("Not a valid visitor: {tid:?}");
        }
        // This is safe, because the visitor either impl Copy or is zero sized
        let v = unsafe { std::ptr::read(&visitor) };
        let mut self_clone = self.clone();
        match v.visit_some(&mut self_clone) {
            Ok(v) => {
                *self = self_clone;
                Ok(v)
            }
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
                check!(*self.expect_type == $type && *self.wire_type == $type, stringify!($type));
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
        match self.expect_type.as_ref() {
            TypeInner::Int => self.deserialize_int(visitor),
            TypeInner::Nat => self.deserialize_nat(visitor),
            TypeInner::Nat8 => self.deserialize_u8(visitor),
            TypeInner::Nat16 => self.deserialize_u16(visitor),
            TypeInner::Nat32 => self.deserialize_u32(visitor),
            TypeInner::Nat64 => self.deserialize_u64(visitor),
            TypeInner::Int8 => self.deserialize_i8(visitor),
            TypeInner::Int16 => self.deserialize_i16(visitor),
            TypeInner::Int32 => self.deserialize_i32(visitor),
            TypeInner::Int64 => self.deserialize_i64(visitor),
            TypeInner::Float32 => self.deserialize_f32(visitor),
            TypeInner::Float64 => self.deserialize_f64(visitor),
            TypeInner::Bool => self.deserialize_bool(visitor),
            TypeInner::Text => self.deserialize_string(visitor),
            TypeInner::Null => self.deserialize_unit(visitor),
            TypeInner::Reserved => {
                if self.wire_type.as_ref() != &TypeInner::Reserved {
                    self.deserialize_ignored_any(serde::de::IgnoredAny)?;
                }
                self.deserialize_reserved(visitor)
            }
            TypeInner::Empty => self.deserialize_empty(visitor),
            TypeInner::Principal => self.deserialize_principal(visitor),
            // construct types
            TypeInner::Opt(_) => self.deserialize_option(visitor),
            TypeInner::Vec(_) => self.deserialize_seq(visitor),
            TypeInner::Record(_) => self.deserialize_struct("_", &[], visitor),
            TypeInner::Variant(_) => self.deserialize_enum("_", &[], visitor),
            TypeInner::Service(_) => self.deserialize_service(visitor),
            TypeInner::Func(_) => self.deserialize_function(visitor),
            TypeInner::Future => self.deserialize_future(visitor),
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

    primitive_impl!(i8, TypeInner::Int8, read_i8);
    primitive_impl!(i16, TypeInner::Int16, read_i16::<LittleEndian>);
    primitive_impl!(i32, TypeInner::Int32, read_i32::<LittleEndian>);
    primitive_impl!(i64, TypeInner::Int64, read_i64::<LittleEndian>);
    primitive_impl!(u8, TypeInner::Nat8, read_u8);
    primitive_impl!(u16, TypeInner::Nat16, read_u16::<LittleEndian>);
    primitive_impl!(u32, TypeInner::Nat32, read_u32::<LittleEndian>);
    primitive_impl!(u64, TypeInner::Nat64, read_u64::<LittleEndian>);
    primitive_impl!(f32, TypeInner::Float32, read_f32::<LittleEndian>);
    primitive_impl!(f64, TypeInner::Float64, read_f64::<LittleEndian>);

    fn is_human_readable(&self) -> bool {
        false
    }
    fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use num_traits::ToPrimitive;
        self.unroll_type()?;
        assert!(*self.expect_type == TypeInner::Int);
        let value: i128 = match self.wire_type.as_ref() {
            TypeInner::Int => {
                let int = Int::decode(&mut self.input).map_err(Error::msg)?;
                int.0
                    .to_i128()
                    .ok_or_else(|| Error::msg("Cannot convert int to i128"))?
            }
            TypeInner::Nat => {
                let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
                nat.0
                    .to_i128()
                    .ok_or_else(|| Error::msg("Cannot convert nat to i128"))?
            }
            t => return Err(Error::subtype(format!("{t} cannot be deserialized to int"))),
        };
        visitor.visit_i128(value)
    }
    fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use num_traits::ToPrimitive;
        self.unroll_type()?;
        check!(
            *self.expect_type == TypeInner::Nat && *self.wire_type == TypeInner::Nat,
            "nat"
        );
        let nat = Nat::decode(&mut self.input).map_err(Error::msg)?;
        let value = nat
            .0
            .to_u128()
            .ok_or_else(|| Error::msg("Cannot convert nat to u128"))?;
        visitor.visit_u128(value)
    }
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.unroll_type()?;
        check!(
            *self.expect_type == TypeInner::Null
                && matches!(*self.wire_type, TypeInner::Null | TypeInner::Reserved),
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
            *self.expect_type == TypeInner::Bool && *self.wire_type == TypeInner::Bool,
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
            *self.expect_type == TypeInner::Text && *self.wire_type == TypeInner::Text,
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
            *self.expect_type == TypeInner::Text && *self.wire_type == TypeInner::Text,
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
        match (self.wire_type.as_ref(), self.expect_type.as_ref()) {
            (TypeInner::Null, TypeInner::Opt(_)) | (TypeInner::Reserved, TypeInner::Opt(_)) => {
                visitor.visit_none()
            }
            (TypeInner::Opt(t1), TypeInner::Opt(t2)) => {
                self.wire_type = t1.clone();
                self.expect_type = t2.clone();
                if BoolValue::read(&mut self.input)?.0 {
                    check_recursion! {
                        self.recoverable_visit_some(visitor)
                    }
                } else {
                    visitor.visit_none()
                }
            }
            (_, TypeInner::Opt(t2)) => {
                self.expect_type = self.table.trace_type(t2)?;
                if !matches!(
                    self.expect_type.as_ref(),
                    TypeInner::Null | TypeInner::Reserved | TypeInner::Opt(_)
                ) {
                    check_recursion! {
                        self.recoverable_visit_some(visitor)
                    }
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
        check_recursion! {
        self.unroll_type()?;
        match (self.expect_type.as_ref(), self.wire_type.as_ref()) {
            (TypeInner::Vec(e), TypeInner::Vec(w)) => {
                let expect = e.clone();
                let wire = self.table.trace_type(w)?;
                let len = Len::read(&mut self.input)?.0;
                if self.is_zero_sized_type(&wire) {
                    if self.zero_sized_values < len {
                        return Err(Error::msg("vec length of zero sized values too large"));
                    }
                    self.zero_sized_values -= len;
                }
                visitor.visit_seq(Compound::new(self, Style::Vector { len, expect, wire }))
            }
            (TypeInner::Record(e), TypeInner::Record(w)) => {
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
    }
    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.unroll_type()?;
        check!(
            *self.expect_type == TypeInner::Vec(TypeInner::Nat8.into())
                && *self.wire_type == TypeInner::Vec(TypeInner::Nat8.into()),
            "vec nat8"
        );
        let len = Len::read(&mut self.input)?.0;
        let bytes = self.borrow_bytes(len)?.to_owned();
        visitor.visit_byte_buf(bytes)
    }
    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.unroll_type()?;
        match self.expect_type.as_ref() {
            TypeInner::Principal => self.deserialize_principal(visitor),
            TypeInner::Vec(t) if **t == TypeInner::Nat8 => {
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
        check_recursion! {
        self.unroll_type()?;
        match (self.expect_type.as_ref(), self.wire_type.as_ref()) {
            (TypeInner::Vec(e), TypeInner::Vec(w)) => {
                let e = self.table.trace_type(e)?;
                let w = self.table.trace_type(w)?;
                match (e.as_ref(), w.as_ref()) {
                    (TypeInner::Record(ref e), TypeInner::Record(ref w)) => {
                        match (&e[..], &w[..]) {
                            (
                                [Field { id: e_id0, ty: ek }, Field { id: e_id1, ty: ev }],
                                [Field { id: w_id0, ty: wk }, Field { id: w_id1, ty: wv }],
                            ) if **e_id0 == Label::Id(0)
                                && **e_id1 == Label::Id(1)
                                && **w_id0 == Label::Id(0)
                                && **w_id1 == Label::Id(1) =>
                            {
                                let expect = (ek.clone(), ev.clone());
                                let wire = (wk.clone(), wv.clone());
                                let len = Len::read(&mut self.input)?.0;
                                visitor.visit_map(Compound::new(
                                    self,
                                    Style::Map { len, expect, wire },
                                ))
                            }
                            _ => Err(Error::subtype("expect a key-value pair")),
                        }
                    }
                    _ => Err(Error::subtype("expect a key-value pair")),
                }
            }
            _ => check!(false),
        }
        }
    }
    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        check_recursion! {
            self.deserialize_seq(visitor)
        }
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
        check_recursion! {
            self.deserialize_seq(visitor)
        }
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
        check_recursion! {
        self.unroll_type()?;
        match (self.expect_type.as_ref(), self.wire_type.as_ref()) {
            (TypeInner::Record(e), TypeInner::Record(w)) => {
                let expect = e.clone().into();
                let wire = w.clone().into();
                let value =
                    visitor.visit_map(Compound::new(self, Style::Struct { expect, wire }))?;
                Ok(value)
            }
            _ => check!(false),
        }
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
        check_recursion! {
        self.unroll_type()?;
        match (self.expect_type.as_ref(), self.wire_type.as_ref()) {
            (TypeInner::Variant(e), TypeInner::Variant(w)) => {
                let index = Len::read(&mut self.input)?.0;
                let len = w.len();
                if index >= len {
                    return Err(Error::msg(format!(
                        "Variant index {index} larger than length {len}"
                    )));
                }
                let wire = w[index].clone();
                let expect = match e.iter().find(|f| f.id == wire.id) {
                    Some(v) => v.clone(),
                    None => {
                        return Err(Error::subtype(format!("Unknown variant field {}", wire.id)));
                    }
                };
                visitor.visit_enum(Compound::new(self, Style::Enum { expect, wire }))
            }
            _ => check!(false),
        }
        }
    }
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.field_name.take() {
            Some(l) => match l.as_ref() {
                Label::Named(name) => visitor.visit_string(name.to_string()),
                Label::Id(hash) | Label::Unnamed(hash) => visitor.visit_u32(*hash),
            },
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
                self.de.expect_type = expect
                    .pop_front()
                    .map(|f| f.ty)
                    .unwrap_or_else(|| TypeInner::Reserved.into());
                self.de.wire_type = wire
                    .pop_front()
                    .map(|f| f.ty)
                    .unwrap_or_else(|| TypeInner::Reserved.into());
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
                                        self.de.expect_type.as_ref(),
                                        TypeInner::Opt(_) | TypeInner::Reserved | TypeInner::Null
                                    ),
                                    format!("field {field} is not optional field")
                                );
                                self.de.wire_type = TypeInner::Reserved.into();
                            }
                            Ordering::Greater => {
                                self.de.set_field_name(Label::Named("_".to_owned()).into());
                                self.de.wire_type = wire.pop_front().unwrap().ty;
                                self.de.expect_type = TypeInner::Reserved.into();
                            }
                        }
                    }
                    (None, Some(_)) => {
                        self.de.set_field_name(Label::Named("_".to_owned()).into());
                        self.de.wire_type = wire.pop_front().unwrap().ty;
                        self.de.expect_type = TypeInner::Reserved.into();
                    }
                    (Some(e), None) => {
                        self.de.set_field_name(e.id.clone());
                        self.de.expect_type = expect.pop_front().unwrap().ty;
                        self.de.wire_type = TypeInner::Reserved.into();
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
                let (mut label, label_type) = match expect.id.as_ref() {
                    Label::Named(name) => (name.clone(), "name"),
                    Label::Id(hash) | Label::Unnamed(hash) => (hash.to_string(), "id"),
                };
                if self.de.is_untyped {
                    let accessor = match expect.ty.as_ref() {
                        TypeInner::Null => "unit",
                        TypeInner::Record(_) => "struct",
                        _ => "newtype",
                    };
                    write!(&mut label, ",{label_type},{accessor}").map_err(Error::msg)?;
                }
                self.de.set_field_name(Label::Named(label).into());
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
            *self.de.expect_type == TypeInner::Null && *self.de.wire_type == TypeInner::Null,
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
