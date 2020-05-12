//! Serialize a Rust data structure to Candid binary format

use error::{Error, Result};

use super::types;
use super::types::{Field, Type};
use parser::value::IDLValue;
use std::collections::HashMap;
use std::io;
use std::vec::Vec;

use leb128::write::{signed as sleb128_encode, unsigned as leb128_encode};

/// Use this struct to serialize a sequence of Rust values (heterogeneous) to IDL binary message.
#[derive(Default)]
pub struct IDLBuilder {
    type_ser: TypeSerialize,
    value_ser: ValueSerializer,
}

impl IDLBuilder {
    pub fn new() -> Self {
        IDLBuilder {
            type_ser: TypeSerialize::new(),
            value_ser: ValueSerializer::new(),
        }
    }
    pub fn arg<'a, T: types::CandidType>(&'a mut self, value: &T) -> Result<&'a mut Self> {
        self.type_ser.push_type(&T::ty())?;
        value.idl_serialize(&mut self.value_ser)?;
        Ok(self)
    }
    pub fn value_arg<'a>(&'a mut self, value: &IDLValue) -> Result<&'a mut Self> {
        use CandidType;
        self.type_ser.push_type(&value.value_ty())?;
        value.idl_serialize(&mut self.value_ser)?;
        Ok(self)
    }
    pub fn serialize<W: io::Write>(&mut self, mut writer: W) -> Result<()> {
        writer.write_all(b"DIDL")?;
        self.type_ser.serialize()?;
        writer.write_all(&self.type_ser.result)?;
        writer.write_all(&self.value_ser.value)?;
        Ok(())
    }
    pub fn serialize_to_vec(&mut self) -> Result<Vec<u8>> {
        let mut vec = Vec::new();
        self.serialize(&mut vec)?;
        Ok(vec)
    }
}

/// A structure for serializing Rust values to IDL.
#[derive(Default)]
pub struct ValueSerializer {
    value: Vec<u8>,
}

impl ValueSerializer {
    /// Creates a new IDL serializer.
    #[inline]
    pub fn new() -> Self {
        ValueSerializer { value: Vec::new() }
    }

    fn write_sleb128(&mut self, value: i64) -> Result<()> {
        sleb128_encode(&mut self.value, value)?;
        Ok(())
    }
    fn write_leb128(&mut self, value: u64) -> Result<()> {
        leb128_encode(&mut self.value, value)?;
        Ok(())
    }
}

impl<'a> types::Serializer for &'a mut ValueSerializer {
    type Error = Error;
    type Compound = Compound<'a>;
    fn serialize_bool(self, v: bool) -> Result<()> {
        let v = if v { 1 } else { 0 };
        self.write_leb128(v)?;
        Ok(())
    }
    fn serialize_int(self, v: i64) -> Result<()> {
        self.write_sleb128(v)?;
        Ok(())
    }
    fn serialize_nat(self, v: u64) -> Result<()> {
        self.write_leb128(v)?;
        Ok(())
    }
    fn serialize_text(self, v: &str) -> Result<()> {
        let mut buf = Vec::from(v.as_bytes());
        self.write_leb128(buf.len() as u64)?;
        self.value.append(&mut buf);
        Ok(())
    }
    fn serialize_null(self, _v: ()) -> Result<()> {
        Ok(())
    }
    fn serialize_option<T: ?Sized>(self, v: Option<&T>) -> Result<()>
    where
        T: super::CandidType,
    {
        match v {
            None => {
                self.write_leb128(0)?;
                Ok(())
            }
            Some(v) => {
                self.write_leb128(1)?;
                v.idl_serialize(self)
            }
        }
    }
    fn serialize_variant(self, index: u64) -> Result<Self::Compound> {
        self.write_leb128(index)?;
        Ok(Self::Compound { ser: self })
    }
    fn serialize_struct(self) -> Result<Self::Compound> {
        Ok(Self::Compound { ser: self })
    }
    fn serialize_vec(self, len: usize) -> Result<Self::Compound> {
        self.write_leb128(len as u64)?;
        Ok(Self::Compound { ser: self })
    }
}

pub struct Compound<'a> {
    ser: &'a mut ValueSerializer,
}
impl<'a> types::Compound for Compound<'a> {
    type Error = Error;
    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<()>
    where
        T: types::CandidType,
    {
        value.idl_serialize(&mut *self.ser)?;
        Ok(())
    }
}

/// A structure for serializing Rust values to IDL types.
#[derive(Default)]
pub struct TypeSerialize {
    type_table: Vec<Vec<u8>>,
    type_map: HashMap<Type, i32>,
    args: Vec<Type>,
    result: Vec<u8>,
}

impl TypeSerialize {
    #[inline]
    pub fn new() -> Self {
        TypeSerialize {
            type_table: Vec::new(),
            type_map: HashMap::new(),
            args: Vec::new(),
            result: Vec::new(),
        }
    }

    #[inline]
    fn build_type(&mut self, t: &Type) -> Result<()> {
        if !types::internal::is_primitive(t) && !self.type_map.contains_key(t) {
            // This is a hack to remove (some) equivalent mu types
            // from the type table.
            // Someone should implement Pottier's O(nlogn) algorithm
            // http://gallium.inria.fr/~fpottier/publis/gauthier-fpottier-icfp04.pdf
            let unrolled = types::internal::unroll(t);
            if let Some(idx) = self.type_map.get(&unrolled) {
                let idx = *idx;
                self.type_map.insert((*t).clone(), idx);
                return Ok(());
            }

            let idx = self.type_table.len();
            self.type_map.insert((*t).clone(), idx as i32);
            self.type_table.push(Vec::new());
            let mut buf = Vec::new();
            match t {
                Type::Opt(ref ty) => {
                    self.build_type(ty)?;
                    sleb128_encode(&mut buf, -18)?;
                    self.encode(&mut buf, ty)?;
                }
                Type::Vec(ref ty) => {
                    self.build_type(ty)?;
                    sleb128_encode(&mut buf, -19)?;
                    self.encode(&mut buf, ty)?;
                }
                Type::Record(fs) => {
                    for Field { ty, .. } in fs.iter() {
                        self.build_type(ty)?;
                    }

                    sleb128_encode(&mut buf, -20)?;
                    leb128_encode(&mut buf, fs.len() as u64)?;
                    for Field { hash, ty, .. } in fs.iter() {
                        leb128_encode(&mut buf, u64::from(*hash))?;
                        self.encode(&mut buf, ty)?;
                    }
                }
                Type::Variant(fs) => {
                    for Field { ty, .. } in fs.iter() {
                        self.build_type(ty)?;
                    }

                    sleb128_encode(&mut buf, -21)?;
                    leb128_encode(&mut buf, fs.len() as u64)?;
                    for Field { hash, ty, .. } in fs.iter() {
                        leb128_encode(&mut buf, u64::from(*hash))?;
                        self.encode(&mut buf, ty)?;
                    }
                }
                _ => panic!("unreachable"),
            };
            self.type_table[idx] = buf;
        };
        Ok(())
    }

    fn push_type(&mut self, t: &Type) -> Result<()> {
        self.args.push(t.clone());
        self.build_type(t)
    }

    fn encode(&self, buf: &mut Vec<u8>, t: &Type) -> Result<()> {
        match t {
            Type::Null => sleb128_encode(buf, -1),
            Type::Bool => sleb128_encode(buf, -2),
            Type::Nat => sleb128_encode(buf, -3),
            Type::Int => sleb128_encode(buf, -4),
            Type::Text => sleb128_encode(buf, -15),
            Type::Knot(id) => {
                let ty = types::internal::find_type(*id).expect("knot TypeId not found");
                let idx = self
                    .type_map
                    .get(&ty)
                    .unwrap_or_else(|| panic!("knot type {:?} not found", ty));
                sleb128_encode(buf, i64::from(*idx))
            }
            _ => {
                let idx = self
                    .type_map
                    .get(&t)
                    .unwrap_or_else(|| panic!("type {:?} not found", t));
                sleb128_encode(buf, i64::from(*idx))
            }
        }?;
        Ok(())
    }

    fn serialize(&mut self) -> Result<()> {
        leb128_encode(&mut self.result, self.type_table.len() as u64)?;
        self.result.append(&mut self.type_table.concat());

        leb128_encode(&mut self.result, self.args.len() as u64)?;
        let mut ty_encode = Vec::new();
        for t in self.args.iter() {
            self.encode(&mut ty_encode, t)?;
        }
        self.result.append(&mut ty_encode);
        Ok(())
    }
}
