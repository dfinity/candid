use crate::parser::typing::TypeEnv;
use crate::types::internal::{Field, Label, Type};
use anyhow::{anyhow, Context, Result};
use binread::io::{Read, Seek, SeekFrom};
use binread::{BinRead, BinResult, Error as BError, ReadOptions};
use std::convert::TryInto;

fn read_leb<R: Read + Seek>(reader: &mut R, ro: &ReadOptions, _: ()) -> BinResult<u64> {
    let pos = reader.seek(SeekFrom::Current(0))?;
    leb128::read::unsigned(reader).map_err(|_| BError::Custom {
        pos,
        err: Box::new(ro.variable_name.unwrap_or("Invalid leb128")),
    })
}
fn read_sleb<R: Read + Seek>(reader: &mut R, ro: &ReadOptions, _: ()) -> BinResult<i64> {
    let pos = reader.seek(SeekFrom::Current(0))?;
    leb128::read::signed(reader).map_err(|_| BError::Custom {
        pos,
        err: Box::new(ro.variable_name.unwrap_or("Invalid sleb128")),
    })
}

#[derive(BinRead, Debug)]
#[br(magic = b"DIDL")]
pub struct Header {
    table: Table,
    #[br(parse_with = read_leb)]
    len: u64,
    #[br(count = len)]
    args: Vec<IndexType>,
}
#[derive(BinRead, Debug)]
struct Table {
    #[br(parse_with = read_leb, assert(len <= i64::MAX as u64, "type table size out of range"))]
    len: u64,
    #[br(count = len)]
    table: Vec<ConsType>,
}
#[derive(BinRead, Debug)]
enum ConsType {
    #[br(magic = 0x6eu8)]
    Opt(Box<IndexType>),
    #[br(magic = 0x6du8)]
    Vec(Box<IndexType>),
    #[br(magic = 0x6cu8)]
    Record(Fields),
    #[br(magic = 0x6bu8)]
    Variant(Fields),
}
#[derive(BinRead, Debug)]
struct IndexType {
    #[br(parse_with = read_sleb, assert(index >= -17 || index == -24, "unknown opcode {}", index))]
    index: i64,
}
#[derive(BinRead, Debug)]
struct Fields {
    #[br(parse_with = read_leb, try_map = |x:u64| x.try_into().map_err(|_| "field length out of 32-bit range"))]
    len: u32,
    #[br(count = len)]
    inner: Vec<FieldType>,
}
#[derive(BinRead, Debug)]
struct FieldType {
    #[br(parse_with = read_leb, try_map = |x:u64| x.try_into().map_err(|_| "field id out of 32-bit range"))]
    id: u32,
    index: IndexType,
}

#[derive(BinRead)]
pub struct BoolValue(
    #[br(try_map = |x:u8| match x { 0u8 => Ok(false), | 1u8 => Ok(true), | _ => Err("Expect 00 or 01") } )]
    pub bool,
);
#[derive(BinRead)]
pub struct Len(
    #[br(parse_with = read_leb, try_map = |x:u64| x.try_into().map_err(|_| "length out of usize range"))]
    pub usize,
);
#[derive(BinRead)]
pub struct PrincipalBytes {
    #[br(assert(flag == 1u8, "Opaque reference not supported"))]
    pub flag: u8,
    #[br(parse_with = read_leb)]
    pub len: u64,
    #[br(count = len, parse_with = binread::helpers::read_bytes)]
    pub inner: Vec<u8>,
}

fn index_to_var(ind: i64) -> String {
    format!("table{}", ind)
}
impl IndexType {
    fn to_type(&self, len: u64) -> Result<Type> {
        Ok(match self.index {
            v if v >= 0 => {
                if v >= len as i64 {
                    return Err(anyhow!("type index {} out of range", v));
                }
                Type::Var(index_to_var(v))
            }
            -1 => Type::Null,
            -2 => Type::Bool,
            -3 => Type::Nat,
            -4 => Type::Int,
            -5 => Type::Nat8,
            -6 => Type::Nat16,
            -7 => Type::Nat32,
            -8 => Type::Nat64,
            -9 => Type::Int8,
            -10 => Type::Int16,
            -11 => Type::Int32,
            -12 => Type::Int64,
            -13 => Type::Float32,
            -14 => Type::Float64,
            -15 => Type::Text,
            -16 => Type::Reserved,
            -17 => Type::Empty,
            -24 => Type::Principal,
            _ => unreachable!(),
        })
    }
}
impl ConsType {
    fn to_type(&self, len: u64) -> Result<Type> {
        Ok(match &self {
            ConsType::Opt(ref ind) => Type::Opt(Box::new(ind.to_type(len)?)),
            ConsType::Vec(ref ind) => Type::Vec(Box::new(ind.to_type(len)?)),
            ConsType::Record(fs) | ConsType::Variant(fs) => {
                let mut res = Vec::new();
                let mut prev = None;
                for f in fs.inner.iter() {
                    if let Some(prev) = prev {
                        if prev >= f.id {
                            return Err(anyhow!("field id {} collision or not sorted", f.id));
                        }
                    }
                    prev = Some(f.id);
                    let field = Field {
                        id: Label::Id(f.id),
                        ty: f.index.to_type(len)?,
                    };
                    res.push(field);
                }
                if matches!(&self, ConsType::Record(_)) {
                    Type::Record(res)
                } else {
                    Type::Variant(res)
                }
            }
        })
    }
}
impl Table {
    fn to_env(&self, len: u64) -> Result<TypeEnv> {
        use std::collections::BTreeMap;
        let mut env = BTreeMap::new();
        for (i, t) in self.table.iter().enumerate() {
            env.insert(
                index_to_var(i as i64),
                t.to_type(len)
                    .with_context(|| format!("Invalid table entry {}: {:?}", i, t))?,
            );
        }
        Ok(TypeEnv(env))
    }
}
impl Header {
    pub fn to_types(&self) -> Result<(TypeEnv, Vec<Type>)> {
        let len = self.table.len;
        let env = self.table.to_env(len)?;
        let mut args = Vec::new();
        for (i, t) in self.args.iter().enumerate() {
            args.push(
                t.to_type(len)
                    .with_context(|| format!("Invalid argument entry {}: {:?}", i, t))?,
            );
        }
        Ok((env, args))
    }
}
