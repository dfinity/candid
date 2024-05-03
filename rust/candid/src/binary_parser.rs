use crate::types::internal::{Field, Function, Label, Type, TypeInner};
use crate::types::{FuncMode, TypeEnv};
use anyhow::{anyhow, Context, Result};
use binread::io::{Read, Seek};
use binread::{BinRead, BinResult, Error as BError, ReadOptions};
use std::convert::TryInto;

fn read_leb<R: Read + Seek>(reader: &mut R, ro: &ReadOptions, (): ()) -> BinResult<u64> {
    let pos = reader.stream_position()?;
    leb128::read::unsigned(reader).map_err(|_| BError::Custom {
        pos,
        err: Box::new(ro.variable_name.unwrap_or("Invalid leb128")),
    })
}
fn read_sleb<R: Read + Seek>(reader: &mut R, ro: &ReadOptions, (): ()) -> BinResult<i64> {
    let pos = reader.stream_position()?;
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
    #[br(magic = 0x6au8)]
    Func(FuncType),
    #[br(magic = 0x69u8)]
    Service(ServType),
    Future(FutureType),
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
#[derive(BinRead, Debug)]
struct FuncType {
    #[br(parse_with = read_leb)]
    arg_len: u64,
    #[br(count = arg_len)]
    args: Vec<IndexType>,
    #[br(parse_with = read_leb)]
    ret_len: u64,
    #[br(count = ret_len)]
    rets: Vec<IndexType>,
    #[br(assert(ann_len <= 1u8, "function annotation length should be at most 1"))]
    ann_len: u8,
    #[br(count = ann_len)]
    ann: Vec<Mode>,
}
#[derive(BinRead, Debug)]
struct ServType {
    #[br(parse_with = read_leb)]
    len: u64,
    #[br(count = len)]
    meths: Vec<Meths>,
}
#[derive(BinRead, Debug)]
struct FutureType {
    #[br(parse_with = read_sleb, assert(opcode < -24, "{} is not a valid future type", opcode))]
    opcode: i64,
    #[br(parse_with = read_leb)]
    len: u64,
    #[br(count = len)]
    blob: Vec<u8>,
}
#[derive(BinRead, Debug)]
struct Meths {
    #[br(parse_with = read_leb)]
    len: u64,
    #[br(count = len, try_map = |x:Vec<u8>| String::from_utf8(x).map_err(|_| "invalid utf8"))]
    name: String,
    ty: IndexType,
}
#[derive(BinRead, Debug)]
struct Mode {
    #[br(try_map = |x:u8| match x { 1u8 => Ok(FuncMode::Query), | 2u8 => Ok(FuncMode::Oneway), | 3u8 => Ok(FuncMode::CompositeQuery), | _ => Err("Unknown annotation") })]
    inner: FuncMode,
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
    #[br(parse_with = read_leb, assert(len <= 29, "Principal is longer than 29 bytes"))]
    pub len: u64,
    #[br(count = len)]
    pub inner: Vec<u8>,
}

fn index_to_var(ind: i64) -> String {
    format!("table{ind}")
}
impl IndexType {
    fn to_type(&self, len: u64) -> Result<Type> {
        Ok(match self.index {
            v if v >= 0 => {
                if v >= len as i64 {
                    return Err(anyhow!("type index {} out of range", v));
                }
                TypeInner::Var(index_to_var(v))
            }
            -1 => TypeInner::Null,
            -2 => TypeInner::Bool,
            -3 => TypeInner::Nat,
            -4 => TypeInner::Int,
            -5 => TypeInner::Nat8,
            -6 => TypeInner::Nat16,
            -7 => TypeInner::Nat32,
            -8 => TypeInner::Nat64,
            -9 => TypeInner::Int8,
            -10 => TypeInner::Int16,
            -11 => TypeInner::Int32,
            -12 => TypeInner::Int64,
            -13 => TypeInner::Float32,
            -14 => TypeInner::Float64,
            -15 => TypeInner::Text,
            -16 => TypeInner::Reserved,
            -17 => TypeInner::Empty,
            -24 => TypeInner::Principal,
            _ => unreachable!(),
        }
        .into())
    }
}
impl ConsType {
    fn to_type(&self, len: u64) -> Result<Type> {
        Ok(match &self {
            ConsType::Opt(ref ind) => TypeInner::Opt(ind.to_type(len)?),
            ConsType::Vec(ref ind) => TypeInner::Vec(ind.to_type(len)?),
            ConsType::Record(fs) | ConsType::Variant(fs) => {
                let mut res = Vec::new();
                let mut prev = None;
                for f in &fs.inner {
                    if let Some(prev) = prev {
                        if prev >= f.id {
                            return Err(anyhow!("field id {} collision or not sorted", f.id));
                        }
                    }
                    prev = Some(f.id);
                    let field = Field {
                        id: Label::Id(f.id).into(),
                        ty: f.index.to_type(len)?,
                    };
                    res.push(field);
                }
                if matches!(&self, ConsType::Record(_)) {
                    TypeInner::Record(res)
                } else {
                    TypeInner::Variant(res)
                }
            }
            ConsType::Func(f) => {
                let mut args = Vec::new();
                let mut rets = Vec::new();
                for arg in &f.args {
                    args.push(arg.to_type(len)?);
                }
                for ret in &f.rets {
                    rets.push(ret.to_type(len)?);
                }
                TypeInner::Func(Function {
                    modes: f.ann.iter().map(|x| x.inner.clone()).collect(),
                    args,
                    rets,
                })
            }
            ConsType::Service(serv) => {
                let mut res = Vec::new();
                let mut prev = None;
                for m in &serv.meths {
                    if let Some(prev) = prev {
                        if prev >= &m.name {
                            return Err(anyhow!("method name {} duplicate or not sorted", m.name));
                        }
                    }
                    prev = Some(&m.name);
                    res.push((m.name.clone(), m.ty.to_type(len)?));
                }
                TypeInner::Service(res)
            }
            ConsType::Future(_) => TypeInner::Future,
        }
        .into())
    }
}
impl Table {
    fn to_env(&self, len: u64) -> Result<TypeEnv> {
        use std::collections::BTreeMap;
        let mut env = BTreeMap::new();
        for (i, t) in self.table.iter().enumerate() {
            let ty = t
                .to_type(len)
                .with_context(|| format!("Invalid table entry {i}: {t:?}"))?;
            env.insert(index_to_var(i as i64), ty);
        }
        // validate method has func type
        for t in env.values() {
            if let TypeInner::Service(ms) = t.as_ref() {
                for (name, ty) in ms {
                    if let TypeInner::Var(id) = ty.as_ref() {
                        if matches!(env.get(id).map(|t| t.as_ref()), Some(TypeInner::Func(_))) {
                            continue;
                        }
                    }
                    return Err(anyhow!("Method {name} has a non-function type {ty}"));
                }
            }
        }
        Ok(TypeEnv(env))
    }
}
impl Header {
    pub fn to_types(&self) -> Result<(TypeEnv, Vec<Type>)> {
        let len = self.table.len;
        let mut env = self.table.to_env(len)?;
        env.replace_empty()?;
        let mut args = Vec::new();
        for (i, t) in self.args.iter().enumerate() {
            args.push(
                t.to_type(len)
                    .with_context(|| format!("Invalid argument entry {i}: {t:?}"))?,
            );
        }
        Ok((env, args))
    }
}
