use crate::parser::typing::TypeEnv;
use crate::types::internal::{Field, Label, Type};
use binread::io::{Read, Seek, SeekFrom};
use binread::{BinRead, BinResult, Error, ReadOptions};
use std::convert::TryInto;

fn read_leb<R: Read + Seek>(reader: &mut R, ro: &ReadOptions, _: ()) -> BinResult<u64> {
    let pos = reader.seek(SeekFrom::Current(0))?;
    leb128::read::unsigned(reader).map_err(|_| Error::Custom {
        pos,
        err: Box::new(ro.variable_name.unwrap_or("Invalid leb128")),
    })
}
fn read_sleb<R: Read + Seek>(reader: &mut R, ro: &ReadOptions, _: ()) -> BinResult<i64> {
    let pos = reader.seek(SeekFrom::Current(0))?;
    leb128::read::signed(reader).map_err(|_| Error::Custom {
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
pub struct Table {
    #[br(parse_with = read_leb)]
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
    #[br(parse_with = read_leb, try_map = |x:u64| x.try_into())]
    len: u32,
    #[br(count = len)]
    inner: Vec<FieldType>,
}
#[derive(BinRead, Debug)]
struct FieldType {
    #[br(parse_with = read_leb, try_map = |x:u64| x.try_into())]
    id: u32,
    index: IndexType,
}

impl IndexType {
    pub fn to_type(&self) -> Type {
        match self.index {
            v if v >= 0 => Type::Var(v.to_string()),
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
        }
    }
}
impl FieldType {
    pub fn to_field(&self) -> Field {
        Field {
            id: Label::Id(self.id),
            ty: self.index.to_type(),
        }
    }
}
impl ConsType {
    pub fn to_type(&self) -> Type {
        match &self {
            ConsType::Opt(ref ind) => Type::Opt(Box::new(ind.to_type())),
            ConsType::Vec(ref ind) => Type::Vec(Box::new(ind.to_type())),
            ConsType::Record(fs) => Type::Record(fs.inner.iter().map(|f| f.to_field()).collect()),
            ConsType::Variant(fs) => Type::Variant(fs.inner.iter().map(|f| f.to_field()).collect()),
        }
    }
}
impl Table {
    pub fn to_env(&self) -> TypeEnv {
        TypeEnv(
            self.table
                .iter()
                .enumerate()
                .map(|(i, t)| (i.to_string(), t.to_type()))
                .collect(),
        )
    }
}

#[test]
fn parse() -> crate::Result<()> {
    use binread::io::Cursor;
    let mut reader =
        Cursor::new(b"DIDL\x03\x6e\x00\x6d\x6f\x6c\x02\x00\x7e\x01\x7a\x02\x02\x03".as_ref());
    let header = crate::error::pretty_read::<Header>(&mut reader)?;
    println!("{}", header.table.to_env());
    let rest = reader.position() as usize;
    println!("remaining {:02x?}", &reader.into_inner()[rest..]);
    Ok(())
}
