use binread::io::{Read, Seek, SeekFrom};
use binread::{BinRead, BinResult, Error, ReadOptions};

fn read_leb<R: Read + Seek>(reader: &mut R, _ro: &ReadOptions, _: ()) -> BinResult<u64> {
    let pos = reader.seek(SeekFrom::Current(0))?;
    leb128::read::unsigned(reader).map_err(|_| Error::Custom {
        pos,
        err: Box::new("Invalid leb128"),
    })
}
fn read_sleb<R: Read + Seek>(reader: &mut R, _ro: &ReadOptions, _: ()) -> BinResult<i64> {
    let pos = reader.seek(SeekFrom::Current(0))?;
    leb128::read::signed(reader).map_err(|_| Error::Custom {
        pos,
        err: Box::new("Invalid sleb128"),
    })
}

#[derive(BinRead, Debug)]
#[br(magic = b"DIDL")]
struct Table {
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
}
#[derive(BinRead, Debug)]
struct IndexType {
    #[br(parse_with = read_sleb)]
    index: i64,
}
#[derive(BinRead, Debug)]
struct Fields {
    #[br(parse_with = read_leb)]
    len: u64,
    #[br(count = len)]
    inner: Vec<FieldType>,
}
#[derive(BinRead, Debug)]
struct FieldType {
    #[br(parse_with = read_leb)]
    id: u64,
    index: IndexType,
}

#[test]
fn parse() -> crate::Result<()> {
    use binread::io::Cursor;
    let mut reader = Cursor::new(b"DIDL\x03\x6e\x00\x6d\x7f\x6c\x01\x00\x7e".as_ref());
    //let table = Table::read(&mut reader)?;
    let table = crate::error::pretty_read::<Table>(&mut reader)?;
    println!("{:?}", table);
    let rest = reader.position() as usize;
    println!("remaining {:02x?}", &reader.into_inner()[rest..]);
    Ok(())
}
