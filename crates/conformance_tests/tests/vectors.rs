//! The conformance vectors, asked of the crates in this workspace.
//!
//! - `candid_types` answers `hash`, `wellformed` and `subtype`. Every other vector
//!   carries types too, and the format promises they are well formed
//!   (`conformance/README.md`), so each of those tables is checked as well: thousands of
//!   tables the model accepts, which `RawTypeTable::check` must accept too.
//! - `candid_binary` reads message headers, and writes values. Every message a `decode`
//!   vector accepts, or calls costly, has a header it must accept; a message the vector
//!   rejects may be rejected for its header or for its values, so only the count of
//!   those whose header is already rejected is reported. Every table above is written in
//!   a message with no arguments and read back, which must give the same table.
//! - `candid_value` reads every `<value>`, and with `candid_binary` writes it at the type
//!   the vector says it has: a `coerce` vector's value at `from` and its expected value at
//!   `to`, and a `decode` or `parse` vector's expected values at its types. Where a
//!   `decode` vector's types are its message's own header and nothing in it was coerced,
//!   the values must give back the message's bytes (`crates/README.md`, "Order of work").
//!
//! Like a runner, this reads strictly: an unknown key, kind or name is an error, never
//! skipped.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use candid_binary::{Encode, Encoder, Header};
use candid_types::{
    Annotation, Composite, FieldId, Primitive, RawTypeTable, Slot, TypeRef, TypeTable,
};
use candid_value::{Float32, Float64, Int, Nat, Principal, Record};
use serde_json::{Map, Value};

type Json = Map<String, Value>;

fn vectors_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../conformance/vectors")
}

#[test]
fn conformance_vectors() {
    let mut files: Vec<_> = std::fs::read_dir(vectors_dir())
        .expect("conformance/vectors")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no vector files found");

    let mut asked: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut failures = Vec::new();
    for file in &files {
        let text = std::fs::read_to_string(file).unwrap();
        let suite: Value = serde_json::from_str(&text).unwrap();
        let suite = obj(&suite, &["version", "vectors"]);
        assert_eq!(suite["version"], 0, "{}", file.display());
        for vector in suite["vectors"].as_array().unwrap() {
            let id = vector["id"].as_str().unwrap();
            match ask(vector) {
                Ok(kind) => *asked.entry(kind).or_default() += 1,
                Err(e) => failures.push(format!("{}: {id}: {e}", file.display())),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // Not vacuous: the suite has vectors of every kind this crate answers.
    for kind in [
        "hash",
        "wellformed",
        "subtype",
        "decode (costly; header)",
        "decode (rejected by the header)",
        "decode (values give back the bytes)",
        "decode (not in shortest form)",
        "coerce (values written)",
        "parse (values written)",
    ] {
        assert!(
            asked.get(kind).copied().unwrap_or(0) > 0,
            "no {kind} vectors"
        );
    }
    println!("{asked:?}");
}

/// Ask one vector. Returns its kind on agreement.
fn ask(vector: &Value) -> Result<&'static str, String> {
    let kind = vector["kind"].as_str().ok_or("kind is not a string")?;
    match kind {
        "hash" => {
            let v = obj(vector, &["id", "kind", "name", "expect"]);
            let name = v["name"].as_str().ok_or("name")?;
            let expect = field_id(&v["expect"])?;
            let got = candid_types::hash_field_name(name);
            agree(got == expect, || {
                format!("hash is {got}, expected {expect}")
            })?;
            Ok("hash")
        }
        "wellformed" => {
            let v = obj(vector, &["id", "kind", "type", "expect"]);
            let expect = v["expect"].as_bool().ok_or("expect")?;
            let (raw, root) = read_type(&v["type"])?;
            let got = match raw.check() {
                Ok(table) => table.root(root).is_some(),
                Err(_) => false,
            };
            agree(got == expect, || {
                format!("well formed is {got}, expected {expect}")
            })?;
            Ok("wellformed")
        }
        "subtype" => {
            let v = obj(vector, &["id", "kind", "subtype", "supertype", "expect"]);
            let expect = v["expect"].as_bool().ok_or("expect")?;
            let (a, s) = checked_type(&v["subtype"])?;
            let (b, t) = checked_type(&v["supertype"])?;
            let got = candid_types::is_subtype(a.root(s).unwrap(), b.root(t).unwrap());
            agree(got == expect, || {
                format!("subtype is {got}, expected {expect}")
            })?;
            Ok("subtype")
        }
        "coerce" => {
            let v = obj(vector, &["id", "kind", "value", "from", "to", "expect"]);
            well_formed_type(&v["from"])?;
            well_formed_type(&v["to"])?;
            // The value has type `from`, and an expected value has type `to`.
            written_at(&v["from"], &v["value"])?;
            if v["expect"] != "reject" {
                written_at(&v["to"], &obj(&v["expect"], &["value"])["value"])?;
            }
            Ok("coerce (values written)")
        }
        "decode" => {
            let v = obj(vector, &["id", "kind", "bytes", "types", "expect"]);
            let types = obj(&v["types"], &["table", "roots"]);
            let roots = types["roots"].as_array().ok_or("roots")?;
            well_formed_types(&types["table"], roots.iter())?;
            let bytes = hex(v["bytes"].as_str().ok_or("bytes")?)?;
            let header = candid_binary::Decoder::new(&bytes);
            if v["expect"] == "reject" {
                return Ok(if header.is_err() {
                    "decode (rejected by the header)"
                } else {
                    "decode (rejected, header accepted)"
                });
            }
            let header = header.map_err(|e| format!("the header is rejected: {e}"))?;
            if v["expect"] == "costly" {
                return Ok("decode (costly; header)");
            }
            let values = read_values(&obj(&v["expect"], &["values"])["values"])?;
            let receiver = read_header(&v["types"])?;
            let written = write(receiver.clone(), &values)
                .map_err(|e| format!("the expected values cannot be written: {e}"))?;
            // Where the receiver's header is the message's, nothing was coerced, and the
            // values give back the bytes -- unless the message has a future type, whose
            // value is skipped, or is not in shortest form.
            if *header.header() != receiver || has_future(receiver.table()) {
                return Ok("decode (header; values written)");
            }
            if written != bytes {
                agree(NOT_SHORTEST.contains(&v["id"].as_str().unwrap()), || {
                    format!("the values are written as {}", to_hex(&written))
                })?;
                return Ok("decode (not in shortest form)");
            }
            Ok("decode (values give back the bytes)")
        }
        "parse" => {
            let v = obj(vector, &["id", "kind", "text", "types", "expect"]);
            let types = obj(&v["types"], &["table", "roots"]);
            let roots = types["roots"].as_array().ok_or("roots")?;
            well_formed_types(&types["table"], roots.iter())?;
            if v["expect"] != "reject" {
                let values = read_values(&obj(&v["expect"], &["values"])["values"])?;
                write(read_header(&v["types"])?, &values)
                    .map_err(|e| format!("the expected values cannot be written: {e}"))?;
            }
            Ok("parse (values written)")
        }
        "did" => {
            let keys: &[&str] = if vector.get("files").is_some() {
                &["id", "kind", "text", "files", "expect"]
            } else {
                &["id", "kind", "text", "expect"]
            };
            let v = obj(vector, keys);
            if v["expect"] == "reject" {
                return Ok("did (types only)");
            }
            let expect = obj(&v["expect"], &["interface"]);
            let iface = obj(&expect["interface"], &["table", "types", "service"]);
            let mut roots: Vec<&Value> = Vec::new();
            for pair in iface["types"].as_array().ok_or("types")? {
                roots.push(&pair.as_array().ok_or("type pair")?[1]);
            }
            if !iface["service"].is_null() {
                let service = obj(&iface["service"], &["init", "type"]);
                roots.push(&service["type"]);
                if let Some(init) = service["init"].as_array() {
                    roots.extend(init);
                }
            }
            well_formed_types(&iface["table"], roots.into_iter())?;
            Ok("did (types only)")
        }
        other => Err(format!("unknown kind {other:?}")),
    }
}

/// The `decode` vectors whose message is not in shortest form, so that writing their
/// values gives other bytes. Each is listed by hand, from its id, so that a writer that
/// gets a value wrong is not excused by a list built from what it writes.
const NOT_SHORTEST: &[&str] = &[
    "decode: nat with redundant continuation bytes",
    "decode: a type reference with redundant continuation bytes",
    "decode: an entry's opcode with redundant continuation bytes",
    "decode: a vector length with redundant continuation bytes",
    "decode: a vector length of zero in ten bytes",
    "prim.test.did: overlong typ table length",
    "prim.test.did: overlong arg length",
    "prim.test.did: nat: leb overlong #33",
    "prim.test.did: nat: leb overlong #34",
    "prim.test.did: int: leb overlong (0s)",
    "prim.test.did: int: leb overlong (1s)",
    "prim.test.did: text: overlong length leb",
];

/// Write `values` in a message with `header`.
fn write(header: Header, values: &[candid_value::Value]) -> Result<Vec<u8>, String> {
    let mut encoder = Encoder::new(header);
    for v in values {
        let writer = encoder.argument().map_err(|e| e.to_string())?;
        v.encode(writer).map_err(|e| e.to_string())?;
    }
    encoder.finish().map_err(|e| e.to_string())
}

/// Write a `<value>` at a `<type>`: it must have the type.
fn written_at(t: &Value, value: &Value) -> Result<(), String> {
    let (table, root) = checked_type(t)?;
    let header = Header::new(table, vec![root]).map_err(|e| e.to_string())?;
    write(header, &[read_value(value)?])
        .map(drop)
        .map_err(|e| format!("{value} cannot be written: {e}"))
}

fn has_future(table: &TypeTable) -> bool {
    table
        .entries()
        .iter()
        .any(|e| matches!(e, Composite::Future { .. }))
}

/// A `<types>`, as a header.
fn read_header(types: &Value) -> Result<Header, String> {
    let types = obj(types, &["table", "roots"]);
    let table = read_table(&types["table"])?
        .check()
        .map_err(|e| e.to_string())?;
    let roots = read_slots(&types["roots"])?;
    Header::new(table, roots).map_err(|e| e.to_string())
}

fn read_values(v: &Value) -> Result<Vec<candid_value::Value>, String> {
    v.as_array()
        .ok_or("values")?
        .iter()
        .map(read_value)
        .collect()
}

/// A `<value>`.
fn read_value(v: &Value) -> Result<candid_value::Value, String> {
    use candid_value::Value as V;
    let o = match v {
        Value::Null => return Ok(V::Null),
        Value::Bool(b) => return Ok(V::Bool(*b)),
        Value::Object(o) => o,
        _ => return Err(format!("not a value: {v}")),
    };
    let [(key, v)] = o.iter().collect::<Vec<_>>()[..] else {
        return Err(format!("a value with more than one key: {v}"));
    };
    let text = || v.as_str().ok_or_else(|| format!("{key} is not a string"));
    fn number<T: std::str::FromStr>(s: &str) -> Result<T, String> {
        s.parse()
            .map_err(|_| format!("not a number in range: {s:?}"))
    }
    fn principal(v: &Value) -> Result<Principal, String> {
        let bytes = hex(v.as_str().ok_or("principal")?)?;
        if bytes.len() > 29 {
            return Err("a principal of more than 29 bytes".into());
        }
        Ok(Principal::from_slice(&bytes))
    }
    Ok(match key.as_str() {
        "nat" => V::Nat(number::<Nat>(text()?)?),
        "int" => V::Int(number::<Int>(text()?)?),
        "nat8" => V::Nat8(number(text()?)?),
        "nat16" => V::Nat16(number(text()?)?),
        "nat32" => V::Nat32(number(text()?)?),
        "nat64" => V::Nat64(number(text()?)?),
        "int8" => V::Int8(number(text()?)?),
        "int16" => V::Int16(number(text()?)?),
        "int32" => V::Int32(number(text()?)?),
        "int64" => V::Int64(number(text()?)?),
        "float32" => V::Float32(Float32::from_bits(
            u32::from_str_radix(text()?, 16).map_err(|e| e.to_string())?,
        )),
        "float64" => V::Float64(Float64::from_bits(
            u64::from_str_radix(text()?, 16).map_err(|e| e.to_string())?,
        )),
        "text" => V::Text(text()?.to_string()),
        "opt" => V::Opt(Box::new(read_value(v)?)),
        "vec" => V::Vec(read_values(v)?),
        "record" => {
            let fields = v
                .as_array()
                .ok_or("record")?
                .iter()
                .map(|f| {
                    let [id, value] = f.as_array().ok_or("field")?.as_slice() else {
                        return Err("field is not a pair".to_string());
                    };
                    Ok((field_id(id)?, read_value(value)?))
                })
                .collect::<Result<Vec<_>, String>>()?;
            // The format promises ascending ids; a record that would need sorting is not
            // in the format.
            agree(fields.windows(2).all(|w| w[0].0 < w[1].0), || {
                "record fields not in ascending id".to_string()
            })?;
            V::Record(Record::from_fields(fields).map_err(|e| e.to_string())?)
        }
        "variant" => {
            let [id, value] = v.as_array().ok_or("variant")?.as_slice() else {
                return Err("variant is not a pair".into());
            };
            V::Variant(field_id(id)?, Box::new(read_value(value)?))
        }
        "principal" => V::Principal(principal(v)?),
        "service" => V::Service(principal(v)?),
        "func" => {
            let [service, method] = v.as_array().ok_or("func")?.as_slice() else {
                return Err("func is not a pair".into());
            };
            V::Func(
                principal(service)?,
                method.as_str().ok_or("method")?.to_string(),
            )
        }
        other => return Err(format!("unknown value {other:?}")),
    })
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn agree(ok: bool, why: impl FnOnce() -> String) -> Result<(), String> {
    if ok { Ok(()) } else { Err(why()) }
}

/// A `<type>` the format promises is well formed, checked, with its root.
fn checked_type(t: &Value) -> Result<(TypeTable, Slot), String> {
    well_formed_type(t)?;
    let (raw, root) = read_type(t)?;
    Ok((raw.check().unwrap(), root))
}

/// A `<type>` the format promises is well formed.
fn well_formed_type(t: &Value) -> Result<(), String> {
    let t = obj(t, &["table", "root"]);
    well_formed_types(&t["table"], std::iter::once(&t["root"]))
}

/// A table and roots in it, which the format promises are well formed.
fn well_formed_types<'a>(
    table: &Value,
    roots: impl Iterator<Item = &'a Value>,
) -> Result<(), String> {
    let table = read_table(table)?
        .check()
        .map_err(|e| format!("a promised-well-formed table is rejected: {e}"))?;
    for root in roots {
        let root = read_slot(root)?;
        agree(table.root(root).is_some(), || {
            format!("a promised root {root:?} does not resolve")
        })?;
    }
    table_roundtrip(table)
}

/// Write a table in a message and read it back: the same table.
fn table_roundtrip(table: TypeTable) -> Result<(), String> {
    let header = candid_binary::Header::new(table, Vec::new()).map_err(|e| e.to_string())?;
    let bytes = candid_binary::Encoder::new(header.clone())
        .finish()
        .map_err(|e| format!("a message cannot be finished: {e}"))?;
    let decoder = candid_binary::Decoder::new(&bytes)
        .map_err(|e| format!("a written table is rejected: {e}"))?;
    agree(
        decoder.header() == &header && decoder.position() == bytes.len(),
        || "a written table reads back differently".to_string(),
    )
}

fn read_type(t: &Value) -> Result<(RawTypeTable, Slot), String> {
    let t = obj(t, &["table", "root"]);
    Ok((read_table(&t["table"])?, read_slot(&t["root"])?))
}

fn read_table(t: &Value) -> Result<RawTypeTable, String> {
    let entries = t.as_array().ok_or("table is not an array")?;
    Ok(RawTypeTable::from_entries(
        entries.iter().map(read_entry).collect::<Result<_, _>>()?,
    ))
}

fn read_slot(s: &Value) -> Result<Slot, String> {
    match s {
        Value::String(name) => Primitive::from_name(name)
            .map(Slot::Primitive)
            .ok_or_else(|| format!("unknown primitive {name:?}")),
        Value::Number(n) => {
            let index = n.as_u64().ok_or("slot index")?;
            Ok(Slot::Ref(TypeRef::new(usize::try_from(index).unwrap())))
        }
        _ => Err(format!("not a slot: {s}")),
    }
}

fn read_slots(v: &Value) -> Result<Vec<Slot>, String> {
    v.as_array().ok_or("slots")?.iter().map(read_slot).collect()
}

fn read_entry(e: &Value) -> Result<Composite, String> {
    let e = e.as_object().ok_or("entry is not an object")?;
    let [(key, v)] = e.iter().collect::<Vec<_>>()[..] else {
        return Err("entry has more than one key".into());
    };
    Ok(match key.as_str() {
        "opt" => Composite::Opt(read_slot(v)?),
        "vec" => Composite::Vec(read_slot(v)?),
        "record" => Composite::Record(read_labelled(v)?),
        "variant" => Composite::Variant(read_labelled(v)?),
        "func" => {
            let f = obj(v, &["parameters", "results", "annotations"]);
            let annotations = f["annotations"]
                .as_array()
                .ok_or("annotations")?
                .iter()
                .map(|a| match a.as_str() {
                    Some("query") => Ok(Annotation::Query),
                    Some("oneway") => Ok(Annotation::Oneway),
                    Some("composite_query") => Ok(Annotation::CompositeQuery),
                    _ => Err(format!("unknown annotation {a}")),
                })
                .collect::<Result<_, _>>()?;
            Composite::Func {
                parameters: read_slots(&f["parameters"])?,
                results: read_slots(&f["results"])?,
                annotations,
            }
        }
        "service" => Composite::Service(
            v.as_array()
                .ok_or("service")?
                .iter()
                .map(|m| {
                    let [name, slot] = m.as_array().ok_or("method")?.as_slice() else {
                        return Err("method is not a pair".to_string());
                    };
                    Ok((
                        name.as_str().ok_or("method name")?.to_string(),
                        read_slot(slot)?,
                    ))
                })
                .collect::<Result<_, _>>()?,
        ),
        "future" => {
            let [opcode, data] = v.as_array().ok_or("future")?.as_slice() else {
                return Err("future is not a pair".into());
            };
            Composite::Future {
                opcode: opcode.as_i64().ok_or("future opcode")?,
                data: hex(data.as_str().ok_or("future data")?)?,
            }
        }
        other => return Err(format!("unknown entry {other:?}")),
    })
}

fn read_labelled(v: &Value) -> Result<Vec<(FieldId, Slot)>, String> {
    v.as_array()
        .ok_or("fields")?
        .iter()
        .map(|f| {
            let [id, slot] = f.as_array().ok_or("field")?.as_slice() else {
                return Err("field is not a pair".to_string());
            };
            Ok((field_id(id)?, read_slot(slot)?))
        })
        .collect()
}

fn field_id(v: &Value) -> Result<FieldId, String> {
    let n = v.as_u64().ok_or("field id")?;
    Ok(FieldId::new(
        u32::try_from(n).map_err(|_| "field id past u32")?,
    ))
}

fn hex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd-length hex".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

/// An object with exactly these keys.
fn obj<'a>(v: &'a Value, keys: &[&str]) -> &'a Json {
    let o = v
        .as_object()
        .unwrap_or_else(|| panic!("not an object: {v}"));
    let mut got: Vec<&str> = o.keys().map(String::as_str).collect();
    let mut want = keys.to_vec();
    got.sort_unstable();
    want.sort_unstable();
    assert_eq!(got, want, "unexpected keys in {v}");
    o
}
