//! The conformance vectors, asked of the crates in this workspace.
//!
//! - `candid_types` answers `hash`, `wellformed` and `subtype`. Every other vector
//!   carries types too, and the format promises they are well formed
//!   (`conformance/README.md`), so each of those tables is checked as well: thousands of
//!   tables the model accepts, which `RawTypeTable::check` must accept too.
//! - `candid_binary` reads message headers so far. Every message a `decode` vector
//!   accepts, or calls costly, has a header it must accept; a message the vector rejects
//!   may be rejected for its header or for its values, so only the count of those whose
//!   header is already rejected is reported. And every table above is encoded as a
//!   header and read back, which must give the same table.
//!
//! Like a runner, this reads strictly: an unknown key, kind or name is an error, never
//! skipped.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use candid_types::{
    Annotation, Composite, FieldId, Primitive, RawTypeTable, Slot, TypeRef, TypeTable,
};
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
        "decode (header)",
        "decode (rejected by the header)",
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
            Ok("coerce (types only)")
        }
        "decode" => {
            let v = obj(vector, &["id", "kind", "bytes", "types", "expect"]);
            let types = obj(&v["types"], &["table", "roots"]);
            let roots = types["roots"].as_array().ok_or("roots")?;
            well_formed_types(&types["table"], roots.iter())?;
            let bytes = hex(v["bytes"].as_str().ok_or("bytes")?)?;
            let header = candid_binary::Header::decode(&bytes);
            if v["expect"] == "reject" {
                return Ok(if header.is_err() {
                    "decode (rejected by the header)"
                } else {
                    "decode (rejected, header accepted)"
                });
            }
            header.map_err(|e| format!("the header is rejected: {e}"))?;
            Ok("decode (header)")
        }
        "parse" => {
            let v = obj(vector, &["id", "kind", "text", "types", "expect"]);
            let types = obj(&v["types"], &["table", "roots"]);
            let roots = types["roots"].as_array().ok_or("roots")?;
            well_formed_types(&types["table"], roots.iter())?;
            Ok("parse (types only)")
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
    let mut slots = Vec::new();
    for root in roots {
        let root = read_slot(root)?;
        agree(table.root(root).is_some(), || {
            format!("a promised root {root:?} does not resolve")
        })?;
        slots.push(root);
    }
    header_roundtrip(table, slots)
}

/// Encode a table and roots as a header, and read it back: the same table, with each
/// entry's fields and methods in the order the format writes them, and the same roots.
fn header_roundtrip(table: TypeTable, roots: Vec<Slot>) -> Result<(), String> {
    let expected: Vec<Composite> = table.entries().iter().map(written_order).collect();
    let header = candid_binary::Header::new(table, roots).ok_or("a root does not resolve")?;
    let mut bytes = Vec::new();
    header.encode(&mut bytes);
    let (back, rest) = candid_binary::Header::decode(&bytes)
        .map_err(|e| format!("an encoded header is rejected: {e}"))?;
    agree(
        rest.is_empty() && back.types() == header.types() && back.table().entries() == expected,
        || "an encoded header reads back differently".to_string(),
    )
}

/// An entry with its fields in order of id and its methods in order of name.
fn written_order(entry: &Composite) -> Composite {
    let mut entry = entry.clone();
    match &mut entry {
        Composite::Record(fs) | Composite::Variant(fs) => fs.sort_unstable_by_key(|f| f.0),
        Composite::Service(ms) => ms.sort_unstable_by(|a, b| a.0.cmp(&b.0)),
        _ => {}
    }
    entry
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
