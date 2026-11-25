//! The conformance vectors, asked of the crates in this workspace.
//!
//! - `candid_types` answers `hash`, `wellformed` and `subtype`. Every other vector
//!   carries types too, and the format promises they are well formed
//!   (`conformance/README.md`), so each of those tables is checked as well: thousands of
//!   tables the model accepts, which `RawTypeTable::check` must accept too.
//! - `candid_binary` reads messages at the receiver's types, and writes them. Every
//!   `decode` vector is read at its types, within the values the oracle decodes before it
//!   calls a message costly: an accepted one must give its values, a rejected one must be
//!   rejected -- not for a resource limit -- and a costly one must run into the limit.
//!   Every table above is written in a message with no arguments and read back, which
//!   must give the same table.
//! - Coercion is decoding: each `coerce` vector's value is written at `from` and read at
//!   `to`, which must give the vector's answer. And then in context
//!   ([`in_context`]): twice as arguments, in a vector, in a record, and under an `opt`,
//!   where after a value that fails there is more to read.
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

use candid_binary::{DecodeError, Decoder, Encode, Encoder, Header, Limits};
use candid_types::{Composite, FieldId, Primitive, RawTypeTable, Slot, TypeRef, TypeTable};
use serde_json::Value;

mod common;

use common::*;

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
        "decode (costly)",
        "decode (rejected by the header)",
        "decode (rejected for its values)",
        "decode (rejected: a value does not coerce)",
        "decode (values read; values written)",
        "decode (values read; values give back the bytes)",
        "decode (not in shortest form)",
        "coerce (values written, and read at to, alone and in context)",
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
            let bytes = written_at(&v["from"], &v["value"])?;
            let want = if v["expect"] == "reject" {
                None
            } else {
                let value = &obj(&v["expect"], &["value"])["value"];
                written_at(&v["to"], value)?;
                Some(vec![read_value(value)?])
            };
            // Coercion is decoding: the value, written at `from` and read at `to`.
            let (table, root) = checked_type(&v["to"])?;
            let receiver = Header::new(table, vec![root]).map_err(|e| e.to_string())?;
            // A rejection is a failure or an error, such as an undefined coercion -- but not a
            // resource limit, which is no answer.
            let got = match decode_at(&bytes, &receiver) {
                Ok(got) => got,
                Err(e) if !e.rejection().is_resource_limit() => None,
                Err(e) => return Err(format!("written at from and read at to: {e}")),
            };
            agree(got == want, || {
                format!("written at from and read at to: {got:?}")
            })?;
            in_context(
                &v["from"],
                &v["to"],
                &read_value(&v["value"])?,
                want.map(|mut w| w.remove(0)),
            )?;
            Ok("coerce (values written, and read at to, alone and in context)")
        }
        "decode" => {
            let v = obj(vector, &["id", "kind", "bytes", "types", "expect"]);
            let types = obj(&v["types"], &["table", "roots"]);
            let roots = types["roots"].as_array().ok_or("roots")?;
            well_formed_types(&types["table"], roots.iter())?;
            let bytes = hex(v["bytes"].as_str().ok_or("bytes")?)?;
            let header = candid_binary::Decoder::new(&bytes);
            let receiver = read_header(&v["types"])?;
            let got = decode_at(&bytes, &receiver);
            if v["expect"] == "reject" {
                return match got {
                    Ok(None) => Ok("decode (rejected: a value does not coerce)"),
                    Err(e) if !e.rejection().is_resource_limit() => Ok(if header.is_err() {
                        "decode (rejected by the header)"
                    } else {
                        "decode (rejected for its values)"
                    }),
                    Err(e) => Err(format!("rejected for a resource limit: {e}")),
                    Ok(Some(vs)) => Err(format!("accepted, as {vs:?}")),
                };
            }
            let header = header.map_err(|e| format!("the header is rejected: {e}"))?;
            if v["expect"] == "costly" {
                return match got {
                    Err(e) if e.rejection().is_resource_limit() => Ok("decode (costly)"),
                    other => Err(format!("costly, but not past the limit: {other:?}")),
                };
            }
            let values = read_values(&obj(&v["expect"], &["values"])["values"])?;
            match got {
                Ok(Some(got)) => agree(got == values, || format!("decoded as {got:?}"))?,
                Ok(None) => return Err("a value does not coerce".into()),
                Err(e) => return Err(format!("rejected: {e}")),
            }
            let written = write(receiver.clone(), &values)
                .map_err(|e| format!("the expected values cannot be written: {e}"))?;
            // Where the receiver's header is the message's, nothing was coerced, and the
            // values give back the bytes -- unless the message has a future type, whose
            // value is skipped, or is not in shortest form.
            if *header.header() != receiver || has_future(receiver.table()) {
                return Ok("decode (values read; values written)");
            }
            if written != bytes {
                agree(NOT_SHORTEST.contains(&v["id"].as_str().unwrap()), || {
                    format!("the values are written as {}", to_hex(&written))
                })?;
                return Ok("decode (not in shortest form)");
            }
            Ok("decode (values read; values give back the bytes)")
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
fn written_at(t: &Value, value: &Value) -> Result<Vec<u8>, String> {
    let (table, root) = checked_type(t)?;
    let header = Header::new(table, vec![root]).map_err(|e| e.to_string())?;
    write(header, &[read_value(value)?]).map_err(|e| format!("{value} cannot be written: {e}"))
}

/// A `coerce` vector's value `v : a`, which coerces to `want : b` or fails, put where a
/// decoder has to go on after it: twice as arguments, twice in a vector, as two fields of
/// a record, and those under an `opt`, where a failure is `null`. What each is read as
/// follows from the vector's answer by the coercion rules, and every byte must be read:
/// the second `v` after the first fails, and the ones the receiver does not expect.
fn in_context(
    from: &Value,
    to: &Value,
    v: &candid_value::Value,
    want: Option<candid_value::Value>,
) -> Result<(), String> {
    use candid_value::{Record, Value as V};
    let (a, t) = checked_type(from)?;
    let (b, u) = checked_type(to)?;
    let (n, m) = (a.len(), b.len());
    let r = |i| Slot::Ref(TypeRef::new(i));
    let pair =
        |i: u32, j: u32, s| Composite::Record(vec![(FieldId::new(i), s), (FieldId::new(j), s)]);
    let extend = |table: &TypeTable, more: Vec<Composite>| {
        let mut entries = table.entries().to_vec();
        entries.extend(more);
        RawTypeTable::from_entries(entries)
            .check()
            .map_err(|e| e.to_string())
    };
    let a = extend(&a, vec![Composite::Vec(t), pair(0, 1, t)])?;
    let b = extend(
        &b,
        vec![
            Composite::Vec(u),
            pair(0, 1, u),
            pair(1, 2, u),
            pair(0, 2, u),
            Composite::Opt(r(m)),
            Composite::Opt(r(m + 1)),
        ],
    )?;
    let header = |types| Header::new(a.clone(), types).map_err(|e| e.to_string());
    let arguments = write(header(vec![t, t])?, &[v.clone(), v.clone()])?;
    let vector = write(header(vec![r(n)])?, &[V::Vec(vec![v.clone(), v.clone()])])?;
    let sent = Record::from_fields([(FieldId::new(0), v.clone()), (FieldId::new(1), v.clone())])
        .map_err(|e| e.to_string())?;
    let record = write(header(vec![r(n + 1)])?, &[V::Record(sent)])?;

    // The receiver's field 2, which the record lacks: `null` if `b` accepts it.
    let accepts_null = match u {
        Slot::Primitive(p) => matches!(p, Primitive::Null | Primitive::Reserved),
        Slot::Ref(i) => matches!(b.lookup(i), Some(Composite::Opt(_))),
    };
    let missing = accepts_null.then_some(V::Null);
    let w = want;
    let record_of = |fs: Vec<(u32, Option<V>)>| -> Option<V> {
        let fs = fs
            .into_iter()
            .map(|(i, x)| x.map(|x| (FieldId::new(i), x)))
            .collect::<Option<Vec<_>>>()?;
        Record::from_fields(fs).ok().map(V::Record)
    };
    let vec_of = w.clone().map(|w| V::Vec(vec![w.clone(), w]));
    let rec01 = record_of(vec![(0, w.clone()), (1, w.clone())]);
    // Under an `opt` a failure is `null`, but an undefined coercion is not: the vector's
    // "reject" is either, and it can be undefined only if an infinite option is reachable
    // from `b`. Then the answer is not known, and the case is not asked.
    let undefined_possible = reaches_infinite_option(&b, u);
    let under_opt = |x: Option<V>| match x {
        Some(x) => Some(Some(V::Opt(Box::new(x)))),
        None if undefined_possible => None,
        None => Some(Some(V::Null)),
    };
    /// What is read, the bytes, the receiver's types, and the answer if it is known.
    type Case<'b> = (&'static str, &'b [u8], Vec<Slot>, Option<Option<V>>);
    let cases: Vec<Case<'_>> = vec![
        (
            "(v, v) at (b, b)",
            &arguments,
            vec![u, u],
            Some(w.clone().map(|w| V::Vec(vec![w.clone(), w]))),
        ),
        ("(v, v) at (b)", &arguments, vec![u], Some(w.clone())),
        (
            "(v, v) at ()",
            &arguments,
            vec![],
            Some(Some(V::Vec(vec![]))),
        ),
        (
            "vec {v; v} at vec b",
            &vector,
            vec![r(m)],
            Some(vec_of.clone()),
        ),
        (
            "record {0 = v; 1 = v} at record {0 : b; 1 : b}",
            &record,
            vec![r(m + 1)],
            Some(rec01.clone()),
        ),
        (
            "record {0 = v; 1 = v} at record {1 : b; 2 : b}",
            &record,
            vec![r(m + 2)],
            Some(record_of(vec![(1, w.clone()), (2, missing.clone())])),
        ),
        (
            "record {0 = v; 1 = v} at record {0 : b; 2 : b}",
            &record,
            vec![r(m + 3)],
            Some(record_of(vec![(0, w.clone()), (2, missing)])),
        ),
        (
            "vec {v; v} at opt vec b",
            &vector,
            vec![r(m + 4)],
            under_opt(vec_of),
        ),
        (
            "record {0 = v; 1 = v} at opt record {0 : b; 1 : b}",
            &record,
            vec![r(m + 5)],
            under_opt(rec01),
        ),
    ];
    for (what, bytes, types, want) in cases {
        // `None`: not asked. Otherwise the values, as one `vec` for several arguments.
        let Some(want) = want else { continue };
        let want = match (types.len(), want) {
            (1, w) => w.map(|w| vec![w]),
            (_, Some(V::Vec(ws))) => Some(ws),
            (_, w) => w.map(|w| vec![w]),
        };
        let receiver = Header::new(b.clone(), types).map_err(|e| e.to_string())?;
        let got = match decode_at(bytes, &receiver) {
            Ok(got) => got,
            Err(e) if !e.rejection().is_resource_limit() => None,
            Err(e) => return Err(format!("{what}: {e}")),
        };
        agree(got == want, || {
            format!("{what}: got {got:?}, want {want:?}")
        })?;
    }
    Ok(())
}

/// Whether an infinite option, such as `type R = opt R`, is reachable from `root`.
fn reaches_infinite_option(table: &TypeTable, root: Slot) -> bool {
    let infinite = |mut s: Slot| {
        for _ in 0..=table.len() {
            match s {
                Slot::Ref(r) => match table.lookup(r) {
                    Some(Composite::Opt(inner)) => s = *inner,
                    _ => return false,
                },
                Slot::Primitive(_) => return false,
            }
        }
        true
    };
    let mut seen = std::collections::BTreeSet::new();
    let mut work = vec![root];
    while let Some(s) = work.pop() {
        if infinite(s) {
            return true;
        }
        if let Slot::Ref(r) = s {
            if seen.insert(r) {
                work.extend(table.lookup(r).into_iter().flat_map(|c| c.slots()));
            }
        }
    }
    false
}

/// Read a message at the receiver's types, within the values the oracle decodes before
/// it calls a message costly (`costlyLimit` in `lean/Candid/Wire.lean`), which counts
/// them as `Limits::values` does. `None` if a value does not coerce.
fn decode_at(
    bytes: &[u8],
    receiver: &Header,
) -> Result<Option<Vec<candid_value::Value>>, DecodeError> {
    let mut limits = Limits::default();
    limits.values = 10_000;
    let mut decoder = Decoder::with_limits(bytes, limits)?;
    let mut values = Vec::new();
    for &t in receiver.types() {
        let expected = receiver.table().root(t).expect("a header's types resolve");
        match decoder.argument(expected)? {
            Some(v) => values.push(v),
            None => {
                decoder.finish()?;
                return Ok(None);
            }
        }
    }
    decoder.finish()?;
    Ok(Some(values))
}

fn has_future(table: &TypeTable) -> bool {
    table
        .entries()
        .iter()
        .any(|e| matches!(e, Composite::Future { .. }))
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
