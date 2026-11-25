//! Reading the conformance format: what `tests/vectors.rs` and `tests/differential.rs`
//! share. Each test compiles its own copy, and uses only some of it.

#![allow(dead_code)]

use candid_binary::Header;
use candid_types::{Annotation, Composite, FieldId, Primitive, RawTypeTable, Slot, TypeRef};
use candid_value::{Float32, Float64, Int, Nat, Principal, Record};
use serde_json::{Map, Value};

pub(crate) type Json = Map<String, Value>;

/// A `<types>`, as a header.
pub(crate) fn read_header(types: &Value) -> Result<Header, String> {
    let types = obj(types, &["table", "roots"]);
    let table = read_table(&types["table"])?
        .check()
        .map_err(|e| e.to_string())?;
    let roots = read_slots(&types["roots"])?;
    Header::new(table, roots).map_err(|e| e.to_string())
}

pub(crate) fn read_values(v: &Value) -> Result<Vec<candid_value::Value>, String> {
    v.as_array()
        .ok_or("values")?
        .iter()
        .map(read_value)
        .collect()
}

/// A `<value>`.
pub(crate) fn read_value(v: &Value) -> Result<candid_value::Value, String> {
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

pub(crate) fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

pub(crate) fn agree(ok: bool, why: impl FnOnce() -> String) -> Result<(), String> {
    if ok { Ok(()) } else { Err(why()) }
}

pub(crate) fn read_type(t: &Value) -> Result<(RawTypeTable, Slot), String> {
    let t = obj(t, &["table", "root"]);
    Ok((read_table(&t["table"])?, read_slot(&t["root"])?))
}

pub(crate) fn read_table(t: &Value) -> Result<RawTypeTable, String> {
    let entries = t.as_array().ok_or("table is not an array")?;
    Ok(RawTypeTable::from_entries(
        entries.iter().map(read_entry).collect::<Result<_, _>>()?,
    ))
}

pub(crate) fn read_slot(s: &Value) -> Result<Slot, String> {
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

pub(crate) fn read_slots(v: &Value) -> Result<Vec<Slot>, String> {
    v.as_array().ok_or("slots")?.iter().map(read_slot).collect()
}

pub(crate) fn read_entry(e: &Value) -> Result<Composite, String> {
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

pub(crate) fn read_labelled(v: &Value) -> Result<Vec<(FieldId, Slot)>, String> {
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

pub(crate) fn field_id(v: &Value) -> Result<FieldId, String> {
    let n = v.as_u64().ok_or("field id")?;
    Ok(FieldId::new(
        u32::try_from(n).map_err(|_| "field id past u32")?,
    ))
}

pub(crate) fn hex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd-length hex".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

/// An object with exactly these keys.
pub(crate) fn obj<'a>(v: &'a Value, keys: &[&str]) -> &'a Json {
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
