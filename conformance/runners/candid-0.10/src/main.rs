//! Runs conformance vectors against `candid` 0.10, the implementation in `rust/`.
//!
//! ```text
//! cargo run --release -- ../../vectors/*.json
//! ```
//!
//! The vectors are the Lean model's answers (`lean/`), so a disagreement means the two
//! differ -- not, by itself, which one is wrong. Each disagreement that has been looked
//! at and is understood goes in `KNOWN`, with the reason. Those are reported but do not
//! fail the run. One that starts agreeing *does* fail it, so a fix in either place
//! cannot land without its entry being removed.
//!
//! This is a bridge, not a second reader: it translates each vector into `candid`'s own
//! types and values and asks `candid`. Whether a vector is valid -- well-formed types, a
//! value of its type -- is the reference reader's to say (`lake exe oracle check`, which
//! CI runs on the same files). A vector this runner cannot translate fails the run.
//!
//! This calls `candid` 0.10's public API only, and it never modifies `rust/`.

use candid::types::subtype::{subtype_with_config, Gamma, OptReport};
use candid::types::value::{IDLField, VariantValue};
use candid::types::{Field, FuncMode, Function, Label, Type, TypeEnv, TypeInner};
use candid::{IDLArgs, IDLValue, Principal};
use serde_json::Value;
use std::collections::BTreeSet;
use std::process::ExitCode;
use std::str::FromStr;

/// Vectors on which `candid` 0.10 is known to disagree with the model: `(id, why)`.
const KNOWN: &[(&str, &str)] = &[
    (
        "annotations agree up to reordering",
        "`subtype.rs` compares `Function::modes` as a `Vec`, so `query composite_query` \
         and `composite_query query` differ; the spec identifies annotation lists up to \
         reordering, and the `.did` grammar accepts `FuncMode*`",
    ),
    (
        "decode: a function type with two annotations",
        "`binary_parser.rs` asserts that a function type has at most one annotation; the \
         spec's `T(func ...)` writes `T*(<funcann>*)`, any number",
    ),
    (
        "decode: oneway function with a result",
        "`binary_parser.rs` does not check a decoded function type, so it accepts a \
         `oneway` function with results; the spec says that result list must be empty",
    ),
    (
        "decode: a principal of 30 bytes",
        "0.10 bounds a principal at 29 bytes, the Internet Computer's limit, in both its \
         decoder and `Principal`; the spec bounds neither",
    ),
];

/// The vector format version this runner reads.
const FORMAT_VERSION: u64 = 0;

const SKIP_WELLFORMED: &str =
    "candid 0.10 has no public function that checks a type table on its own";

type Result<T> = std::result::Result<T, String>;

enum Outcome {
    Agree,
    Disagree(String),
    /// The vector asks something this runner has no way to put to `candid` 0.10.
    Skip,
}

fn main() -> ExitCode {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        eprintln!("usage: conformance-candid-0-10 <vector file>...");
        return ExitCode::from(2);
    }
    let known: BTreeSet<&str> = KNOWN.iter().map(|(id, _)| *id).collect();
    let mut ids = BTreeSet::new();
    let (mut agree, mut skipped, mut known_hits, mut failed) = (0, 0, 0, 0);

    for path in &paths {
        let vectors = match read_file(path) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("{path}: {e}");
                return ExitCode::FAILURE;
            }
        };
        for (i, v) in vectors.iter().enumerate() {
            let id = v["id"].as_str().unwrap_or("").to_string();
            match (run(v), known.contains(id.as_str())) {
                (Err(e), _) => {
                    println!("FAIL  {path}: vector {i} ({id}) cannot be run -- {e}");
                    failed += 1;
                }
                (Ok(Outcome::Skip), _) => skipped += 1,
                (Ok(Outcome::Agree), false) => agree += 1,
                (Ok(Outcome::Agree), true) => {
                    println!("FAIL  {id} -- listed in KNOWN but now agrees; remove it");
                    failed += 1;
                }
                (Ok(Outcome::Disagree(d)), true) => {
                    println!("known {id} -- {d}");
                    known_hits += 1;
                }
                (Ok(Outcome::Disagree(d)), false) => {
                    println!("FAIL  {id} -- {d}");
                    failed += 1;
                }
            }
            ids.insert(id);
        }
    }
    for (id, _) in KNOWN {
        if !ids.contains(*id) {
            println!("FAIL  {id} -- listed in KNOWN but no vector has this id");
            failed += 1;
        }
    }

    println!();
    println!("{agree} agree, {known_hits} known divergences, {skipped} skipped, {failed} failed");
    if skipped > 0 {
        println!("skipped: wellformed vectors -- {SKIP_WELLFORMED}");
    }
    if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn read_file(path: &str) -> Result<Vec<Value>> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let file: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    if file["version"].as_u64() != Some(FORMAT_VERSION) {
        return Err(format!(
            "vector format version {}; this runner reads {FORMAT_VERSION}",
            file["version"]
        ));
    }
    Ok(array(&file["vectors"])?.clone())
}

// ---------------------------------------------------------------------------
//  Asking candid 0.10
// ---------------------------------------------------------------------------

fn run(v: &Value) -> Result<Outcome> {
    match string(&v["kind"])? {
        "hash" => {
            let got = candid::idl_hash(string(&v["name"])?);
            let want = field_id(&v["expect"])?;
            Ok(agreement(got == want, || format!("got {got}, want {want}")))
        }
        "wellformed" => Ok(Outcome::Skip),
        "subtype" => {
            // `candid` 0.10 takes one environment for both types, so the two tables
            // go into one, each under its own prefix. This is the merge every caller
            // of `subtype` does today.
            let mut env = TypeEnv::new();
            let a = load(&v["sub"], &mut env, "A")?;
            let b = load(&v["sup"], &mut env, "B")?;
            let want = v["expect"].as_bool().ok_or("`expect` is not a boolean")?;
            // `Silence`: the special `opt` rule is part of the relation the vectors
            // assert, and the other settings report it rather than change the answer
            // -- except `Error`, which turns it into another relation.
            let got =
                subtype_with_config(OptReport::Silence, &mut Gamma::new(), &env, &a, &b).is_ok();
            Ok(agreement(got == want, || {
                format!("got {}, want {}", rel(got), rel(want))
            }))
        }
        "coerce" => coerce(v),
        "decode" => decode(v),
        k => Err(format!("unknown vector kind {k:?}")),
    }
}

/// Encode the value at `from` and decode the bytes at `to`: coercion is what a decoder
/// does, and 0.10 has no other entry point to it. Each table goes in its own
/// environment, since the encoder's and the decoder's are separate anyway.
///
/// The result is compared with the expected value by encoding both at `to`. That
/// leaves the representation to 0.10's encoder -- which `IDLValue` a `null` is at an
/// option or at `reserved`, the order of record fields, a variant's index -- and it
/// compares floats by their bits, where `IDLValue`'s `==` would find NaN unequal to
/// itself.
fn coerce(v: &Value) -> Result<Outcome> {
    let (mut a_env, mut b_env) = (TypeEnv::new(), TypeEnv::new());
    let a = load(&v["from"], &mut a_env, "A")?;
    let b = load(&v["to"], &mut b_env, "B")?;
    let encode = |val: IDLValue, env: &TypeEnv, ty: &Type| {
        IDLArgs::new(&[val]).to_bytes_with_types(env, std::slice::from_ref(ty))
    };
    let bytes = encode(value(&v["value"])?, &a_env, &a)
        .map_err(|e| format!("cannot encode the value: {e}"))?;
    let got = IDLArgs::from_bytes_with_types(&bytes, &b_env, std::slice::from_ref(&b))
        .map(|mut args| args.args.remove(0));
    let want = match &v["expect"] {
        Value::String(s) if s == "reject" => None,
        e => Some(value(&e["value"])?),
    };
    Ok(match (got, want) {
        (Err(_), None) => Outcome::Agree,
        (Err(e), Some(w)) => Outcome::Disagree(format!("rejected ({e}), want {w}")),
        (Ok(g), None) => Outcome::Disagree(format!("got {g}, want reject")),
        (Ok(g), Some(w)) => {
            let want = encode(w.clone(), &b_env, &b)
                .map_err(|e| format!("cannot encode the expected value: {e}"))?;
            let same = encode(g.clone(), &b_env, &b).is_ok_and(|got| got == want);
            agreement(same, || format!("got {g}, want {w}"))
        }
    })
}

/// Decode the bytes at the vector's types, as a receiver would. The decoded values are
/// compared with the expected ones by encoding both at those types, as for `coerce`.
fn decode(v: &Value) -> Result<Outcome> {
    let bytes = hex(&v["bytes"])?;
    let mut env = TypeEnv::new();
    let types = load_seq(&v["types"], &mut env, "B")?;
    let got = IDLArgs::from_bytes_with_types(&bytes, &env, &types).map(|args| args.args);
    // An expected value that 0.10 cannot represent is a disagreement, not a broken
    // vector: the question -- bytes and types -- translated, and what 0.10 cannot hold
    // is the answer the model gives.
    let want = match &v["expect"] {
        Value::String(s) if s == "reject" => None,
        e => match array(&e["values"])?
            .iter()
            .map(value)
            .collect::<Result<Vec<_>>>()
        {
            Ok(w) => Some(w),
            Err(err) => {
                return Ok(Outcome::Disagree(match got {
                    Ok(g) => format!("got {g:?}; the expected values are not representable: {err}"),
                    Err(e) => {
                        format!("rejected ({e}); the expected values are not representable: {err}")
                    }
                }))
            }
        },
    };
    let encode = |vals: Vec<IDLValue>| IDLArgs::new(&vals).to_bytes_with_types(&env, &types);
    Ok(match (got, want) {
        (Err(_), None) => Outcome::Agree,
        (Err(e), Some(w)) => Outcome::Disagree(format!("rejected ({e}), want {w:?}")),
        (Ok(g), None) => Outcome::Disagree(format!("got {g:?}, want reject")),
        (Ok(g), Some(w)) => {
            let want =
                encode(w.clone()).map_err(|e| format!("cannot encode the expected values: {e}"))?;
            let same = encode(g.clone()).is_ok_and(|got| got == want);
            agreement(same, || format!("got {g:?}, want {w:?}"))
        }
    })
}

fn agreement(agree: bool, detail: impl FnOnce() -> String) -> Outcome {
    if agree {
        Outcome::Agree
    } else {
        Outcome::Disagree(detail())
    }
}

fn rel(b: bool) -> &'static str {
    if b {
        "<:"
    } else {
        "!<:"
    }
}

// ---------------------------------------------------------------------------
//  Translating vectors into candid's types and values
// ---------------------------------------------------------------------------

fn array(v: &Value) -> Result<&Vec<Value>> {
    v.as_array().ok_or_else(|| format!("not an array: {v}"))
}

fn string(v: &Value) -> Result<&str> {
    v.as_str().ok_or_else(|| format!("not a string: {v}"))
}

fn field_id(v: &Value) -> Result<u32> {
    v.as_u64()
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| format!("not a 32-bit field id: {v}"))
}

/// `[a, b]`.
fn pair(v: &Value) -> Result<(&Value, &Value)> {
    match v.as_array().map(Vec::as_slice) {
        Some([a, b]) => Ok((a, b)),
        _ => Err(format!("not a pair: {v}")),
    }
}

/// An object with exactly one key, as table entries and values are written.
fn tagged(v: &Value) -> Result<(&str, &Value)> {
    match v
        .as_object()
        .map(|o| o.iter().collect::<Vec<_>>())
        .as_deref()
    {
        Some([(k, body)]) => Ok((k.as_str(), *body)),
        _ => Err(format!("not a one-key object: {v}")),
    }
}

/// A slot: a primitive's name, or a reference to entry `{prefix}{i}`.
fn slot(v: &Value, prefix: &str) -> Result<Type> {
    if let Some(i) = v.as_u64() {
        return Ok(TypeInner::Var(format!("{prefix}{i}")).into());
    }
    let t = match string(v)? {
        "null" => TypeInner::Null,
        "bool" => TypeInner::Bool,
        "nat" => TypeInner::Nat,
        "int" => TypeInner::Int,
        "nat8" => TypeInner::Nat8,
        "nat16" => TypeInner::Nat16,
        "nat32" => TypeInner::Nat32,
        "nat64" => TypeInner::Nat64,
        "int8" => TypeInner::Int8,
        "int16" => TypeInner::Int16,
        "int32" => TypeInner::Int32,
        "int64" => TypeInner::Int64,
        "float32" => TypeInner::Float32,
        "float64" => TypeInner::Float64,
        "text" => TypeInner::Text,
        "reserved" => TypeInner::Reserved,
        "empty" => TypeInner::Empty,
        "principal" => TypeInner::Principal,
        name => return Err(format!("unknown primitive type {name:?}")),
    };
    Ok(t.into())
}

/// Add a vector's type table to `env`, entry `i` named `{prefix}{i}`, and return its
/// root.
///
/// A vector lists a type's members in no particular order, but 0.10 expects them
/// sorted, as its parser leaves them: its encoder writes a type's fields in the order
/// it is given them, and its decoder rejects a header that is not sorted. So fields
/// are sorted by id and methods by name here.
fn load(fixture: &Value, env: &mut TypeEnv, prefix: &str) -> Result<Type> {
    let ty = |s: &Value| slot(s, prefix);
    let slots = |v: &Value| array(v)?.iter().map(ty).collect::<Result<Vec<_>>>();
    let fields = |v: &Value| {
        let mut fs = array(v)?
            .iter()
            .map(|f| {
                let (id, s) = pair(f)?;
                Ok(Field {
                    id: Label::Id(field_id(id)?).into(),
                    ty: ty(s)?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        fs.sort_by_key(|f| f.id.get_id());
        Ok::<_, String>(fs)
    };
    for (i, entry) in array(&fixture["table"])?.iter().enumerate() {
        let t = match tagged(entry)? {
            ("opt", s) => TypeInner::Opt(ty(s)?),
            ("vec", s) => TypeInner::Vec(ty(s)?),
            ("record", fs) => TypeInner::Record(fields(fs)?),
            ("variant", fs) => TypeInner::Variant(fields(fs)?),
            ("func", f) => TypeInner::Func(Function {
                modes: array(&f["annots"])?
                    .iter()
                    .map(|a| match a.as_str() {
                        Some("query") => Ok(FuncMode::Query),
                        Some("oneway") => Ok(FuncMode::Oneway),
                        Some("composite_query") => Ok(FuncMode::CompositeQuery),
                        _ => Err(format!("unknown function annotation {a}")),
                    })
                    .collect::<Result<_>>()?,
                args: slots(&f["args"])?,
                rets: slots(&f["rets"])?,
            }),
            ("service", ms) => {
                let mut ms = array(ms)?
                    .iter()
                    .map(|m| {
                        let (name, s) = pair(m)?;
                        Ok((string(name)?.to_string(), ty(s)?))
                    })
                    .collect::<Result<Vec<_>>>()?;
                ms.sort_by(|(a, _), (b, _)| a.cmp(b));
                TypeInner::Service(ms)
            }
            (k, _) => return Err(format!("unknown table entry {k:?}")),
        };
        env.0.insert(format!("{prefix}{i}"), t.into());
    }
    ty(&fixture["root"])
}

/// A type sequence, `{"table": [...], "roots": [...]}`, as the types a message is
/// decoded at.
fn load_seq(seq: &Value, env: &mut TypeEnv, prefix: &str) -> Result<Vec<Type>> {
    let roots = array(&seq["roots"])?;
    let mut types = Vec::new();
    for root in roots {
        let fixture = serde_json::json!({"table": seq["table"], "root": root});
        types.push(load(&fixture, env, prefix)?);
    }
    // With no roots the table is still translated, so that an entry 0.10 cannot
    // represent is an error here as it would be with one.
    if roots.is_empty() {
        load(
            &serde_json::json!({"table": seq["table"], "root": "null"}),
            env,
            prefix,
        )?;
    }
    Ok(types)
}

/// Lowercase hex, as bytes.
fn hex(v: &Value) -> Result<Vec<u8>> {
    let s = string(v)?;
    if s.len() % 2 != 0 {
        return Err(format!("odd number of hex digits: {s:?}"));
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(s.get(2 * i..2 * i + 2).unwrap_or("?"), 16))
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|_| format!("not hex bytes: {s:?}"))
}

/// A number written as a decimal string.
fn number<T: FromStr>(v: &Value) -> Result<T> {
    let s = string(v)?;
    s.parse()
        .map_err(|_| format!("not a number of this width: {s:?}"))
}

fn principal(v: &Value) -> Result<Principal> {
    let s = string(v)?;
    let bytes = (0..s.len() / 2)
        .map(|i| u8::from_str_radix(s.get(2 * i..2 * i + 2).unwrap_or("?"), 16))
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|_| format!("not hex bytes: {s:?}"))?;
    Principal::try_from_slice(&bytes).map_err(|e| e.to_string())
}

/// A value, as an `IDLValue`. A vector's `null` is `IDLValue::Null` here whatever its
/// type; encoding it at its type turns it into `None` at an option and `Reserved` at
/// `reserved`, and recomputes a variant's index.
fn value(v: &Value) -> Result<IDLValue> {
    let (tag, body) = match v {
        Value::Null => return Ok(IDLValue::Null),
        Value::Bool(b) => return Ok(IDLValue::Bool(*b)),
        v => tagged(v)?,
    };
    let bits =
        |v: &Value| u64::from_str_radix(string(v)?, 16).map_err(|_| format!("not hex bits: {v}"));
    Ok(match tag {
        "nat" => IDLValue::Nat(number(body)?),
        "int" => IDLValue::Int(number(body)?),
        "nat8" => IDLValue::Nat8(number(body)?),
        "nat16" => IDLValue::Nat16(number(body)?),
        "nat32" => IDLValue::Nat32(number(body)?),
        "nat64" => IDLValue::Nat64(number(body)?),
        "int8" => IDLValue::Int8(number(body)?),
        "int16" => IDLValue::Int16(number(body)?),
        "int32" => IDLValue::Int32(number(body)?),
        "int64" => IDLValue::Int64(number(body)?),
        "float32" => IDLValue::Float32(f32::from_bits(bits(body)? as u32)),
        "float64" => IDLValue::Float64(f64::from_bits(bits(body)?)),
        "text" => IDLValue::Text(string(body)?.to_string()),
        "opt" => IDLValue::Opt(Box::new(value(body)?)),
        "vec" => IDLValue::Vec(array(body)?.iter().map(value).collect::<Result<_>>()?),
        "record" => IDLValue::Record(
            array(body)?
                .iter()
                .map(|f| {
                    let (id, v) = pair(f)?;
                    Ok(IDLField {
                        id: Label::Id(field_id(id)?),
                        val: value(v)?,
                    })
                })
                .collect::<Result<_>>()?,
        ),
        "variant" => {
            let (id, v) = pair(body)?;
            let field = IDLField {
                id: Label::Id(field_id(id)?),
                val: value(v)?,
            };
            IDLValue::Variant(VariantValue(Box::new(field), 0))
        }
        "principal" => IDLValue::Principal(principal(body)?),
        "service" => IDLValue::Service(principal(body)?),
        "func" => {
            let (id, m) = pair(body)?;
            IDLValue::Func(principal(id)?, string(m)?.to_string())
        }
        k => return Err(format!("unknown value {k:?}")),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn agrees(v: Value) -> bool {
        matches!(run(&v), Ok(Outcome::Agree))
    }

    fn coerce(value: Value, from: Value, to: Value, expect: Value) -> Value {
        json!({"id": "t", "kind": "coerce", "value": value, "from": from, "to": to, "expect": expect})
    }

    #[test]
    fn asks_each_kind() {
        let nat = json!({"table": [], "root": "nat"});
        let int = json!({"table": [], "root": "int"});
        assert!(agrees(
            json!({"id": "t", "kind": "hash", "name": "a", "expect": 97})
        ));
        let sub = json!({"id": "t", "kind": "subtype", "sub": nat, "sup": int, "expect": true});
        assert!(agrees(sub));
        let ok = coerce(
            json!({"nat": "5"}),
            nat.clone(),
            int.clone(),
            json!({"value": {"int": "5"}}),
        );
        assert!(agrees(ok));
        let reject = coerce(json!({"int": "-5"}), int, nat, json!("reject"));
        assert!(agrees(reject));
        let nats = json!({"table": [], "roots": ["nat"]});
        let decode = |bytes: &str, expect: Value| json!({"id": "t", "kind": "decode", "bytes": bytes, "types": nats, "expect": expect});
        assert!(agrees(decode(
            "4449444c00017d05",
            json!({"values": [{"nat": "5"}]})
        )));
        assert!(agrees(decode("4449444c00017d0500", json!("reject"))));
    }

    /// Members of a record, variant or service type are in no particular order in a
    /// vector, and 0.10's encoder writes a type's fields in the order it is given them.
    /// An unsorted type must still roundtrip, and must not reject for that reason.
    #[test]
    fn type_member_order_does_not_matter() {
        let unsorted = json!({"table": [{"record": [[1, "nat"], [0, "nat"]]}], "root": 0});
        let value = json!({"record": [[0, {"nat": "0"}], [1, {"nat": "1"}]]});
        let v = coerce(
            value.clone(),
            unsorted.clone(),
            unsorted,
            json!({"value": value}),
        );
        assert!(agrees(v));
        let unsorted = json!({"table": [{"variant": [[1, "nat"], [0, "text"]]}], "root": 0});
        let value = json!({"variant": [0, {"text": "x"}]});
        let v = coerce(
            value.clone(),
            unsorted.clone(),
            unsorted,
            json!({"value": value}),
        );
        assert!(agrees(v));
    }

    /// The comparison is by encoding, so a NaN is equal to itself.
    #[test]
    fn nan_is_compared_by_its_bits() {
        let f = json!({"table": [], "root": "float64"});
        let nan = json!({"float64": "7ff8000000000001"});
        assert!(agrees(coerce(
            nan.clone(),
            f.clone(),
            f,
            json!({"value": nan})
        )));
    }

    /// A vector this runner cannot translate is an error, never an answer.
    #[test]
    fn non_ascii_bytes_are_an_error() {
        assert!(hex(&json!("€a")).is_err());
        assert_eq!(hex(&json!("00ff")), Ok(vec![0, 255]));
    }

    #[test]
    fn untranslatable_vectors_are_errors() {
        let nat = json!({"table": [], "root": "nat"});
        assert!(run(&json!({"id": "t", "kind": "subtype", "sub": nat})).is_err());
        assert!(run(&coerce(
            json!({"natural": "5"}),
            nat.clone(),
            nat,
            json!("reject")
        ))
        .is_err());
    }
}
