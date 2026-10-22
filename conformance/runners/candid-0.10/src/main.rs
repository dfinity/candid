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
//! A vector is read in full before anything is asked of `candid`, and a vector that
//! cannot be read fails the run whatever `KNOWN` says: `KNOWN` excuses an answer, never
//! a broken question. Reading is as strict as the reference reader in
//! `lean/Oracle/Vector.lean` -- unknown keys, missing keys and malformed types are
//! errors -- so this runner accepts exactly the files `oracle check` accepts.
//!
//! This calls `candid` 0.10's public API only, and it never modifies `rust/`.

use candid::types::subtype::{subtype_with_config, Gamma, OptReport};
use candid::types::value::{IDLField, VariantValue};
use candid::types::{Field, FuncMode, Function, Label, Type, TypeEnv, TypeInner};
use candid::{IDLArgs, IDLValue, Principal};
use serde_json::{Map, Value};
use std::collections::BTreeSet;
use std::process::ExitCode;

/// Vectors on which `candid` 0.10 is known to disagree with the model: `(id, why)`.
const KNOWN: &[(&str, &str)] = &[(
    "annotations agree up to reordering",
    "`subtype.rs` compares `Function::modes` as a `Vec`, so `query composite_query` \
         and `composite_query query` differ; the spec identifies annotation lists up to \
         reordering, and the `.did` grammar accepts `FuncMode*`",
)];

/// The vector format version this runner reads.
const FORMAT_VERSION: u64 = 0;

const SKIP_WELLFORMED: &str =
    "candid 0.10 has no public function that checks a type table on its own";

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
        for (i, raw) in vectors.iter().enumerate() {
            let v = match Vector::parse(raw) {
                Ok(v) => v,
                Err(e) => {
                    println!("FAIL  {path}: vector {i} cannot be read -- {e}");
                    failed += 1;
                    continue;
                }
            };
            let id = v.id.as_str();
            if !ids.insert(v.id.clone()) {
                println!("FAIL  {id} -- duplicate vector id");
                failed += 1;
                continue;
            }
            match (v.run(), known.contains(id)) {
                (Outcome::Invalid(e), _) => {
                    println!("FAIL  {id} -- bad vector: {e}");
                    failed += 1;
                }
                (Outcome::Skip, _) => skipped += 1,
                (Outcome::Agree, false) => agree += 1,
                (Outcome::Agree, true) => {
                    println!("FAIL  {id} -- listed in KNOWN but now agrees; remove it");
                    failed += 1;
                }
                (Outcome::Disagree(d), true) => {
                    println!("known {id} -- {d}");
                    known_hits += 1;
                }
                (Outcome::Disagree(d), false) => {
                    println!("FAIL  {id} -- {d}");
                    failed += 1;
                }
            }
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

fn read_file(path: &str) -> Result<Vec<Value>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let file: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    parse_file(&file)
}

fn parse_file(file: &Value) -> Result<Vec<Value>, String> {
    let file = object(file, &["version", "vectors"])?;
    let version = file["version"].as_u64();
    if version != Some(FORMAT_VERSION) {
        return Err(format!(
            "vector format version {}; this runner reads {FORMAT_VERSION}",
            file["version"]
        ));
    }
    Ok(array(&file["vectors"])?.clone())
}

// ---------------------------------------------------------------------------
//  Reading
// ---------------------------------------------------------------------------

/// A vector, read in full. Mirrors `Oracle.Vector` in `lean/Oracle/Vector.lean`.
#[derive(Debug)]
struct Vector {
    id: String,
    assertion: Assertion,
}

#[derive(Debug)]
enum Assertion {
    Hash {
        name: String,
        want: u32,
    },
    WellFormed,
    Subtype {
        sub: Fixture,
        sup: Fixture,
        want: bool,
    },
    /// `value : from ~> want : to`, or no such value when `want` is `None`.
    Coerce {
        value: Val,
        from: Fixture,
        to: Fixture,
        want: Option<Val>,
    },
}

/// A value as a vector writes it. Mirrors `Candid.Value` in `lean/Candid/Value.lean`:
/// one `Null` for the values `IDLValue` calls `Null`, `None` and `Reserved`; floats as
/// their bits; `nat` and `int` as canonical decimal strings; record fields in ascending
/// id order.
#[derive(Debug, Clone, PartialEq)]
enum Val {
    Null,
    Bool(bool),
    Nat(String),
    Int(String),
    Nat8(u8),
    Nat16(u16),
    Nat32(u32),
    Nat64(u64),
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Float32(u32),
    Float64(u64),
    Text(String),
    Opt(Box<Val>),
    Vec(Vec<Val>),
    Record(Vec<(u32, Val)>),
    Variant(u32, Box<Val>),
    Principal(Vec<u8>),
    Service(Vec<u8>),
    Func(Vec<u8>, String),
}

/// A type as a vector writes it: a table, not yet checked, and a root.
#[derive(Debug)]
struct Fixture {
    table: Vec<Entry>,
    root: Slot,
}

#[derive(Debug, Clone)]
enum Slot {
    Prim(TypeInner),
    Ref(usize),
}

#[derive(Debug)]
enum Entry {
    Opt(Slot),
    Vec(Slot),
    Record(Vec<(u32, Slot)>),
    Variant(Vec<(u32, Slot)>),
    Func {
        args: Vec<Slot>,
        rets: Vec<Slot>,
        modes: Vec<FuncMode>,
    },
    Service(Vec<(String, Slot)>),
}

/// The object's keys, exactly.
fn object<'a>(v: &'a Value, keys: &[&str]) -> Result<&'a Map<String, Value>, String> {
    let obj = v.as_object().ok_or_else(|| format!("not an object: {v}"))?;
    let got: BTreeSet<&str> = obj.keys().map(String::as_str).collect();
    let want: BTreeSet<&str> = keys.iter().copied().collect();
    if got != want {
        return Err(format!("expected keys {want:?}, got {got:?}"));
    }
    Ok(obj)
}

fn array(v: &Value) -> Result<&Vec<Value>, String> {
    v.as_array().ok_or_else(|| format!("not an array: {v}"))
}

fn string(v: &Value) -> Result<&str, String> {
    v.as_str().ok_or_else(|| format!("not a string: {v}"))
}

fn boolean(v: &Value) -> Result<bool, String> {
    v.as_bool().ok_or_else(|| format!("not a boolean: {v}"))
}

fn field_id(v: &Value) -> Result<u32, String> {
    v.as_u64()
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| format!("not a 32-bit field id: {v}"))
}

impl Vector {
    fn parse(v: &Value) -> Result<Vector, String> {
        let obj = v.as_object().ok_or_else(|| format!("not an object: {v}"))?;
        let id = string(obj.get("id").ok_or("no \"id\"")?)?.to_string();
        let kind = string(obj.get("kind").ok_or("no \"kind\"")?)?;
        let assertion = match kind {
            "hash" => {
                let obj = object(v, &["id", "kind", "name", "expect"])?;
                Assertion::Hash {
                    name: string(&obj["name"])?.to_string(),
                    want: field_id(&obj["expect"])?,
                }
            }
            "wellformed" => {
                // Not asked of `candid` 0.10, but read all the same: a malformed vector
                // is an error whether or not this runner has a question for it.
                let obj = object(v, &["id", "kind", "type", "expect"])?;
                Fixture::parse(&obj["type"])?;
                boolean(&obj["expect"])?;
                Assertion::WellFormed
            }
            "subtype" => {
                let obj = object(v, &["id", "kind", "sub", "sup", "expect"])?;
                Assertion::Subtype {
                    sub: Fixture::parse(&obj["sub"])?,
                    sup: Fixture::parse(&obj["sup"])?,
                    want: boolean(&obj["expect"])?,
                }
            }
            "coerce" => {
                let obj = object(v, &["id", "kind", "value", "from", "to", "expect"])?;
                let want = match &obj["expect"] {
                    Value::String(s) if s == "reject" => None,
                    e => Some(Val::parse(&object(e, &["value"])?["value"])?),
                };
                Assertion::Coerce {
                    value: Val::parse(&obj["value"])?,
                    from: Fixture::parse(&obj["from"])?,
                    to: Fixture::parse(&obj["to"])?,
                    want,
                }
            }
            k => return Err(format!("unknown vector kind {k:?}")),
        };
        Ok(Vector { id, assertion })
    }
}

impl Slot {
    /// A primitive's name, or a table index.
    fn parse(v: &Value) -> Result<Slot, String> {
        if let Some(i) = v.as_u64() {
            let i = usize::try_from(i).map_err(|_| format!("index out of range: {i}"))?;
            return Ok(Slot::Ref(i));
        }
        let name = v.as_str().ok_or_else(|| format!("not a slot: {v}"))?;
        Ok(Slot::Prim(match name {
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
            _ => return Err(format!("unknown primitive type {name:?}")),
        }))
    }
}

fn slots(v: &Value) -> Result<Vec<Slot>, String> {
    array(v)?.iter().map(Slot::parse).collect()
}

/// `[[key, slot], ...]`, with the key read by `key`.
fn pairs<K>(
    v: &Value,
    key: impl Fn(&Value) -> Result<K, String>,
) -> Result<Vec<(K, Slot)>, String> {
    array(v)?
        .iter()
        .map(|p| match p.as_array().map(Vec::as_slice) {
            Some([k, s]) => Ok((key(k)?, Slot::parse(s)?)),
            _ => Err(format!("not a pair: {p}")),
        })
        .collect()
}

impl Entry {
    /// An object with exactly one key, naming the composite.
    fn parse(v: &Value) -> Result<Entry, String> {
        let obj = v
            .as_object()
            .ok_or_else(|| format!("not a table entry: {v}"))?;
        let [(key, body)] = obj.iter().collect::<Vec<_>>()[..] else {
            return Err(format!("not a table entry: {v}"));
        };
        Ok(match key.as_str() {
            "opt" => Entry::Opt(Slot::parse(body)?),
            "vec" => Entry::Vec(Slot::parse(body)?),
            "record" => Entry::Record(pairs(body, field_id)?),
            "variant" => Entry::Variant(pairs(body, field_id)?),
            "func" => {
                let f = object(body, &["args", "rets", "annots"])?;
                let modes = array(&f["annots"])?
                    .iter()
                    .map(|a| match a.as_str() {
                        Some("query") => Ok(FuncMode::Query),
                        Some("oneway") => Ok(FuncMode::Oneway),
                        Some("composite_query") => Ok(FuncMode::CompositeQuery),
                        _ => Err(format!("unknown function annotation {a}")),
                    })
                    .collect::<Result<_, _>>()?;
                Entry::Func {
                    args: slots(&f["args"])?,
                    rets: slots(&f["rets"])?,
                    modes,
                }
            }
            "service" => Entry::Service(pairs(body, |k| string(k).map(str::to_string))?),
            k => return Err(format!("unknown table entry {k:?}")),
        })
    }
}

/// A decimal string in canonical form, as Lean's `toString` writes it: no sign, no
/// leading zero, no separator.
fn decimal_nat(v: &Value) -> Result<String, String> {
    let s = string(v)?;
    let canonical =
        !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) && (s == "0" || !s.starts_with('0'));
    match canonical {
        true => Ok(s.to_string()),
        false => Err(format!("not a canonical decimal natural: {s:?}")),
    }
}

/// As `decimal_nat`, with an optional `-` and no `-0`.
fn decimal_int(v: &Value) -> Result<String, String> {
    let s = string(v)?;
    let magnitude = s.strip_prefix('-').unwrap_or(s);
    match decimal_nat(&Value::String(magnitude.to_string())) {
        Ok(_) if !(s.starts_with('-') && magnitude == "0") => Ok(s.to_string()),
        _ => Err(format!("not a canonical decimal integer: {s:?}")),
    }
}

/// A fixed-width number, written in decimal.
fn bounded<T: TryFrom<i128>>(v: &Value) -> Result<T, String> {
    let s = decimal_int(v)?;
    s.parse::<i128>()
        .ok()
        .and_then(|n| T::try_from(n).ok())
        .ok_or_else(|| format!("{s} is out of range"))
}

/// Lowercase hex digits, exactly `width` of them.
fn hex_fixed(v: &Value, width: usize) -> Result<u64, String> {
    let s = string(v)?;
    let lower = s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    if s.len() != width || !lower {
        return Err(format!("expected {width} lowercase hex digits: {s:?}"));
    }
    u64::from_str_radix(s, 16).map_err(|e| e.to_string())
}

fn hex_bytes(v: &Value) -> Result<Vec<u8>, String> {
    let s = string(v)?;
    if s.len() % 2 != 0 || !s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {
        return Err(format!("not lowercase hex bytes: {s:?}"));
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

fn two(v: &Value) -> Result<(&Value, &Value), String> {
    match v.as_array().map(Vec::as_slice) {
        Some([a, b]) => Ok((a, b)),
        _ => Err(format!("not a pair: {v}")),
    }
}

impl Val {
    fn parse(v: &Value) -> Result<Val, String> {
        match v {
            Value::Null => return Ok(Val::Null),
            Value::Bool(b) => return Ok(Val::Bool(*b)),
            _ => {}
        }
        let obj = v.as_object().ok_or_else(|| format!("not a value: {v}"))?;
        let [(key, body)] = obj.iter().collect::<Vec<_>>()[..] else {
            return Err(format!("not a value: {v}"));
        };
        Ok(match key.as_str() {
            "nat" => Val::Nat(decimal_nat(body)?),
            "int" => Val::Int(decimal_int(body)?),
            "nat8" => Val::Nat8(bounded(body)?),
            "nat16" => Val::Nat16(bounded(body)?),
            "nat32" => Val::Nat32(bounded(body)?),
            "nat64" => Val::Nat64(bounded(body)?),
            "int8" => Val::Int8(bounded(body)?),
            "int16" => Val::Int16(bounded(body)?),
            "int32" => Val::Int32(bounded(body)?),
            "int64" => Val::Int64(bounded(body)?),
            "float32" => Val::Float32(hex_fixed(body, 8)? as u32),
            "float64" => Val::Float64(hex_fixed(body, 16)?),
            "text" => Val::Text(string(body)?.to_string()),
            "opt" => Val::Opt(Box::new(Val::parse(body)?)),
            "vec" => Val::Vec(
                array(body)?
                    .iter()
                    .map(Val::parse)
                    .collect::<Result<_, _>>()?,
            ),
            "record" => Val::Record(
                array(body)?
                    .iter()
                    .map(|f| {
                        let (id, v) = two(f)?;
                        Ok((field_id(id)?, Val::parse(v)?))
                    })
                    .collect::<Result<_, String>>()?,
            ),
            "variant" => {
                let (id, v) = two(body)?;
                Val::Variant(field_id(id)?, Box::new(Val::parse(v)?))
            }
            "principal" => Val::Principal(hex_bytes(body)?),
            "service" => Val::Service(hex_bytes(body)?),
            "func" => {
                let (id, m) = two(body)?;
                Val::Func(hex_bytes(id)?, string(m)?.to_string())
            }
            k => return Err(format!("unknown value {k:?}")),
        })
    }
}

impl Fixture {
    fn parse(v: &Value) -> Result<Fixture, String> {
        let obj = object(v, &["table", "root"])?;
        Ok(Fixture {
            table: array(&obj["table"])?
                .iter()
                .map(Entry::parse)
                .collect::<Result<_, _>>()?,
            root: Slot::parse(&obj["root"])?,
        })
    }

    /// Well-formedness, as `RawTypeTable.check` and `TypeTable.root?` in
    /// `lean/Candid/Types.lean` define it: every reference resolves, no label
    /// repeats, a `oneway` function has no results, and every method is a function.
    /// Subtyping is not defined on a malformed type, and `candid` 0.10 would answer
    /// one anyway -- an unresolved variable comes back as an error, which reads as
    /// `!<:` -- so a subtype vector carrying one is rejected before it is asked.
    fn check(&self) -> Result<(), String> {
        let resolves = |s: &Slot| match s {
            Slot::Prim(_) => Ok(()),
            Slot::Ref(i) if *i < self.table.len() => Ok(()),
            Slot::Ref(i) => Err(format!("reference {i} does not resolve")),
        };
        fn distinct<K: Ord>(keys: impl Iterator<Item = K>) -> Result<(), String> {
            let mut seen = BTreeSet::new();
            match keys.into_iter().all(|k| seen.insert(k)) {
                true => Ok(()),
                false => Err("a label repeats".to_string()),
            }
        }
        for entry in &self.table {
            match entry {
                Entry::Opt(t) | Entry::Vec(t) => resolves(t)?,
                Entry::Record(fs) | Entry::Variant(fs) => {
                    distinct(fs.iter().map(|(id, _)| id))?;
                    fs.iter().try_for_each(|(_, s)| resolves(s))?;
                }
                Entry::Func { args, rets, modes } => {
                    if modes.contains(&FuncMode::Oneway) && !rets.is_empty() {
                        return Err("a oneway function has results".to_string());
                    }
                    args.iter().chain(rets).try_for_each(resolves)?;
                }
                Entry::Service(ms) => {
                    distinct(ms.iter().map(|(name, _)| name))?;
                    for (name, s) in ms {
                        match s {
                            Slot::Ref(i)
                                if matches!(self.table.get(*i), Some(Entry::Func { .. })) => {}
                            _ => return Err(format!("method {name:?} is not a function")),
                        }
                    }
                }
            }
        }
        resolves(&self.root)
    }
}

// ---------------------------------------------------------------------------
//  Asking candid 0.10
// ---------------------------------------------------------------------------

enum Outcome {
    Agree,
    Disagree(String),
    /// The vector asks something this runner has no way to put to `candid` 0.10.
    Skip,
    /// The vector reads, but is not a valid question. Never excused by `KNOWN`.
    Invalid(String),
}

impl Vector {
    fn run(&self) -> Outcome {
        match &self.assertion {
            Assertion::Hash { name, want } => {
                let got = candid::idl_hash(name);
                agreement(got == *want, || format!("got {got}, want {want}"))
            }
            Assertion::WellFormed => Outcome::Skip,
            Assertion::Coerce {
                value,
                from,
                to,
                want,
            } => {
                if let Err(e) = from.check().and_then(|()| to.check()) {
                    return Outcome::Invalid(format!("a type is malformed: {e}"));
                }
                if !from.has_type(value, &from.root) {
                    return Outcome::Invalid("the value does not have its type".to_string());
                }
                if want.as_ref().is_some_and(|w| !to.has_type(w, &to.root)) {
                    return Outcome::Invalid("the expected value does not have its type".into());
                }
                coerce(value, from, to, want.as_ref())
            }
            Assertion::Subtype { sub, sup, want } => {
                if let Err(e) = sub.check().and_then(|()| sup.check()) {
                    return Outcome::Invalid(format!("a type is malformed: {e}"));
                }
                // `candid` 0.10 takes one environment for both types, so the two
                // tables go into one, each under its own prefix. This is the merge
                // every caller of `subtype` does today.
                let mut env = TypeEnv::new();
                let a = sub.load(&mut env, "A");
                let b = sup.load(&mut env, "B");
                // `Silence`: the special `opt` rule is part of the relation the
                // vectors assert, and the other settings report it rather than change
                // the answer -- except `Error`, which turns it into another relation.
                // Both types are well formed, so an error here can only mean `!<:`.
                let got = subtype_with_config(OptReport::Silence, &mut Gamma::new(), &env, &a, &b)
                    .is_ok();
                agreement(got == *want, || {
                    format!("got {}, want {}", rel(got), rel(*want))
                })
            }
        }
    }
}

/// Encode `value` at `from` and decode the bytes at `to`: coercion is what a decoder
/// does, and 0.10 has no other entry point to it. Each table goes in its own
/// environment, since the encoder's and the decoder's are separate anyway.
fn coerce(value: &Val, from: &Fixture, to: &Fixture, want: Option<&Val>) -> Outcome {
    let (mut a_env, mut b_env) = (TypeEnv::new(), TypeEnv::new());
    let a = from.load(&mut a_env, "A");
    let b = to.load(&mut b_env, "B");
    let arg = match from.to_idl(value, &from.root) {
        Ok(v) => v,
        Err(e) => return Outcome::Disagree(format!("cannot express the value: {e}")),
    };
    let bytes = match IDLArgs::new(&[arg]).to_bytes_with_types(&a_env, &[a]) {
        Ok(b) => b,
        Err(e) => return Outcome::Disagree(format!("cannot encode the value: {e}")),
    };
    let got = IDLArgs::from_bytes_with_types(&bytes, &b_env, &[b]);
    match (got, want) {
        (Err(_), None) => Outcome::Agree,
        (Err(e), Some(w)) => Outcome::Disagree(format!("rejected ({e}), want {w:?}")),
        (Ok(args), want) => match (from_idl(&args.args[0]), want) {
            (Ok(v), Some(w)) => agreement(v == *w, || format!("got {v:?}, want {w:?}")),
            (Ok(v), None) => Outcome::Disagree(format!("got {v:?}, want reject")),
            (Err(e), _) => Outcome::Disagree(format!("decoded to an unexpected value: {e}")),
        },
    }
}

/// A decoded value, in the model's terms.
fn from_idl(v: &IDLValue) -> Result<Val, String> {
    Ok(match v {
        IDLValue::Null | IDLValue::None | IDLValue::Reserved => Val::Null,
        IDLValue::Bool(b) => Val::Bool(*b),
        IDLValue::Nat(n) => Val::Nat(n.0.to_string()),
        IDLValue::Int(i) => Val::Int(i.0.to_string()),
        IDLValue::Nat8(n) => Val::Nat8(*n),
        IDLValue::Nat16(n) => Val::Nat16(*n),
        IDLValue::Nat32(n) => Val::Nat32(*n),
        IDLValue::Nat64(n) => Val::Nat64(*n),
        IDLValue::Int8(i) => Val::Int8(*i),
        IDLValue::Int16(i) => Val::Int16(*i),
        IDLValue::Int32(i) => Val::Int32(*i),
        IDLValue::Int64(i) => Val::Int64(*i),
        IDLValue::Float32(f) => Val::Float32(f.to_bits()),
        IDLValue::Float64(f) => Val::Float64(f.to_bits()),
        IDLValue::Text(t) => Val::Text(t.clone()),
        IDLValue::Opt(v) => Val::Opt(Box::new(from_idl(v)?)),
        IDLValue::Vec(vs) => Val::Vec(vs.iter().map(from_idl).collect::<Result<_, _>>()?),
        IDLValue::Blob(bs) => Val::Vec(bs.iter().map(|b| Val::Nat8(*b)).collect()),
        IDLValue::Record(fs) => {
            let mut fs = fs
                .iter()
                .map(|f| Ok((f.id.get_id(), from_idl(&f.val)?)))
                .collect::<Result<Vec<_>, String>>()?;
            fs.sort_by_key(|(id, _)| *id);
            Val::Record(fs)
        }
        IDLValue::Variant(VariantValue(f, _)) => {
            Val::Variant(f.id.get_id(), Box::new(from_idl(&f.val)?))
        }
        IDLValue::Principal(p) => Val::Principal(p.as_slice().to_vec()),
        IDLValue::Service(p) => Val::Service(p.as_slice().to_vec()),
        IDLValue::Func(p, m) => Val::Func(p.as_slice().to_vec(), m.clone()),
        IDLValue::Number(n) => return Err(format!("an untyped number {n}")),
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

impl Slot {
    /// A primitive, or a type variable naming entry `{prefix}{i}`.
    fn to_type(&self, prefix: &str) -> Type {
        match self {
            Slot::Prim(p) => p.clone().into(),
            Slot::Ref(i) => TypeInner::Var(format!("{prefix}{i}")).into(),
        }
    }
}

impl Fixture {
    /// Add the table to `env`, entry `i` named `{prefix}{i}`, and return the root.
    ///
    /// A vector lists a type's members in no particular order, but 0.10 expects them
    /// sorted, as its parser leaves them: its encoder writes a type's fields in the
    /// order it is given them, and its decoder rejects a header that is not sorted. So
    /// fields are sorted by id and methods by name here.
    fn load(&self, env: &mut TypeEnv, prefix: &str) -> Type {
        let ty = |s: &Slot| s.to_type(prefix);
        let fields = |fs: &[(u32, Slot)]| {
            let mut fs: Vec<Field> = fs
                .iter()
                .map(|(id, s)| Field {
                    id: Label::Id(*id).into(),
                    ty: ty(s),
                })
                .collect();
            fs.sort_by_key(|f| f.id.get_id());
            fs
        };
        for (i, entry) in self.table.iter().enumerate() {
            let t = match entry {
                Entry::Opt(s) => TypeInner::Opt(ty(s)),
                Entry::Vec(s) => TypeInner::Vec(ty(s)),
                Entry::Record(fs) => TypeInner::Record(fields(fs)),
                Entry::Variant(fs) => TypeInner::Variant(fields(fs)),
                Entry::Func { args, rets, modes } => TypeInner::Func(Function {
                    modes: modes.clone(),
                    args: args.iter().map(ty).collect(),
                    rets: rets.iter().map(ty).collect(),
                }),
                Entry::Service(ms) => {
                    let mut ms: Vec<_> = ms.iter().map(|(n, s)| (n.clone(), ty(s))).collect();
                    ms.sort_by(|(a, _), (b, _)| a.cmp(b));
                    TypeInner::Service(ms)
                }
            };
            env.0.insert(format!("{prefix}{i}"), t.into());
        }
        ty(&self.root)
    }
}

fn field_at<'a, K: PartialEq>(fs: &'a [(K, Slot)], k: &K) -> Option<&'a Slot> {
    fs.iter().find(|(id, _)| id == k).map(|(_, s)| s)
}

impl Fixture {
    fn entry(&self, s: &Slot) -> Option<&Entry> {
        match s {
            Slot::Ref(i) => self.table.get(*i),
            Slot::Prim(_) => None,
        }
    }

    /// `v : t`, as `TypeTable.hasType` in `lean/Candid/Value.lean` defines it.
    fn has_type(&self, v: &Val, t: &Slot) -> bool {
        if let Slot::Prim(p) = t {
            return matches!(
                (v, p),
                (Val::Null, TypeInner::Null | TypeInner::Reserved)
                    | (Val::Bool(_), TypeInner::Bool)
                    | (Val::Nat(_), TypeInner::Nat)
                    | (Val::Int(_), TypeInner::Int)
                    | (Val::Nat8(_), TypeInner::Nat8)
                    | (Val::Nat16(_), TypeInner::Nat16)
                    | (Val::Nat32(_), TypeInner::Nat32)
                    | (Val::Nat64(_), TypeInner::Nat64)
                    | (Val::Int8(_), TypeInner::Int8)
                    | (Val::Int16(_), TypeInner::Int16)
                    | (Val::Int32(_), TypeInner::Int32)
                    | (Val::Int64(_), TypeInner::Int64)
                    | (Val::Float32(_), TypeInner::Float32)
                    | (Val::Float64(_), TypeInner::Float64)
                    | (Val::Text(_), TypeInner::Text)
                    | (Val::Principal(_), TypeInner::Principal)
            );
        }
        match (v, self.entry(t)) {
            (Val::Null, Some(Entry::Opt(_))) => true,
            (Val::Opt(w), Some(Entry::Opt(t))) => self.has_type(w, t),
            (Val::Vec(ws), Some(Entry::Vec(t))) => ws.iter().all(|w| self.has_type(w, t)),
            (Val::Record(vs), Some(Entry::Record(fs))) => {
                vs.windows(2).all(|p| p[0].0 < p[1].0)
                    && vs.len() == fs.len()
                    && vs
                        .iter()
                        .all(|(id, w)| field_at(fs, id).is_some_and(|t| self.has_type(w, t)))
            }
            (Val::Variant(id, w), Some(Entry::Variant(fs))) => {
                field_at(fs, id).is_some_and(|t| self.has_type(w, t))
            }
            (Val::Service(_), Some(Entry::Service(_))) => true,
            (Val::Func(..), Some(Entry::Func { .. })) => true,
            _ => false,
        }
    }

    /// The value as an `IDLValue` of type `t`. The type picks which `IDLValue` a
    /// `null` is; the rest is a change of representation.
    fn to_idl(&self, v: &Val, t: &Slot) -> Result<IDLValue, String> {
        let principal = |bs: &[u8]| Principal::try_from_slice(bs).map_err(|e| e.to_string());
        let entry = self.entry(t);
        Ok(match v {
            Val::Null => match (t, entry) {
                (Slot::Prim(TypeInner::Reserved), _) => IDLValue::Reserved,
                (_, Some(Entry::Opt(_))) => IDLValue::None,
                _ => IDLValue::Null,
            },
            Val::Bool(b) => IDLValue::Bool(*b),
            Val::Nat(n) => IDLValue::Nat(n.parse().map_err(|e| format!("{e:?}"))?),
            Val::Int(i) => IDLValue::Int(i.parse().map_err(|e| format!("{e:?}"))?),
            Val::Nat8(n) => IDLValue::Nat8(*n),
            Val::Nat16(n) => IDLValue::Nat16(*n),
            Val::Nat32(n) => IDLValue::Nat32(*n),
            Val::Nat64(n) => IDLValue::Nat64(*n),
            Val::Int8(i) => IDLValue::Int8(*i),
            Val::Int16(i) => IDLValue::Int16(*i),
            Val::Int32(i) => IDLValue::Int32(*i),
            Val::Int64(i) => IDLValue::Int64(*i),
            Val::Float32(b) => IDLValue::Float32(f32::from_bits(*b)),
            Val::Float64(b) => IDLValue::Float64(f64::from_bits(*b)),
            Val::Text(s) => IDLValue::Text(s.clone()),
            Val::Opt(w) => match entry {
                Some(Entry::Opt(t)) => IDLValue::Opt(Box::new(self.to_idl(w, t)?)),
                _ => return Err("an option at a type that is not one".into()),
            },
            Val::Vec(ws) => match entry {
                Some(Entry::Vec(t)) => IDLValue::Vec(
                    ws.iter()
                        .map(|w| self.to_idl(w, t))
                        .collect::<Result<_, _>>()?,
                ),
                _ => return Err("a vector at a type that is not one".into()),
            },
            Val::Record(vs) => match entry {
                Some(Entry::Record(fs)) => IDLValue::Record(
                    vs.iter()
                        .map(|(id, w)| {
                            let t = field_at(fs, id).ok_or("an undeclared field")?;
                            Ok(IDLField {
                                id: Label::Id(*id),
                                val: self.to_idl(w, t)?,
                            })
                        })
                        .collect::<Result<_, String>>()?,
                ),
                _ => return Err("a record at a type that is not one".into()),
            },
            // The index is recomputed from the type when the value is encoded.
            Val::Variant(id, w) => match entry {
                Some(Entry::Variant(fs)) => {
                    let t = field_at(fs, id).ok_or("an undeclared tag")?;
                    let field = IDLField {
                        id: Label::Id(*id),
                        val: self.to_idl(w, t)?,
                    };
                    IDLValue::Variant(VariantValue(Box::new(field), 0))
                }
                _ => return Err("a variant at a type that is not one".into()),
            },
            Val::Principal(bs) => IDLValue::Principal(principal(bs)?),
            Val::Service(bs) => IDLValue::Service(principal(bs)?),
            Val::Func(bs, m) => IDLValue::Func(principal(bs)?, m.clone()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn nat() -> Value {
        json!({"table": [], "root": "nat"})
    }

    fn subtype(sub: Value, sup: Value, expect: Value) -> Value {
        json!({"id": "t", "kind": "subtype", "sub": sub, "sup": sup, "expect": expect})
    }

    fn rejects(v: Value) {
        assert!(Vector::parse(&v).is_err(), "accepted {v}");
    }

    fn invalid(v: Value) {
        let v = Vector::parse(&v).unwrap();
        assert!(matches!(v.run(), Outcome::Invalid(_)), "asked {v:?}");
    }

    #[test]
    fn reads_a_well_formed_vector() {
        let v = Vector::parse(&subtype(nat(), nat(), json!(true))).unwrap();
        assert!(matches!(v.run(), Outcome::Agree));
    }

    #[test]
    fn rejects_unknown_and_missing_keys() {
        assert!(parse_file(&json!({"version": 0, "vectors": [], "extra": 1})).is_err());
        assert!(parse_file(&json!({"vectors": []})).is_err());
        let mut v = subtype(nat(), nat(), json!(true));
        v["note"] = json!("x");
        rejects(v);
        rejects(json!({"kind": "subtype", "sub": nat(), "sup": nat(), "expect": true}));
        rejects(json!({"id": 1, "kind": "hash", "name": "a", "expect": 97}));
        rejects(json!({"id": "t", "kind": "hash", "name": "a"}));
        rejects(subtype(
            json!({"table": [], "root": "nat", "x": 0}),
            nat(),
            json!(true),
        ));
        let func = json!({"table": [{"func": {"args": [], "rets": [], "annots": [], "x": []}}], "root": 0});
        rejects(subtype(func, nat(), json!(false)));
    }

    #[test]
    fn rejects_values_of_the_wrong_shape() {
        rejects(subtype(nat(), nat(), json!("true")));
        rejects(json!({"id": "t", "kind": "hash", "name": "a", "expect": 1u64 << 32}));
        rejects(subtype(
            json!({"table": [{"opt": "nat", "vec": "nat"}], "root": 0}),
            nat(),
            json!(true),
        ));
        rejects(subtype(
            json!({"table": [], "root": "natural"}),
            nat(),
            json!(true),
        ));
    }

    #[test]
    fn reads_wellformed_vectors_before_skipping_them() {
        let ok = json!({"id": "t", "kind": "wellformed", "type": nat(), "expect": true});
        assert!(matches!(Vector::parse(&ok).unwrap().run(), Outcome::Skip));
        rejects(json!({"id": "t", "kind": "wellformed", "type": {"root": "nat"}, "expect": true}));
        rejects(json!({"id": "t", "kind": "wellformed", "type": nat(), "expect": 1}));
    }

    fn coerce(value: Value, from: Value, to: Value, expect: Value) -> Value {
        json!({"id": "t", "kind": "coerce", "value": value, "from": from, "to": to, "expect": expect})
    }

    #[test]
    fn decodes_a_coerce_vector() {
        let int = json!({"table": [], "root": "int"});
        let v = coerce(
            json!({"nat": "5"}),
            nat(),
            int,
            json!({"value": {"int": "5"}}),
        );
        assert!(matches!(Vector::parse(&v).unwrap().run(), Outcome::Agree));
        let v = coerce(
            json!({"int": "-5"}),
            json!({"table": [], "root": "int"}),
            nat(),
            json!("reject"),
        );
        assert!(matches!(Vector::parse(&v).unwrap().run(), Outcome::Agree));
    }

    #[test]
    fn rejects_malformed_values() {
        for value in [
            json!({"nat": 5}),
            json!({"nat": "05"}),
            json!({"nat": "+5"}),
            json!({"int": "-0"}),
            json!({"nat8": "256"}),
            json!({"int8": "-129"}),
            json!({"float32": "3F800000"}),
            json!({"float32": "3f80000"}),
            json!({"principal": "abc"}),
            json!({"nat": "5", "int": "5"}),
            json!({"natural": "5"}),
        ] {
            rejects(coerce(value, nat(), nat(), json!("reject")));
        }
        rejects(coerce(json!({"nat": "5"}), nat(), nat(), json!("accept")));
        rejects(coerce(
            json!({"nat": "5"}),
            nat(),
            nat(),
            json!({"value": {"nat": "5"}, "x": 1}),
        ));
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
        assert!(matches!(Vector::parse(&v).unwrap().run(), Outcome::Agree));
        let unsorted = json!({"table": [{"variant": [[1, "nat"], [0, "text"]]}], "root": 0});
        let value = json!({"variant": [0, {"text": "x"}]});
        let v = coerce(
            value.clone(),
            unsorted.clone(),
            unsorted,
            json!({"value": value}),
        );
        assert!(matches!(Vector::parse(&v).unwrap().run(), Outcome::Agree));
    }

    /// Coercion is only defined on well-typed values, and an expected result that is
    /// not of the target type cannot be right whatever 0.10 answers.
    #[test]
    fn rejects_ill_typed_coerce_vectors() {
        invalid(coerce(json!({"int": "5"}), nat(), nat(), json!("reject")));
        invalid(coerce(
            json!({"nat": "5"}),
            nat(),
            nat(),
            json!({"value": {"int": "5"}}),
        ));
        let record = json!({"table": [{"record": [[0, "nat"], [1, "nat"]]}], "root": 0});
        let unsorted = json!({"record": [[1, {"nat": "1"}], [0, {"nat": "0"}]]});
        invalid(coerce(unsorted, record.clone(), record, json!("reject")));
    }

    /// The case that would otherwise pass as a negative example: an unresolved
    /// variable makes `subtype` return an error, which reads as `!<:`.
    #[test]
    fn rejects_malformed_types_in_subtype_vectors() {
        invalid(subtype(
            json!({"table": [], "root": 0}),
            nat(),
            json!(false),
        ));
        invalid(subtype(
            json!({"table": [{"vec": 1}], "root": 0}),
            nat(),
            json!(false),
        ));
        invalid(subtype(
            json!({"table": [{"record": [[0, "nat"], [0, "text"]]}], "root": 0}),
            nat(),
            json!(false),
        ));
        invalid(subtype(
            json!({"table": [{"func": {"args": [], "rets": ["nat"], "annots": ["oneway"]}}], "root": 0}),
            nat(),
            json!(false),
        ));
        invalid(subtype(
            json!({"table": [{"service": [["m", "nat"]]}], "root": 0}),
            nat(),
            json!(false),
        ));
        invalid(subtype(
            json!({"table": [{"vec": "nat"}, {"service": [["m", 0]]}], "root": 1}),
            nat(),
            json!(false),
        ));
    }
}
