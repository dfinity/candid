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
use candid::types::{Field, FuncMode, Function, Label, Type, TypeEnv, TypeInner};
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
    fn load(&self, env: &mut TypeEnv, prefix: &str) -> Type {
        let ty = |s: &Slot| s.to_type(prefix);
        let fields = |fs: &[(u32, Slot)]| {
            fs.iter()
                .map(|(id, s)| Field {
                    id: Label::Id(*id).into(),
                    ty: ty(s),
                })
                .collect()
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
                    TypeInner::Service(ms.iter().map(|(n, s)| (n.clone(), ty(s))).collect())
                }
            };
            env.0.insert(format!("{prefix}{i}"), t.into());
        }
        ty(&self.root)
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
