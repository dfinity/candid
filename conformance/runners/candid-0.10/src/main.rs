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
//! This calls `candid` 0.10's public API only. It does not test the binding of that API
//! to anything else, and it never modifies `rust/`.

use candid::types::subtype::{subtype_with_config, Gamma, OptReport};
use candid::types::{Field, FuncMode, Function, Label, Type, TypeEnv, TypeInner};
use serde_json::Value;
use std::collections::BTreeSet;
use std::process::ExitCode;

/// Vectors on which `candid` 0.10 is known to disagree with the model: `(id, why)`.
const KNOWN: &[(&str, &str)] = &[
    (
        "annotations agree up to reordering",
        "`subtype.rs` compares `Function::modes` as a `Vec`, so `query composite_query` \
         and `composite_query query` differ; the spec identifies annotation lists up to \
         reordering, and the `.did` grammar accepts `FuncMode*`",
    ),
    (
        "record { X; X' } !<: record { opt Y; Y' } (assumption from a failed opt attempt)",
        "candid 0.10 bug: the `opt` rule probes `t <: t'` with `subtype_`, and a failed \
         probe removes from `gamma` only the pair that failed, keeping pairs proved \
         under it. A later comparison is then answered from `gamma`. Reachable from \
         `didc check`, which accepts a breaking upgrade this way",
    ),
];

/// The vector format version this runner reads.
const FORMAT_VERSION: u64 = 0;

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
    let mut seen_known = BTreeSet::new();
    let (mut agree, mut skipped, mut known_hits, mut failed) = (0, 0, 0, 0);

    for path in &paths {
        let vectors = match read_file(path) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("{path}: {e}");
                return ExitCode::FAILURE;
            }
        };
        for v in &vectors {
            let id = v["id"].as_str().unwrap_or("<no id>");
            let outcome = run(v).unwrap_or_else(|e| Outcome::Disagree(format!("bad vector: {e}")));
            let is_known = known.contains(id);
            if is_known {
                seen_known.insert(id.to_string());
            }
            match (outcome, is_known) {
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
                (Outcome::Skip, _) => skipped += 1,
            }
        }
    }
    for (id, _) in KNOWN {
        if !seen_known.contains(*id) {
            println!("FAIL  {id} -- listed in KNOWN but no vector has this id");
            failed += 1;
        }
    }

    println!();
    println!("{agree} agree, {known_hits} known divergences, {skipped} skipped, {failed} failed");
    if skipped > 0 {
        println!("skipped: wellformed vectors -- {}", SKIP_WELLFORMED);
    }
    if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

const SKIP_WELLFORMED: &str =
    "candid 0.10 has no public function that checks a type table on its own";

fn read_file(path: &str) -> Result<Vec<Value>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let file: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    if file["version"].as_u64() != Some(FORMAT_VERSION) {
        return Err(format!(
            "vector format version {}; this runner reads {FORMAT_VERSION}",
            file["version"]
        ));
    }
    file["vectors"]
        .as_array()
        .cloned()
        .ok_or_else(|| "no \"vectors\" array".to_string())
}

fn run(v: &Value) -> Result<Outcome, String> {
    let kind = v["kind"].as_str().ok_or("no \"kind\"")?;
    Ok(match kind {
        "hash" => {
            let name = v["name"].as_str().ok_or("no \"name\"")?;
            let want = v["expect"].as_u64().ok_or("no \"expect\"")?;
            let got = candid::idl_hash(name);
            if u64::from(got) == want {
                Outcome::Agree
            } else {
                Outcome::Disagree(format!("got {got}, want {want}"))
            }
        }
        "wellformed" => Outcome::Skip,
        "subtype" => {
            let want = v["expect"].as_bool().ok_or("no \"expect\"")?;
            // `candid` 0.10 takes one environment for both types, so the two tables
            // go into one, each under its own prefix. This is the merge every caller
            // of `subtype` does today.
            let mut env = TypeEnv::new();
            let sub = load(&mut env, &v["sub"], "A")?;
            let sup = load(&mut env, &v["sup"], "B")?;
            // `Silence`: the special `opt` rule is part of the relation the vectors
            // assert, and the other settings report it rather than change the answer
            // -- except `Error`, which turns it into a different relation.
            let got = subtype_with_config(OptReport::Silence, &mut Gamma::new(), &env, &sub, &sup)
                .is_ok();
            if got == want {
                Outcome::Agree
            } else {
                Outcome::Disagree(format!("got {}, want {}", rel(got), rel(want)))
            }
        }
        k => return Err(format!("unknown vector kind {k:?}")),
    })
}

fn rel(b: bool) -> &'static str {
    if b {
        "<:"
    } else {
        "!<:"
    }
}

/// Add a type's table to `env`, entry `i` named `{prefix}{i}`, and return its root.
fn load(env: &mut TypeEnv, ty: &Value, prefix: &str) -> Result<Type, String> {
    let table = ty["table"].as_array().ok_or("no \"table\"")?;
    for (i, entry) in table.iter().enumerate() {
        env.0
            .insert(format!("{prefix}{i}"), composite(entry, prefix)?);
    }
    slot(&ty["root"], prefix)
}

/// A slot is a primitive's name or a table index; an index becomes a type variable.
fn slot(v: &Value, prefix: &str) -> Result<Type, String> {
    if let Some(i) = v.as_u64() {
        return Ok(TypeInner::Var(format!("{prefix}{i}")).into());
    }
    let name = v.as_str().ok_or_else(|| format!("not a slot: {v}"))?;
    Ok(match name {
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
    }
    .into())
}

fn slots(v: &Value, prefix: &str) -> Result<Vec<Type>, String> {
    let items = v.as_array().ok_or_else(|| format!("not a list: {v}"))?;
    items.iter().map(|s| slot(s, prefix)).collect()
}

/// `[[key, slot], ...]`, with the key read by `key`.
fn pairs<K>(
    v: &Value,
    prefix: &str,
    key: impl Fn(&Value) -> Option<K>,
) -> Result<Vec<(K, Type)>, String> {
    let items = v.as_array().ok_or_else(|| format!("not a list: {v}"))?;
    items
        .iter()
        .map(|p| match p.as_array().map(Vec::as_slice) {
            Some([k, s]) => Ok((
                key(k).ok_or_else(|| format!("bad key: {k}"))?,
                slot(s, prefix)?,
            )),
            _ => Err(format!("not a pair: {p}")),
        })
        .collect()
}

fn fields(v: &Value, prefix: &str) -> Result<Vec<Field>, String> {
    let id = |k: &Value| k.as_u64().and_then(|n| u32::try_from(n).ok());
    Ok(pairs(v, prefix, id)?
        .into_iter()
        .map(|(id, ty)| Field {
            id: Label::Id(id).into(),
            ty,
        })
        .collect())
}

fn composite(v: &Value, prefix: &str) -> Result<Type, String> {
    let obj = v
        .as_object()
        .ok_or_else(|| format!("not a table entry: {v}"))?;
    let [(key, body)] = obj.iter().collect::<Vec<_>>()[..] else {
        return Err(format!("not a table entry: {v}"));
    };
    Ok(match key.as_str() {
        "opt" => TypeInner::Opt(slot(body, prefix)?),
        "vec" => TypeInner::Vec(slot(body, prefix)?),
        "record" => TypeInner::Record(fields(body, prefix)?),
        "variant" => TypeInner::Variant(fields(body, prefix)?),
        "func" => {
            let modes = body["annots"]
                .as_array()
                .ok_or("no \"annots\"")?
                .iter()
                .map(|a| match a.as_str() {
                    Some("query") => Ok(FuncMode::Query),
                    Some("oneway") => Ok(FuncMode::Oneway),
                    Some("composite_query") => Ok(FuncMode::CompositeQuery),
                    _ => Err(format!("unknown function annotation {a}")),
                })
                .collect::<Result<_, _>>()?;
            TypeInner::Func(Function {
                modes,
                args: slots(&body["args"], prefix)?,
                rets: slots(&body["rets"], prefix)?,
            })
        }
        "service" => TypeInner::Service(pairs(body, prefix, |k| k.as_str().map(str::to_string))?),
        k => return Err(format!("unknown table entry {k:?}")),
    }
    .into())
}
