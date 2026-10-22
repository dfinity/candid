//! A pair proved while assuming another pair does not outlive that assumption.
//!
//! The opt rule probes `t <: t'` and falls back to the special rule when the
//! probe fails. Pairs proved inside the probe may have been proved *from* the
//! pair that then failed, so they must leave `Gamma` with it; otherwise a later
//! comparison is answered from them.

use candid::types::internal::{Field, Label, Type, TypeInner};
use candid::types::subtype::{subtype, subtype_check_all, Gamma};
use candid::types::TypeEnv;
use std::rc::Rc;

fn var(name: &str) -> Type {
    TypeInner::Var(name.to_string()).into()
}

fn record(fields: Vec<(u32, Type)>) -> Type {
    TypeInner::Record(
        fields
            .into_iter()
            .map(|(id, ty)| Field {
                id: Rc::new(Label::Id(id)),
                ty,
            })
            .collect(),
    )
    .into()
}

/// ```text
/// X  = record { 0 : X2; 1 : nat }     Y  = record { 0 : Y2; 1 : text }
/// X2 = record { 0 : X }               Y2 = record { 0 : Y }
/// ```
///
/// `X2 <: Y2` needs `X <: Y`, which needs `nat <: text`, so neither holds.
fn env() -> TypeEnv {
    let mut env = TypeEnv::new();
    let nat = TypeInner::Nat.into();
    let text = TypeInner::Text.into();
    env.0
        .insert("X".into(), record(vec![(0, var("X2")), (1, nat)]));
    env.0.insert("X2".into(), record(vec![(0, var("X"))]));
    env.0
        .insert("Y".into(), record(vec![(0, var("Y2")), (1, text)]));
    env.0.insert("Y2".into(), record(vec![(0, var("Y"))]));
    env
}

/// Field 0 probes `X <: Y` under an `opt`. The probe assumes `X <: Y`, proves
/// `X2 <: Y2` from it, and then fails on `nat <: text`. Field 1 asks
/// `X2 <: Y2` directly and must not find it already proved.
#[test]
fn failed_opt_probe_leaves_no_derived_assumption() {
    let env = env();
    let t1 = record(vec![(0, var("X")), (1, var("X2"))]);
    let t2 = record(vec![(0, TypeInner::Opt(var("Y")).into()), (1, var("Y2"))]);
    assert!(subtype(&mut Gamma::new(), &env, &var("X2"), &var("Y2")).is_err());
    assert!(subtype(&mut Gamma::new(), &env, &t1, &t2).is_err());
    assert!(!subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).is_empty());
}

/// A failed check leaves nothing in a `Gamma` that a later check reuses, as
/// the decoder does across the arguments of one message.
#[test]
fn failed_check_leaves_no_derived_assumption() {
    let env = env();
    let mut gamma = Gamma::new();
    assert!(subtype(&mut gamma, &env, &var("X"), &var("Y")).is_err());
    assert!(subtype(&mut gamma, &env, &var("X2"), &var("Y2")).is_err());

    let mut gamma = Gamma::new();
    assert!(!subtype_check_all(&mut gamma, &env, &var("X"), &var("Y")).is_empty());
    assert!(subtype(&mut gamma, &env, &var("X2"), &var("Y2")).is_err());
}
