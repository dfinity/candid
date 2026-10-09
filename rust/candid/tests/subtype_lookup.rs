//! A type variable that fails to resolve during a subtype or equality check is
//! an error, and that error leaves no trace in the `Gamma` the check shares
//! with its later steps.

use candid::types::internal::{Field, Label, Type, TypeInner};
use candid::types::subtype::{equal, subtype, subtype_check_all, Gamma};
use candid::types::TypeEnv;
use std::rc::Rc;

fn unbound() -> Type {
    TypeInner::Var("unbound".to_string()).into()
}

fn record(fields: Vec<(&str, Type)>) -> Type {
    TypeInner::Record(
        fields
            .into_iter()
            .map(|(name, ty)| Field {
                id: Rc::new(Label::Named(name.to_string())),
                ty,
            })
            .collect(),
    )
    .into()
}

#[test]
fn unresolved_variable_is_an_error() {
    let env = TypeEnv::new();
    let nat: Type = TypeInner::Nat.into();
    assert!(subtype(&mut Gamma::new(), &env, &unbound(), &nat).is_err());
    assert!(subtype(&mut Gamma::new(), &env, &nat, &unbound()).is_err());
    assert!(equal(&mut Gamma::new(), &env, &unbound(), &nat).is_err());
    assert!(equal(&mut Gamma::new(), &env, &nat, &unbound()).is_err());
    assert!(!subtype_check_all(&mut Gamma::new(), &env, &unbound(), &nat).is_empty());
    assert!(!subtype_check_all(&mut Gamma::new(), &env, &nat, &unbound()).is_empty());
}

/// Field `a` probes `unbound <: nat` under an `opt`, where a failure is
/// tolerated by the special opt rule. Field `b` then asks the same question
/// directly, and must not find a stale coinductive assumption from the probe.
#[test]
fn failed_lookup_leaves_no_assumption_behind() {
    let env = TypeEnv::new();
    let nat: Type = TypeInner::Nat.into();
    let t1 = record(vec![
        ("a", TypeInner::Opt(unbound()).into()),
        ("b", unbound()),
    ]);
    let t2 = record(vec![("a", TypeInner::Opt(nat.clone()).into()), ("b", nat)]);
    assert!(subtype(&mut Gamma::new(), &env, &t1, &t2).is_err());
    assert!(!subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).is_empty());
}
