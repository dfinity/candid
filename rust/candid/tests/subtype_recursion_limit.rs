//! Hitting the recursion limit fails the whole check at once.
//!
//! Where the limit is hit depends on the stack, not on the types, so nothing
//! derived from such a failure may be cached, and an opt-rule probe that hits
//! it must not fall back to the special rule. Each test runs on a thread with
//! a fixed stack so that the limit is reached at a predictable depth.

use candid::types::internal::{Field, Label, Type, TypeInner};
use candid::types::subtype::{subtype, subtype_check_all, Gamma, Incompatibility};
use candid::types::TypeEnv;
use std::rc::Rc;

const STACK_SIZE: usize = 1 << 20;

fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

fn var(name: &str) -> Type {
    TypeInner::Var(name.to_string()).into()
}

fn opt(t: Type) -> Type {
    TypeInner::Opt(t).into()
}

fn record(fields: Vec<Type>) -> Type {
    TypeInner::Record(
        fields
            .into_iter()
            .enumerate()
            .map(|(id, ty)| Field {
                id: Rc::new(Label::Id(id as u32)),
                ty,
            })
            .collect(),
    )
    .into()
}

/// `{prefix}0 = record { {prefix}1 }`, …, `{prefix}{len} = end`.
fn chain(env: &mut TypeEnv, prefix: &str, len: usize, end: Type) {
    for i in 0..len {
        env.0.insert(
            format!("{prefix}{i}"),
            record(vec![var(&format!("{prefix}{}", i + 1))]),
        );
    }
    env.0.insert(format!("{prefix}{len}"), end);
}

fn hit_limit(errors: &[Incompatibility]) -> bool {
    errors
        .iter()
        .any(|e| e.message.contains("recursion limit exceeded"))
}

/// The shortest chain `C <: D` that hits the limit on this thread.
fn shortest_overflowing_chain() -> usize {
    let overflows = |len: usize| {
        on_small_stack(move || {
            let mut env = TypeEnv::new();
            chain(&mut env, "C", len, TypeInner::Nat.into());
            chain(&mut env, "D", len, TypeInner::Nat.into());
            hit_limit(&subtype_check_all(
                &mut Gamma::new(),
                &env,
                &var("C0"),
                &var("D0"),
            ))
        })
    };
    let mut hi = 16;
    while !overflows(hi) {
        hi *= 2;
    }
    let mut lo = hi / 2 + 1;
    while lo < hi {
        let mid = (lo + hi) / 2;
        if overflows(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

/// `A_i = record { opt A_{i+1}; opt A_{i+1}; C0 }`, ending in `nat`, against
/// the same shape ending in `text`, where `C0 <: D0` only fails by hitting the
/// limit. Each probe of `opt A_{i+1}` fails that way; if such failures were
/// re-explored on every path this would take 2^64 steps.
#[test]
fn probe_that_hits_the_limit_fails_the_check() {
    let len = shortest_overflowing_chain() * 2;
    on_small_stack(move || {
        let depth = 64;
        let mut env = TypeEnv::new();
        for (a, c, leaf) in [("A", "C", TypeInner::Nat), ("B", "D", TypeInner::Text)] {
            for i in 0..depth {
                let next = var(&format!("{a}{}", i + 1));
                env.0.insert(
                    format!("{a}{i}"),
                    record(vec![opt(next.clone()), opt(next), var(&format!("{c}0"))]),
                );
            }
            env.0.insert(format!("{a}{depth}"), leaf.into());
            chain(&mut env, c, len, TypeInner::Nat.into());
        }
        let errors = subtype_check_all(&mut Gamma::new(), &env, &var("A0"), &var("B0"));
        assert!(hit_limit(&errors), "{errors:?}");
        assert!(subtype(&mut Gamma::new(), &env, &var("A0"), &var("B0")).is_err());
    });
}

/// `X <: Y` holds, but checking it needs almost the whole stack. Field 0
/// reaches it below a wrapper chain and hits the limit inside it; field 1
/// reaches it directly. Field 1 must not be reported as a known failure
/// (`… (see above)`).
#[test]
fn pair_that_hit_the_limit_is_not_reported_as_incompatible() {
    let shortest = shortest_overflowing_chain();
    on_small_stack(move || {
        let mut env = TypeEnv::new();
        chain(&mut env, "C", shortest - shortest / 8, TypeInner::Nat.into());
        chain(&mut env, "D", shortest - shortest / 8, TypeInner::Nat.into());
        env.0.insert("X".into(), record(vec![var("C0")]));
        env.0.insert("Y".into(), record(vec![var("D0")]));
        chain(&mut env, "V", shortest / 2, var("X"));
        chain(&mut env, "W", shortest / 2, var("Y"));
        assert!(subtype_check_all(&mut Gamma::new(), &env, &var("X"), &var("Y")).is_empty());

        let t1 = record(vec![var("V0"), var("X")]);
        let t2 = record(vec![var("W0"), var("Y")]);
        let errors = subtype_check_all(&mut Gamma::new(), &env, &t1, &t2);
        assert!(hit_limit(&errors), "{errors:?}");
        assert!(
            !errors.iter().any(|e| e.message.contains("(see above)")),
            "{errors:?}"
        );
    });
}
