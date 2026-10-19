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

/// `{prefix}0 = {prefix}1`, …, `{prefix}{len} = end`.
fn aliases(env: &mut TypeEnv, prefix: &str, len: usize, end: Type) {
    for i in 0..len {
        env.0
            .insert(format!("{prefix}{i}"), var(&format!("{prefix}{}", i + 1)));
    }
    env.0.insert(format!("{prefix}{len}"), end);
}

/// The message is `recursion limit exceeded` from the collector and
/// `Recursion limit exceeded at depth …` from type lookups.
fn hit_limit(errors: &[Incompatibility]) -> bool {
    errors.iter().any(|e| {
        e.message
            .to_lowercase()
            .contains("recursion limit exceeded")
    })
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
        let len = shortest - shortest / 8;
        let mut env = TypeEnv::new();
        chain(&mut env, "C", len, TypeInner::Nat.into());
        chain(&mut env, "D", len, TypeInner::Nat.into());
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

/// Field 0 proves `nat <: L0` and leaves it in `Gamma`. Field 1 reaches
/// `nat <: opt L0` below `k` wrappers: the probe `nat <: L0` is answered from
/// `Gamma`, and tracing the alias chain `L0` to see whether it is an `opt`
/// may then hit the limit. That must not count as passing the ordinary opt
/// rule, and field 2's `nat <: text` must still fail the check. Where exactly
/// the limit is hit depends on frame sizes, so try every `k` around it.
#[test]
fn overflow_while_tracing_an_alias_fails_the_check() {
    let shortest = shortest_overflowing_chain();
    on_small_stack(move || {
        let nat = || -> Type { TypeInner::Nat.into() };
        let t1 = record(vec![nat(), var("V0"), nat()]);
        let t2 = record(vec![var("L0"), var("W0"), TypeInner::Text.into()]);
        for k in 0..=2 * shortest {
            let mut env = TypeEnv::new();
            aliases(&mut env, "L", shortest / 2, nat());
            chain(&mut env, "V", k, record(vec![nat()]));
            chain(&mut env, "W", k, record(vec![opt(var("L0"))]));
            let errors = subtype_check_all(&mut Gamma::new(), &env, &t1, &t2);
            assert!(!errors.is_empty(), "k = {k}: passed");
            assert!(
                subtype(&mut Gamma::new(), &env, &t1, &t2).is_err(),
                "k = {k}: passed"
            );
        }
    });
}
