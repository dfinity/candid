//! The subtype check takes time linear in the depth of an opt chain.
//!
//! The special opt rule `t <: opt t'` probes `t <: t'` only when `t'` is not
//! `null`, `reserved` or an `opt`. When it probed first and tested that side
//! condition after, every level of an `opt` chain probed a fresh pair whose
//! answer was then thrown away, and comparing two chains that differ at the
//! leaf explored every pair of levels: about 2n² steps, which took seconds
//! for a chain of a thousand aliases and minutes for a few thousand. These
//! tests use chains long enough that the quadratic version takes minutes in a
//! debug build, and fail if a check takes more than `LIMIT`, which is over a
//! hundred times what the linear version needs.

use candid::types::internal::{Field, Label, Type, TypeInner};
use candid::types::subtype::{subtype_check_all, subtype_with_config, Gamma, OptReport};
use candid::types::TypeEnv;
use std::time::{Duration, Instant};

/// Enough stack that these chains never reach the recursion limit, so the
/// tests measure the work and not where the stack runs out.
const STACK_SIZE: usize = 64 << 20;

/// Aliases in each chain, and `opt`s in each alias.
const LINKS: usize = 2000;
const OPTS: usize = 2;

const LIMIT: Duration = Duration::from_secs(20);

fn on_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    let start = Instant::now();
    let res = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
    let elapsed = start.elapsed();
    assert!(elapsed < LIMIT, "took {elapsed:?}");
    res
}

fn var(name: &str) -> Type {
    TypeInner::Var(name.to_string()).into()
}

/// `{prefix}0 = opt … opt {prefix}1`, …, `{prefix}{LINKS} = leaf`.
fn opt_chain(env: &mut TypeEnv, prefix: &str, leaf: TypeInner) -> Type {
    for i in 0..LINKS {
        let mut t = var(&format!("{prefix}{}", i + 1));
        for _ in 0..OPTS {
            t = TypeInner::Opt(t).into();
        }
        env.0.insert(format!("{prefix}{i}"), t);
    }
    env.0.insert(format!("{prefix}{LINKS}"), leaf.into());
    var(&format!("{prefix}0"))
}

/// Two chains of the same shape whose leaves are `int` and `nat`, so that
/// `int_chain <: nat_chain` fails only at the leaf.
fn chains() -> (TypeEnv, Type, Type) {
    let mut env = TypeEnv::new();
    let ints = opt_chain(&mut env, "i", TypeInner::Int);
    let nats = opt_chain(&mut env, "n", TypeInner::Nat);
    (env, ints, nats)
}

#[test]
fn failing_opt_chains_error() {
    on_big_stack(|| {
        let (env, ints, nats) = chains();
        let err = subtype_with_config(OptReport::Error, &mut Gamma::new(), &env, &ints, &nats)
            .unwrap_err()
            .to_string();
        assert!(!err.contains("Recursion limit"), "{err}");
        // The other direction holds without the special rule.
        subtype_with_config(OptReport::Error, &mut Gamma::new(), &env, &nats, &ints).unwrap();
    });
}

#[test]
fn failing_opt_chains_silence() {
    on_big_stack(|| {
        let (env, ints, nats) = chains();
        // The special rule accepts it, after probing the chain.
        subtype_with_config(OptReport::Silence, &mut Gamma::new(), &env, &ints, &nats).unwrap();
    });
}

#[test]
fn failing_opt_chains_check_all() {
    on_big_stack(|| {
        let (env, ints, nats) = chains();
        let errors = subtype_check_all(&mut Gamma::new(), &env, &ints, &nats);
        assert!(
            errors
                .iter()
                .all(|e| !e.message.contains("recursion limit")),
            "{errors:?}"
        );
    });
}

/// `a0 = a1 = … = a{LONG} = leaf`, a chain of aliases with nothing in between.
const LONG: usize = 20_000;

/// Fields in each record below. Checking whether `a0` is `null`, `reserved`
/// or an `opt` walks its chain; doing that once per field would take
/// `FIELDS × LONG` steps, so the answer is kept for the rest of the check.
const FIELDS: usize = 20_000;

fn alias_chain(leaf: TypeInner) -> TypeEnv {
    let mut env = TypeEnv::new();
    for i in 0..LONG {
        env.0.insert(format!("a{i}"), var(&format!("a{}", i + 1)));
    }
    env.0.insert(format!("a{LONG}"), leaf.into());
    env
}

fn record(n: usize, ty: impl Fn() -> Type) -> Type {
    TypeInner::Record(
        (0..n as u32)
            .map(|i| Field {
                id: Label::Id(i).into(),
                ty: ty(),
            })
            .collect(),
    )
    .into()
}

/// `record { 0 : bool; … }` against `record { 0 : opt a0; … }`.
fn bools_against_opts(leaf: TypeInner) -> (TypeEnv, Type, Type) {
    let bools = record(FIELDS, || TypeInner::Bool.into());
    let opts = record(FIELDS, || TypeInner::Opt(var("a0")).into());
    (alias_chain(leaf), bools, opts)
}

/// `record {}` against `record { 0 : a0; … }`: every field is missing.
fn missing_fields(leaf: TypeInner) -> (TypeEnv, Type, Type) {
    let empty = record(0, || unreachable!());
    let fields = record(FIELDS, || var("a0"));
    (alias_chain(leaf), empty, fields)
}

/// The special rule accepts every field, in both kinds of check.
fn special_rule_accepts((env, t1, t2): (TypeEnv, Type, Type)) {
    subtype_with_config(OptReport::Silence, &mut Gamma::new(), &env, &t1, &t2).unwrap();
    let errors = subtype_check_all(&mut Gamma::new(), &env, &t1, &t2);
    assert!(errors.is_empty(), "{:?}", &errors[..1]);
}

#[test]
fn probe_refuted_against_long_alias_chain() {
    // `bool <: a0` fails, so the probe is refuted for the later fields.
    on_big_stack(|| special_rule_accepts(bools_against_opts(TypeInner::Nat)));
}

#[test]
fn probe_skipped_against_long_alias_chain() {
    // `a0` is `null`, so the side condition fails and nothing is probed.
    on_big_stack(|| special_rule_accepts(bools_against_opts(TypeInner::Null)));
}

#[test]
fn probe_holds_against_long_alias_chain() {
    // `bool <: a0` holds, and stays assumed for the later fields.
    on_big_stack(|| {
        let (env, t1, t2) = bools_against_opts(TypeInner::Bool);
        subtype_with_config(OptReport::Error, &mut Gamma::new(), &env, &t1, &t2).unwrap();
        assert!(subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).is_empty());
    });
}

#[test]
fn missing_fields_typed_by_long_alias_chain() {
    on_big_stack(|| {
        // Each missing field may be left out: `a0` is an `opt`.
        let (env, t1, t2) = missing_fields(TypeInner::Opt(TypeInner::Nat.into()));
        subtype_with_config(OptReport::Error, &mut Gamma::new(), &env, &t1, &t2).unwrap();
        assert!(subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).is_empty());
        // Each one is required: `a0` is `nat`, so all are reported.
        let (env, t1, t2) = missing_fields(TypeInner::Nat);
        subtype_with_config(OptReport::Error, &mut Gamma::new(), &env, &t1, &t2).unwrap_err();
        assert_eq!(
            subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).len(),
            FIELDS
        );
    });
}
