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

use candid::types::internal::{Type, TypeInner};
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
