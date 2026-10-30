//! A separately allocated but structurally equal subtree is reflexively a
//! subtype, so it must be accepted even when it is too deep to walk within the
//! recursion guard.
//!
//! De-quadratic subtype checking (#603) stopped running the deep `t1 == t2` at
//! every recursion level. A first cut detected equality only by pointer, which
//! missed separately allocated equal subtrees: one whose parents differ (so the
//! entry-point whole-type `==` cannot fire) was walked level by level into the
//! depth guard, turning a valid check into a "recursion limit exceeded" error
//! (PR #780 review). The per-level check is now a memoized deep equality, which
//! short-circuits such a subtree before it reaches the guard.
//!
//! The limit is reached at a depth that depends on the stack, not the types, so
//! each check runs on a thread with a fixed stack (as in
//! `subtype_recursion_limit.rs`) to make the depth predictable.

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

/// `vec^depth(leaf)`, freshly allocated so the trees share no node.
fn vec_chain(depth: usize, leaf: TypeInner) -> Type {
    let mut t: Type = leaf.into();
    for _ in 0..depth {
        t = TypeInner::Vec(t).into();
    }
    t
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

fn var(name: &str) -> Type {
    TypeInner::Var(name.to_string()).into()
}

fn hit_limit(errors: &[Incompatibility]) -> bool {
    errors.iter().any(|e| {
        e.message
            .to_lowercase()
            .contains("recursion limit exceeded")
    })
}

/// Shortest `vec^d(nat) <: vec^d(text)` that hits the limit on this thread: a
/// mismatched chain of this depth is walked straight into the guard, so it is a
/// depth at which an equal subtree would be too, were it not short-circuited.
fn shortest_overflowing_depth() -> usize {
    let overflows = |d: usize| {
        on_small_stack(move || {
            let env = TypeEnv::new();
            hit_limit(&subtype_check_all(
                &mut Gamma::new(),
                &env,
                &vec_chain(d, TypeInner::Nat),
                &vec_chain(d, TypeInner::Text),
            ))
        })
    };
    let mut hi = 64;
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

/// `record { 0: vec^d nat; 1: nat } <: record { 0: vec^d nat }` at a depth that
/// overflows. The shared field is separately allocated but equal; the records
/// differ, so the whole-type `==` fast path cannot fire. The equal field must
/// be accepted as reflexive, not driven into the guard.
#[test]
fn deep_equal_subtree_under_differing_parents_is_accepted() {
    let d = shortest_overflowing_depth();
    on_small_stack(move || {
        let env = TypeEnv::new();
        // Sanity: a mismatched chain of this depth really does reach the guard,
        // so the structural recursion is being driven that deep here.
        assert!(
            hit_limit(&subtype_check_all(
                &mut Gamma::new(),
                &env,
                &vec_chain(d, TypeInner::Nat),
                &vec_chain(d, TypeInner::Text),
            )),
            "expected the mismatched chain at depth {d} to hit the limit"
        );

        let t1 = record(vec![vec_chain(d, TypeInner::Nat), TypeInner::Nat.into()]);
        let t2 = record(vec![vec_chain(d, TypeInner::Nat)]);
        assert!(
            subtype(&mut Gamma::new(), &env, &t1, &t2).is_ok(),
            "equal deep subtree under differing parents must be accepted"
        );
        assert!(
            subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).is_empty(),
            "equal deep subtree under differing parents must report no incompatibility"
        );
    });
}

/// The same, but the equal subtree is reached through two different `Var`
/// aliases (`A` and `B`, each a separately allocated `vec^d nat`). The
/// entry-point `==` misses it because the aliases differ by name; after one
/// resolution step the per-level equality must still accept the resolved subtree
/// before it reaches the guard.
#[test]
fn equal_subtree_through_different_aliases_is_accepted() {
    let d = shortest_overflowing_depth();
    on_small_stack(move || {
        let mut env = TypeEnv::new();
        env.0.insert("A".into(), vec_chain(d, TypeInner::Nat));
        env.0.insert("B".into(), vec_chain(d, TypeInner::Nat));
        let t1 = record(vec![var("A"), TypeInner::Nat.into()]);
        let t2 = record(vec![var("B")]);
        assert!(
            subtype(&mut Gamma::new(), &env, &t1, &t2).is_ok(),
            "equal subtree via different aliases must be accepted"
        );
        assert!(
            subtype_check_all(&mut Gamma::new(), &env, &t1, &t2).is_empty(),
            "equal subtree via different aliases must report no incompatibility"
        );
    });
}
