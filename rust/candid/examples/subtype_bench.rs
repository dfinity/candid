//! Micro-benchmark for issue #603: quadratic subtype traversal.
//!
//! Builds deeply nested `vec` types and times `subtype` for growing depth.
//! Three workloads:
//! - widening  : vec^d(nat) <: vec^d(int)  -> succeeds (Nat <: Int at leaf)
//! - rejection : vec^d(nat) <: vec^d(text) -> fails at the leaf
//! - equal     : vec^d(nat) <: vec^d(nat)  -> succeeds, two separately allocated
//!   but structurally equal trees (the case the naive ptr_eq patch regressed)
//!
//! BEFORE the fix, widening/rejection are O(depth^2) (the `t1 == t2` deep
//! structural compare runs at every recursion level). `equal` is O(depth) via
//! the deep-compare short-circuit and is the regression guard.
//!
//! Run: cargo run --release --example subtype_bench

use candid::types::subtype::{subtype, Gamma};
use candid::types::{Type, TypeEnv, TypeInner};
use std::time::Instant;

/// vec^depth(leaf), freshly allocated each call.
fn nest(depth: usize, leaf: TypeInner) -> Type {
    let mut t: Type = leaf.into();
    for _ in 0..depth {
        t = TypeInner::Vec(t).into();
    }
    t
}

/// Median per-operation time in nanoseconds, over `runs` runs of `iters` ops.
fn bench<F: FnMut()>(iters: u64, runs: usize, mut f: F) -> f64 {
    let mut samples: Vec<f64> = Vec::with_capacity(runs);
    for _ in 0..runs {
        let start = Instant::now();
        for _ in 0..iters {
            f();
        }
        let elapsed = start.elapsed().as_nanos() as f64;
        samples.push(elapsed / iters as f64);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    samples[samples.len() / 2]
}

fn run_case(name: &str, t1: &Type, t2: &Type, expect_ok: bool, iters: u64, runs: usize) -> f64 {
    let env = TypeEnv::new();
    // Sanity: confirm the subtype relation is what we expect, so a "fast"
    // number is never fast because it short-circuited the wrong way.
    let mut g: Gamma = Gamma::new();
    let ok = subtype(&mut g, &env, t1, t2).is_ok();
    assert_eq!(ok, expect_ok, "{name}: unexpected subtype result");
    bench(iters, runs, || {
        let mut gamma: Gamma = Gamma::new();
        let _ = subtype(&mut gamma, &env, t1, t2);
    })
}

fn main() {
    let runs = 9;
    let depths = [16usize, 32, 64, 128, 256, 384, 512];
    let env_leaf = TypeEnv::new();
    let _ = &env_leaf;

    println!("# subtype_bench (issue #603)  median ns/op over {runs} runs");
    println!();
    for (name, build) in [
        (
            "widening  vec^d(nat) <: vec^d(int)",
            Box::new(|d: usize| (nest(d, TypeInner::Nat), nest(d, TypeInner::Int), true))
                as Box<dyn Fn(usize) -> (Type, Type, bool)>,
        ),
        (
            "rejection vec^d(nat) <: vec^d(text)",
            Box::new(|d: usize| (nest(d, TypeInner::Nat), nest(d, TypeInner::Text), false)),
        ),
        (
            "equal     vec^d(nat) <: vec^d(nat)",
            Box::new(|d: usize| (nest(d, TypeInner::Nat), nest(d, TypeInner::Nat), true)),
        ),
    ] {
        println!("## {name}");
        println!("{:>6} | {:>14} | {:>14}", "depth", "ns/op", "ns/op/depth");
        println!("{:->6}-+-{:-<14}-+-{:-<14}", "", "", "");
        for &d in &depths {
            let (t1, t2, ok) = build(d);
            // Scale iterations so each run is a meaningful duration regardless
            // of how fast the operation is; fewer iters for the slow BEFORE
            // deep-nesting cases, more for the fast ones.
            let iters: u64 = (2_000_000 / (d as u64 * d as u64 / 16 + 1)).clamp(200, 200_000);
            let ns = run_case(name, &t1, &t2, ok, iters, runs);
            println!("{d:>6} | {ns:>14.1} | {:>14.3}", ns / d as f64);
        }
        println!();
    }
}
