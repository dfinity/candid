//! Loading a `.did` file takes time linear in its length, and stack that does
//! not grow with the length of an alias chain.
//!
//! The cycle check used to walk the whole chain again from every alias, which
//! is quadratic: 20,000 aliases took minutes. Validation followed each alias
//! recursively, so a long chain overflowed the stack and aborted the process.
//! Each test loads on a small stack, in which the old validation overflowed
//! at a few hundred aliases in a debug build.

use candid_parser::utils::CandidSource;

const STACK_SIZE: usize = 256 << 10;

const LINKS: usize = 20_000;

fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// `type t0 = {wrap}t1; …; type t{LINKS} = {last};` and a service using `t0`.
fn chain(wrap: &str, last: &str) -> String {
    let mut s = String::new();
    for i in 0..LINKS {
        s.push_str(&format!("type t{i} = {wrap}t{};\n", i + 1));
    }
    s.push_str(&format!("type t{LINKS} = {last};\n"));
    s.push_str("service : { f : (t0) -> (t0) }\n");
    s
}

fn load_err(text: String) -> String {
    on_small_stack(move || match CandidSource::Text(&text).load() {
        Ok(_) => panic!("expected the load to fail"),
        Err(e) => e.to_string(),
    })
}

#[test]
fn long_alias_chain_loads() {
    on_small_stack(|| {
        CandidSource::Text(&chain("", "nat")).load().unwrap();
    });
}

#[test]
fn long_opt_chain_loads() {
    on_small_stack(|| {
        CandidSource::Text(&chain("opt ", "nat")).load().unwrap();
    });
}

#[test]
fn long_alias_cycle_is_rejected() {
    let err = load_err(chain("", "t0"));
    assert!(err.contains("cyclic type definition"), "{err}");
}

#[test]
fn alias_cycle_not_through_the_first_name_is_rejected() {
    // `a` leads into the cycle `b = c = b` without being part of it.
    let err = load_err("type a = b; type b = c; type c = b; service : {}".to_string());
    assert!(err.contains("a has cyclic type definition"), "{err}");
}

#[test]
fn long_chain_to_a_bad_service_is_rejected() {
    // Validation still reaches the end of the chain: the service there has a
    // method whose type is not a function.
    let err = load_err(chain("opt ", "service { m : leaf };\ntype leaf = nat"));
    assert!(err.contains("not a function"), "{err}");
}
