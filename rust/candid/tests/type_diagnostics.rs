//! A diagnostic naming a wire type stays bounded, whatever shape that type has.
//!
//! What it costs to render a type follows that type's own width and depth, and a wire
//! type is chosen by the sender, so a mismatch has to describe one without letting its
//! shape decide the cost of the description.
//!
//! These decode on a thread given only a modest amount of room, so that a diagnostic
//! whose cost tracked the type would be caught here rather than in production.

use candid::types::value::{IDLField, IDLValue};
use candid::types::Label;
use candid::{CandidType, Decode, DecoderConfig, IDLArgs};
use serde::Deserialize;

/// Wide enough that rendering the type would dwarf any real interface.
const WIDE: u32 = 250_000;
const SMALL_STACK: usize = 1024 * 1024;
/// A bounded diagnostic. Rendering an outsized type in full runs far past this.
const SANE_LEN: usize = 4096;
/// Marker the decoder substitutes for a type too large to render.
const ELIDED: &str = "type elided";

fn record(mut fields: Vec<IDLField>) -> IDLValue {
    fields.sort_by_key(|f| f.id.get_id());
    IDLValue::Record(fields)
}
fn field(name: &str, val: IDLValue) -> IDLField {
    IDLField {
        id: Label::Named(name.to_string()),
        val,
    }
}
fn wide_record() -> IDLValue {
    record(
        (0..WIDE)
            .map(|id| IDLField {
                id: Label::Id(id),
                val: IDLValue::Int8(0),
            })
            .collect(),
    )
}

/// The header of these payloads is itself far over the default header bound, which
/// would reject them before any diagnostic is built. Raise it so that what is under
/// test is the diagnostic, not the bound.
fn config(full_error_message: bool) -> DecoderConfig {
    let mut c = DecoderConfig::new();
    c.set_skipping_quota(10_000)
        .set_full_error_message(full_error_message)
        .set_max_header_len(usize::MAX);
    c
}

/// Runs `f` with a modest amount of room, propagating a failure to the test.
fn on_small_stack<F: FnOnce() + Send + 'static>(f: F) {
    let h = std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(f)
        .unwrap();
    h.join()
        .expect("decode did not complete within the room given");
}

/// `verbose` mirrors `full_error_message`: it asks for the raw input to be included,
/// which is proportional to the message by design. What must hold either way is that
/// no *type* is rendered in full, since that is what makes the cost unbounded.
fn check_bounded(label: &'static str, verbose: bool, err: candid::Error) {
    let rendered = err.to_string();
    if verbose {
        assert!(
            rendered.contains(ELIDED),
            "{label}: an outsized type should be elided, got {} chars starting {:?}",
            rendered.len(),
            rendered.chars().take(120).collect::<String>()
        );
    } else {
        assert!(
            rendered.len() < SANE_LEN,
            "{label}: diagnostic ran to {} chars",
            rendered.len()
        );
    }
    // Discarding the error is part of its cost, so account for it here too.
    drop(err);
}

/// A required `int` field given a very wide record. This one is reached whatever the
/// `full_error_message` setting, so both are covered.
#[test]
fn an_outsized_wire_type_against_int() {
    #[derive(CandidType, Deserialize, Debug)]
    struct WantsI128 {
        amount: i128,
        tag: u8,
    }
    for full in [false, true] {
        let payload = IDLArgs::new(&[record(vec![
            field("amount", wide_record()),
            field("tag", IDLValue::Nat8(1)),
        ])])
        .to_bytes()
        .unwrap();
        let cfg = config(full);
        on_small_stack(move || {
            let err = Decode!([cfg]; &payload, WantsI128).expect_err("a record is not an int");
            check_bounded("int", full, err);
        });
    }
}

/// A required `nat16` field given a very wide record, the shape a canister HTTP
/// response takes.
#[test]
fn an_outsized_wire_type_against_nat16() {
    #[derive(CandidType, Deserialize, Debug)]
    struct Response {
        status_code: u16,
        body: Vec<u8>,
    }
    for full in [false, true] {
        let payload = IDLArgs::new(&[record(vec![
            field("status_code", wide_record()),
            field("body", IDLValue::Blob(vec![])),
        ])])
        .to_bytes()
        .unwrap();
        let cfg = config(full);
        on_small_stack(move || {
            let err = Decode!([cfg]; &payload, Response).expect_err("a record is not a nat16");
            check_bounded("nat16", full, err);
        });
    }
}

/// A required function reference given a very wide record.
#[test]
fn an_outsized_wire_type_against_a_func() {
    candid::define_function!(TransformFunc : (Vec<u8>) -> (Vec<u8>) query);
    #[derive(CandidType, Deserialize, Debug)]
    struct Transform {
        function: TransformFunc,
        context: Vec<u8>,
    }
    for full in [false, true] {
        let payload = IDLArgs::new(&[record(vec![
            field("function", wide_record()),
            field("context", IDLValue::Blob(vec![])),
        ])])
        .to_bytes()
        .unwrap();
        let cfg = config(full);
        on_small_stack(move || {
            let err = Decode!([cfg]; &payload, Transform).expect_err("a record is not a func");
            check_bounded("func", full, err);
        });
    }
}

/// The default configuration, which off-wasm asks for verbose errors, must be bounded
/// as well.
#[test]
fn the_default_configuration_is_bounded() {
    #[derive(CandidType, Deserialize, Debug)]
    struct WantsI128 {
        amount: i128,
    }
    let payload = IDLArgs::new(&[record(vec![field("amount", wide_record())])])
        .to_bytes()
        .unwrap();
    let mut cfg = DecoderConfig::new();
    cfg.set_max_header_len(usize::MAX);
    // the default asks for verbose errors off-wasm and terse ones on wasm
    let cfg_verbose = !cfg!(target_arch = "wasm32");
    on_small_stack(move || {
        let err = Decode!([cfg]; &payload, WantsI128).expect_err("a record is not an int");
        check_bounded("default config", cfg_verbose, err);
    });
}

/// Eliding an outsized type must not cost the ordinary case its detail: a small
/// mismatch still names both types.
#[test]
fn ordinary_mismatches_still_name_their_types() {
    let payload = IDLArgs::new(&[IDLValue::Text("x".to_string())])
        .to_bytes()
        .unwrap();
    let e = Decode!([config(false)]; &payload, u32)
        .expect_err("text is not a nat32")
        .to_string();
    assert!(
        e.contains("text") && e.contains("nat32"),
        "an ordinary mismatch should still name both types, got: {e}"
    );
}

/// A service constructor has no rendering of its own. Naming one in a diagnostic must
/// still produce an error rather than asking the printer for the impossible.
#[test]
fn a_service_constructor_is_elided_not_rendered() {
    use candid::types::internal::{Type, TypeInner};
    use candid::types::subtype::{equal, Gamma};
    use candid::types::TypeEnv;

    let serv: Type = TypeInner::Service(vec![("m".to_string(), TypeInner::Nat.into())]).into();
    let class: Type = TypeInner::Class(vec![TypeInner::Nat.into()], serv).into();
    let other: Type = TypeInner::Text.into();

    let env = TypeEnv::new();
    let mut gamma = Gamma::new();
    let e = equal(&mut gamma, &env, &class, &other)
        .expect_err("a service constructor is not equal to text")
        .to_string();
    assert!(
        e.contains(ELIDED),
        "a service constructor should be elided, got: {e}"
    );
}
