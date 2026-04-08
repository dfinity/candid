use candid::types::subtype::{format_report, Incompatibility};
use candid_parser::utils::{service_compatibility_report, service_compatible, CandidSource};

// ---------------------------------------------------------------------------
//  Helpers
// ---------------------------------------------------------------------------

fn check_compatible(new: &str, old: &str, desc: &str) {
    service_compatible(CandidSource::Text(new), CandidSource::Text(old))
        .unwrap_or_else(|e| panic!("[{desc}] expected compatible, got error: {e}"));
}

fn check_incompatible(new: &str, old: &str, desc: &str) {
    assert!(
        service_compatible(CandidSource::Text(new), CandidSource::Text(old)).is_err(),
        "[{desc}] expected incompatible, but check passed"
    );
}

fn get_errors(new: &str, old: &str) -> Vec<Incompatibility> {
    service_compatibility_report(CandidSource::Text(new), CandidSource::Text(old))
        .expect("failed to load interfaces")
}

fn error_strings(new: &str, old: &str) -> Vec<String> {
    get_errors(new, old)
        .into_iter()
        .map(|e| e.to_string())
        .collect()
}

// ===========================================================================
//  Backward-compatible changes must PASS (no false positives)
// ===========================================================================

#[test]
fn compatible_service_changes() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "identical service",
            "service : { greet : (text) -> (text) }",
            "service : { greet : (text) -> (text) }",
        ),
        (
            "add new method",
            "service : { greet : (text) -> (text); hello : () -> (text) }",
            "service : { greet : (text) -> (text) }",
        ),
        (
            "widen input nat→int (contravariant)",
            "service : { pay : (int) -> () }",
            "service : { pay : (nat) -> () }",
        ),
        (
            "narrow return int→nat (covariant, nat <: int)",
            "service : { get : () -> (nat) }",
            "service : { get : () -> (int) }",
        ),
    ];
    for &(desc, new, old) in cases {
        check_compatible(new, old, desc);
    }
}

#[test]
fn compatible_record_field_changes() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "add opt field to input record",
            "type R = record { name : text; age : opt nat }; service : { f : (R) -> () }",
            "type R = record { name : text }; service : { f : (R) -> () }",
        ),
        (
            "add opt field to return record",
            "type R = record { id : nat; extra : opt text }; service : { f : () -> (R) }",
            "type R = record { id : nat }; service : { f : () -> (R) }",
        ),
        (
            "add null field to return record",
            "service : { f : () -> (record { a : nat; b : null }) }",
            "service : { f : () -> (record { a : nat }) }",
        ),
        (
            "add reserved field to return record",
            "service : { f : () -> (record { a : nat; b : reserved }) }",
            "service : { f : () -> (record { a : nat }) }",
        ),
        (
            "remove non-opt field from input record (extra fields in subtype are fine)",
            "type R = record { name : text }; service : { f : (R) -> () }",
            "type R = record { name : text; age : nat }; service : { f : (R) -> () }",
        ),
    ];
    for &(desc, new, old) in cases {
        check_compatible(new, old, desc);
    }
}

#[test]
fn compatible_variant_and_vec_changes() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "add variant case to input (contravariant: old callers still match)",
            "type V = variant { a; b; c }; service : { f : (V) -> () }",
            "type V = variant { a; b }; service : { f : (V) -> () }",
        ),
        (
            "identical vec types",
            "service : { f : () -> (vec nat) }",
            "service : { f : () -> (vec nat) }",
        ),
    ];
    for &(desc, new, old) in cases {
        check_compatible(new, old, desc);
    }
}

// ===========================================================================
//  Backward-INCOMPATIBLE changes must be caught (no false negatives)
// ===========================================================================

#[test]
fn incompatible_method_changes() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "remove method",
            "service : { greet : (text) -> (text) }",
            "service : { greet : (text) -> (text); hello : () -> (text) }",
        ),
        (
            "change func mode query→update",
            "service : { get : () -> (nat) }",
            "service : { get : () -> (nat) query }",
        ),
        (
            "change return type nat→text",
            "service : { get : () -> (text) }",
            "service : { get : () -> (nat) }",
        ),
        (
            "change input type nat→text",
            "service : { set : (text) -> () }",
            "service : { set : (nat) -> () }",
        ),
        (
            "widen return nat→int (covariant: int </: nat)",
            "service : { get : () -> (int) }",
            "service : { get : () -> (nat) }",
        ),
    ];
    for &(desc, new, old) in cases {
        check_incompatible(new, old, desc);
    }
}

#[test]
fn incompatible_record_and_variant_changes() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "add required field to input record",
            "type R = record { name : text; age : nat }; service : { f : (R) -> () }",
            "type R = record { name : text }; service : { f : (R) -> () }",
        ),
        (
            "remove required field from return record",
            "type R = record { name : text }; service : { f : () -> (R) }",
            "type R = record { name : text; age : nat }; service : { f : () -> (R) }",
        ),
        (
            "remove variant case from input (old callers may send it)",
            "type V = variant { start; stop }; service : { f : (V) -> () }",
            "type V = variant { start; stop; pause }; service : { f : (V) -> () }",
        ),
        (
            "change vec element type",
            "service : { f : () -> (vec text) }",
            "service : { f : () -> (vec nat) }",
        ),
    ];
    for &(desc, new, old) in cases {
        check_incompatible(new, old, desc);
    }
}

// ===========================================================================
//  ALL incompatibilities collected (not just the first)
// ===========================================================================

#[test]
fn collects_all_incompatible_methods() {
    let old = r#"service : {
        method_a : (nat) -> (nat);
        method_b : (text) -> (text);
        method_c : () -> (nat);
        method_d : () -> ();
    }"#;
    // method_a: OK, method_b: removed, method_c: return changed, method_d: removed
    let new = r#"service : {
        method_a : (nat) -> (nat);
        method_c : () -> (text);
    }"#;
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 3, "got: {errors:?}");

    let joined = errors.join("\n");
    for name in ["method_b", "method_c", "method_d"] {
        assert!(joined.contains(name), "missing {name} in: {joined}");
    }
    assert!(
        !joined.contains("method_a"),
        "method_a is compatible, should not appear: {joined}"
    );
}

#[test]
fn collects_all_incompatible_record_fields() {
    let old = "type R = record { a : nat; b : text; c : bool }; service : { f : () -> (R) }";
    let new = "type R = record { a : text; b : nat; c : bool }; service : { f : () -> (R) }";
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 2, "got: {errors:?}");

    let joined = errors.join("\n");
    assert!(
        joined.contains("record field a"),
        "missing field a: {joined}"
    );
    assert!(
        joined.contains("record field b"),
        "missing field b: {joined}"
    );
}

#[test]
fn collects_both_input_and_return_errors() {
    let old = "service : { call : (nat) -> (nat) }";
    let new = "service : { call : (text) -> (bool) }";
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 2, "got: {errors:?}");

    let joined = errors.join("\n");
    assert!(
        joined.contains("input type"),
        "missing input error: {joined}"
    );
    assert!(
        joined.contains("return type"),
        "missing return error: {joined}"
    );
}

#[test]
fn collects_variant_field_errors() {
    // Old callers may send variant cases b or c; new input must accept them
    let old = "type V = variant { a; b; c }; service : { f : (V) -> () }";
    let new = "type V = variant { a }; service : { f : (V) -> () }";
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 2, "got: {errors:?}");

    let joined = errors.join("\n");
    assert!(joined.contains("b"), "missing variant b: {joined}");
    assert!(joined.contains("c"), "missing variant c: {joined}");
}

// ===========================================================================
//  Error message quality + path context
// ===========================================================================

#[test]
fn missing_method_error_is_clear() {
    let old = "service : { transfer : (nat) -> (); balance : () -> (nat) }";
    let new = "service : { balance : () -> (nat) }";
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 1);
    assert!(errors[0].contains("transfer"), "should name the method");
    assert!(errors[0].contains("missing"), "should say 'missing'");
}

#[test]
fn type_mismatch_error_names_both_types() {
    let old = "service : { f : () -> (nat) }";
    let new = "service : { f : () -> (text) }";
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 1);
    assert!(
        errors[0].contains("text") && errors[0].contains("nat"),
        "should mention both types: {}",
        errors[0]
    );
}

#[test]
fn missing_required_field_error_is_clear() {
    let old = "type R = record { name : text; age : nat }; service : { f : () -> (R) }";
    let new = "type R = record { name : text }; service : { f : () -> (R) }";
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 1);
    let msg = &errors[0];
    assert!(msg.contains("age"), "should mention field name: {msg}");
    assert!(
        msg.contains("missing") || msg.contains("not optional"),
        "should explain the problem: {msg}"
    );
}

#[test]
fn nested_path_shows_full_context() {
    let old = r#"
        type Inner = record { x : nat };
        type Outer = record { inner : Inner };
        service : { get : () -> (Outer) }
    "#;
    let new = r#"
        type Inner = record { x : text };
        type Outer = record { inner : Inner };
        service : { get : () -> (Outer) }
    "#;
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 1, "got: {errors:?}");
    let msg = &errors[0];
    assert!(msg.contains("method"), "path should include method: {msg}");
    assert!(
        msg.contains("return type"),
        "path should include return type: {msg}"
    );
    assert!(
        msg.contains("record field inner"),
        "path should include outer field: {msg}"
    );
    assert!(
        msg.contains("record field x"),
        "path should include inner field: {msg}"
    );
}

// ===========================================================================
//  Multi-arg functions
// ===========================================================================

#[test]
fn multi_arg_function_incompatibilities() {
    let old = "service : { f : (nat, text) -> (bool, nat) }";
    let new = "service : { f : (nat, bool) -> (bool, text) }";
    // Input: old (nat, text) must <: new (nat, bool) → field 1 text </: bool
    // Return: new (bool, text) must <: old (bool, nat) → field 1 text </: nat
    let errors = error_strings(new, old);
    assert_eq!(errors.len(), 2, "got: {errors:?}");
    let joined = errors.join("\n");
    assert!(joined.contains("input"), "missing input error: {joined}");
    assert!(joined.contains("return"), "missing return error: {joined}");
}

// ===========================================================================
//  service_compatible and service_compatibility_report agree
// ===========================================================================

#[test]
fn report_and_simple_check_agree() {
    let compatible = [
        (
            "service : { f : (text) -> (text); g : () -> () }",
            "service : { f : (text) -> (text) }",
        ),
        (
            "service : { f : (int) -> () }",
            "service : { f : (nat) -> () }",
        ),
    ];
    for (new, old) in compatible {
        let report = get_errors(new, old);
        assert!(report.is_empty(), "report should be empty for compatible");
        assert!(
            service_compatible(CandidSource::Text(new), CandidSource::Text(old)).is_ok(),
            "service_compatible should pass for compatible"
        );
    }

    let incompatible = [
        (
            "service : { f : (text) -> (text) }",
            "service : { f : (text) -> (text); g : () -> () }",
        ),
        (
            "service : { f : (nat) -> () }",
            "service : { f : (int) -> () }",
        ),
    ];
    for (new, old) in incompatible {
        let report = get_errors(new, old);
        assert!(!report.is_empty(), "report should have errors");
        assert!(
            service_compatible(CandidSource::Text(new), CandidSource::Text(old)).is_err(),
            "service_compatible should fail"
        );
    }
}

// ===========================================================================
//  Hierarchical report formatting
// ===========================================================================

#[test]
fn format_report_groups_by_method_and_nests() {
    let old = r#"service : {
        transfer : (record { from : text; to : text; amount : nat }) -> (record { ok : bool; balance : nat });
        balance  : () -> (nat);
        audit    : () -> (record { count : nat; log : text }) query;
        config   : () -> (record { flag : bool });
    }"#;
    let new = r#"service : {
        transfer : (record { from : text; to : text; amount : text }) -> (record { ok : text; balance : text });
        balance  : () -> (text);
        audit    : () -> (record { count : text; log : nat });
    }"#;
    let errors = get_errors(new, old);
    assert!(errors.len() >= 6, "expected many errors, got: {errors:?}");

    let report = format_report(&errors);

    // Each method should appear exactly once as a group header
    for method in ["transfer", "balance", "config"] {
        let header_count = report
            .lines()
            .filter(|l| {
                let trimmed = l.trim_start();
                trimmed.starts_with(&format!("method \"{method}\""))
                    || trimmed.contains(&format!("method \"{method}\""))
            })
            .count();
        assert!(
            header_count <= 1,
            "{method} should appear at most once as header, got {header_count} in:\n{report}"
        );
    }

    // Should have indented sub-groups
    assert!(
        report.contains("  return type") || report.contains("  input type"),
        "should have indented sub-groups:\n{report}"
    );
}

#[test]
fn format_report_inlines_single_leaf() {
    let old = "service : { get : () -> (nat) }";
    let new = "service : { get : () -> (text) }";
    let report = format_report(&get_errors(new, old));
    // Single error under method > return type should inline compactly
    assert!(
        report.lines().count() <= 3,
        "single error should be compact:\n{report}"
    );
}

#[test]
fn format_report_handles_path_and_pathless_errors() {
    // Pathless errors (e.g. top-level type mismatch) should render as "- message"
    let errors = vec![
        Incompatibility {
            path: vec![],
            message: "top-level mismatch".to_string(),
        },
        Incompatibility {
            path: vec!["method \"foo\"".to_string()],
            message: "missing in new interface".to_string(),
        },
    ];
    let report = format_report(&errors);
    assert!(
        report.contains("- top-level mismatch"),
        "pathless error should render with bullet:\n{report}"
    );
    assert!(
        report.contains("method \"foo\""),
        "pathed error should render:\n{report}"
    );
}
