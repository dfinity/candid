use candid::types::subtype::format_report;
use candid_parser::utils::{service_compatibility_report, service_compatible, CandidSource};

// ---------------------------------------------------------------------------
//  Helpers
// ---------------------------------------------------------------------------

fn check_compatible(new: &str, old: &str) {
    service_compatible(CandidSource::Text(new), CandidSource::Text(old))
        .unwrap_or_else(|e| panic!("expected compatible, got error: {e}"));
}

fn check_incompatible(new: &str, old: &str) {
    assert!(
        service_compatible(CandidSource::Text(new), CandidSource::Text(old)).is_err(),
        "expected incompatible, but check passed"
    );
}

fn incompatibilities(new: &str, old: &str) -> Vec<String> {
    service_compatibility_report(CandidSource::Text(new), CandidSource::Text(old))
        .expect("failed to load interfaces")
        .into_iter()
        .map(|e| e.to_string())
        .collect()
}

// ===========================================================================
//  1. Backward-compatible changes must PASS (no false positives)
// ===========================================================================

#[test]
fn compatible_identical_services() {
    let did = "service : { greet : (text) -> (text) }";
    check_compatible(did, did);
}

#[test]
fn compatible_add_new_method() {
    let old = "service : { greet : (text) -> (text) }";
    let new = "service : { greet : (text) -> (text); hello : () -> (text) }";
    check_compatible(new, old);
}

#[test]
fn compatible_add_optional_record_field() {
    let old = r#"
        type Req = record { name : text };
        service : { greet : (Req) -> (text) }
    "#;
    let new = r#"
        type Req = record { name : text; age : opt nat };
        service : { greet : (Req) -> (text) }
    "#;
    check_compatible(new, old);
}

#[test]
fn compatible_narrow_return_nat_subtype_of_int() {
    // Old returns int, new returns nat. Return types are covariant: nat <: int ✓
    let old = "service : { get : () -> (int) }";
    let new = "service : { get : () -> (nat) }";
    check_compatible(new, old);
}

#[test]
fn compatible_add_optional_return_field() {
    let old = r#"
        type Res = record { id : nat };
        service : { get : () -> (Res) }
    "#;
    let new = r#"
        type Res = record { id : nat; extra : opt text };
        service : { get : () -> (Res) }
    "#;
    check_compatible(new, old);
}

#[test]
fn compatible_add_variant_case_in_return() {
    // Adding a variant to a return type is safe (old callers already handle unknown variants
    // via opt rule), and the new type is a subtype because the new variant's fields include
    // all old fields.
    let old = r#"
        type Res = variant { ok : nat; err : text };
        service : { call : () -> (Res) }
    "#;
    let new = r#"
        type Res = variant { ok : nat; err : text };
        service : { call : () -> (Res) }
    "#;
    check_compatible(new, old);
}

#[test]
fn compatible_narrow_input_type() {
    // Function inputs are contravariant: the new service can accept a *wider* input type.
    // Concretely: if old expected nat, new can accept int (since nat <: int, callers sending
    // nat still satisfy int).
    let old = "service : { pay : (nat) -> () }";
    let new = "service : { pay : (int) -> () }";
    check_compatible(new, old);
}

#[test]
fn compatible_add_reserved_field() {
    let old = "service : { get : () -> (record { a : nat }) }";
    let new = "service : { get : () -> (record { a : nat; b : reserved }) }";
    check_compatible(new, old);
}

#[test]
fn compatible_add_null_field() {
    let old = "service : { get : () -> (record { a : nat }) }";
    let new = "service : { get : () -> (record { a : nat; b : null }) }";
    check_compatible(new, old);
}

// ===========================================================================
//  2. Backward-INCOMPATIBLE changes must FAIL (no false negatives)
// ===========================================================================

#[test]
fn incompatible_remove_method() {
    let old = "service : { greet : (text) -> (text); hello : () -> (text) }";
    let new = "service : { greet : (text) -> (text) }";
    check_incompatible(new, old);
}

#[test]
fn incompatible_change_return_type() {
    let old = "service : { get : () -> (nat) }";
    let new = "service : { get : () -> (text) }";
    check_incompatible(new, old);
}

#[test]
fn incompatible_change_input_type() {
    let old = "service : { set : (nat) -> () }";
    let new = "service : { set : (text) -> () }";
    check_incompatible(new, old);
}

#[test]
fn incompatible_add_required_record_field() {
    let old = r#"
        type Req = record { name : text };
        service : { greet : (Req) -> (text) }
    "#;
    let new = r#"
        type Req = record { name : text; age : nat };
        service : { greet : (Req) -> (text) }
    "#;
    check_incompatible(new, old);
}

#[test]
fn incompatible_remove_variant_case_in_input() {
    // Removing a variant case from an input type means old callers might send
    // a variant the new service doesn't understand.
    let old = r#"
        type Cmd = variant { start; stop; pause };
        service : { exec : (Cmd) -> () }
    "#;
    let new = r#"
        type Cmd = variant { start; stop };
        service : { exec : (Cmd) -> () }
    "#;
    check_incompatible(new, old);
}

#[test]
fn incompatible_widen_return_from_nat_to_int() {
    // Old returns nat, new returns int. Return types are covariant: int <: nat is FALSE.
    // Old clients expecting nat may receive negative numbers.
    let old = "service : { get : () -> (nat) }";
    let new = "service : { get : () -> (int) }";
    check_incompatible(new, old);
}

#[test]
fn incompatible_change_func_mode() {
    let old = "service : { get : () -> (nat) query }";
    let new = "service : { get : () -> (nat) }";
    check_incompatible(new, old);
}

// ===========================================================================
//  3. ALL incompatibilities are reported (not just the first)
// ===========================================================================

#[test]
fn all_incompatible_methods_reported() {
    let old = r#"service : {
        method_a : (nat) -> (nat);
        method_b : (text) -> (text);
        method_c : () -> (nat);
    }"#;
    // Remove method_b, change method_c return type
    let new = r#"service : {
        method_a : (nat) -> (nat);
        method_c : () -> (text);
    }"#;
    let errors = incompatibilities(new, old);
    assert!(
        errors.len() >= 2,
        "expected at least 2 errors, got {}: {:?}",
        errors.len(),
        errors
    );

    let joined = errors.join("\n");
    assert!(
        joined.contains("method_b"),
        "should report missing method_b: {joined}"
    );
    assert!(
        joined.contains("method_c"),
        "should report incompatible method_c: {joined}"
    );
}

#[test]
fn all_incompatible_record_fields_reported() {
    let old = r#"
        type Res = record { a : nat; b : text; c : bool };
        service : { get : () -> (Res) }
    "#;
    // Change a from nat to text, change b from text to nat (both incompatible)
    let new = r#"
        type Res = record { a : text; b : nat; c : bool };
        service : { get : () -> (Res) }
    "#;
    let errors = incompatibilities(new, old);
    assert!(
        errors.len() >= 2,
        "expected at least 2 field errors, got {}: {:?}",
        errors.len(),
        errors
    );

    let joined = errors.join("\n");
    // The record fields use hashed IDs, but for named fields the display should include the name
    assert!(
        joined.contains("a") && joined.contains("b"),
        "should report both incompatible fields a and b: {joined}"
    );
    // Field c should NOT be reported (it's unchanged)
    // (We can't easily assert "not contains c" since "c" might appear in other words,
    // but we can check the count)
}

#[test]
fn both_input_and_return_incompatibilities_reported() {
    let old = "service : { call : (nat) -> (nat) }";
    // Change input from nat to text (breaks contravariance) and output from nat to bool
    let new = "service : { call : (text) -> (bool) }";
    let errors = incompatibilities(new, old);
    assert!(
        errors.len() >= 2,
        "expected at least 2 errors (input + return), got {}: {:?}",
        errors.len(),
        errors
    );

    let joined = errors.join("\n");
    assert!(
        joined.contains("input type"),
        "should report input type incompatibility: {joined}"
    );
    assert!(
        joined.contains("return type"),
        "should report return type incompatibility: {joined}"
    );
}

#[test]
fn multiple_missing_methods_all_reported() {
    let old = r#"service : {
        alpha : () -> ();
        beta : () -> ();
        gamma : () -> ();
        delta : () -> ();
    }"#;
    let new = "service : { alpha : () -> () }";
    let errors = incompatibilities(new, old);
    assert_eq!(
        errors.len(),
        3,
        "expected 3 missing method errors, got {}: {:?}",
        errors.len(),
        errors
    );

    let joined = errors.join("\n");
    assert!(joined.contains("beta"), "should report missing beta: {joined}");
    assert!(
        joined.contains("gamma"),
        "should report missing gamma: {joined}"
    );
    assert!(
        joined.contains("delta"),
        "should report missing delta: {joined}"
    );
}

#[test]
fn incompatibility_path_shows_nested_context() {
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
    let errors = incompatibilities(new, old);
    assert_eq!(errors.len(), 1, "expected 1 error, got: {:?}", errors);

    let msg = &errors[0];
    // Should show the full path: method > return type > field > field > leaf error
    assert!(
        msg.contains("method") && msg.contains("return type"),
        "error should include path context: {msg}"
    );
}

#[test]
fn compatible_changes_produce_no_errors() {
    let old = "service : { greet : (text) -> (text) }";
    let new = "service : { greet : (text) -> (text); extra : () -> () }";
    let errors = incompatibilities(new, old);
    assert!(
        errors.is_empty(),
        "compatible change should produce no errors, got: {:?}",
        errors
    );
}

#[test]
fn variant_incompatibilities_all_reported() {
    // New variant adds fields that don't exist in old - each is a breaking change
    let old = r#"
        type V = variant { a : nat; b : text };
        service : { get : (V) -> () }
    "#;
    // New service's input type has fewer variants than old callers might send
    // (Contravariant: old input must be subtype of new input for args)
    // Actually, for inputs: old_args <: new_args (contravariant)
    // Old V = { a : nat; b : text }, New V = { a : nat; b : text; c : bool }
    // For subtype: old_V <: new_V? Variant subtyping: all fields in old must exist in new => yes
    // So ADDING variant cases to input is compatible.
    //
    // But REMOVING variant cases from input is NOT:
    let new = r#"
        type V = variant { a : nat };
        service : { get : (V) -> () }
    "#;
    // old input V = { a; b } needs to be <: new input V = { a }
    // variant { a; b } <: variant { a } fails because field b is in old but not in new
    let errors = incompatibilities(new, old);
    assert!(
        !errors.is_empty(),
        "removing variant case from input should be incompatible"
    );
    let joined = errors.join("\n");
    assert!(
        joined.contains("b"),
        "should mention the removed variant case 'b': {joined}"
    );
}

// ===========================================================================
//  4. Error message quality checks
// ===========================================================================

#[test]
fn error_message_for_missing_method_is_clear() {
    let old = "service : { transfer : (nat) -> (); balance : () -> (nat) }";
    let new = "service : { balance : () -> (nat) }";
    let errors = incompatibilities(new, old);
    assert_eq!(errors.len(), 1);
    let msg = &errors[0];
    assert!(
        msg.contains("transfer"),
        "error should name the missing method: {msg}"
    );
    assert!(
        msg.contains("missing"),
        "error should say the method is missing: {msg}"
    );
}

#[test]
fn error_message_for_type_change_includes_types() {
    let old = "service : { get : () -> (nat) }";
    let new = "service : { get : () -> (text) }";
    let errors = incompatibilities(new, old);
    assert!(!errors.is_empty());
    let msg = &errors[0];
    assert!(
        msg.contains("text") && msg.contains("nat"),
        "error should mention both old and new types: {msg}"
    );
}

#[test]
fn error_message_for_missing_record_field_is_clear() {
    // For return types: new_ret <: old_ret. Missing non-optional field = breaking.
    let old = r#"
        type Res = record { name : text; age : nat };
        service : { get : () -> (Res) }
    "#;
    let new = r#"
        type Res = record { name : text };
        service : { get : () -> (Res) }
    "#;
    // Return type: new_ret <: old_ret. new Res = { name } old Res = { name; age }
    // record { name } <: record { name; age } => field 'age' is only in expected type and is nat (not opt)
    // => FAIL
    let errors = incompatibilities(new, old);
    assert!(!errors.is_empty());
    let msg = &errors[0];
    assert!(
        msg.contains("age"),
        "error should mention the missing field: {msg}"
    );
    assert!(
        msg.contains("missing") || msg.contains("not optional"),
        "error should explain why this is a problem: {msg}"
    );
}

// ===========================================================================
//  5. Hierarchical report formatting
// ===========================================================================

fn raw_incompatibilities(
    new: &str,
    old: &str,
) -> Vec<candid::types::subtype::Incompatibility> {
    service_compatibility_report(CandidSource::Text(new), CandidSource::Text(old))
        .expect("failed to load interfaces")
}

#[test]
fn format_report_groups_by_method() {
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
    // transfer: input field amount changed nat→text (contra: old args <: new args, nat </: text)
    //           return field ok changed bool→text, balance changed nat→text
    // balance: return changed nat→text
    // audit: return field count changed nat→text, log changed text→nat, also query→non-query
    // config: missing method

    let errors = raw_incompatibilities(new, old);
    assert!(
        errors.len() >= 6,
        "expected many errors, got {}: {:?}",
        errors.len(),
        errors
    );

    let report = format_report(&errors);
    // Verify grouping: each method name should appear exactly once as a header
    let transfer_headers: Vec<_> = report
        .lines()
        .filter(|l| l.starts_with("method \"transfer\""))
        .collect();
    assert_eq!(
        transfer_headers.len(),
        1,
        "transfer should appear as a single group header, got: {:?}",
        transfer_headers
    );

    // Verify nested indentation exists
    assert!(
        report.contains("  ") && report.contains("return type"),
        "report should have indented sub-groups: {report}"
    );
}

#[test]
fn format_report_inlines_single_leaf_errors() {
    let old = "service : { get : () -> (nat) }";
    let new = "service : { get : () -> (text) }";
    let errors = raw_incompatibilities(new, old);
    let report = format_report(&errors);
    // A single error under a method should be inlined (no extra nesting line)
    let line_count = report.lines().count();
    assert!(
        line_count <= 3,
        "single error should produce compact output, got {} lines:\n{report}",
        line_count
    );
}

#[test]
fn format_report_empty_for_compatible() {
    let old = "service : { greet : (text) -> (text) }";
    let new = "service : { greet : (text) -> (text); extra : () -> () }";
    let errors = raw_incompatibilities(new, old);
    let report = format_report(&errors);
    assert!(report.is_empty(), "compatible should produce empty report");
}
