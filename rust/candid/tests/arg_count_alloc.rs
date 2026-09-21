//! Wire-declared structural lengths must not turn into oversized up-front
//! allocations. A length prefix need not match the bytes actually present, so an
//! out-of-range argument, field, function-arity or method count must fail as an
//! ordinary parse error rather than reserving a correspondingly large buffer.
//!
//! The type table already carries this bound; these cases cover the remaining
//! length prefixes so that every `count`-sized allocation stays proportional to
//! the type description rather than to the raw byte length.

use candid::de::IDLDeserialize;
use candid::{DecoderConfig, Encode};

/// Drive the full deserialize, including skipping every declared argument, so a
/// healthy parser rejects a malformed length and returns normally.
fn decode(hex: &str) -> candid::Result<()> {
    let bytes = hex::decode(hex).unwrap();
    let mut de = IDLDeserialize::new(&bytes)?;
    while !de.is_done() {
        de.get_value::<candid::Reserved>()?;
    }
    Ok(())
}

#[test]
fn argument_count_out_of_range_is_rejected() {
    // "DIDL" 00 <uleb arg-count = 2^62> with an empty type table and no args.
    assert!(decode("4449444c00808080808080808040").is_err());
}

#[test]
fn record_field_count_out_of_range_is_rejected() {
    // "DIDL" 01 6c <uleb field-count = 2^31>: a record type declaring 2^31
    // fields. The field count is a u32 on the wire, so the value is chosen to
    // fit in u32 and reach the new bound rather than failing the u32 conversion.
    assert!(decode("4449444c016c8080808008").is_err());
}

#[test]
fn function_arity_out_of_range_is_rejected() {
    // "DIDL" 01 6a <uleb arg-len = 2^62>: a func type declaring 2^62 arguments.
    assert!(decode("4449444c016a808080808080808040").is_err());
}

#[test]
fn function_result_count_out_of_range_is_rejected() {
    // "DIDL" 01 6a 00 <uleb ret-len = 2^62>: a func type with zero arguments
    // and 2^62 results, so the independent result-count bound is exercised.
    assert!(decode("4449444c016a00808080808080808040").is_err());
}

#[test]
fn service_method_count_out_of_range_is_rejected() {
    // "DIDL" 01 69 <uleb method-count = 2^62>: a service declaring 2^62 methods.
    assert!(decode("4449444c0169808080808080808040").is_err());
}

/// A well-formed message with trailing arguments that are skipped through the
/// option/backtracking path still round-trips. This exercises the shared
/// argument queue across the top-level pops that follow a backtracking clone.
#[test]
fn trailing_optional_arguments_still_decode() {
    // encode (nat32, opt nat32, opt nat32) and decode only the first value,
    // letting `done()` drain the rest through the skip path.
    let bytes = Encode!(&7u32, &Some(8u32), &Some(9u32)).unwrap();
    let mut de = IDLDeserialize::new(&bytes).unwrap();
    let first: u32 = de.get_value().unwrap();
    assert_eq!(first, 7);
    de.done().unwrap();
}

/// A present `opt` whose inner wire type is not a subtype of the expected inner
/// type takes the backtracking arm: `recoverable_visit_some` restores the
/// snapshot and decodes the value as `None`. The following argument must still
/// decode, proving the shared argument queue survives the restore intact.
#[test]
fn mismatched_optional_restores_shared_queue() {
    // wire: (opt text = ?"x", nat32 = 42); decode the first into Option<u32>.
    let bytes = Encode!(&Some("x".to_string()), &42u32).unwrap();
    let mut de = IDLDeserialize::new(&bytes).unwrap();
    let first: Option<u32> = de.get_value().unwrap();
    assert_eq!(first, None);
    let second: u32 = de.get_value().unwrap();
    assert_eq!(second, 42);
    de.done().unwrap();
}

/// `max_type_len` bounds the top-level argument count in addition to the type
/// table size, so a message declaring more arguments than the limit is rejected
/// while one within the limit still decodes.
#[test]
fn max_type_len_bounds_argument_count() {
    let two_args = Encode!(&1u32, &2u32).unwrap();

    let mut too_small = DecoderConfig::new();
    too_small.set_max_type_len(1);
    assert!(IDLDeserialize::new_with_config(&two_args, &too_small).is_err());

    let mut big_enough = DecoderConfig::new();
    big_enough.set_max_type_len(2);
    assert!(IDLDeserialize::new_with_config(&two_args, &big_enough).is_ok());
}
