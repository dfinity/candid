//! Wire-declared structural lengths must not turn into oversized up-front
//! allocations. A length prefix need not match the bytes actually present, so an
//! out-of-range argument, field, function-arity or method count must fail as an
//! ordinary parse error rather than reserving a correspondingly large buffer.
//!
//! The type table already carries this bound; these cases cover the remaining
//! length prefixes so that every `count`-sized allocation stays proportional to
//! the type description rather than to the raw byte length.

use candid::de::IDLDeserialize;
use candid::Encode;

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
    // "DIDL" 01 6c <uleb field-count = 2^62>: a record type declaring 2^62 fields.
    assert!(decode("4449444c016c808080808080808040").is_err());
}

#[test]
fn function_arity_out_of_range_is_rejected() {
    // "DIDL" 01 6a <uleb arg-len = 2^62>: a func type declaring 2^62 arguments.
    assert!(decode("4449444c016a808080808080808040").is_err());
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
