//! Parsing the type-table header must not turn a wire-declared length into an
//! oversized up-front allocation. A length prefix need not match the bytes
//! actually present, so an out-of-range value must fail as an ordinary parse
//! error rather than reserving a correspondingly large buffer.

use candid::de::IDLDeserialize;

/// Decode only exercises the header parse; the payloads below carry no argument
/// section, so a healthy parser rejects them with an error and returns normally.
fn decode(hex: &str) -> candid::Result<()> {
    let bytes = hex::decode(hex).unwrap();
    IDLDeserialize::new(&bytes).map(|_| ())
}

#[test]
fn future_blob_out_of_range_length_is_rejected() {
    // "DIDL" 01 67 <sleb opcode> <uleb len = 2^62> with no blob bytes present.
    assert!(decode("4449444c0167808080808080808040").is_err());
}

#[test]
fn future_blob_short_input_is_rejected() {
    // Same shape, a modest declared length (1024) but a truncated blob.
    assert!(decode("4449444c01678008").is_err());
}

#[test]
fn service_method_name_out_of_range_length_is_rejected() {
    // A `service` table entry (0x69) with one method whose name declares a
    // 2^62-byte length: "DIDL" 01 69 01 <uleb name-len = 2^62>, no name bytes.
    assert!(decode("4449444c016901808080808080808040").is_err());
}
