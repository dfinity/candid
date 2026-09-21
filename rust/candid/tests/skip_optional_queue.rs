//! The deserializer shares its undecoded argument queue behind a reference
//! count, so the option/backtracking path no longer copies it. These tests lock
//! the correctness of that shared queue across the top-level pops that follow a
//! backtracking snapshot, and guard against reintroducing a per-`opt` copy whose
//! cost grows with the number of remaining arguments.

use candid::de::IDLDeserialize;
use candid::Encode;
use std::time::{Duration, Instant};

/// A well-formed message with trailing arguments that are skipped through the
/// option path still round-trips. Skipping each present `opt` takes the snapshot
/// arm, so this exercises the shared queue across the pops that follow it.
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

/// Build a message declaring `n` arguments of type `opt null`, whose first
/// `present` values are `?null` and the rest `null`. Decoding argument 0 and
/// skipping the remainder walks every present `opt` through the snapshot arm.
fn opt_null_message(n: usize, present: usize) -> Vec<u8> {
    let mut b = vec![0x44, 0x49, 0x44, 0x4c]; // "DIDL"
    b.extend_from_slice(&[0x01, 0x6e, 0x7f]); // type table: opt (0x6e) of null (0x7f)
    let mut count = n as u64; // argument count as LEB128
    loop {
        let mut byte = (count & 0x7f) as u8;
        count >>= 7;
        if count != 0 {
            byte |= 0x80;
        }
        b.push(byte);
        if count == 0 {
            break;
        }
    }
    b.extend(std::iter::repeat(0x00).take(n)); // each argument references table index 0
    b.extend((0..n).map(|i| if i < present { 0x01 } else { 0x00 })); // present/absent flags
    b
}

/// Skipping many present optional arguments must stay proportional to the number
/// of arguments, not to arguments times present-opts. When the snapshot copies
/// the whole remaining queue, this is quadratic and takes many seconds; sharing
/// the queue keeps it in the millisecond range. The threshold is deliberately
/// loose so it only trips on a return of the quadratic behavior.
#[test]
fn skipping_many_present_optionals_is_not_quadratic() {
    let bytes = opt_null_message(150_000, 15_000);
    let start = Instant::now();
    let mut de = IDLDeserialize::new(&bytes).unwrap();
    let _first: Option<()> = de.get_value().unwrap();
    de.done().unwrap();
    let elapsed = start.elapsed();
    assert!(
        elapsed < Duration::from_secs(2),
        "skipping present optionals took {elapsed:?}; the argument queue is likely being copied per opt again"
    );
}
