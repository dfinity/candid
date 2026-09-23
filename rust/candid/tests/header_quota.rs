//! The decoding quota bounds header parsing as it happens, not only after the fact.

use candid::{de::IDLDeserialize, DecoderConfig};

fn leb(mut v: u64) -> Vec<u8> {
    let mut out = vec![];
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return out;
        }
        out.push(b | 0x80);
    }
}

fn quota(n: usize) -> DecoderConfig {
    let mut c = DecoderConfig::new();
    c.set_decoding_quota(n).set_full_error_message(true);
    c
}

/// `count` elements declared, but the bytes are not there. Without a quota this
/// reaches the short read; with one, the count is out of budget before that.
fn truncated(opcode: Option<u64>, count: u64) -> Vec<u8> {
    let mut b = b"DIDL".to_vec();
    match opcode {
        None => {
            b.extend(leb(0));
            b.extend(leb(count));
        }
        Some(op) => {
            b.extend(leb(1));
            b.extend(leb(op));
            b.extend(leb(count));
        }
    }
    b
}

fn err(bytes: &[u8], config: &DecoderConfig) -> String {
    match IDLDeserialize::new_with_config(bytes, config) {
        Ok(_) => String::new(),
        Err(e) => format!("{e:?}"),
    }
}

#[test]
fn quota_bounds_each_declared_count() {
    // args, record fields, variant fields, service methods, func args.
    let cases: [(&str, Vec<u8>); 5] = [
        ("argument", truncated(None, 8_000_000)),
        ("field", truncated(Some(0x6c), 8_000_000)),
        ("field", truncated(Some(0x6b), 8_000_000)),
        ("service method", truncated(Some(0x69), 8_000_000)),
        ("function argument", truncated(Some(0x6a), 8_000_000)),
    ];
    for (what, bytes) in cases {
        let e = err(&bytes, &quota(100_000));
        assert!(
            e.contains("exceeds decoding quota"),
            "{what}: expected a quota rejection, got: {e}"
        );
    }
}

#[test]
fn no_quota_leaves_counts_unbounded() {
    // Without a quota the count itself is never rejected; parsing fails only
    // because the declared elements are not present.
    for bytes in [
        truncated(None, 8_000_000),
        truncated(Some(0x6c), 8_000_000),
        truncated(Some(0x69), 8_000_000),
        truncated(Some(0x6a), 8_000_000),
    ] {
        let e = err(&bytes, &DecoderConfig::new());
        assert!(
            !e.contains("exceeds decoding quota"),
            "no quota was set, so the count must not be bounded: {e}"
        );
    }
}

#[test]
fn counts_a_generous_quota_can_pay_for_are_accepted() {
    use candid::{encode_one, Decode, Encode};
    use std::collections::BTreeMap;

    // A record with many fields, well within a generous quota, still decodes.
    #[derive(candid::CandidType, serde::Deserialize, PartialEq, Debug)]
    struct Big {
        a: u32,
        b: String,
        c: Vec<u64>,
        d: Option<i64>,
    }
    let v = Big {
        a: 1,
        b: "x".into(),
        c: vec![1, 2, 3],
        d: Some(-1),
    };
    let bytes = Encode!(&v).unwrap();
    let mut d = IDLDeserialize::new_with_config(&bytes, &quota(20_000_000)).unwrap();
    assert_eq!(d.get_value::<Big>().unwrap(), v);

    let m: BTreeMap<String, u64> = (0..100).map(|i| (i.to_string(), i)).collect();
    let bytes = encode_one(&m).unwrap();
    let mut d = IDLDeserialize::new_with_config(&bytes, &quota(20_000_000)).unwrap();
    assert_eq!(d.get_value::<BTreeMap<String, u64>>().unwrap(), m);

    let _ = Decode!(&bytes, BTreeMap<String, u64>).unwrap();
}

/// The bound must never reject a header whose post-hoc charge would have been
/// affordable: an element costs at least one byte and the header is charged 4
/// units per byte, so the early check and the charge agree at the boundary.
#[test]
fn early_bound_agrees_with_the_charge_it_replaces() {
    for q in [40usize, 400, 4_000, 40_000] {
        let max_ok = (q / 4) as u64;
        // At the limit: not rejected for exceeding the quota (it fails later, on
        // the short read, or decodes).
        let e = err(&truncated(None, max_ok), &quota(q));
        assert!(
            !e.contains("exceeds decoding quota"),
            "quota {q}: count {max_ok} is within budget but was rejected: {e}"
        );
        // One past the limit: the charge could not have been paid, so rejecting
        // early changes the timing, not the outcome.
        let e = err(&truncated(None, max_ok + 1), &quota(q));
        assert!(
            e.contains("exceeds decoding quota"),
            "quota {q}: count {} is unaffordable and should be rejected: {e}",
            max_ok + 1
        );
    }
}
