//! The type-table header carries its own size bound, independent of the payload.

use candid::{de::IDLDeserialize, DecoderConfig, Encode};

fn leb(mut v: u64) -> Vec<u8> {
    let mut o = vec![];
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            o.push(b);
            return o;
        }
        o.push(b | 0x80);
    }
}

/// `n` declared arguments, all `null`: 1 byte of header each.
fn args(n: u64) -> Vec<u8> {
    let mut b = b"DIDL".to_vec();
    b.extend(leb(0));
    b.extend(leb(n));
    b.extend(std::iter::repeat(0x7f).take(n as usize));
    b
}
/// A single type-table entry declaring `n` fields.
fn fields(opcode: u64, n: u64) -> Vec<u8> {
    let mut b = b"DIDL".to_vec();
    b.extend(leb(1));
    b.extend(leb(opcode));
    b.extend(leb(n));
    for i in 0..n {
        b.extend(leb(i));
        b.push(0x7f);
    }
    b.extend(leb(1));
    b.extend(leb(0));
    b
}

fn cfg(max_header_len: Option<usize>) -> DecoderConfig {
    let mut c = DecoderConfig::new();
    c.set_full_error_message(false);
    if let Some(n) = max_header_len {
        c.set_max_header_len(n);
    }
    c
}

fn err(bytes: &[u8], c: &DecoderConfig) -> String {
    match IDLDeserialize::new_with_config(bytes, c) {
        Ok(_) => String::new(),
        // the specific cause sits under the "Cannot parse header" context
        Err(e) => format!("{e:#}"),
    }
}

#[test]
fn oversized_header_is_rejected_by_default() {
    // 4 MB of declared arguments, well past the 64 KiB default.
    for msg in [
        args(4_000_000),
        fields(0x6c, 2_000_000),
        fields(0x6b, 2_000_000),
    ] {
        let e = err(&msg, &cfg(None));
        assert!(
            e.contains("exceeds the limit"),
            "expected a header-size rejection, got: {e}"
        );
    }
}

#[test]
fn one_bound_covers_every_declared_count() {
    // args, record fields, variant fields, service methods, function args all become
    // header bytes, so a single byte bound reaches each of them.
    let mut serv = b"DIDL".to_vec();
    serv.extend(leb(1));
    serv.extend(leb(0x69));
    serv.extend(leb(500_000));
    for _ in 0..500_000u64 {
        serv.extend_from_slice(&[1, b'm', 0x7f]);
    }
    serv.extend(leb(1));
    serv.extend(leb(0));

    let mut func = b"DIDL".to_vec();
    func.extend(leb(1));
    func.extend(leb(0x6a));
    func.extend(leb(500_000));
    func.extend(std::iter::repeat(0x7f).take(500_000));
    func.extend(leb(0));
    func.push(0);
    func.extend(leb(1));
    func.extend(leb(0));

    for msg in [serv, func] {
        assert!(err(&msg, &cfg(None)).contains("exceeds the limit"));
    }
}

#[test]
fn the_bound_is_on_the_header_not_the_payload() {
    // A 2 MB value section decodes fine under a deliberately tiny header bound:
    // the bound constrains the type description, not how much data it describes.
    let blob = serde_bytes::ByteBuf::from(vec![7u8; 2_000_000]);
    let bytes = Encode!(&blob).unwrap();
    let mut c = cfg(Some(64));
    c.set_decoding_quota(100_000_000);
    let mut d = IDLDeserialize::new_with_config(&bytes, &c).unwrap();
    let out = d.get_value::<serde_bytes::ByteBuf>().unwrap();
    assert_eq!(out.len(), 2_000_000);
}

#[test]
fn boundary_is_exact() {
    // header = "DIDL" + table_len + arg_count + n x 1 byte
    for limit in [64usize, 1_000, 10_000] {
        let n = (limit - 4 - 1 - leb(limit as u64).len()) as u64;
        let at = args(n);
        assert!(at.len() <= limit);
        assert!(
            !err(&at, &cfg(Some(limit))).contains("exceeds the limit"),
            "a {}-byte header must pass a {limit}-byte bound",
            at.len()
        );
        let over = args(n + 200);
        assert!(over.len() > limit);
        assert!(
            err(&over, &cfg(Some(limit))).contains("exceeds the limit"),
            "a {}-byte header must fail a {limit}-byte bound",
            over.len()
        );
    }
}

#[test]
fn realistic_headers_are_unaffected() {
    // The largest header among the IC's own interfaces is ~2 KB; the management
    // canister's largest is ~214 B. Anything of that scale must be untouched.
    #[derive(candid::CandidType, serde::Deserialize, PartialEq, Debug)]
    struct Settings {
        controllers: Option<Vec<candid::Principal>>,
        compute_allocation: Option<u64>,
        memory_allocation: Option<u64>,
        freezing_threshold: Option<u64>,
        reserved_cycles_limit: Option<u64>,
        wasm_memory_limit: Option<u64>,
        log_visibility: Option<u8>,
    }
    let v = Settings {
        controllers: Some(vec![candid::Principal::anonymous()]),
        compute_allocation: Some(1),
        memory_allocation: Some(2),
        freezing_threshold: Some(3),
        reserved_cycles_limit: Some(4),
        wasm_memory_limit: Some(5),
        log_visibility: Some(0),
    };
    let bytes = Encode!(&v).unwrap();
    let mut d = IDLDeserialize::new_with_config(&bytes, &cfg(None)).unwrap();
    assert_eq!(d.get_value::<Settings>().unwrap(), v);
}

#[test]
fn a_larger_bound_can_be_opted_into() {
    let msg = args(200_000); // ~200 KB header, over the default
    assert!(err(&msg, &cfg(None)).contains("exceeds the limit"));
    // Raising the bound admits it again (it then fails later, on the absent values).
    let e = err(&msg, &cfg(Some(1 << 20)));
    assert!(
        !e.contains("exceeds the limit"),
        "raised bound should admit the header: {e}"
    );
}
