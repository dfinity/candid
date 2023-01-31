#![no_main]
use libfuzzer_sys::fuzz_target;
use std::slice;
use candid::parser::{
    types::IDLProg
};
use candid::types::{
    value::{IDLArgs, IDLValue},
};

use candid::types::Label;
use candid::{decode_args, decode_one, Decode};

fuzz_target!(|data: &[u8]| {
    let decoded = match IDLArgs::from_bytes(&data) {
        Ok(_v) => _v,
        Err(e) => return,
    };
    decoded.get_types();
    decoded.to_bytes();
    decoded.to_string();
});
