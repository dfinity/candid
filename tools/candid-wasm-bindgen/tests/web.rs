//! Test suite for the Web and headless browsers.

#![cfg(target_arch = "wasm32")]

extern crate wasm_bindgen_test;
use std::assert_eq;

use candid_wasm_bindgen::js;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
fn pass() {
    assert_eq!(1 + 1, 2);
}

#[wasm_bindgen_test]
fn argh() {
    let foo = js("type f = func (int8) -> (int8);
    type g = f;
    type h = func (f) -> (f);
    type o = opt o;
    service : { f : (nat) -> (h); g : f; h : g; o : (o) -> (o) }");
    assert_eq!(foo, "export const idlFactory = ({ IDL }) => {\n  const o = IDL.Rec();\n  const f = IDL.Func([IDL.Int8], [IDL.Int8], []);\n  const h = IDL.Func([f], [f], []);\n  const g = f;\n  o.fill(IDL.Opt(o));\n  return IDL.Service({\n    'f' : IDL.Func([IDL.Nat], [h], []),\n    'g' : f,\n    'h' : g,\n    'o' : IDL.Func([o], [o], []),\n  });\n};\nexport const init = ({ IDL }) => { return []; };");
}
