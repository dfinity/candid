use candid::{check_prog, IDLProg, TypeEnv};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Bindings {
    js: String,
    ts: String,
}

#[wasm_bindgen]
impl Bindings {
    #[wasm_bindgen(getter)]
    pub fn js(&self) -> String {
        self.js.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn ts(&self) -> String {
        self.ts.clone()
    }
}

#[wasm_bindgen]
pub fn generate(prog: &str) -> Option<Bindings> {
    let ast = prog.parse::<IDLProg>().ok()?;
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).ok()?;
    Some(Bindings {
        js: candid::bindings::javascript::compile(&env, &actor),
        ts: candid::bindings::typescript::compile(&env, &actor),
    })
}
