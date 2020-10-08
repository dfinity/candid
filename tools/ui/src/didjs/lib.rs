use candid::{check_prog, IDLProg, TypeEnv};

#[ic_cdk_macros::query]
fn did_to_js(prog: String) -> Option<String> {
    let ast = prog.parse::<IDLProg>().ok()?;
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).ok()?;
    let res = candid::bindings::javascript::compile(&env, &actor);
    Some(res)
}
