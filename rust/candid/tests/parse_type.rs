use candid::bindings::{candid as candid_export, javascript};
use candid::parser::types::IDLProg;
use candid::parser::typing::{check_prog, TypeEnv};
use candid::types::Type;
use goldenfile::Mint;
use std::io::Write;
use std::path::Path;

fn compile(env: &mut TypeEnv, file: &Path) -> candid::Result<Option<Type>> {
    let prog = std::fs::read_to_string(&file)?;
    let ast = prog.parse::<IDLProg>()?;
    check_prog(env, &ast)
}

#[test_generator::test_resources("rust/candid/tests/assets/*.did")]
fn compiler_test(resource: &str) {
    let base_path = std::env::current_dir().unwrap().join("tests/assets");
    let mut mint = Mint::new(base_path.join("ok"));

    let filename = Path::new(Path::new(resource).file_name().unwrap());
    let candid_path = base_path.join(filename);

    let mut env = TypeEnv::new();
    match compile(&mut env, &candid_path) {
        Ok(actor) => {
            {
                let mut output = mint.new_goldenfile(filename.with_extension("did")).unwrap();
                let content = candid_export::compile(&env, &actor);
                // Type check output
                let ast = content.parse::<IDLProg>().unwrap();
                check_prog(&mut TypeEnv::new(), &ast).unwrap();
                writeln!(output, "{}", content).unwrap();
            }
            {
                let mut output = mint.new_goldenfile(filename.with_extension("js")).unwrap();
                let content = javascript::compile(&env, &actor);
                writeln!(output, "{}", content).unwrap();
            }
        }
        Err(e) => {
            let mut fail_output = mint
                .new_goldenfile(filename.with_extension("fail"))
                .unwrap();
            writeln!(fail_output, "{}", e.to_string()).unwrap();
        }
    }
}
