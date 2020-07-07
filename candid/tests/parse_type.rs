use candid::bindings::javascript;
use candid::parser::types::{to_pretty, IDLProg};
use candid::parser::typing::{check_prog, TypeEnv};
use candid::types::Type;
use goldenfile::Mint;
use std::io::Write;
use std::path::Path;

#[test]
fn parse_idl_prog() {
    let prog = r#"
import "test.did";
type my_type = principal;
type List = opt record { head: int; tail: List };
type f = func (List, func (int32) -> (int64)) -> (opt List);
type broker = service {
  find : (name: text) ->
    (service {up:() -> (); current:() -> (nat32)});
};
type nested = record { nat; nat; record { nat; 0x2a:nat; nat8; }; 42:nat; 40:nat; variant{ A; 0x2a; B; C }; };

service server : {
  f : (test: blob, opt bool) -> () oneway;
  g : (my_type, List, opt List) -> (int) query;
  h : (vec opt text, variant { A: nat; B: opt text }, opt List) -> (record { id: nat; 0x2a: record {} });
  i : f;
}
    "#;
    let ast = prog.parse::<IDLProg>().unwrap();
    let pretty = to_pretty(&ast, 80);
    let ast2 = pretty.parse::<IDLProg>().unwrap();
    assert_eq!(format!("{:?}", ast2), format!("{:?}", ast));
}

fn compile(env: &mut TypeEnv, file: &Path) -> candid::Result<Option<Type>> {
    let prog = std::fs::read_to_string(&file)?;
    let ast = prog.parse::<IDLProg>()?;
    check_prog(env, &ast)
}

#[test_generator::test_resources("candid/tests/assets/*.did")]
fn compiler_test(resource: &str) {
    let base_path = std::env::current_dir().unwrap().join("tests/assets");
    let mut mint = Mint::new(base_path.join("ok"));

    let filename = Path::new(Path::new(resource).file_name().unwrap());
    let candid_path = base_path.join(filename);

    let mut env = TypeEnv::new();
    match compile(&mut env, &candid_path) {
        Ok(actor) => {
            let mut js_output = mint.new_goldenfile(filename.with_extension("js")).unwrap();
            let js = javascript::compile(&env, &actor);
            writeln!(js_output, "{}", js).unwrap();
        }
        Err(e) => {
            let mut fail_output = mint
                .new_goldenfile(filename.with_extension("fail"))
                .unwrap();
            writeln!(fail_output, "{}", e.to_string()).unwrap();
        }
    }
}
