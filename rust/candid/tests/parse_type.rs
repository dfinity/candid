use candid::bindings::{candid as candid_export, javascript, motoko, rust, typescript};
use candid::parser::types::{to_pretty, IDLProg};
use candid::parser::typing::{check_file, check_prog, TypeEnv};
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

#[test_generator::test_resources("rust/candid/tests/assets/*.did")]
fn compiler_test(resource: &str) {
    let base_path = std::env::current_dir().unwrap().join("tests/assets");
    let mut mint = Mint::new(base_path.join("ok"));

    let filename = Path::new(Path::new(resource).file_name().unwrap());
    let candid_path = base_path.join(filename);

    match check_file(&candid_path) {
        Ok((env, actor)) => {
            {
                let mut output = mint.new_goldenfile(filename.with_extension("did")).unwrap();
                let content = candid_export::compile(&env, &actor);
                // Type check output
                let ast = content.parse::<IDLProg>().unwrap();
                check_prog(&mut TypeEnv::new(), &ast).unwrap();
                writeln!(output, "{}", content).unwrap();
            }
            {
                match filename.file_name().unwrap().to_str().unwrap() {
                    "unicode.did" | "escape.did" => {
                        check_error(|| motoko::compile(&env, &actor), "not a valid Motoko id")
                    }
                    _ => {
                        let mut output =
                            mint.new_goldenfile(filename.with_extension("mo")).unwrap();
                        let content = motoko::compile(&env, &actor);
                        writeln!(output, "{}", content).unwrap();
                    }
                }
            }
            {
                let mut output = mint.new_goldenfile(filename.with_extension("rs")).unwrap();
                let content = rust::compile(&env, &actor);
                writeln!(output, "{}", content).unwrap();
            }
            {
                let mut output = mint.new_goldenfile(filename.with_extension("js")).unwrap();
                let content = javascript::compile(&env, &actor);
                writeln!(output, "{}", content).unwrap();
            }
            {
                let mut output = mint
                    .new_goldenfile(filename.with_extension("d.ts"))
                    .unwrap();
                let content = typescript::compile(&env, &actor);
                writeln!(output, "{}", content).unwrap();
            }
        }
        Err(e) => {
            let mut fail_output = mint
                .new_goldenfile(filename.with_extension("fail"))
                .unwrap();
            writeln!(fail_output, "{}", e).unwrap();
        }
    }
}

fn check_error<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F, str: &str) {
    assert_eq!(
        std::panic::catch_unwind(f)
            .err()
            .and_then(|a| a.downcast_ref::<String>().map(|s| { s.contains(str) })),
        Some(true)
    );
}
