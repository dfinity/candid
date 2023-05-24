use candid::pretty::candid::compile;
use candid::types::TypeEnv;
use candid_parser::bindings::{javascript, motoko, rust, typescript};
use candid_parser::types::IDLProg;
use candid_parser::typing::{check_file, check_prog, check_file_with_options, CheckFileOptions};
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
    prog.parse::<IDLProg>().unwrap();
}

#[test_generator::test_resources("rust/candid_parser/tests/assets/*.did")]
fn compiler_test(resource: &str) {
    let base_path = std::env::current_dir().unwrap().join("tests/assets");
    let mut mint = Mint::new(base_path.join("ok"));

    let filename = Path::new(Path::new(resource).file_name().unwrap());
    let candid_path = base_path.join(filename);

    if filename.file_name().unwrap().to_str().unwrap() == "combine_actors.did" {
        return;
    }

    match check_file(&candid_path) {
        Ok((env, actor)) => {
            {
                let mut output = mint.new_goldenfile(filename.with_extension("did")).unwrap();
                let content = compile(&env, &actor);
                // Type check output
                let ast = content.parse::<IDLProg>().unwrap();
                check_prog(&mut TypeEnv::new(), &ast).unwrap();
                writeln!(output, "{content}").unwrap();
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
                        writeln!(output, "{content}").unwrap();
                    }
                }
            }
            {
                let mut config = rust::Config::new();
                config.set_canister_id(candid::Principal::from_text("aaaaa-aa").unwrap());
                if filename.file_name().unwrap().to_str().unwrap() == "management.did" {
                    config.set_target(rust::Target::Agent);
                }
                let mut output = mint.new_goldenfile(filename.with_extension("rs")).unwrap();
                let content = rust::compile(&config, &env, &actor);
                writeln!(output, "{content}").unwrap();
            }
            {
                let mut output = mint.new_goldenfile(filename.with_extension("js")).unwrap();
                let content = javascript::compile(&env, &actor);
                writeln!(output, "{content}").unwrap();
            }
            {
                let mut output = mint
                    .new_goldenfile(filename.with_extension("d.ts"))
                    .unwrap();
                let content = typescript::compile(&env, &actor);
                writeln!(output, "{content}").unwrap();
            }
        }
        Err(e) => {
            let mut fail_output = mint
                .new_goldenfile(filename.with_extension("fail"))
                .unwrap();
            writeln!(fail_output, "{e}").unwrap();
        }
    }
}

#[test]
fn test_combine_actors() {
    let base_path = std::env::current_dir().unwrap().join("tests/assets");
    let mut mint = Mint::new(base_path.join("ok"));
    let filename = Path::new("combine_actors.did");
    let candid_path = base_path.join(filename);

    match check_file_with_options(
        &candid_path,
        &CheckFileOptions {
            pretty_errors: false,
            combine_actors: true,
        },
    ) {
        Ok(result) => {
            {
                let mut output = mint.new_goldenfile(filename.with_extension("did")).unwrap();
                let content = compile(&result.types, &result.actor);
                // Type check output
                let ast = content.parse::<IDLProg>().unwrap();
                check_prog(&mut TypeEnv::new(), &ast).unwrap();
                writeln!(output, "{}", content).unwrap();
            }

            {
                let mut output = mint
                    .new_goldenfile(filename.with_extension("imports"))
                    .unwrap();
                let mut imports = result
                    .imports
                    .into_iter()
                    .map(|f| f.file_name().unwrap().to_str().unwrap().to_owned())
                    .collect::<Vec<_>>();
                imports.sort();
                writeln!(output, "{:?}", imports).unwrap();
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
