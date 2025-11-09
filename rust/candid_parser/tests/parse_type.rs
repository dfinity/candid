use candid::types::TypeEnv;
use candid_parser::{
    bindings::{javascript, motoko, rust, typescript},
    configs::Configs,
    syntax::{pretty_print, Dec, IDLProg, IDLTypeKind},
    typing::{check_file, check_prog},
};
use goldenfile::Mint;
use std::io::Write;
use std::path::Path;

#[test]
fn test_parse_idl_prog() {
    let prog = r#"
import "test.did";
// Doc comment for my_type
type my_type = principal;
type List = opt record {
  // Doc comment for List.head
  head: int;
  tail: List
};
type f = func (List, func (int32) -> (int64)) -> (opt List);
type broker = service {
  find : (name: text) ->
    (service {up:() -> (); current:() -> (nat32)});
};
type nested = record { nat; nat; record { nat; 0x2a:nat; nat8; }; 42:nat; 40:nat; variant{ A; 0x2a; B; C }; };

// Doc comment for service
service server : {
  // Doc comment for f
  f : (test: blob, opt bool) -> () oneway;
  g : (my_type, List, opt List) -> (int) query;
  h : (vec opt text, variant { A: nat; B: opt text }, opt List) -> (record { id: nat; 0x2a: record {} });
  i : f;
}
    "#;
    let ast = prog.parse::<IDLProg>().unwrap();

    // Assert doc comments
    let actor = ast.actor.unwrap();
    assert_eq!(actor.docs, vec!["Doc comment for service"]);

    let methods = if let IDLTypeKind::ServT(methods) = &actor.typ {
        methods
    } else {
        panic!("actor is not a service");
    };
    assert_eq!(methods[0].docs, vec!["Doc comment for f"]);
    assert!(methods[1].docs.is_empty());
    assert!(methods[2].docs.is_empty());
    assert!(methods[3].docs.is_empty());

    let my_type = ast
        .decs
        .iter()
        .find_map(|dec| {
            if let Dec::TypD(binding) = dec {
                if binding.id == "my_type" {
                    Some(binding)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(my_type.docs, vec!["Doc comment for my_type"]);

    let list = ast
        .decs
        .iter()
        .find_map(|dec| {
            if let Dec::TypD(binding) = dec {
                if binding.id == "List" {
                    Some(binding)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .unwrap();
    match &list.typ {
        IDLTypeKind::OptT(list_inner) => {
            let fields = if let IDLTypeKind::RecordT(fields) = list_inner.as_ref() {
                fields
            } else {
                panic!("inner is not a record");
            };
            assert_eq!(fields[0].docs, vec!["Doc comment for List.head"]);
            assert!(fields[1].docs.is_empty());
        }
        _ => panic!("list is not an opt"),
    }

    let nested = ast
        .decs
        .iter()
        .find_map(|dec| {
            if let Dec::TypD(binding) = dec {
                if binding.id == "nested" {
                    Some(binding)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .unwrap();
    assert!(nested.docs.is_empty());
}

#[test_generator::test_resources("rust/candid_parser/tests/assets/*.did")]
fn compiler_test(resource: &str) {
    let base_path = std::env::current_dir().unwrap().join("tests/assets");
    let mut mint = Mint::new(base_path.join("ok"));

    let filename = Path::new(Path::new(resource).file_name().unwrap());
    let candid_path = base_path.join(filename);

    match check_file(&candid_path) {
        Ok((env, actor, prog)) => {
            {
                let mut output = mint.new_goldenfile(filename.with_extension("did")).unwrap();
                let content = pretty_print(&prog);
                // Type check output
                let ast = content
                    .parse::<IDLProg>()
                    .unwrap_or_else(|_| panic!("failed to parse candid. Content: {content}"));
                check_prog(&mut TypeEnv::new(), &ast).unwrap();
                writeln!(output, "{content}").unwrap();
            }
            {
                match filename.file_name().unwrap().to_str().unwrap() {
                    "unicode.did" | "escape.did" => check_error(
                        || motoko::compile(&env, &actor, &prog),
                        "not a valid Motoko id",
                    ),
                    _ => {
                        let mut output =
                            mint.new_goldenfile(filename.with_extension("mo")).unwrap();
                        let content = motoko::compile(&env, &actor, &prog);
                        writeln!(output, "{content}").unwrap();
                    }
                }
            }
            {
                use rust::{Config, ExternalConfig};
                use std::str::FromStr;
                let mut config = Config::new(Configs::from_str("").unwrap());
                let mut external = ExternalConfig::default();
                external
                    .0
                    .insert("canister_id".to_string(), "aaaaa-aa".to_string());
                match filename.file_name().unwrap().to_str().unwrap() {
                    "management.did" => {
                        drop(external.0.insert("target".to_string(), "agent".to_string()))
                    }
                    "class.did" => {
                        drop(external.0.insert("target".to_string(), "stub".to_string()))
                    }
                    "example.did" => {
                        let configs = std::fs::read_to_string(base_path.join("example.toml"))
                            .unwrap()
                            .parse::<Configs>()
                            .unwrap();
                        config = Config::new(configs);
                    }
                    _ => (),
                }
                let mut output = mint.new_goldenfile(filename.with_extension("rs")).unwrap();
                let (content, unused) = rust::compile(&config, &env, &actor, &prog, external);
                assert!(
                    unused.is_empty(),
                    "Expected no unused fields, got {unused:?}"
                );
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
                let content = typescript::compile(&env, &actor, &prog);
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

fn check_error<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F, str: &str) {
    assert_eq!(
        std::panic::catch_unwind(f)
            .err()
            .and_then(|a| a.downcast_ref::<String>().map(|s| { s.contains(str) })),
        Some(true)
    );
}
