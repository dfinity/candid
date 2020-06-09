use candid::parser::types::{to_pretty, IDLProg};
use candid::parser::typing::{check_prog, TypeEnv};
use std::path::Path;

#[test]
fn parse_idl_prog() {
    let prog = r#"
import "test.did";
type my_type = nat8;
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
    println!("{}", pretty);
    let ast2 = pretty.parse::<IDLProg>().unwrap();
    assert_eq!(format!("{:?}", ast2), format!("{:?}", ast));
    let mut env = TypeEnv::new();
    let _actor = check_prog(&mut env, &ast).unwrap();
}

#[test_generator::test_resources("candid/tests/assets/candid/*.did")]
fn compiler_test(resource: &str) {
    let path = std::env::current_dir()
        .unwrap()
        .parent()
        .unwrap()
        .join(Path::new(resource));
    let prog = std::fs::read_to_string(&path).unwrap();
    let ast = prog.parse::<IDLProg>().unwrap();
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).unwrap();
    assert!(!env.0.is_empty());
    assert!(!actor.is_empty());
}
