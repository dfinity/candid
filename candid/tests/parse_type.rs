use candid::parser::grammar::IDLProgParser;
use candid::parser::lexer::Lexer;
use candid::parser::types::{to_pretty, IDLProg};

fn parse_idl(input: &str) -> IDLProg {
    let lexer = Lexer::new(input);
    IDLProgParser::new().parse(lexer).unwrap()
}

#[test]
fn parse_idl_prog() {
    let prog = r#"
import "test.did";
type my_type = nat8;
type List = record { head: int; tail: List };
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
    let ast = parse_idl(&prog);
    let pretty = to_pretty(&ast, 80);
    println!("{}", pretty);
    let ast2 = parse_idl(&pretty);
    assert_eq!(format!("{:?}", ast2), format!("{:?}", ast));
}
