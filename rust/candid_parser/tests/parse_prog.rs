use candid_parser::{
    parse_idl_prog_from_tokens, parse_prog_lossy,
    syntax::Dec,
    token::{self, TriviaMap},
};

fn decl_names(decs: &[Dec]) -> Vec<&str> {
    decs.iter()
        .filter_map(|dec| match dec {
            Dec::TypD(binding) => Some(binding.id.as_str()),
            _ => None,
        })
        .collect()
}

#[test]
fn parses_program_from_recorded_tokens() {
    let source = r#"
        // doc: Foo
        type Foo = record { field : int };
        service : { foo : () -> (); };
    "#;
    let trivia = TriviaMap::default();
    let tokens: Vec<_> = token::Tokenizer::new_with_trivia(source, trivia.clone()).collect();
    let prog = parse_idl_prog_from_tokens(Some(&trivia), tokens).expect("parses");

    let names = decl_names(&prog.decs);
    assert_eq!(names, vec!["Foo"]);
    let docs = match &prog.decs[0] {
        Dec::TypD(binding) => binding.docs.clone(),
        _ => unreachable!(),
    };
    assert_eq!(docs, vec!["doc: Foo".to_string()]);
    assert!(
        prog.actor.is_some(),
        "service definition should be preserved"
    );
}

#[test]
fn lossy_parser_recovers_declarations_and_reports_errors() {
    let source = r#"
        type Good = record { foo : int };
        type Broken = record { foo : };
        type AlsoGood = record { bar : text };
        service : {
            bad : ( -> ) -> ();
            ok : () -> ();
        };
    "#;

    let (maybe_prog, errors) = parse_prog_lossy(source);
    assert!(
        errors.len() >= 2,
        "should surface multiple parse errors, got {errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|err| matches!(err, lalrpop_util::ParseError::UnrecognizedToken { .. })),
        "expected at least one syntax error in the error list"
    );
    let prog = maybe_prog.expect("should recover valid declarations");
    let names = decl_names(&prog.decs);
    assert_eq!(names, vec!["Good", "AlsoGood"]);
    assert!(
        prog.actor.is_none(),
        "actor should be dropped due to unrecoverable service parse error"
    );
}
