use candid_parser::syntax::{Binding, Dec, IDLProg, IDLType, TypeField};

#[test]
fn test_doc_comments_separated_by_blank_line() {
    // Test that comments separated by blank lines are not attached
    let input = r#"
// This comment is separated by a blank line
// and should NOT be attached to the type

type network = variant {
  mainnet;
  testnet;
  regtest;
};
"#;

    let prog: IDLProg = input.parse().unwrap();
    let binding = extract_type_declaration(&prog.decs[0]);

    assert_eq!(binding.id, "network");
    assert!(
        binding.docs.is_empty(),
        "Comments separated by blank line should not be attached, but found: {:?}",
        binding.docs
    );
}

#[test]
fn test_inline_comments_not_attached() {
    // Test that inline comments are not attached to the next field
    let input = r#"
type network = variant {
  mainnet;
  testnet;  // Bitcoin testnet4.
  regtest;
};
"#;

    let prog: IDLProg = input.parse().unwrap();
    let binding = extract_type_declaration(&prog.decs[0]);
    assert_eq!(binding.id, "network");

    // No field should have the inline comment
    let fields = extract_variant_fields(&binding.typ);
    assert_eq!(fields.len(), 3);
    for field in fields {
        assert!(
            field.docs.is_empty(),
            "Inline comment should not be attached to next field, but found: {:?} for field {}",
            field.docs,
            field.label
        );
    }
}

#[test]
fn test_adjacent_comments_are_attached() {
    // Test that adjacent comments (no blank line) are attached
    let input = r#"
// Doc comment for network
type network = variant {
  mainnet;
  // Doc comment for testnet
  testnet;
  regtest;
};
"#;

    let prog: IDLProg = input.parse().unwrap();
    let binding = extract_type_declaration(&prog.decs[0]);

    // Check that the network type has the doc comment attached
    assert_eq!(binding.id, "network");
    assert_eq!(
        binding.docs.len(),
        1,
        "Adjacent comment should be attached to type"
    );
    assert_eq!(binding.docs[0], "Doc comment for network");

    let fields = extract_variant_fields(&binding.typ);
    assert_eq!(fields.len(), 3);

    // Check that only the testnet field has the doc comment
    for field in fields {
        if format!("{}", field.label) == "testnet" {
            assert_eq!(field.docs[0], "Doc comment for testnet");
        } else {
            assert!(field.docs.is_empty());
        }
    }
}

#[test]
fn test_multiple_blank_lines() {
    // Test that multiple blank lines prevent attachment
    let input = r#"
// Comment separated by multiple blank lines


type my_type = nat;
"#;

    let prog: IDLProg = input.parse().unwrap();
    let binding = extract_type_declaration(&prog.decs[0]);

    assert_eq!(binding.id, "my_type");
    assert!(
        binding.docs.is_empty(),
        "Comments separated by multiple blank lines should not be attached, but found: {:?}",
        binding.docs
    );
}

fn extract_type_declaration(dec: &Dec) -> &Binding {
    if let Dec::TypD(binding) = dec {
        return binding;
    }
    panic!("Expected a type declaration");
}

fn extract_variant_fields(typ: &IDLType) -> &[TypeField] {
    if let IDLType::VariantT(fields) = typ {
        return fields;
    }
    panic!("Expected a variant type");
}
