use candid::parser::test::{check, Test};

#[test_generator::test_resources("test/prim.test.did")]
fn decode_test(resource: &str) {
    let path = std::env::current_dir()
        .unwrap()
        .join("../../")
        .join(resource);
    let test = std::fs::read_to_string(path).unwrap();
    let ast = test.parse::<Test>().unwrap();
    check(ast).unwrap();
}
