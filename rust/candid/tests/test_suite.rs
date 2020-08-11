use candid::parser::test::Test;

#[test_generator::test_resources("test/*.test.did")]
fn decode_test(resource: &str) {
    let path = std::env::current_dir()
        .unwrap()
        .join("../../")
        .join(resource);
    let test = std::fs::read_to_string(path).unwrap();
    let _ast = test.parse::<Test>().unwrap();
}
