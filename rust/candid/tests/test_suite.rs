use candid::parser::test::{check, Test};

#[test_generator::test_resources("test/*.test.did")]
fn decode_test(resource: &str) {
    let path = std::env::current_dir()
        .unwrap()
        .join("../../")
        .join(resource);
    let test = std::fs::read_to_string(path).unwrap();
    let ast = test.parse::<Test>().unwrap();
    match check(ast) {
        Ok(()) => (),
        Err(err) => println!("Failed: {}", err)
    }
}

#[test_generator::test_resources("test/*.test.did")]
fn js_test(resource: &str) {
    use candid::bindings::javascript::test::test_generate;
    let path = std::env::current_dir()
        .unwrap()
        .join("../../")
        .join(resource);
    let test = std::fs::read_to_string(path).unwrap();
    match test.parse::<Test>() {
        Ok(ast) => println!("{}", test_generate(ast)),
        Err(err) => println!("Failed: {}", err)
    }
}
