fn main() {
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .force_build(true)
        .process_file("src/parser/grammar.lalrpop")
        .unwrap();
}
