fn main() {
    lalrpop::Configuration::new()
        .generate_in_source_tree()
        .force_build(true)
        .process_file("src/parser/grammar.lalrpop")
        .unwrap();
}
