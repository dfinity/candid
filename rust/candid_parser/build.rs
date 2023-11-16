fn main() {
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .emit_rerun_directives(true)
        .process_file("src/grammar.lalrpop")
        .unwrap();
}
