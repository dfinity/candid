fn main() {
    lalrpop::Configuration::new()
        .generate_in_source_tree()
        .emit_rerun_directives(true)
        .process()
        .unwrap();
}
