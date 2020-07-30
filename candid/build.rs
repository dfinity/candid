fn main() {
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .emit_rerun_directives(true)
        .process_file("src/parser/grammar.lalrpop")
        .unwrap();

    // Make sure we only rerun the build script if we need to.
    eprintln!("cargo:rerun-if-changed=src/parser/grammar.lalrpop");
    eprintln!("cargo:rerun-if-changed=build.rs");
}
