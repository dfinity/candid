extern crate lalrpop;

fn main() {
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .force_build(false)
        .process()
        .unwrap();
}
