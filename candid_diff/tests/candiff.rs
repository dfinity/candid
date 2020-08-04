use predicates::prelude::*;
use assert_cmd::Command;

#[test]
fn help() {
    let mut cmd = Command::cargo_bin("candiff").unwrap();
    cmd.arg("help");
    cmd.assert().success();
}

fn candiff() -> Command {
    Command::cargo_bin("candiff").unwrap()
}

mod echo {
    use super::*;

    #[test]
    fn number() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("1");
        cmd.assert()
            .stdout(predicate::eq(b"1\n" as &[u8]))
            .success();
    }

    #[test]
    fn number_debug() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("1").arg("-d");
        cmd.assert()
            .stdout(predicate::eq(b"Number(\"1\")\n" as &[u8]))
            .success();
    }

    #[test]
    fn nat_debug() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("1").arg("-t nat").arg("-d");
        cmd.assert()
            .stdout(predicate::eq(b"Nat(Nat(BigUint { data: [1] }))\n" as &[u8]))
            .success();
    }

    #[test]
    fn int_debug() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("1").arg("-t int").arg("-d");
        cmd.assert()
            .stdout(predicate::eq(b"Int(Int(BigInt { sign: Plus, data: BigUint { data: [1] } }))\n" as &[u8]))
            .success();
    }

    #[test]
    fn vec_num() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("vec {1; 2}");
        cmd.assert()
            .stdout(predicate::eq(b"vec { 1; 2; }\n" as &[u8]))
            .success();
    }

    #[test]
    fn variant_num() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("variant { 1 = 2 }");
        cmd.assert()
            .stdout(predicate::eq(b"variant { 1 = 2 }\n" as &[u8]))
            .success();
    }

    #[test]
    fn variant_label() {
        let mut cmd = candiff();
        cmd.arg("echo").arg("variant { xyz = 2 }");
        cmd.assert()
            .stdout(predicate::eq(b"variant { xyz = 2 }\n" as &[u8]))
            .success();
    }
}

mod diff {
    use super::*;

    #[test]
    fn true_true() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("true").arg("true");
        cmd.assert()
            .stdout(predicate::eq(b"" as &[u8]))
            .success();
    }

    #[test]
    fn true_false() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("true").arg("false");
        cmd.assert()
            .stdout(predicate::eq(b"put { false }\n" as &[u8]))
            .success();
    }

    #[test]
    fn false_true() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("false").arg("true");
        cmd.assert()
            .stdout(predicate::eq(b"put { true }\n" as &[u8]))
            .success();
    }

    #[test]
    fn one_one() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("1").arg("1");
        cmd.assert()
            .stdout(predicate::eq(b"" as &[u8]))
            .success();
    }

    #[test]
    fn one_two() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("1").arg("2");
        cmd.assert()
            .stdout(predicate::eq(b"put { 2 }\n" as &[u8]))
            .success();
    }

    #[test]
    fn neg_one_neg_one_typed() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("vec { -1 }").arg("vec { -1 }").arg("-t vec int");
        cmd.assert()
            .stdout(predicate::eq(b"" as &[u8]))
            .success();
    }

    #[test]
    fn neg_one_neg_one_untyped() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("vec { -1 }").arg("vec { -1 }").arg("-d");
        cmd.assert()
            .stdout(predicate::eq(b"" as &[u8]))
            .success();
    }

    #[test]
    fn null_null() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("null").arg("null");
        cmd.assert()
            .stdout(predicate::eq(b"" as &[u8]))
            .success();
    }

    #[test]
    fn text_empty_empty() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("\"\"").arg("\"\"");
        cmd.assert()
            .stdout(predicate::eq(b"" as &[u8]))
            .success();
    }

    #[test]
    fn text_a_text_b() {
        let mut cmd = candiff();
        cmd.arg("diff").arg("\"a\"").arg("\"b\"");
        cmd.assert()
            .stdout(predicate::eq(b"put { \"b\" }\n" as &[u8]))
            .success();
    }

    #[test]
    fn vec_nat_put() {
        let v1 = "vec { vec { 0; 0; } ; vec{ 1 ; 1; } ; vec {2; 2;} ; }";
        let v2 = "vec { vec { 0; 0; } ; vec{ 1 ; 3; } ; vec {2; 2;} ; }";
        let mut cmd = candiff();
        cmd.arg("diff").arg(v1).arg(v2).arg("-t vec vec nat");
        cmd.assert()
            .stdout(predicate::eq(b"vec { edit { 1 vec { edit { 1 put { 3 } }; } }; }\n" as &[u8]))
            .success();
    }

    #[test]
    fn vec_nat_insert() {
        let v1 = "vec { vec { 0; 0; } ; vec{ 1 ; 1; } ; vec {2; 2;} ; }";
        let v2 = "vec { vec { 0; 0; } ; vec{ 1 ; 1; } ; vec {2; 2; 2} ; }";
        let mut cmd = candiff();
        cmd.arg("diff").arg(v1).arg(v2).arg("-t vec vec nat");
        cmd.assert()
            .stdout(predicate::eq(b"vec { edit { 2 vec { insert { 2 2 }; } }; }\n" as &[u8]))
            .success();
    }
}
