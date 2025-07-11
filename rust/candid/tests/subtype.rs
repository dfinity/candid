use std::collections::HashSet;

use candid::types::subtype::{subtype, subtype_with_config, OptReport};
use candid_parser::utils::CandidSource;

const CANDID1: &str = r#"
type Token = variant {
    ICP;
    USDC
};

type Asset = record {
    token : opt Token
};

service : {
    "go" : (Asset) -> (Asset) query
}
"#;
const CANDID2: &str = r#"
type Token = variant {
    ICP;
    USDC;
    USDT
};

type Asset = record {
    token : opt Token
};

service : {
    "go" : (Asset) -> (Asset) query
}
"#;

#[test]
fn test_subtype() {
    let (mut env, opt_new) = CandidSource::Text(CANDID1).load().unwrap();
    let new_type = opt_new.unwrap();
    let (env2, opt_old) = CandidSource::Text(CANDID2).load().unwrap();
    let old_type = opt_old.unwrap();
    let mut gamma = HashSet::new();
    let old_type = env.merge_type(env2, old_type);

    let result = subtype(&mut gamma, &env, &new_type, &old_type);
    assert!(result.is_ok(), "{result:?}");

    let result_with_config =
        subtype_with_config(OptReport::Error, &mut gamma, &env, &new_type, &old_type);
    assert!(result_with_config.is_ok(), "{result_with_config:?}");
}

#[test]
fn test_subtype_with_config() {
    let (mut env, opt_new) = CandidSource::Text(CANDID1).load().unwrap();
    let new_type = opt_new.unwrap();
    let (env2, opt_old) = CandidSource::Text(CANDID2).load().unwrap();
    let old_type = opt_old.unwrap();
    let mut gamma = HashSet::new();
    let old_type = env.merge_type(env2, old_type);

    let result = subtype_with_config(OptReport::Error, &mut gamma, &env, &new_type, &old_type);
    assert!(result.is_ok(), "{result:?}");
}

#[test]
fn test_subtype_inverse() {
    let (mut env, opt_new) = CandidSource::Text(CANDID2).load().unwrap();
    let new_type = opt_new.unwrap();
    let (env2, opt_old) = CandidSource::Text(CANDID1).load().unwrap();
    let old_type = opt_old.unwrap();
    let mut gamma = HashSet::new();
    let old_type = env.merge_type(env2, old_type);

    let result = subtype(&mut gamma, &env, &new_type, &old_type);
    // By default, the inner subtype_ does not return errors.
    assert!(result.is_ok(), "{result:?}");
}

#[test]
fn test_subtype_with_config_inverse() {
    let (mut env, opt_new) = CandidSource::Text(CANDID2).load().unwrap();
    let new_type = opt_new.unwrap();
    let (env2, opt_old) = CandidSource::Text(CANDID1).load().unwrap();
    let old_type = opt_old.unwrap();
    let mut gamma = HashSet::new();
    let old_type = env.merge_type(env2, old_type);

    let result = subtype_with_config(OptReport::Error, &mut gamma, &env, &new_type, &old_type);
    assert!(result.is_err());
}
