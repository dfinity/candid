// #![allow(deprecated)]

use ic_principal::Principal;
#[cfg(feature = "convert")]
use ic_principal::PrincipalError;

const MANAGEMENT_CANISTER_BYTES: [u8; 0] = [];
#[allow(dead_code)]
const MANAGEMENT_CANISTER_TEXT: &str = "aaaaa-aa";

const ANONYMOUS_CANISTER_BYTES: [u8; 1] = [4u8];
#[allow(dead_code)]
const ANONYMOUS_CANISTER_TEXT: &str = "2vxsx-fae";

const TEST_CASE_BYTES: [u8; 9] = [0xef, 0xcd, 0xab, 0, 0, 0, 0, 0, 1];
#[allow(dead_code)]
const TEST_CASE_TEXT: &str = "2chl6-4hpzw-vqaaa-aaaaa-c";

#[cfg(feature = "convert")]
mod try_convert_from_bytes {
    use super::*;

    #[test]
    fn try_from_test_case_ok() {
        assert!(Principal::try_from_slice(&TEST_CASE_BYTES).is_ok());
    }

    #[test]
    fn try_from_slice_length_0_29_ok() {
        let array = [0u8; 29];
        for len in 0..30 {
            assert!(Principal::try_from_slice(&array[..len]).is_ok());
        }
    }

    #[test]
    fn try_from_slice_length_30_err() {
        assert_eq!(
            Principal::try_from_slice(&[0u8; 30]),
            Err(PrincipalError::BytesTooLong())
        );
    }
}

mod convert_from_bytes {
    use super::*;

    #[test]
    fn from_test_case_ok() {
        Principal::from_slice(&TEST_CASE_BYTES);
    }

    #[test]
    fn from_slice_length_0_29_ok() {
        let array = [0u8; 29];
        for len in 0..30 {
            Principal::from_slice(&array[..len]);
        }
    }

    #[test]
    #[should_panic]
    fn from_slice_length_30_err() {
        Principal::from_slice(&[0u8; 30]);
    }
}

#[cfg(feature = "convert")]
mod convert_from_text {
    use super::*;

    #[test]
    fn convert_from_test_case_ok() {
        // input must be 8~63 chars including `-`s
        // using empty blob as shortest test case
        assert!(Principal::from_text(TEST_CASE_TEXT).is_ok());
    }

    #[test]
    fn convert_from_management_canister_text_ok() {
        // input must be 8~63 chars including `-`s
        // using empty blob as shortest test case
        assert!(Principal::from_text(MANAGEMENT_CANISTER_TEXT).is_ok());
    }

    #[test]
    fn convert_from_29_0u8_ok() {
        // input must be 8~63 chars including `-`s
        // using [0u8; 29] as longest test case
        assert!(Principal::from_text(
            "bnkmk-jqaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaa"
        )
        .is_ok());
    }

    #[test]
    fn convert_from_6a_invalid_base_32() {
        assert_eq!(
            Principal::from_text("aaaaa-a"),
            Err(PrincipalError::InvalidBase32())
        );
    }

    #[test]
    fn convert_from_5a_text_too_short() {
        assert_eq!(
            Principal::from_text("aaaaa"),
            Err(PrincipalError::TextTooShort())
        );
    }

    #[test]
    fn convert_from_30_0u8_text_too_long() {
        assert_eq!(
            Principal::from_text(
                "aacd5-niaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa-aaaaa"
            ),
            Err(PrincipalError::TextTooLong())
        );
    }

    #[test]
    fn convert_from_wrong_dash_position_err() {
        assert_eq!(
            Principal::from_text("aaaaaaa"),
            Err(PrincipalError::AbnormalGrouped(
                Principal::management_canister()
            ))
        );
        assert_eq!(
            Principal::from_text("aaaaaa-a"),
            Err(PrincipalError::AbnormalGrouped(
                Principal::management_canister()
            ))
        );
        assert_eq!(
            Principal::from_text("aaaaaaa-"),
            Err(PrincipalError::AbnormalGrouped(
                Principal::management_canister()
            ))
        );
        assert_eq!(
            Principal::from_text("-aaaaaaa"),
            Err(PrincipalError::AbnormalGrouped(
                Principal::management_canister()
            ))
        );
        assert_eq!(
            Principal::from_text("aaa-aaaa"),
            Err(PrincipalError::AbnormalGrouped(
                Principal::management_canister()
            ))
        );
    }

    #[test]
    fn convert_from_uppercase_ok() {
        assert_eq!(
            Principal::from_text("AAAAA-AA"),
            Ok(Principal::management_canister())
        );
        assert_eq!(
            Principal::from_text("aaaaa-AA"),
            Ok(Principal::management_canister())
        );
    }
}

mod convert_to_bytes {
    use super::*;

    #[test]
    fn managements_canister_converts_to_empty_slice() {
        assert_eq!(
            Principal::management_canister().as_slice(),
            &MANAGEMENT_CANISTER_BYTES
        );
    }

    #[test]
    fn anonymouse_converts_to_single_byte_04() {
        assert_eq!(Principal::anonymous().as_slice(), &ANONYMOUS_CANISTER_BYTES);
    }

    #[test]
    #[cfg(feature = "convert")]
    fn test_case_to_bytes_correct() {
        assert_eq!(
            Principal::from_text(TEST_CASE_TEXT).unwrap().as_slice(),
            &TEST_CASE_BYTES
        );
    }
}

#[cfg(feature = "convert")]
mod convert_to_text {
    use super::*;

    #[test]
    fn managements_canister_to_text_correct() {
        assert_eq!(
            Principal::management_canister().to_text(),
            MANAGEMENT_CANISTER_TEXT.to_string()
        );
    }

    #[test]
    fn anonymous_to_text_correct() {
        assert_eq!(
            Principal::anonymous().to_text(),
            ANONYMOUS_CANISTER_TEXT.to_string()
        );
    }

    #[test]
    fn test_case_to_text_correct() {
        assert_eq!(
            Principal::try_from_slice(&TEST_CASE_BYTES)
                .unwrap()
                .to_text(),
            TEST_CASE_TEXT.to_string()
        );
    }
}

#[cfg(feature = "serde")]
mod ser_de {
    use super::*;
    use serde_test::{assert_tokens, Configure, Token};

    #[test]
    fn management_canister_serde_match() {
        let p = Principal::management_canister();
        assert_tokens(&p.compact(), &[Token::Bytes(&MANAGEMENT_CANISTER_BYTES)]);
        assert_tokens(&p.readable(), &[Token::Str(MANAGEMENT_CANISTER_TEXT)]);
    }

    #[test]
    fn test_case_serde_match() {
        let p = Principal::try_from_slice(&TEST_CASE_BYTES).unwrap();
        assert_tokens(&p.compact(), &[Token::Bytes(&TEST_CASE_BYTES)]);
        assert_tokens(&p.readable(), &[Token::Str(TEST_CASE_TEXT)]);
    }
}

#[test]
fn impl_traits() {
    #[cfg(feature = "serde")]
    use serde::{Deserialize, Serialize};
    #[cfg(feature = "convert")]
    use std::convert::TryFrom;
    use std::fmt::Debug;
    #[cfg(feature = "convert")]
    use std::fmt::Display;
    use std::hash::Hash;
    #[cfg(feature = "convert")]
    use std::str::FromStr;

    assert!(impls::impls!(
        Principal: Debug & Clone & Copy & Eq & PartialOrd & Ord & Hash
    ));

    #[cfg(feature = "convert")]
    assert!(
        impls::impls!(Principal: Display & FromStr & TryFrom<&'static str> & TryFrom<Vec<u8>> & TryFrom<&'static Vec<u8>> & TryFrom<&'static [u8]> & AsRef<[u8]>)
    );

    #[cfg(feature = "serde")]
    assert!(impls::impls!(Principal: Serialize & Deserialize<'static>));
}

#[test]
#[cfg(feature = "convert")]
fn long_blobs_ending_04_is_valid_principal() {
    let blob: [u8; 18] = [
        10, 116, 105, 100, 0, 0, 0, 0, 0, 144, 0, 51, 1, 1, 0, 0, 0, 4,
    ];
    assert!(Principal::try_from_slice(&blob).is_ok());
}

#[test]
#[cfg(feature = "self_authenticating")]
fn self_authenticating_ok() {
    // self_authenticating doesn't verify the input bytes
    // this test checks:
    // 1. Sha224 hash is used
    // 2. 0x02 was added in the end
    // 3. total length is 29
    let p1 = Principal::self_authenticating([]);
    let p2 = Principal::from_slice(&[
        209, 74, 2, 140, 42, 58, 43, 201, 71, 97, 2, 187, 40, 130, 52, 196, 21, 162, 176, 31, 130,
        142, 166, 42, 197, 179, 228, 47, 2,
    ]);
    assert_eq!(p1, p2);
}
