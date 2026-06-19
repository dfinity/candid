use candid::{CandidType, Decode, Deserialize, Encode};

#[test]
fn record_vectors_remain_backward_and_forward_compatible() {
    #[derive(Clone, Debug, PartialEq, Eq, Deserialize, CandidType)]
    struct Old {
        id: u32,
        flag: bool,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Deserialize, CandidType)]
    struct New {
        extra: Option<u8>,
        id: u32,
        flag: bool,
    }

    let old_values = vec![Old { id: 1, flag: true }, Old { id: 2, flag: false }];
    let old_bytes = Encode!(&old_values).unwrap();
    let decoded_new_values = Decode!(&old_bytes, Vec<New>).unwrap();
    assert_eq!(
        decoded_new_values,
        vec![
            New {
                extra: None,
                id: 1,
                flag: true,
            },
            New {
                extra: None,
                id: 2,
                flag: false,
            },
        ]
    );

    let new_values = vec![
        New {
            extra: Some(10),
            id: 1,
            flag: true,
        },
        New {
            extra: None,
            id: 2,
            flag: false,
        },
    ];
    let new_bytes = Encode!(&new_values).unwrap();
    let decoded_old_values = Decode!(&new_bytes, Vec<Old>).unwrap();
    assert_eq!(decoded_old_values, old_values);
}
