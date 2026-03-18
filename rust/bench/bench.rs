use canbench_rs::{bench, bench_fn, bench_scope, BenchResult};
use candid::{
    CandidType, Decode, DecoderConfig, Deserialize, Encode, IDLArgs, IDLValue, Int, Nat, Principal,
};
use std::collections::BTreeMap;

#[allow(clippy::all)]
mod nns;

const N: usize = 2097152;
const COST: usize = 25_000_000;
const SKIP: usize = 10_000;

#[bench(raw)]
fn blob() -> BenchResult {
    use serde_bytes::ByteBuf;
    let vec: Vec<u8> = vec![0x61; N];
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&ByteBuf::from(vec)).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, ByteBuf).unwrap();
        }
    })
}

#[bench(raw)]
fn text() -> BenchResult {
    let vec: Vec<u8> = vec![0x61; N];
    let text = String::from_utf8(vec).unwrap();
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&text).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, String).unwrap();
        }
    })
}

#[bench(raw)]
fn vec_int16() -> BenchResult {
    let vec: Vec<i16> = vec![-1; N];
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&vec).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<i16>).unwrap();
        }
    })
}

#[bench(raw)]
fn vec_nat() -> BenchResult {
    let vec: Vec<Nat> = (0u64..262144).map(Nat::from).collect();
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&vec).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<Nat>).unwrap();
        }
    })
}

#[bench(raw)]
fn vec_nat64() -> BenchResult {
    let vec: Vec<u64> = (0u64..N as u64).collect();
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&vec).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<u64>).unwrap();
        }
    })
}

#[bench(raw)]
fn vec_nat32() -> BenchResult {
    let vec: Vec<u32> = (0u32..N as u32).collect();
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&vec).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<u32>).unwrap();
        }
    })
}

#[bench(raw)]
fn btreemap() -> BenchResult {
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    let n = 1048576;
    let map: BTreeMap<String, Nat> = (0u32..n as u32)
        .map(|i| (i.to_string(), Nat::from(i)))
        .collect();
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&map).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, BTreeMap<String, Nat>).unwrap();
        }
    })
}

#[bench(raw)]
fn option_list() -> BenchResult {
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    let n = 2048;
    #[derive(CandidType, Deserialize)]
    struct List {
        head: Int,
        tail: Option<Box<List>>,
    }
    let list: Option<Box<List>> = (0..n).fold(None, |acc, x| {
        Some(Box::new(List {
            head: Int::from(x),
            tail: acc,
        }))
    });
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&list).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Option<Box<List>>).unwrap();
        }
    })
}

#[bench(raw)]
fn variant_list() -> BenchResult {
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    let n = 2048;
    #[derive(CandidType, Deserialize)]
    enum VariantList {
        Nil,
        Cons(Int, Box<VariantList>),
    }
    let list: VariantList = (0..n).fold(VariantList::Nil, |acc, x| {
        VariantList::Cons(Int::from(x), Box::new(acc))
    });
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&list).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, VariantList).unwrap();
        }
    })
}

#[bench(raw)]
fn nns() -> BenchResult {
    use candid_parser::utils::CandidSource;
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    let nns_did = CandidSource::Text(include_str!("./nns.did"));
    let motion_proposal = r#"
(
  record {
    id = opt record { id = 32_768 : nat64 };
    command = opt variant {
      MakeProposal = record {
        url = "http://127.0.0.1";
        title = opt "make a proposal";
        action = opt variant {
          CreateServiceNervousSystem = record {
            url = opt "http://127.0.0.1";
            governance_parameters = opt record {
              neuron_maximum_dissolve_delay_bonus = opt record { basis_points = opt (30 : nat64);};
              neuron_maximum_age_for_age_bonus = opt record { seconds = opt (1_000 : nat64);};
              neuron_maximum_dissolve_delay = opt record { seconds = opt (2_000 : nat64);};
              neuron_minimum_dissolve_delay_to_vote = opt record { seconds = opt (1_000 : nat64);};
              neuron_maximum_age_bonus = opt record { basis_points = opt (30 : nat64);};
              neuron_minimum_stake = opt record { e8s = opt (500 : nat64);};
              proposal_wait_for_quiet_deadline_increase = opt record { seconds = opt (30 : nat64);};
              proposal_initial_voting_period = opt record { seconds = opt (10 : nat64);};
              proposal_rejection_fee = opt record { e8s = opt (1_000 : nat64);};
              voting_reward_parameters = opt record { reward_rate_transition_duration = opt record { seconds = opt (42 : nat64);}; initial_reward_rate = opt record { basis_points = opt (200 : nat64);}; final_reward_rate = opt record { basis_points = opt (300 : nat64);};};
            };
            fallback_controller_principal_ids = vec {
              principal "2vxsx-fae";
              principal "aaaaa-aa";
              principal "a4gq6-oaaaa-aaaab-qaa4q-cai";
            };
            logo = opt record { base64_encoding = opt "LOGO_BASE64" };
            name = opt "field name";
            ledger_parameters = opt record {
              transaction_fee = opt record { e8s = opt (1_000 : nat64);};
              token_symbol = opt "ICP";
              token_logo = opt record { base64_encoding = opt "LOGO_BASE64";};
              token_name = opt "ICP";
            };
            description = opt "description";
            dapp_canisters = vec {
              record { id = opt principal "a4gq6-oaaaa-aaaab-qaa4q-cai" };
            };
            swap_parameters = opt record {
              minimum_participants = opt (10 : nat64);
              neurons_fund_participation = opt true;
              duration = opt record { seconds = opt (100 : nat64);};
              neuron_basket_construction_parameters = opt record { dissolve_delay_interval = opt record { seconds = opt (20 : nat64);}; count = opt (20 : nat64);};
              confirmation_text = opt "confirmation";
              maximum_participant_icp = opt record { e8s = opt (10_000 : nat64);};
              minimum_icp = opt record { e8s = opt (10 : nat64);};
              minimum_direct_participation_icp = opt record { e8s = opt (1 : nat64);};
              minimum_participant_icp = opt record { e8s = opt (1 : nat64);};
              start_time = opt record { seconds_after_utc_midnight = opt (0 : nat64);};
              maximum_direct_participation_icp = opt record { e8s = opt (10_000 : nat64);};
              maximum_icp = opt record { e8s = opt (10_000 : nat64);};
              neurons_fund_investment_icp = opt record { e8s = opt (1_000 : nat64);};
            };
            initial_token_distribution = opt record {
              treasury_distribution = opt record { total = opt record { e8s = opt (1_000 : nat64);};};
              developer_distribution = opt record { developer_neurons = vec { record { controller = opt principal "a4gq6-oaaaa-aaaab-qaa4q-cai"; stake = opt record { e8s = opt (100 : nat64);};};};};
              swap_distribution = opt record { total = opt record { e8s = opt (1_000 : nat64);};};
            };
          }
        };
        summary = "summary";
      }
    };
    neuron_id_or_subaccount = opt variant { Subaccount = blob "\be\ef" };
  },
)
"#;
    bench_fn(|| {
        let _p = bench_scope("0. Parsing");
        let (env, serv) = nns_did.load().unwrap();
        let args = candid_parser::parse_idl_args(motion_proposal).unwrap();
        let serv = serv.unwrap();
        let method = &env.get_method(&serv, "manage_neuron").unwrap();
        drop(_p);
        let bytes = {
            let _p = bench_scope("1. Encoding");
            args.to_bytes_with_types(&env, &method.args).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, nns::ManageNeuron).unwrap();
        }
    })
}

#[bench(raw)]
fn nns_list_proposal() -> BenchResult {
    use crate::nns::{ListProposalInfoResponse, ProposalInfo};
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);
    let proposal = ProposalInfo {
        id: None,
        status: 42,
        topic: 42,
        failure_reason: None,
        ballots: vec![],
        proposal_timestamp_seconds: 42,
        reward_event_round: 42,
        deadline_timestamp_seconds: Some(42),
        failed_timestamp_seconds: 42,
        reject_cost_e8s: 42,
        derived_proposal_information: None,
        latest_tally: None,
        reward_status: 42,
        decided_timestamp_seconds: 42,
        proposal: None,
        proposer: None,
        executed_timestamp_seconds: 42,
    };
    let list_proposals_info_response = ListProposalInfoResponse {
        proposal_info: std::iter::repeat(proposal).take(1000).collect(),
    };
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&list_proposals_info_response).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, ListProposalInfoResponse).unwrap();
        }
    })
}

#[bench(raw)]
fn extra_args() -> BenchResult {
    let mut config = DecoderConfig::new();
    config.set_skipping_quota(SKIP);
    let vec_null = hex::decode("4449444c036c01d6fca702016d026c00010080ade204").unwrap();
    let vec_opt_record = hex::decode("4449444c176c02017f027f6c02010002006c02000101016c02000201026c02000301036c02000401046c02000501056c02000601066c02000701076c02000801086c02000901096c02000a010a6c02000b010b6c02000c010c6c02000d020d6c02000e010e6c02000f010f6c02001001106c02001101116c02001201126c02001301136e146d150116050101010101").unwrap();
    bench_fn(|| {
        assert!(Decode!([config]; &vec_null).is_err());
        assert!(Decode!([config]; &vec_opt_record).is_err());
    })
}

// Vec of fully populated complex structs (21 fields, nested vecs/maps/opts)
// Exercises the dominant real-world payload shape: list endpoints returning large records.
// The existing nns_list_proposal benchmark uses mostly-empty ProposalInfo; this uses
// fully-populated Neurons which are ~5-10x heavier per element.
#[bench(raw)]
fn nns_list_neurons() -> BenchResult {
    use crate::nns::*;
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);

    let make_neuron = |i: u64| Neuron {
        id: Some(NeuronId { id: i }),
        staked_maturity_e8s_equivalent: Some(1_000_000),
        controller: Some(Principal::from_slice(&i.to_be_bytes())),
        recent_ballots: (0..100)
            .map(|j| BallotInfo {
                vote: if j % 2 == 0 { 1 } else { 2 },
                proposal_id: Some(NeuronId { id: j }),
            })
            .collect(),
        kyc_verified: true,
        neuron_type: Some(1),
        not_for_profit: false,
        maturity_e8s_equivalent: 500_000,
        cached_neuron_stake_e8s: 10_000_000_000,
        created_timestamp_seconds: 1_700_000_000 + i,
        auto_stake_maturity: Some(true),
        aging_since_timestamp_seconds: 1_700_000_000,
        hot_keys: (0..5)
            .map(|j| Principal::from_slice(&[j as u8; 10]))
            .collect(),
        account: serde_bytes::ByteBuf::from(vec![i as u8; 32]),
        joined_community_fund_timestamp_seconds: Some(1_700_000_000),
        dissolve_state: Some(DissolveState::DissolveDelaySeconds(15_778_800)),
        followees: (0..10)
            .map(|topic| {
                (
                    topic,
                    Followees {
                        followees: (0..5).map(|f| NeuronId { id: f as u64 }).collect(),
                    },
                )
            })
            .collect(),
        neuron_fees_e8s: 10_000,
        transfer: Some(NeuronStakeTransfer {
            to_subaccount: serde_bytes::ByteBuf::from(vec![0u8; 32]),
            neuron_stake_e8s: 10_000_000_000,
            from: Some(Principal::from_slice(&[1u8; 10])),
            memo: 42,
            from_subaccount: serde_bytes::ByteBuf::from(vec![0u8; 32]),
            transfer_timestamp: 1_700_000_000,
            block_height: 1_000_000,
        }),
        known_neuron_data: Some(KnownNeuronData {
            name: format!("neuron-{}", i),
            description: Some(format!("A known neuron #{}", i)),
        }),
        spawn_at_timestamp_seconds: None,
    };

    let neuron_infos: Vec<(u64, nns::NeuronInfo)> = (0..100)
        .map(|i| {
            (
                i,
                nns::NeuronInfo {
                    dissolve_delay_seconds: 15_778_800,
                    recent_ballots: (0..100)
                        .map(|j| BallotInfo {
                            vote: 1,
                            proposal_id: Some(NeuronId { id: j }),
                        })
                        .collect(),
                    neuron_type: Some(1),
                    created_timestamp_seconds: 1_700_000_000,
                    state: 1,
                    stake_e8s: 10_000_000_000,
                    joined_community_fund_timestamp_seconds: Some(1_700_000_000),
                    retrieved_at_timestamp_seconds: 1_700_000_000,
                    known_neuron_data: Some(KnownNeuronData {
                        name: format!("neuron-{}", i),
                        description: Some(format!("Known neuron #{}", i)),
                    }),
                    voting_power: 20_000_000_000,
                    age_seconds: 31_557_600,
                },
            )
        })
        .collect();

    let response = nns::ListNeuronsResponse {
        neuron_infos,
        full_neurons: (0..100).map(make_neuron).collect(),
    };

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&response).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, nns::ListNeuronsResponse).unwrap();
        }
    })
}

// Schema evolution — encode with a newer type (16 fields), decode with an older
// type (4 fields). Forces the decoder to skip 12 unknown fields per record, exercising
// the field-skipping mechanism that has zero coverage in the existing benchmark.
#[bench(raw)]
fn subtype_decode() -> BenchResult {
    #[derive(CandidType)]
    struct RecordV2 {
        id: u64,
        name: String,
        balance: u64,
        active: bool,
        score: f64,
        owner: Principal,
        data: serde_bytes::ByteBuf,
        count: u32,
        extra_field_1: String,
        extra_field_2: u64,
        extra_field_3: Option<String>,
        extra_field_4: Vec<u8>,
        extra_field_5: bool,
        extra_field_6: f64,
        extra_field_7: Principal,
        extra_field_8: u32,
    }

    #[derive(CandidType, Deserialize)]
    struct RecordV1 {
        id: u64,
        name: String,
        balance: u64,
        active: bool,
    }

    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST);

    let records: Vec<RecordV2> = (0..1000)
        .map(|i| RecordV2 {
            id: i as u64,
            name: format!("record-{}", i),
            balance: i as u64 * 1000,
            active: i % 2 == 0,
            score: i as f64 * 1.5,
            owner: Principal::from_slice(&(i as u32).to_be_bytes()),
            data: serde_bytes::ByteBuf::from(vec![i as u8; 64]),
            count: i as u32,
            extra_field_1: format!("extra-{}", i),
            extra_field_2: i as u64 * 42,
            extra_field_3: Some(format!("optional-{}", i)),
            extra_field_4: vec![i as u8; 16],
            extra_field_5: i % 3 == 0,
            extra_field_6: i as f64 * 2.7,
            extra_field_7: Principal::from_slice(&(i as u32 + 1000).to_be_bytes()),
            extra_field_8: i as u32 * 7,
        })
        .collect();

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&records).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<RecordV1>).unwrap();
        }
    })
}

// Vec of service references (subscriber/registry collection pattern).
// This is the ONLY decode path where check_subtype() fires (deserialize_service
// and deserialize_function). The existing benchmark has zero coverage of this
// code path. See https://github.com/dfinity/candid/issues/603
#[bench(raw)]
fn vec_service() -> BenchResult {
    use candid::types::{Function, TypeEnv, TypeInner};

    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST);

    let method_type: candid::types::Type = TypeInner::Func(Function {
        modes: vec![],
        args: vec![TypeInner::Text.into()],
        rets: vec![TypeInner::Nat64.into()],
    })
    .into();

    let methods: Vec<(String, candid::types::Type)> = (0..20)
        .map(|i| (format!("method_{:02}", i), method_type.clone()))
        .collect();

    let service_type: candid::types::Type = TypeInner::Service(methods).into();
    let vec_service_type: candid::types::Type = TypeInner::Vec(service_type).into();

    let services: Vec<IDLValue> = (0..1000)
        .map(|i| {
            let bytes = (i as u64).to_be_bytes();
            IDLValue::Service(Principal::from_slice(&bytes))
        })
        .collect();

    let args = IDLArgs::new(&[IDLValue::Vec(services)]);
    let env = TypeEnv::new();
    let types = vec![vec_service_type.clone()];

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            args.to_bytes_with_types(&env, &types).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            IDLArgs::from_bytes_with_types_with_config(&bytes, &env, &types, &config).unwrap();
        }
    })
}

// Ok/Err discriminated union — the canonical ICP canister return type.
// Every canister method returns variant { Ok: Record; Err: ErrorEnum }.
// Tests heterogeneous variant payloads (struct vs enum) which the existing
// variant_list benchmark (homogeneous recursive) does not cover.
#[bench(raw)]
fn result_variant() -> BenchResult {
    #[derive(CandidType, Deserialize)]
    struct AccountResponse {
        account: Principal,
        balance_real: i128,
        balance_fake: i128,
        balance_ledger: i128,
        last_update: u64,
        overdraft_limit: u128,
        name: String,
    }

    #[derive(CandidType, Deserialize)]
    enum AccountError {
        NotAuthorized(Principal),
        AccountNotFound,
        InsufficientBalance { needed: u128, available: i128 },
        InternalError(String),
    }

    #[derive(CandidType, Deserialize)]
    enum AccountResult {
        Ok(AccountResponse),
        Err(AccountError),
    }

    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);

    let results: Vec<AccountResult> = (0..1000)
        .map(|i| {
            if i % 4 == 0 {
                AccountResult::Err(AccountError::InsufficientBalance {
                    needed: i as u128 * 1000,
                    available: i as i128 * 100,
                })
            } else if i % 4 == 1 {
                AccountResult::Err(AccountError::NotAuthorized(Principal::from_slice(
                    &(i as u32).to_be_bytes(),
                )))
            } else {
                AccountResult::Ok(AccountResponse {
                    account: Principal::from_slice(&(i as u32).to_be_bytes()),
                    balance_real: i as i128 * 1_000_000,
                    balance_fake: 0,
                    balance_ledger: i as i128 * 1_000_000,
                    last_update: 1_700_000_000 + i as u64,
                    overdraft_limit: 10_000_000_000,
                    name: format!("account-{}", i),
                })
            }
        })
        .collect();

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&results).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<AccountResult>).unwrap();
        }
    })
}

// GovernanceCachedMetrics — 34+ fields including ~10 bucket maps of
// vec record { nat64; float64 }. Tests field hash matching overhead at scale
// and exercises float64 encoding (not covered elsewhere).
#[bench(raw)]
fn wide_record() -> BenchResult {
    use crate::nns::GovernanceCachedMetrics;
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);

    let buckets: Vec<(u64, f64)> = (0..20)
        .map(|i| (i * 15_778_800, i as f64 * 1_000_000.0))
        .collect();
    let count_buckets: Vec<(u64, u64)> = (0..20).map(|i| (i * 15_778_800, i * 100)).collect();

    let metrics = GovernanceCachedMetrics {
        total_maturity_e8s_equivalent: 50_000_000_000_000,
        not_dissolving_neurons_e8s_buckets: buckets.clone(),
        dissolving_neurons_staked_maturity_e8s_equivalent_sum: 1_000_000_000,
        garbage_collectable_neurons_count: 42,
        dissolving_neurons_staked_maturity_e8s_equivalent_buckets: buckets.clone(),
        neurons_with_invalid_stake_count: 3,
        not_dissolving_neurons_count_buckets: count_buckets.clone(),
        ect_neuron_count: 100,
        total_supply_icp: 500_000_000_000_000_000,
        neurons_with_less_than_6_months_dissolve_delay_count: 5_000,
        dissolved_neurons_count: 10_000,
        community_fund_total_maturity_e8s_equivalent: 1_000_000_000_000,
        total_staked_e8s_seed: 2_000_000_000_000,
        total_staked_maturity_e8s_equivalent_ect: 500_000_000,
        total_staked_e8s: 100_000_000_000_000_000,
        not_dissolving_neurons_count: 30_000,
        total_locked_e8s: 80_000_000_000_000_000,
        neurons_fund_total_active_neurons: 200,
        total_staked_maturity_e8s_equivalent: 5_000_000_000_000,
        not_dissolving_neurons_e8s_buckets_ect: buckets.clone(),
        total_staked_e8s_ect: 3_000_000_000_000,
        not_dissolving_neurons_staked_maturity_e8s_equivalent_sum: 2_000_000_000,
        dissolved_neurons_e8s: 500_000_000_000,
        dissolving_neurons_e8s_buckets_seed: buckets.clone(),
        neurons_with_less_than_6_months_dissolve_delay_e8s: 1_000_000_000_000,
        not_dissolving_neurons_staked_maturity_e8s_equivalent_buckets: buckets.clone(),
        dissolving_neurons_count_buckets: count_buckets.clone(),
        dissolving_neurons_e8s_buckets_ect: buckets.clone(),
        dissolving_neurons_count: 15_000,
        dissolving_neurons_e8s_buckets: buckets.clone(),
        total_staked_maturity_e8s_equivalent_seed: 700_000_000,
        community_fund_total_staked_e8s: 5_000_000_000_000,
        not_dissolving_neurons_e8s_buckets_seed: buckets,
        timestamp_seconds: 1_700_000_000,
        seed_neuron_count: 500,
    };

    let metrics_vec: Vec<GovernanceCachedMetrics> = std::iter::repeat(metrics).take(100).collect();

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&metrics_vec).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<GovernanceCachedMetrics>).unwrap();
        }
    })
}

// 21-arm enum with mixed payload shapes (unit, tuple, struct variants).
// The existing variant_list only tests a 2-arm recursive variant. This tests
// variant tag matching overhead at scale with heterogeneous payloads.
#[bench(raw)]
fn large_variant() -> BenchResult {
    #[derive(CandidType, Deserialize, Clone)]
    enum LargeAction {
        Transfer {
            from: Principal,
            to: Principal,
            amount: u64,
            memo: Option<u64>,
        },
        Approve {
            spender: Principal,
            amount: u64,
            expires_at: Option<u64>,
        },
        Burn {
            amount: u64,
        },
        Mint {
            to: Principal,
            amount: u64,
        },
        SetFee(u64),
        SetAdmin(Principal),
        Pause,
        Unpause,
        Upgrade(serde_bytes::ByteBuf),
        AddMinter(Principal),
        RemoveMinter(Principal),
        SetName(String),
        SetSymbol(String),
        SetLogo(String),
        SetMetadata {
            key: String,
            value: String,
        },
        CreateProposal {
            title: String,
            summary: String,
            url: String,
        },
        Vote {
            proposal_id: u64,
            vote: bool,
        },
        Execute(u64),
        Reject(u64),
        RegisterNeuron {
            stake: u64,
            dissolve_delay: u64,
        },
        DisburseNeuron {
            neuron_id: u64,
            to: Principal,
            amount: Option<u64>,
        },
    }

    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);

    let actions: Vec<LargeAction> = (0..2100)
        .map(|i| {
            let p = Principal::from_slice(&(i as u32).to_be_bytes());
            match i % 21 {
                0 => LargeAction::Transfer {
                    from: p,
                    to: p,
                    amount: i as u64 * 100,
                    memo: Some(42),
                },
                1 => LargeAction::Approve {
                    spender: p,
                    amount: i as u64,
                    expires_at: Some(1_700_000_000),
                },
                2 => LargeAction::Burn {
                    amount: i as u64 * 50,
                },
                3 => LargeAction::Mint {
                    to: p,
                    amount: i as u64 * 1000,
                },
                4 => LargeAction::SetFee(i as u64),
                5 => LargeAction::SetAdmin(p),
                6 => LargeAction::Pause,
                7 => LargeAction::Unpause,
                8 => LargeAction::Upgrade(serde_bytes::ByteBuf::from(vec![i as u8; 32])),
                9 => LargeAction::AddMinter(p),
                10 => LargeAction::RemoveMinter(p),
                11 => LargeAction::SetName(format!("name-{}", i)),
                12 => LargeAction::SetSymbol(format!("SYM{}", i)),
                13 => LargeAction::SetLogo(format!("https://example.com/logo-{}.png", i)),
                14 => LargeAction::SetMetadata {
                    key: format!("key-{}", i),
                    value: format!("val-{}", i),
                },
                15 => LargeAction::CreateProposal {
                    title: format!("Proposal {}", i),
                    summary: format!("Summary for {}", i),
                    url: format!("https://example.com/{}", i),
                },
                16 => LargeAction::Vote {
                    proposal_id: i as u64,
                    vote: i % 2 == 0,
                },
                17 => LargeAction::Execute(i as u64),
                18 => LargeAction::Reject(i as u64),
                19 => LargeAction::RegisterNeuron {
                    stake: i as u64 * 100_000_000,
                    dissolve_delay: 15_778_800,
                },
                _ => LargeAction::DisburseNeuron {
                    neuron_id: i as u64,
                    to: p,
                    amount: Some(i as u64 * 100),
                },
            }
        })
        .collect();

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&actions).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<LargeAction>).unwrap();
        }
    })
}

// Option<Option<T>> — "3-state update" semantics used in real ICP APIs.
// None = don't change, Some(None) = clear, Some(Some(x)) = set.
// Exercises Candid's opt subtyping rules with double-wrapped optionals.
#[bench(raw)]
fn double_option() -> BenchResult {
    #[derive(CandidType, Deserialize)]
    struct UpdateRequest {
        target_balance: Option<Option<i128>>,
        expiration: Option<Option<u64>>,
        spending_limit: Option<Option<u128>>,
        description: Option<Option<String>>,
        account: Principal,
    }

    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);

    let requests: Vec<UpdateRequest> = (0..1000)
        .map(|i| match i % 3 {
            0 => UpdateRequest {
                target_balance: None,
                expiration: None,
                spending_limit: None,
                description: None,
                account: Principal::from_slice(&(i as u32).to_be_bytes()),
            },
            1 => UpdateRequest {
                target_balance: Some(None),
                expiration: Some(None),
                spending_limit: Some(None),
                description: Some(None),
                account: Principal::from_slice(&(i as u32).to_be_bytes()),
            },
            _ => UpdateRequest {
                target_balance: Some(Some(i as i128 * 1_000_000)),
                expiration: Some(Some(1_700_000_000 + i as u64)),
                spending_limit: Some(Some(i as u128 * 500)),
                description: Some(Some(format!("update-{}", i))),
                account: Principal::from_slice(&(i as u32).to_be_bytes()),
            },
        })
        .collect();

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&requests).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<UpdateRequest>).unwrap();
        }
    })
}

// Multi-argument Encode!/Decode! — real canister calls often pass multiple
// arguments (e.g., principal + amount + memo). This exercises a different
// internal code path than single-struct encoding.
#[bench(raw)]
fn multi_arg() -> BenchResult {
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(COST).set_skipping_quota(SKIP);

    let principals: Vec<Principal> = (0..1000)
        .map(|i| Principal::from_slice(&(i as u64).to_be_bytes()))
        .collect();
    let amounts: Vec<u64> = (0..1000).map(|i| i * 1_000_000).collect();
    let memos: Vec<String> = (0..1000).map(|i| format!("memo-{}", i)).collect();

    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&principals, &amounts, &memos).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([config]; &bytes, Vec<Principal>, Vec<u64>, Vec<String>).unwrap();
        }
    })
}

fn main() {}
