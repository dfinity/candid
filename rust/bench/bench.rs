use canbench_rs::{bench, bench_fn, bench_scope, BenchResult};
use candid::{CandidType, Decode, DecoderConfig, Deserialize, Encode, Int, Nat};
use std::collections::BTreeMap;

#[allow(clippy::all)]
mod nns;

const N: usize = 2097152;
const COST: usize = 20_000_000;
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
        let arg_tys = method
            .args
            .iter()
            .map(|arg| arg.typ.clone())
            .collect::<Vec<_>>();
        drop(_p);
        let bytes = {
            let _p = bench_scope("1. Encoding");
            args.to_bytes_with_types(&env, &arg_tys).unwrap()
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

fn main() {}
