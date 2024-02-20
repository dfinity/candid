use canbench_rs::{bench, bench_fn, bench_scope, BenchResult};
use candid::{CandidType, Decode, Deserialize, Encode, Int, Nat};
use std::collections::BTreeMap;

#[allow(clippy::all)]
mod nns;

const N: usize = 2097152;
const COST: usize = 20_000_000;

#[bench(raw)]
fn blob() -> BenchResult {
    use serde_bytes::ByteBuf;
    let vec: Vec<u8> = vec![0x61; N];
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&ByteBuf::from(vec)).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([COST]; &bytes, ByteBuf).unwrap();
        }
    })
}

#[bench(raw)]
fn text() -> BenchResult {
    let vec: Vec<u8> = vec![0x61; N];
    let text = String::from_utf8(vec).unwrap();
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&text).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([COST]; &bytes, String).unwrap();
        }
    })
}

#[bench(raw)]
fn vec_int16() -> BenchResult {
    let vec: Vec<i16> = vec![-1; N];
    bench_fn(|| {
        let bytes = {
            let _p = bench_scope("1. Encoding");
            Encode!(&vec).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([COST]; &bytes, Vec<i16>).unwrap();
        }
    })
}

#[bench(raw)]
fn btreemap() -> BenchResult {
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
            Decode!([COST]; &bytes, BTreeMap<String, Nat>).unwrap();
        }
    })
}

#[bench(raw)]
fn option_list() -> BenchResult {
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
            Decode!([COST]; &bytes, Option<Box<List>>).unwrap();
        }
    })
}

#[bench(raw)]
fn variant_list() -> BenchResult {
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
            Decode!([COST]; &bytes, VariantList).unwrap();
        }
    })
}

#[bench(raw)]
fn nns() -> BenchResult {
    use candid_parser::utils::CandidSource;
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
        let arg_tys = &env.get_method(&serv, "manage_neuron").unwrap().args;
        drop(_p);
        let bytes = {
            let _p = bench_scope("1. Encoding");
            args.to_bytes_with_types(&env, arg_tys).unwrap()
        };
        {
            let _p = bench_scope("2. Decoding");
            Decode!([COST]; &bytes, nns::ManageNeuron).unwrap();
        }
    })
}

#[bench(raw)]
fn extra_args() -> BenchResult {
    let bytes = hex::decode("4449444c036c01d6fca702016d026c00010080ade204").unwrap();
    bench_fn(|| {
        let _ = Decode!([COST]; &bytes);
    })
}

fn main() {}
