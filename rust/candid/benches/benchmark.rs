use candid::{CandidType, Decode, Deserialize, Encode, Int, Nat, Principal};
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use std::collections::BTreeMap;

const COST: usize = 20_000_000;

fn bench_blob(c: &mut Criterion) {
    use serde_bytes::{ByteBuf, Bytes};
    let vec: Vec<u8> = vec![0x61; 524288];
    let mut group = c.benchmark_group("Blob");
    group.bench_function("ByteBuf", |b| {
        b.iter_batched(
            || vec.clone(),
            |vec| {
                let bytes = Encode!(&ByteBuf::from(vec)).unwrap();
                Decode!([COST] & bytes, ByteBuf).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("Bytes", |b| {
        b.iter_batched_ref(
            || vec.clone(),
            |vec| {
                let bytes = Encode!(&Bytes::new(vec)).unwrap();
                Decode!([COST] & bytes, &Bytes).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    let text = String::from_utf8(vec).unwrap();
    group.bench_function("String", |b| {
        b.iter_batched(
            || text.clone(),
            |text| {
                let bytes = Encode!(&text).unwrap();
                Decode!([COST] & bytes, String).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("&str", |b| {
        b.iter_batched_ref(
            || text.clone(),
            |text| {
                let bytes = Encode!(text).unwrap();
                Decode!([COST] & bytes, &str).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.finish();
}

fn bench_collections(c: &mut Criterion) {
    let mut group = c.benchmark_group("Collections");
    {
        let vec8: Vec<u8> = vec![0x61; 524288];
        group.bench_function("vec nat8", |b| {
            b.iter_batched(
                || vec8.clone(),
                |vec| {
                    let bytes = Encode!(&vec).unwrap();
                    Decode!([COST] & bytes, Vec<u8>).unwrap();
                },
                BatchSize::SmallInput,
            )
        });
    }
    {
        let vec64: Vec<i64> = vec![-1; 524288];
        group.bench_function("vec int64", |b| {
            b.iter_batched(
                || vec64.clone(),
                |vec| {
                    let bytes = Encode!(&vec).unwrap();
                    Decode!([COST] & bytes, Vec<i64>).unwrap();
                },
                BatchSize::SmallInput,
            )
        });
    }
    {
        let vec: Vec<Int> = vec![Int::from(-1); 65536];
        group.bench_function("vec int", |b| {
            b.iter_batched(
                || vec.clone(),
                |vec| {
                    let bytes = Encode!(&vec).unwrap();
                    Decode!([COST] & bytes, Vec<candid::Int>).unwrap();
                },
                BatchSize::SmallInput,
            )
        });
    }
    {
        let map: BTreeMap<String, Nat> = (0u32..65536u32)
            .map(|i| (i.to_string(), Nat::from(i)))
            .collect();
        group.bench_function("vec (text, nat)", |b| {
            b.iter_batched(
                || map.clone(),
                |map| {
                    let bytes = Encode!(&map).unwrap();
                    Decode!(&bytes, BTreeMap<String, Nat>).unwrap();
                },
                BatchSize::SmallInput,
            )
        });
    }
}

fn bench_recursion(c: &mut Criterion) {
    let n = 1024;
    #[derive(CandidType, Deserialize, Clone)]
    struct List {
        head: Int,
        tail: Option<Box<List>>,
    }
    #[derive(CandidType, Deserialize, Clone)]
    enum VariantList {
        Nil,
        Cons(Int, Box<VariantList>),
    }
    {
        let list: Option<Box<List>> = (0..n).fold(None, |acc, x| {
            Some(Box::new(List {
                head: Int::from(x),
                tail: acc,
            }))
        });
        c.bench_with_input(BenchmarkId::new("option list", n), &list, |b, list| {
            b.iter(|| {
                let bytes = Encode!(list).unwrap();
                Decode!(&bytes, Option<Box<List>>).unwrap()
            })
        });
    }
    {
        let list: VariantList = (0..n).fold(VariantList::Nil, |acc, x| {
            VariantList::Cons(Int::from(x), Box::new(acc))
        });
        c.bench_with_input(BenchmarkId::new("variant list", n), &list, |b, list| {
            b.iter(|| {
                let bytes = Encode!(list).unwrap();
                Decode!(&bytes, VariantList).unwrap()
            })
        });
    }
}

fn bench_profile(c: &mut Criterion) {
    #[derive(CandidType, Deserialize, Clone)]
    #[allow(non_snake_case)]
    struct Profile {
        id: Principal,
        imgUrl: String,
        title: String,
        education: String,
        experience: String,
        company: String,
        lastName: String,
        firstName: String,
    }
    let profile = Profile {
        id: Principal::from_text("27u75-h7div-y6axr-knc2i-3bsij-dr5wo-jdb5t-ndd2n-mh22v-ooz2s-iqe").unwrap(),
        firstName: "Dominic".to_string(),
        lastName: "Williams".to_string(),
        title: "Founder & Chief Scientist".to_string(),
        company: "DFINITY".to_string(),
        experience: "**President & Chief Scientist**, DFINITY  \nJan 2015 – Present  \nPalo Alto, CA\n\n**President & CTO**, String Labs, Inc  \nJun 2015 – Feb 2018  \nPalo Alto, CA".to_string(),
        education: "**King's College London**  \nBA, Computer Science".to_string(),
        imgUrl: "https://media-exp1.licdn.com/dms/image/C5603AQHdxGV6zMbg-A/profile-displayphoto-shrink_200_200/0?e=1592438400&v=beta&t=NlR0J9mgJXd3SO6K3YJ6xBC_wCip20u5THPNKu6ImYQ".to_string(),
    };
    let profiles: Vec<_> = std::iter::repeat(profile).take(1024).collect();
    c.bench_with_input(
        BenchmarkId::new("profiles", profiles.len()),
        &profiles,
        |b, vec| {
            b.iter(|| {
                let bytes = Encode!(vec).unwrap();
                Decode!(&bytes, Vec<Profile>).unwrap()
            })
        },
    );
}

criterion_group!(
    benches,
    bench_blob,
    bench_collections,
    bench_profile,
    bench_recursion
);
criterion_main!(benches);
