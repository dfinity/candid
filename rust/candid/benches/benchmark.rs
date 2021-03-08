use candid::{CandidType, Decode, Deserialize, Encode, Principal};
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};

fn bench_blob(c: &mut Criterion) {
    use serde_bytes::{ByteBuf, Bytes};
    let vec: Vec<u8> = vec![0x61; 524288];
    let mut group = c.benchmark_group("Blob");
    /*group.bench_function("Vector", |b| {
        b.iter_batched(
            || vec.clone(),
            |vec| {
                let bytes = Encode!(&vec).unwrap();
                Decode!(&bytes, Vec<u8>).unwrap();
            },
            BatchSize::SmallInput,
        )
    });*/
    group.bench_function("ByteBuf", |b| {
        b.iter_batched(
            || vec.clone(),
            |vec| {
                let bytes = Encode!(&ByteBuf::from(vec)).unwrap();
                Decode!(&bytes, ByteBuf).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("Bytes", |b| {
        b.iter_batched_ref(
            || vec.clone(),
            |vec| {
                let bytes = Encode!(&Bytes::new(vec)).unwrap();
                Decode!(&bytes, &Bytes).unwrap();
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
                Decode!(&bytes, String).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("&str", |b| {
        b.iter_batched_ref(
            || text.clone(),
            |text| {
                let bytes = Encode!(text).unwrap();
                Decode!(&bytes, &str).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.finish();
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
    let profiles: Vec<_> = std::iter::repeat(profile).take(500).collect();
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

criterion_group!(benches, bench_blob, bench_profile);
criterion_main!(benches);
