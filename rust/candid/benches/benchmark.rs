use iai::{main};
use candid::{CandidType, Deserialize, Encode, Decode, Result};

fn test_str() -> Result<()> {
    #[derive(CandidType, Deserialize)]
    struct A {
        inner: Vec<u8>
    }
    let vec: Vec<u8> = vec![0; 1024];
    let bytes = Encode!(&A{inner: vec})?;
    let _ = Decode!(&bytes, A)?;
    Ok(())
}

main!(test_str);
