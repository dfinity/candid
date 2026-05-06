// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type Self = actor {
    identity32 : shared Float32 -> async Float32;
    to_f32 : shared Float -> async Float32;
    to_f64 : shared Float32 -> async Float;
  }
}
