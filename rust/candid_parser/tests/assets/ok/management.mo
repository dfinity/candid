// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type BitcoinAddress = Text;
  public type BitcoinNetwork = { #mainnet; #testnet };
  public type BlockHash = Blob;
  public type CanisterId = Principal;
  public type CanisterSettings = {
    freezing_threshold : ?Nat;
    controllers : ?[Principal];
    memory_allocation : ?Nat;
    compute_allocation : ?Nat;
  };
  public type DefiniteCanisterSettings = {
    freezing_threshold : Nat;
    controllers : [Principal];
    memory_allocation : Nat;
    compute_allocation : Nat;
  };
  public type EcdsaCurve = { #secp256k1 };
  public type GetBalanceRequest = {
    network : BitcoinNetwork;
    address : BitcoinAddress;
    min_confirmations : ?Nat32;
  };
  public type GetCurrentFeePercentilesRequest = { network : BitcoinNetwork };
  public type GetUtxosRequest = {
    network : BitcoinNetwork;
    filter : ?{ #page : Blob; #min_confirmations : Nat32 };
    address : BitcoinAddress;
  };
  public type GetUtxosResponse = {
    next_page : ?Blob;
    tip_height : Nat32;
    tip_block_hash : BlockHash;
    utxos : [Utxo];
  };
  public type HttpHeader = { value : Text; name : Text };
  public type HttpResponse = {
    status : Nat;
    body : Blob;
    headers : [HttpHeader];
  };
  public type MillisatoshiPerByte = Nat64;
  public type Outpoint = { txid : Blob; vout : Nat32 };
  public type Satoshi = Nat64;
  public type SendTransactionRequest = {
    transaction : Blob;
    network : BitcoinNetwork;
  };
  public type UserId = Principal;
  public type Utxo = { height : Nat32; value : Satoshi; outpoint : Outpoint };
  public type WasmModule = Blob;
  public type Self = actor {
    bitcoin_get_balance : shared GetBalanceRequest -> async Satoshi;
    bitcoin_get_current_fee_percentiles : shared GetCurrentFeePercentilesRequest -> async [
        MillisatoshiPerByte
      ];
    bitcoin_get_utxos : shared GetUtxosRequest -> async GetUtxosResponse;
    bitcoin_send_transaction : shared SendTransactionRequest -> async ();
    canister_status : shared { canister_id : CanisterId } -> async {
        status : { #stopped; #stopping; #running };
        memory_size : Nat;
        cycles : Nat;
        settings : DefiniteCanisterSettings;
        idle_cycles_burned_per_day : Nat;
        module_hash : ?Blob;
      };
    create_canister : shared { settings : ?CanisterSettings } -> async {
        canister_id : CanisterId;
      };
    delete_canister : shared { canister_id : CanisterId } -> async ();
    deposit_cycles : shared { canister_id : CanisterId } -> async ();
    ecdsa_public_key : shared {
        key_id : { name : Text; curve : EcdsaCurve };
        canister_id : ?CanisterId;
        derivation_path : [Blob];
      } -> async { public_key : Blob; chain_code : Blob };
    http_request : shared {
        url : Text;
        method : { #get; #head; #post };
        max_response_bytes : ?Nat64;
        body : ?Blob;
        transform : ?{
          function : shared query {
              context : Blob;
              response : HttpResponse;
            } -> async HttpResponse;
          context : Blob;
        };
        headers : [HttpHeader];
      } -> async HttpResponse;
    install_code : shared {
        arg : Blob;
        wasm_module : WasmModule;
        mode : { #reinstall; #upgrade; #install };
        canister_id : CanisterId;
      } -> async ();
    provisional_create_canister_with_cycles : shared {
        settings : ?CanisterSettings;
        specified_id : ?CanisterId;
        amount : ?Nat;
      } -> async { canister_id : CanisterId };
    provisional_top_up_canister : shared {
        canister_id : CanisterId;
        amount : Nat;
      } -> async ();
    raw_rand : shared () -> async Blob;
    sign_with_ecdsa : shared {
        key_id : { name : Text; curve : EcdsaCurve };
        derivation_path : [Blob];
        message_hash : Blob;
      } -> async { signature : Blob };
    start_canister : shared { canister_id : CanisterId } -> async ();
    stop_canister : shared { canister_id : CanisterId } -> async ();
    uninstall_code : shared { canister_id : CanisterId } -> async ();
    update_settings : shared {
        canister_id : Principal;
        settings : CanisterSettings;
      } -> async ();
  }
}
