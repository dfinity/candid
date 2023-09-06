// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal, Encode, Decode};
type Result<T> = std::result::Result<T, ic_agent::AgentError>;

#[derive(CandidType, Deserialize)]
pub enum BitcoinNetwork {
  #[serde(rename="mainnet")]
  Mainnet,
  #[serde(rename="testnet")]
  Testnet,
}

pub type BitcoinAddress = String;
#[derive(CandidType, Deserialize)]
pub struct GetBalanceRequest {
  network: BitcoinNetwork,
  address: BitcoinAddress,
  min_confirmations: Option<u32>,
}

pub type Satoshi = u64;
#[derive(CandidType, Deserialize)]
pub struct GetCurrentFeePercentilesRequest { network: BitcoinNetwork }

pub type MillisatoshiPerByte = u64;
#[derive(CandidType, Deserialize)]
pub enum GetUtxosRequestFilterInner {
  #[serde(rename="page")]
  Page(serde_bytes::ByteBuf),
  #[serde(rename="min_confirmations")]
  MinConfirmations(u32),
}

#[derive(CandidType, Deserialize)]
pub struct GetUtxosRequest {
  network: BitcoinNetwork,
  filter: Option<GetUtxosRequestFilterInner>,
  address: BitcoinAddress,
}

pub type BlockHash = serde_bytes::ByteBuf;
#[derive(CandidType, Deserialize)]
pub struct Outpoint { txid: serde_bytes::ByteBuf, vout: u32 }

#[derive(CandidType, Deserialize)]
pub struct Utxo { height: u32, value: Satoshi, outpoint: Outpoint }

#[derive(CandidType, Deserialize)]
pub struct GetUtxosResponse {
  next_page: Option<serde_bytes::ByteBuf>,
  tip_height: u32,
  tip_block_hash: BlockHash,
  utxos: Vec<Utxo>,
}

#[derive(CandidType, Deserialize)]
pub struct SendTransactionRequest {
  transaction: serde_bytes::ByteBuf,
  network: BitcoinNetwork,
}

pub type CanisterId = Principal;
#[derive(CandidType, Deserialize)]
pub struct CanisterStatusArg { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub enum CanisterStatusRetStatus {
  #[serde(rename="stopped")]
  Stopped,
  #[serde(rename="stopping")]
  Stopping,
  #[serde(rename="running")]
  Running,
}

#[derive(CandidType, Deserialize)]
pub struct DefiniteCanisterSettings {
  freezing_threshold: candid::Nat,
  controllers: Vec<Principal>,
  memory_allocation: candid::Nat,
  compute_allocation: candid::Nat,
}

#[derive(CandidType, Deserialize)]
pub struct CanisterStatusRet {
  status: CanisterStatusRetStatus,
  memory_size: candid::Nat,
  cycles: candid::Nat,
  settings: DefiniteCanisterSettings,
  idle_cycles_burned_per_day: candid::Nat,
  module_hash: Option<serde_bytes::ByteBuf>,
}

#[derive(CandidType, Deserialize)]
pub struct CanisterSettings {
  freezing_threshold: Option<candid::Nat>,
  controllers: Option<Vec<Principal>>,
  memory_allocation: Option<candid::Nat>,
  compute_allocation: Option<candid::Nat>,
}

#[derive(CandidType, Deserialize)]
pub struct CreateCanisterArg { settings: Option<CanisterSettings> }

#[derive(CandidType, Deserialize)]
pub struct CreateCanisterRet { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub struct DeleteCanisterArg { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub struct DepositCyclesArg { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub enum EcdsaCurve { #[serde(rename="secp256k1")] Secp256K1 }

#[derive(CandidType, Deserialize)]
pub struct EcdsaPublicKeyArgKeyId { name: String, curve: EcdsaCurve }

#[derive(CandidType, Deserialize)]
pub struct EcdsaPublicKeyArg {
  key_id: EcdsaPublicKeyArgKeyId,
  canister_id: Option<CanisterId>,
  derivation_path: Vec<serde_bytes::ByteBuf>,
}

#[derive(CandidType, Deserialize)]
pub struct EcdsaPublicKeyRet {
  public_key: serde_bytes::ByteBuf,
  chain_code: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize)]
pub enum HttpRequestArgMethod {
  #[serde(rename="get")]
  Get,
  #[serde(rename="head")]
  Head,
  #[serde(rename="post")]
  Post,
}

#[derive(CandidType, Deserialize)]
pub struct HttpHeader { value: String, name: String }

#[derive(CandidType, Deserialize)]
pub struct HttpResponse {
  status: candid::Nat,
  body: serde_bytes::ByteBuf,
  headers: Vec<HttpHeader>,
}

#[derive(CandidType, Deserialize)]
pub struct HttpRequestArgTransformInnerFunctionArg {
  context: serde_bytes::ByteBuf,
  response: HttpResponse,
}

candid::define_function!(pub HttpRequestArgTransformInnerFunction : (
    HttpRequestArgTransformInnerFunctionArg,
  ) -> (HttpResponse) query);
#[derive(CandidType, Deserialize)]
pub struct HttpRequestArgTransformInner {
  function: HttpRequestArgTransformInnerFunction,
  context: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize)]
pub struct HttpRequestArg {
  url: String,
  method: HttpRequestArgMethod,
  max_response_bytes: Option<u64>,
  body: Option<serde_bytes::ByteBuf>,
  transform: Option<HttpRequestArgTransformInner>,
  headers: Vec<HttpHeader>,
}

pub type WasmModule = serde_bytes::ByteBuf;
#[derive(CandidType, Deserialize)]
pub enum InstallCodeArgMode {
  #[serde(rename="reinstall")]
  Reinstall,
  #[serde(rename="upgrade")]
  Upgrade,
  #[serde(rename="install")]
  Install,
}

#[derive(CandidType, Deserialize)]
pub struct InstallCodeArg {
  arg: serde_bytes::ByteBuf,
  wasm_module: WasmModule,
  mode: InstallCodeArgMode,
  canister_id: CanisterId,
}

#[derive(CandidType, Deserialize)]
pub struct ProvisionalCreateCanisterWithCyclesArg {
  settings: Option<CanisterSettings>,
  specified_id: Option<CanisterId>,
  amount: Option<candid::Nat>,
}

#[derive(CandidType, Deserialize)]
pub struct ProvisionalCreateCanisterWithCyclesRet { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub struct ProvisionalTopUpCanisterArg {
  canister_id: CanisterId,
  amount: candid::Nat,
}

#[derive(CandidType, Deserialize)]
pub struct SignWithEcdsaArgKeyId { name: String, curve: EcdsaCurve }

#[derive(CandidType, Deserialize)]
pub struct SignWithEcdsaArg {
  key_id: SignWithEcdsaArgKeyId,
  derivation_path: Vec<serde_bytes::ByteBuf>,
  message_hash: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize)]
pub struct SignWithEcdsaRet { signature: serde_bytes::ByteBuf }

#[derive(CandidType, Deserialize)]
pub struct StartCanisterArg { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub struct StopCanisterArg { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub struct UninstallCodeArg { canister_id: CanisterId }

#[derive(CandidType, Deserialize)]
pub struct UpdateSettingsArg {
  canister_id: Principal,
  settings: CanisterSettings,
}

pub struct Service<'a>(pub Principal, pub &'a ic_agent::Agent);
impl<'a> Service<'a> {
  pub async fn bitcoin_get_balance(&self, arg0: GetBalanceRequest) -> Result<
    Satoshi
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "bitcoin_get_balance").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, Satoshi)?)
  }
  pub async fn bitcoin_get_current_fee_percentiles(
    &self,
    arg0: GetCurrentFeePercentilesRequest,
  ) -> Result<Vec<MillisatoshiPerByte>> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "bitcoin_get_current_fee_percentiles").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, Vec<MillisatoshiPerByte>)?)
  }
  pub async fn bitcoin_get_utxos(&self, arg0: GetUtxosRequest) -> Result<
    GetUtxosResponse
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "bitcoin_get_utxos").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, GetUtxosResponse)?)
  }
  pub async fn bitcoin_send_transaction(
    &self,
    arg0: SendTransactionRequest,
  ) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "bitcoin_send_transaction").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn canister_status(&self, arg0: CanisterStatusArg) -> Result<
    CanisterStatusRet
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "canister_status").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, CanisterStatusRet)?)
  }
  pub async fn create_canister(&self, arg0: CreateCanisterArg) -> Result<
    CreateCanisterRet
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "create_canister").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, CreateCanisterRet)?)
  }
  pub async fn delete_canister(&self, arg0: DeleteCanisterArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "delete_canister").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn deposit_cycles(&self, arg0: DepositCyclesArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "deposit_cycles").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn ecdsa_public_key(&self, arg0: EcdsaPublicKeyArg) -> Result<
    EcdsaPublicKeyRet
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "ecdsa_public_key").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, EcdsaPublicKeyRet)?)
  }
  pub async fn http_request(&self, arg0: HttpRequestArg) -> Result<
    HttpResponse
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "http_request").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, HttpResponse)?)
  }
  pub async fn install_code(&self, arg0: InstallCodeArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "install_code").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn provisional_create_canister_with_cycles(
    &self,
    arg0: ProvisionalCreateCanisterWithCyclesArg,
  ) -> Result<ProvisionalCreateCanisterWithCyclesRet> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "provisional_create_canister_with_cycles").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, ProvisionalCreateCanisterWithCyclesRet)?)
  }
  pub async fn provisional_top_up_canister(
    &self,
    arg0: ProvisionalTopUpCanisterArg,
  ) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "provisional_top_up_canister").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn raw_rand(&self) -> Result<serde_bytes::ByteBuf> {
    let args = Encode!()?;
    let bytes = self.1.update(&self.0, "raw_rand").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, serde_bytes::ByteBuf)?)
  }
  pub async fn sign_with_ecdsa(&self, arg0: SignWithEcdsaArg) -> Result<
    SignWithEcdsaRet
  > {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "sign_with_ecdsa").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes, SignWithEcdsaRet)?)
  }
  pub async fn start_canister(&self, arg0: StartCanisterArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "start_canister").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn stop_canister(&self, arg0: StopCanisterArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "stop_canister").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn uninstall_code(&self, arg0: UninstallCodeArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "uninstall_code").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
  pub async fn update_settings(&self, arg0: UpdateSettingsArg) -> Result<()> {
    let args = Encode!(&arg0)?;
    let bytes = self.1.update(&self.0, "update_settings").with_arg(args).call_and_wait().await?;
    Ok(Decode!(&bytes)?)
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa

