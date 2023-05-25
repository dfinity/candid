// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
type Result<T> = std::result::Result<T, ic_agent::AgentError>;
#[derive(CandidType, Deserialize)]
pub enum bitcoin_network { mainnet, testnet }

pub type bitcoin_address = String;
#[derive(CandidType, Deserialize)]
pub struct get_balance_request {
  network: bitcoin_network,
  address: bitcoin_address,
  min_confirmations: Option<u32>,
}

pub type satoshi = u64;
#[derive(CandidType, Deserialize)]
pub struct get_current_fee_percentiles_request { network: bitcoin_network }

pub type millisatoshi_per_byte = u64;
#[derive(CandidType, Deserialize)]
pub enum get_utxos_request_filter_inner {
  page(serde_bytes::ByteBuf),
  min_confirmations(u32),
}

#[derive(CandidType, Deserialize)]
pub struct get_utxos_request {
  network: bitcoin_network,
  filter: Option<get_utxos_request_filter_inner>,
  address: bitcoin_address,
}

pub type block_hash = serde_bytes::ByteBuf;
#[derive(CandidType, Deserialize)]
pub struct outpoint { txid: serde_bytes::ByteBuf, vout: u32 }

#[derive(CandidType, Deserialize)]
pub struct utxo { height: u32, value: satoshi, outpoint: outpoint }

#[derive(CandidType, Deserialize)]
pub struct get_utxos_response {
  next_page: Option<serde_bytes::ByteBuf>,
  tip_height: u32,
  tip_block_hash: block_hash,
  utxos: Vec<utxo>,
}

#[derive(CandidType, Deserialize)]
pub struct send_transaction_request {
  transaction: serde_bytes::ByteBuf,
  network: bitcoin_network,
}

pub type canister_id = Principal;
#[derive(CandidType, Deserialize)]
pub struct canister_status_arg0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub enum canister_status_ret0_status { stopped, stopping, running }

#[derive(CandidType, Deserialize)]
pub struct definite_canister_settings {
  freezing_threshold: candid::Nat,
  controllers: Vec<Principal>,
  memory_allocation: candid::Nat,
  compute_allocation: candid::Nat,
}

#[derive(CandidType, Deserialize)]
pub struct canister_status_ret0 {
  status: canister_status_ret0_status,
  memory_size: candid::Nat,
  cycles: candid::Nat,
  settings: definite_canister_settings,
  idle_cycles_burned_per_day: candid::Nat,
  module_hash: Option<serde_bytes::ByteBuf>,
}

#[derive(CandidType, Deserialize)]
pub struct canister_settings {
  freezing_threshold: Option<candid::Nat>,
  controllers: Option<Vec<Principal>>,
  memory_allocation: Option<candid::Nat>,
  compute_allocation: Option<candid::Nat>,
}

#[derive(CandidType, Deserialize)]
pub struct create_canister_arg0 { settings: Option<canister_settings> }

#[derive(CandidType, Deserialize)]
pub struct create_canister_ret0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub struct delete_canister_arg0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub struct deposit_cycles_arg0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub enum ecdsa_curve { secp256k1 }

#[derive(CandidType, Deserialize)]
pub struct ecdsa_public_key_arg0_key_id { name: String, curve: ecdsa_curve }

#[derive(CandidType, Deserialize)]
pub struct ecdsa_public_key_arg0 {
  key_id: ecdsa_public_key_arg0_key_id,
  canister_id: Option<canister_id>,
  derivation_path: Vec<serde_bytes::ByteBuf>,
}

#[derive(CandidType, Deserialize)]
pub struct ecdsa_public_key_ret0 {
  public_key: serde_bytes::ByteBuf,
  chain_code: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize)]
pub enum http_request_arg0_method { get, head, post }

#[derive(CandidType, Deserialize)]
pub struct http_header { value: String, name: String }

#[derive(CandidType, Deserialize)]
pub struct http_response {
  status: candid::Nat,
  body: serde_bytes::ByteBuf,
  headers: Vec<http_header>,
}

#[derive(CandidType, Deserialize)]
pub struct http_request_arg0_transform_inner_function_arg0 {
  context: serde_bytes::ByteBuf,
  response: http_response,
}

candid::define_function!(pub http_request_arg0_transform_inner_function : (
    http_request_arg0_transform_inner_function_arg0,
  ) -> (http_response) query);
#[derive(CandidType, Deserialize)]
pub struct http_request_arg0_transform_inner {
  function: http_request_arg0_transform_inner_function,
  context: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize)]
pub struct http_request_arg0 {
  url: String,
  method: http_request_arg0_method,
  max_response_bytes: Option<u64>,
  body: Option<serde_bytes::ByteBuf>,
  transform: Option<http_request_arg0_transform_inner>,
  headers: Vec<http_header>,
}

pub type wasm_module = serde_bytes::ByteBuf;
#[derive(CandidType, Deserialize)]
pub enum install_code_arg0_mode { reinstall, upgrade, install }

#[derive(CandidType, Deserialize)]
pub struct install_code_arg0 {
  arg: serde_bytes::ByteBuf,
  wasm_module: wasm_module,
  mode: install_code_arg0_mode,
  canister_id: canister_id,
}

#[derive(CandidType, Deserialize)]
pub struct provisional_create_canister_with_cycles_arg0 {
  settings: Option<canister_settings>,
  specified_id: Option<canister_id>,
  amount: Option<candid::Nat>,
}

#[derive(CandidType, Deserialize)]
pub struct provisional_create_canister_with_cycles_ret0 {
  canister_id: canister_id,
}

#[derive(CandidType, Deserialize)]
pub struct provisional_top_up_canister_arg0 {
  canister_id: canister_id,
  amount: candid::Nat,
}

#[derive(CandidType, Deserialize)]
pub struct sign_with_ecdsa_arg0_key_id { name: String, curve: ecdsa_curve }

#[derive(CandidType, Deserialize)]
pub struct sign_with_ecdsa_arg0 {
  key_id: sign_with_ecdsa_arg0_key_id,
  derivation_path: Vec<serde_bytes::ByteBuf>,
  message_hash: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize)]
pub struct sign_with_ecdsa_ret0 { signature: serde_bytes::ByteBuf }

#[derive(CandidType, Deserialize)]
pub struct start_canister_arg0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub struct stop_canister_arg0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub struct uninstall_code_arg0 { canister_id: canister_id }

#[derive(CandidType, Deserialize)]
pub struct update_settings_arg0 {
  canister_id: Principal,
  settings: canister_settings,
}

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn bitcoin_get_balance(
    &self, agent: &ic_agent::Agent,
    arg0: get_balance_request,
  ) -> Result<satoshi> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "bitcoin_get_balance").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, satoshi)?)
  }
  pub async fn bitcoin_get_current_fee_percentiles(
    &self, agent: &ic_agent::Agent,
    arg0: get_current_fee_percentiles_request,
  ) -> Result<Vec<millisatoshi_per_byte>> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "bitcoin_get_current_fee_percentiles").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, Vec<millisatoshi_per_byte>)?)
  }
  pub async fn bitcoin_get_utxos(
    &self, agent: &ic_agent::Agent,
    arg0: get_utxos_request,
  ) -> Result<get_utxos_response> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "bitcoin_get_utxos").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, get_utxos_response)?)
  }
  pub async fn bitcoin_send_transaction(
    &self, agent: &ic_agent::Agent,
    arg0: send_transaction_request,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "bitcoin_send_transaction").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn canister_status(
    &self, agent: &ic_agent::Agent,
    arg0: canister_status_arg0,
  ) -> Result<canister_status_ret0> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "canister_status").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, canister_status_ret0)?)
  }
  pub async fn create_canister(
    &self, agent: &ic_agent::Agent,
    arg0: create_canister_arg0,
  ) -> Result<create_canister_ret0> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "create_canister").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, create_canister_ret0)?)
  }
  pub async fn delete_canister(
    &self, agent: &ic_agent::Agent,
    arg0: delete_canister_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "delete_canister").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn deposit_cycles(
    &self, agent: &ic_agent::Agent,
    arg0: deposit_cycles_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "deposit_cycles").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn ecdsa_public_key(
    &self, agent: &ic_agent::Agent,
    arg0: ecdsa_public_key_arg0,
  ) -> Result<ecdsa_public_key_ret0> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "ecdsa_public_key").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, ecdsa_public_key_ret0)?)
  }
  pub async fn http_request(
    &self, agent: &ic_agent::Agent,
    arg0: http_request_arg0,
  ) -> Result<http_response> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "http_request").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, http_response)?)
  }
  pub async fn install_code(
    &self, agent: &ic_agent::Agent,
    arg0: install_code_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "install_code").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn provisional_create_canister_with_cycles(
    &self, agent: &ic_agent::Agent,
    arg0: provisional_create_canister_with_cycles_arg0,
  ) -> Result<provisional_create_canister_with_cycles_ret0> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "provisional_create_canister_with_cycles").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, provisional_create_canister_with_cycles_ret0)?)
  }
  pub async fn provisional_top_up_canister(
    &self, agent: &ic_agent::Agent,
    arg0: provisional_top_up_canister_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "provisional_top_up_canister").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn raw_rand(&self, agent: &ic_agent::Agent) -> Result<
    serde_bytes::ByteBuf
  > {
    let args = candid::Encode!()?;
    let bytes = agent.update(self.0, "raw_rand").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, serde_bytes::ByteBuf)?)
  }
  pub async fn sign_with_ecdsa(
    &self, agent: &ic_agent::Agent,
    arg0: sign_with_ecdsa_arg0,
  ) -> Result<sign_with_ecdsa_ret0> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "sign_with_ecdsa").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes, sign_with_ecdsa_ret0)?)
  }
  pub async fn start_canister(
    &self, agent: &ic_agent::Agent,
    arg0: start_canister_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "start_canister").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn stop_canister(
    &self, agent: &ic_agent::Agent,
    arg0: stop_canister_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "stop_canister").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn uninstall_code(
    &self, agent: &ic_agent::Agent,
    arg0: uninstall_code_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "uninstall_code").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
  pub async fn update_settings(
    &self, agent: &ic_agent::Agent,
    arg0: update_settings_arg0,
  ) -> Result<()> {
    let args = candid::Encode!(arg0)?;
    let bytes = agent.update(self.0, "update_settings").with_arg(args).call_and_wait().await?;
    Ok(candid::Decode!(&bytes)?)
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
