// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Decode, Deserialize, Encode, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronId {
    pub id: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Followees {
    pub followees: Vec<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct KnownNeuronData {
    pub name: String,
    pub description: Option<String>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct KnownNeuron {
    pub id: Option<NeuronId>,
    pub known_neuron_data: Option<KnownNeuronData>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Spawn {
    pub percentage_to_spawn: Option<u32>,
    pub new_controller: Option<Principal>,
    pub nonce: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Split {
    pub amount_e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Follow {
    pub topic: i32,
    pub followees: Vec<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ClaimOrRefreshNeuronFromAccount {
    pub controller: Option<Principal>,
    pub memo: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum By {
    NeuronIdOrSubaccount {},
    MemoAndController(ClaimOrRefreshNeuronFromAccount),
    Memo(u64),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ClaimOrRefresh {
    pub by: Option<By>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RemoveHotKey {
    pub hot_key_to_remove: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct AddHotKey {
    pub new_hot_key: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ChangeAutoStakeMaturity {
    pub requested_setting_for_auto_stake_maturity: bool,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct IncreaseDissolveDelay {
    pub additional_dissolve_delay_seconds: u32,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SetDissolveTimestamp {
    pub dissolve_timestamp_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Operation {
    RemoveHotKey(RemoveHotKey),
    AddHotKey(AddHotKey),
    ChangeAutoStakeMaturity(ChangeAutoStakeMaturity),
    StopDissolving {},
    StartDissolving {},
    IncreaseDissolveDelay(IncreaseDissolveDelay),
    JoinCommunityFund {},
    LeaveCommunityFund {},
    SetDissolveTimestamp(SetDissolveTimestamp),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Configure {
    pub operation: Option<Operation>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RegisterVote {
    pub vote: i32,
    pub proposal: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Merge {
    pub source_neuron_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct DisburseToNeuron {
    pub dissolve_delay_seconds: u64,
    pub kyc_verified: bool,
    pub amount_e8s: u64,
    pub new_controller: Option<Principal>,
    pub nonce: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct StakeMaturity {
    pub percentage_to_stake: Option<u32>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct MergeMaturity {
    pub percentage_to_merge: u32,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct AccountIdentifier {
    pub hash: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Amount {
    pub e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Disburse {
    pub to_account: Option<AccountIdentifier>,
    pub amount: Option<Amount>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Command {
    Spawn(Spawn),
    Split(Split),
    Follow(Follow),
    ClaimOrRefresh(ClaimOrRefresh),
    Configure(Configure),
    RegisterVote(RegisterVote),
    Merge(Merge),
    DisburseToNeuron(DisburseToNeuron),
    MakeProposal(Box<Proposal>),
    StakeMaturity(StakeMaturity),
    MergeMaturity(MergeMaturity),
    Disburse(Disburse),
}

#[derive(CandidType, Deserialize, Clone)]
pub enum NeuronIdOrSubaccount {
    Subaccount(serde_bytes::ByteBuf),
    NeuronId(NeuronId),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ManageNeuron {
    pub id: Option<NeuronId>,
    pub command: Option<Command>,
    pub neuron_id_or_subaccount: Option<NeuronIdOrSubaccount>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Percentage {
    pub basis_points: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Duration {
    pub seconds: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Tokens {
    pub e8s: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct VotingRewardParameters {
    pub reward_rate_transition_duration: Option<Duration>,
    pub initial_reward_rate: Option<Percentage>,
    pub final_reward_rate: Option<Percentage>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct GovernanceParameters {
    pub neuron_maximum_dissolve_delay_bonus: Option<Percentage>,
    pub neuron_maximum_age_for_age_bonus: Option<Duration>,
    pub neuron_maximum_dissolve_delay: Option<Duration>,
    pub neuron_minimum_dissolve_delay_to_vote: Option<Duration>,
    pub neuron_maximum_age_bonus: Option<Percentage>,
    pub neuron_minimum_stake: Option<Tokens>,
    pub proposal_wait_for_quiet_deadline_increase: Option<Duration>,
    pub proposal_initial_voting_period: Option<Duration>,
    pub proposal_rejection_fee: Option<Tokens>,
    pub voting_reward_parameters: Option<VotingRewardParameters>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Image {
    pub base64_encoding: Option<String>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct LedgerParameters {
    pub transaction_fee: Option<Tokens>,
    pub token_symbol: Option<String>,
    pub token_logo: Option<Image>,
    pub token_name: Option<String>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Canister {
    pub id: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronBasketConstructionParameters {
    pub dissolve_delay_interval: Option<Duration>,
    pub count: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct GlobalTimeOfDay {
    pub seconds_after_utc_midnight: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Countries {
    pub iso_codes: Vec<String>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SwapParameters {
    pub minimum_participants: Option<u64>,
    pub neurons_fund_participation: Option<bool>,
    pub duration: Option<Duration>,
    pub neuron_basket_construction_parameters: Option<NeuronBasketConstructionParameters>,
    pub confirmation_text: Option<String>,
    pub maximum_participant_icp: Option<Tokens>,
    pub minimum_icp: Option<Tokens>,
    pub minimum_direct_participation_icp: Option<Tokens>,
    pub minimum_participant_icp: Option<Tokens>,
    pub start_time: Option<GlobalTimeOfDay>,
    pub maximum_direct_participation_icp: Option<Tokens>,
    pub maximum_icp: Option<Tokens>,
    pub neurons_fund_investment_icp: Option<Tokens>,
    pub restricted_countries: Option<Countries>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SwapDistribution {
    pub total: Option<Tokens>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronDistribution {
    pub controller: Option<Principal>,
    pub dissolve_delay: Option<Duration>,
    pub memo: Option<u64>,
    pub vesting_period: Option<Duration>,
    pub stake: Option<Tokens>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct DeveloperDistribution {
    pub developer_neurons: Vec<NeuronDistribution>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct InitialTokenDistribution {
    pub treasury_distribution: Option<SwapDistribution>,
    pub developer_distribution: Option<DeveloperDistribution>,
    pub swap_distribution: Option<SwapDistribution>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct CreateServiceNervousSystem {
    pub url: Option<String>,
    pub governance_parameters: Option<GovernanceParameters>,
    pub fallback_controller_principal_ids: Vec<Principal>,
    pub logo: Option<Image>,
    pub name: Option<String>,
    pub ledger_parameters: Option<LedgerParameters>,
    pub description: Option<String>,
    pub dapp_canisters: Vec<Canister>,
    pub swap_parameters: Option<SwapParameters>,
    pub initial_token_distribution: Option<InitialTokenDistribution>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ExecuteNnsFunction {
    pub nns_function: i32,
    pub payload: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NodeProvider {
    pub id: Option<Principal>,
    pub reward_account: Option<AccountIdentifier>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RewardToNeuron {
    pub dissolve_delay_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RewardToAccount {
    pub to_account: Option<AccountIdentifier>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum RewardMode {
    RewardToNeuron(RewardToNeuron),
    RewardToAccount(RewardToAccount),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RewardNodeProvider {
    pub node_provider: Option<NodeProvider>,
    pub reward_mode: Option<RewardMode>,
    pub amount_e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronBasketConstructionParameters1 {
    pub dissolve_delay_interval_seconds: u64,
    pub count: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Params {
    pub min_participant_icp_e8s: u64,
    pub neuron_basket_construction_parameters: Option<NeuronBasketConstructionParameters1>,
    pub max_icp_e8s: u64,
    pub swap_due_timestamp_seconds: u64,
    pub min_participants: u32,
    pub sns_token_e8s: u64,
    pub sale_delay_seconds: Option<u64>,
    pub max_participant_icp_e8s: u64,
    pub min_direct_participation_icp_e8s: Option<u64>,
    pub min_icp_e8s: u64,
    pub max_direct_participation_icp_e8s: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct OpenSnsTokenSwap {
    pub community_fund_investment_e8s: Option<u64>,
    pub target_swap_canister_id: Option<Principal>,
    pub params: Option<Params>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct TimeWindow {
    pub start_timestamp_seconds: u64,
    pub end_timestamp_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SetOpenTimeWindowRequest {
    pub open_time_window: Option<TimeWindow>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SetSnsTokenSwapOpenTimeWindow {
    pub request: Option<SetOpenTimeWindowRequest>,
    pub swap_canister_id: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SetDefaultFollowees {
    pub default_followees: Vec<(i32, Followees)>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RewardNodeProviders {
    pub use_registry_derived_rewards: Option<bool>,
    pub rewards: Vec<RewardNodeProvider>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NetworkEconomics {
    pub neuron_minimum_stake_e8s: u64,
    pub max_proposals_to_keep_per_topic: u32,
    pub neuron_management_fee_per_proposal_e8s: u64,
    pub reject_cost_e8s: u64,
    pub transaction_fee_e8s: u64,
    pub neuron_spawn_dissolve_delay_seconds: u64,
    pub minimum_icp_xdr_rate: u64,
    pub maximum_node_provider_rewards_e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ApproveGenesisKyc {
    pub principals: Vec<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Change {
    ToRemove(NodeProvider),
    ToAdd(NodeProvider),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct AddOrRemoveNodeProvider {
    pub change: Option<Change>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Motion {
    pub motion_text: String,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Action {
    RegisterKnownNeuron(KnownNeuron),
    ManageNeuron(ManageNeuron),
    CreateServiceNervousSystem(CreateServiceNervousSystem),
    ExecuteNnsFunction(ExecuteNnsFunction),
    RewardNodeProvider(RewardNodeProvider),
    OpenSnsTokenSwap(OpenSnsTokenSwap),
    SetSnsTokenSwapOpenTimeWindow(SetSnsTokenSwapOpenTimeWindow),
    SetDefaultFollowees(SetDefaultFollowees),
    RewardNodeProviders(RewardNodeProviders),
    ManageNetworkEconomics(NetworkEconomics),
    ApproveGenesisKyc(ApproveGenesisKyc),
    AddOrRemoveNodeProvider(AddOrRemoveNodeProvider),
    Motion(Motion),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Proposal {
    pub url: String,
    pub title: Option<String>,
    pub action: Option<Action>,
    pub summary: String,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct MakingSnsProposal {
    pub proposal: Option<Box<Proposal>>,
    pub caller: Option<Principal>,
    pub proposer_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct MostRecentMonthlyNodeProviderRewards {
    pub timestamp: u64,
    pub rewards: Vec<RewardNodeProvider>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct GovernanceCachedMetrics {
    pub total_maturity_e8s_equivalent: u64,
    pub not_dissolving_neurons_e8s_buckets: Vec<(u64, f64)>,
    pub dissolving_neurons_staked_maturity_e8s_equivalent_sum: u64,
    pub garbage_collectable_neurons_count: u64,
    pub dissolving_neurons_staked_maturity_e8s_equivalent_buckets: Vec<(u64, f64)>,
    pub neurons_with_invalid_stake_count: u64,
    pub not_dissolving_neurons_count_buckets: Vec<(u64, u64)>,
    pub ect_neuron_count: u64,
    pub total_supply_icp: u64,
    pub neurons_with_less_than_6_months_dissolve_delay_count: u64,
    pub dissolved_neurons_count: u64,
    pub community_fund_total_maturity_e8s_equivalent: u64,
    pub total_staked_e8s_seed: u64,
    pub total_staked_maturity_e8s_equivalent_ect: u64,
    pub total_staked_e8s: u64,
    pub not_dissolving_neurons_count: u64,
    pub total_locked_e8s: u64,
    pub neurons_fund_total_active_neurons: u64,
    pub total_staked_maturity_e8s_equivalent: u64,
    pub not_dissolving_neurons_e8s_buckets_ect: Vec<(u64, f64)>,
    pub total_staked_e8s_ect: u64,
    pub not_dissolving_neurons_staked_maturity_e8s_equivalent_sum: u64,
    pub dissolved_neurons_e8s: u64,
    pub dissolving_neurons_e8s_buckets_seed: Vec<(u64, f64)>,
    pub neurons_with_less_than_6_months_dissolve_delay_e8s: u64,
    pub not_dissolving_neurons_staked_maturity_e8s_equivalent_buckets: Vec<(u64, f64)>,
    pub dissolving_neurons_count_buckets: Vec<(u64, u64)>,
    pub dissolving_neurons_e8s_buckets_ect: Vec<(u64, f64)>,
    pub dissolving_neurons_count: u64,
    pub dissolving_neurons_e8s_buckets: Vec<(u64, f64)>,
    pub total_staked_maturity_e8s_equivalent_seed: u64,
    pub community_fund_total_staked_e8s: u64,
    pub not_dissolving_neurons_e8s_buckets_seed: Vec<(u64, f64)>,
    pub timestamp_seconds: u64,
    pub seed_neuron_count: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct RewardEvent {
    pub rounds_since_last_distribution: Option<u64>,
    pub day_after_genesis: u64,
    pub actual_timestamp_seconds: u64,
    pub total_available_e8s_equivalent: u64,
    pub latest_round_available_e8s_equivalent: Option<u64>,
    pub distributed_e8s_equivalent: u64,
    pub settled_proposals: Vec<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronStakeTransfer {
    pub to_subaccount: serde_bytes::ByteBuf,
    pub neuron_stake_e8s: u64,
    pub from: Option<Principal>,
    pub memo: u64,
    pub from_subaccount: serde_bytes::ByteBuf,
    pub transfer_timestamp: u64,
    pub block_height: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Followers {
    pub followers: Vec<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct FollowersMap {
    pub followers_map: Vec<(u64, Followers)>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Progress {
    LastNeuronId(NeuronId),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Migration {
    pub status: Option<i32>,
    pub failure_reason: Option<String>,
    pub progress: Option<Progress>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Migrations {
    pub neuron_indexes_migration: Option<Migration>,
    pub copy_inactive_neurons_to_stable_memory_migration: Option<Migration>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct GovernanceError {
    pub error_message: String,
    pub error_type: i32,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct CfNeuron {
    pub has_created_neuron_recipes: Option<bool>,
    pub nns_neuron_id: u64,
    pub amount_icp_e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct CfParticipant {
    pub hotkey_principal: String,
    pub cf_neurons: Vec<CfNeuron>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Ballot {
    pub vote: i32,
    pub voting_power: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SwapParticipationLimits {
    pub min_participant_icp_e8s: Option<u64>,
    pub max_participant_icp_e8s: Option<u64>,
    pub min_direct_participation_icp_e8s: Option<u64>,
    pub max_direct_participation_icp_e8s: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronsFundNeuronPortion {
    pub hotkey_principal: Option<Principal>,
    pub is_capped: Option<bool>,
    pub maturity_equivalent_icp_e8s: Option<u64>,
    pub nns_neuron_id: Option<NeuronId>,
    pub amount_icp_e8s: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronsFundSnapshot {
    pub neurons_fund_neuron_portions: Vec<NeuronsFundNeuronPortion>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct IdealMatchedParticipationFunction {
    pub serialized_representation: Option<String>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronsFundParticipation {
    pub total_maturity_equivalent_icp_e8s: Option<u64>,
    pub intended_neurons_fund_participation_icp_e8s: Option<u64>,
    pub direct_participation_icp_e8s: Option<u64>,
    pub swap_participation_limits: Option<SwapParticipationLimits>,
    pub max_neurons_fund_swap_participation_icp_e8s: Option<u64>,
    pub neurons_fund_reserves: Option<NeuronsFundSnapshot>,
    pub ideal_matched_participation_function: Option<IdealMatchedParticipationFunction>,
    pub allocated_neurons_fund_participation_icp_e8s: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronsFundData {
    pub final_neurons_fund_participation: Option<NeuronsFundParticipation>,
    pub initial_neurons_fund_participation: Option<NeuronsFundParticipation>,
    pub neurons_fund_refunds: Option<NeuronsFundSnapshot>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct CanisterStatusResultV2 {
    pub status: Option<i32>,
    pub freezing_threshold: Option<u64>,
    pub controllers: Vec<Principal>,
    pub memory_size: Option<u64>,
    pub cycles: Option<u64>,
    pub idle_cycles_burned_per_day: Option<u64>,
    pub module_hash: serde_bytes::ByteBuf,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct CanisterSummary {
    pub status: Option<CanisterStatusResultV2>,
    pub canister_id: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SwapBackgroundInformation {
    pub ledger_index_canister_summary: Option<CanisterSummary>,
    pub fallback_controller_principal_ids: Vec<Principal>,
    pub ledger_archive_canister_summaries: Vec<CanisterSummary>,
    pub ledger_canister_summary: Option<CanisterSummary>,
    pub swap_canister_summary: Option<CanisterSummary>,
    pub governance_canister_summary: Option<CanisterSummary>,
    pub root_canister_summary: Option<CanisterSummary>,
    pub dapp_canister_summaries: Vec<CanisterSummary>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct DerivedProposalInformation {
    pub swap_background_information: Option<SwapBackgroundInformation>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Tally {
    pub no: u64,
    pub yes: u64,
    pub total: u64,
    pub timestamp_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct WaitForQuietState {
    pub current_deadline_timestamp_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ProposalData {
    pub id: Option<NeuronId>,
    pub failure_reason: Option<GovernanceError>,
    pub cf_participants: Vec<CfParticipant>,
    pub ballots: Vec<(u64, Ballot)>,
    pub proposal_timestamp_seconds: u64,
    pub reward_event_round: u64,
    pub failed_timestamp_seconds: u64,
    pub neurons_fund_data: Option<NeuronsFundData>,
    pub reject_cost_e8s: u64,
    pub derived_proposal_information: Option<DerivedProposalInformation>,
    pub latest_tally: Option<Tally>,
    pub sns_token_swap_lifecycle: Option<i32>,
    pub decided_timestamp_seconds: u64,
    pub proposal: Option<Box<Proposal>>,
    pub proposer: Option<NeuronId>,
    pub wait_for_quiet_state: Option<WaitForQuietState>,
    pub executed_timestamp_seconds: u64,
    pub original_total_community_fund_maturity_e8s_equivalent: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Command2 {
    Spawn(NeuronId),
    Split(Split),
    Configure(Configure),
    Merge(Merge),
    DisburseToNeuron(DisburseToNeuron),
    SyncCommand {},
    ClaimOrRefreshNeuron(ClaimOrRefresh),
    MergeMaturity(MergeMaturity),
    Disburse(Disburse),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronInFlightCommand {
    pub command: Option<Command2>,
    pub timestamp: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct BallotInfo {
    pub vote: i32,
    pub proposal_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum DissolveState {
    DissolveDelaySeconds(u64),
    WhenDissolvedTimestampSeconds(u64),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Neuron {
    pub id: Option<NeuronId>,
    pub staked_maturity_e8s_equivalent: Option<u64>,
    pub controller: Option<Principal>,
    pub recent_ballots: Vec<BallotInfo>,
    pub kyc_verified: bool,
    pub neuron_type: Option<i32>,
    pub not_for_profit: bool,
    pub maturity_e8s_equivalent: u64,
    pub cached_neuron_stake_e8s: u64,
    pub created_timestamp_seconds: u64,
    pub auto_stake_maturity: Option<bool>,
    pub aging_since_timestamp_seconds: u64,
    pub hot_keys: Vec<Principal>,
    pub account: serde_bytes::ByteBuf,
    pub joined_community_fund_timestamp_seconds: Option<u64>,
    pub dissolve_state: Option<DissolveState>,
    pub followees: Vec<(i32, Followees)>,
    pub neuron_fees_e8s: u64,
    pub transfer: Option<NeuronStakeTransfer>,
    pub known_neuron_data: Option<KnownNeuronData>,
    pub spawn_at_timestamp_seconds: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Governance {
    pub default_followees: Vec<(i32, Followees)>,
    pub making_sns_proposal: Option<MakingSnsProposal>,
    pub most_recent_monthly_node_provider_rewards: Option<MostRecentMonthlyNodeProviderRewards>,
    pub maturity_modulation_last_updated_at_timestamp_seconds: Option<u64>,
    pub wait_for_quiet_threshold_seconds: u64,
    pub metrics: Option<GovernanceCachedMetrics>,
    pub neuron_management_voting_period_seconds: Option<u64>,
    pub node_providers: Vec<NodeProvider>,
    pub cached_daily_maturity_modulation_basis_points: Option<i32>,
    pub economics: Option<NetworkEconomics>,
    pub spawning_neurons: Option<bool>,
    pub latest_reward_event: Option<RewardEvent>,
    pub to_claim_transfers: Vec<NeuronStakeTransfer>,
    pub short_voting_period_seconds: u64,
    pub topic_followee_index: Vec<(i32, FollowersMap)>,
    pub migrations: Option<Migrations>,
    pub proposals: Vec<(u64, ProposalData)>,
    pub in_flight_commands: Vec<(u64, NeuronInFlightCommand)>,
    pub neurons: Vec<(u64, Neuron)>,
    pub genesis_timestamp_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result_ {
    Ok,
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result1 {
    Error(GovernanceError),
    NeuronId(NeuronId),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ClaimOrRefreshNeuronFromAccountResponse {
    pub result: Option<Result1>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result2 {
    Ok(Neuron),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result3 {
    Ok(GovernanceCachedMetrics),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result4 {
    Ok(RewardNodeProviders),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronInfo {
    pub dissolve_delay_seconds: u64,
    pub recent_ballots: Vec<BallotInfo>,
    pub neuron_type: Option<i32>,
    pub created_timestamp_seconds: u64,
    pub state: i32,
    pub stake_e8s: u64,
    pub joined_community_fund_timestamp_seconds: Option<u64>,
    pub retrieved_at_timestamp_seconds: u64,
    pub known_neuron_data: Option<KnownNeuronData>,
    pub voting_power: u64,
    pub age_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result5 {
    Ok(NeuronInfo),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct GetNeuronsFundAuditInfoRequest {
    pub nns_proposal_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronsFundAuditInfo {
    pub final_neurons_fund_participation: Option<NeuronsFundParticipation>,
    pub initial_neurons_fund_participation: Option<NeuronsFundParticipation>,
    pub neurons_fund_refunds: Option<NeuronsFundSnapshot>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Ok {
    pub neurons_fund_audit_info: Option<NeuronsFundAuditInfo>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result6 {
    Ok(Ok),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct GetNeuronsFundAuditInfoResponse {
    pub result: Option<Result6>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result7 {
    Ok(NodeProvider),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ProposalInfo {
    pub id: Option<NeuronId>,
    pub status: i32,
    pub topic: i32,
    pub failure_reason: Option<GovernanceError>,
    pub ballots: Vec<(u64, Ballot)>,
    pub proposal_timestamp_seconds: u64,
    pub reward_event_round: u64,
    pub deadline_timestamp_seconds: Option<u64>,
    pub failed_timestamp_seconds: u64,
    pub reject_cost_e8s: u64,
    pub derived_proposal_information: Option<DerivedProposalInformation>,
    pub latest_tally: Option<Tally>,
    pub reward_status: i32,
    pub decided_timestamp_seconds: u64,
    pub proposal: Option<Box<Proposal>>,
    pub proposer: Option<NeuronId>,
    pub executed_timestamp_seconds: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ListKnownNeuronsResponse {
    pub known_neurons: Vec<KnownNeuron>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ListNeurons {
    pub neuron_ids: Vec<u64>,
    pub include_neurons_readable_by_caller: bool,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ListNeuronsResponse {
    pub neuron_infos: Vec<(u64, NeuronInfo)>,
    pub full_neurons: Vec<Neuron>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ListNodeProvidersResponse {
    pub node_providers: Vec<NodeProvider>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ListProposalInfo {
    pub include_reward_status: Vec<i32>,
    pub omit_large_fields: Option<bool>,
    pub before_proposal: Option<NeuronId>,
    pub limit: u32,
    pub exclude_topic: Vec<i32>,
    pub include_all_manage_neuron_proposals: Option<bool>,
    pub include_status: Vec<i32>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ListProposalInfoResponse {
    pub proposal_info: Vec<ProposalInfo>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SpawnResponse {
    pub created_neuron_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ClaimOrRefreshResponse {
    pub refreshed_neuron_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct MergeResponse {
    pub target_neuron: Option<Neuron>,
    pub source_neuron: Option<Neuron>,
    pub target_neuron_info: Option<NeuronInfo>,
    pub source_neuron_info: Option<NeuronInfo>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct MakeProposalResponse {
    pub message: Option<String>,
    pub proposal_id: Option<NeuronId>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct StakeMaturityResponse {
    pub maturity_e8s: u64,
    pub staked_maturity_e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct MergeMaturityResponse {
    pub merged_maturity_e8s: u64,
    pub new_stake_e8s: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct DisburseResponse {
    pub transfer_block_height: u64,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Command1 {
    Error(GovernanceError),
    Spawn(SpawnResponse),
    Split(SpawnResponse),
    Follow {},
    ClaimOrRefresh(ClaimOrRefreshResponse),
    Configure {},
    RegisterVote {},
    Merge(MergeResponse),
    DisburseToNeuron(SpawnResponse),
    MakeProposal(MakeProposalResponse),
    StakeMaturity(StakeMaturityResponse),
    MergeMaturity(MergeMaturityResponse),
    Disburse(DisburseResponse),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct ManageNeuronResponse {
    pub command: Option<Command1>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Committed {
    pub total_direct_contribution_icp_e8s: Option<u64>,
    pub total_neurons_fund_contribution_icp_e8s: Option<u64>,
    pub sns_governance_canister_id: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result8 {
    Committed(Committed),
    Aborted {},
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SettleCommunityFundParticipation {
    pub result: Option<Result8>,
    pub open_sns_token_swap_proposal_id: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Committed1 {
    pub total_direct_participation_icp_e8s: Option<u64>,
    pub total_neurons_fund_participation_icp_e8s: Option<u64>,
    pub sns_governance_canister_id: Option<Principal>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result9 {
    Committed(Committed1),
    Aborted {},
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SettleNeuronsFundParticipationRequest {
    pub result: Option<Result9>,
    pub nns_proposal_id: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct NeuronsFundNeuron {
    pub hotkey_principal: Option<String>,
    pub is_capped: Option<bool>,
    pub nns_neuron_id: Option<u64>,
    pub amount_icp_e8s: Option<u64>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct Ok1 {
    pub neurons_fund_neuron_portions: Vec<NeuronsFundNeuron>,
}

#[derive(CandidType, Deserialize, Clone)]
pub enum Result10 {
    Ok(Ok1),
    Err(GovernanceError),
}

#[derive(CandidType, Deserialize, Clone)]
pub struct SettleNeuronsFundParticipationResponse {
    pub result: Option<Result10>,
}

#[derive(CandidType, Deserialize, Clone)]
pub struct UpdateNodeProvider {
    pub reward_account: Option<AccountIdentifier>,
}

pub struct Service(pub Principal);
impl Service {
    pub async fn claim_gtc_neurons(
        &self,
        arg0: Principal,
        arg1: Vec<NeuronId>,
    ) -> Result<(Result_,)> {
        ic_cdk::call(self.0, "claim_gtc_neurons", (arg0, arg1)).await
    }
    pub async fn claim_or_refresh_neuron_from_account(
        &self,
        arg0: ClaimOrRefreshNeuronFromAccount,
    ) -> Result<(ClaimOrRefreshNeuronFromAccountResponse,)> {
        ic_cdk::call(self.0, "claim_or_refresh_neuron_from_account", (arg0,)).await
    }
    pub async fn get_build_metadata(&self) -> Result<(String,)> {
        ic_cdk::call(self.0, "get_build_metadata", ()).await
    }
    pub async fn get_full_neuron(&self, arg0: u64) -> Result<(Result2,)> {
        ic_cdk::call(self.0, "get_full_neuron", (arg0,)).await
    }
    pub async fn get_full_neuron_by_id_or_subaccount(
        &self,
        arg0: NeuronIdOrSubaccount,
    ) -> Result<(Result2,)> {
        ic_cdk::call(self.0, "get_full_neuron_by_id_or_subaccount", (arg0,)).await
    }
    pub async fn get_latest_reward_event(&self) -> Result<(RewardEvent,)> {
        ic_cdk::call(self.0, "get_latest_reward_event", ()).await
    }
    pub async fn get_metrics(&self) -> Result<(Result3,)> {
        ic_cdk::call(self.0, "get_metrics", ()).await
    }
    pub async fn get_monthly_node_provider_rewards(&self) -> Result<(Result4,)> {
        ic_cdk::call(self.0, "get_monthly_node_provider_rewards", ()).await
    }
    pub async fn get_most_recent_monthly_node_provider_rewards(
        &self,
    ) -> Result<(Option<MostRecentMonthlyNodeProviderRewards>,)> {
        ic_cdk::call(self.0, "get_most_recent_monthly_node_provider_rewards", ()).await
    }
    pub async fn get_network_economics_parameters(&self) -> Result<(NetworkEconomics,)> {
        ic_cdk::call(self.0, "get_network_economics_parameters", ()).await
    }
    pub async fn get_neuron_ids(&self) -> Result<(Vec<u64>,)> {
        ic_cdk::call(self.0, "get_neuron_ids", ()).await
    }
    pub async fn get_neuron_info(&self, arg0: u64) -> Result<(Result5,)> {
        ic_cdk::call(self.0, "get_neuron_info", (arg0,)).await
    }
    pub async fn get_neuron_info_by_id_or_subaccount(
        &self,
        arg0: NeuronIdOrSubaccount,
    ) -> Result<(Result5,)> {
        ic_cdk::call(self.0, "get_neuron_info_by_id_or_subaccount", (arg0,)).await
    }
    pub async fn get_neurons_fund_audit_info(
        &self,
        arg0: GetNeuronsFundAuditInfoRequest,
    ) -> Result<(GetNeuronsFundAuditInfoResponse,)> {
        ic_cdk::call(self.0, "get_neurons_fund_audit_info", (arg0,)).await
    }
    pub async fn get_node_provider_by_caller(&self, arg0: ()) -> Result<(Result7,)> {
        ic_cdk::call(self.0, "get_node_provider_by_caller", (arg0,)).await
    }
    pub async fn get_pending_proposals(&self) -> Result<(Vec<ProposalInfo>,)> {
        ic_cdk::call(self.0, "get_pending_proposals", ()).await
    }
    pub async fn get_proposal_info(&self, arg0: u64) -> Result<(Option<ProposalInfo>,)> {
        ic_cdk::call(self.0, "get_proposal_info", (arg0,)).await
    }
    pub async fn list_known_neurons(&self) -> Result<(ListKnownNeuronsResponse,)> {
        ic_cdk::call(self.0, "list_known_neurons", ()).await
    }
    pub async fn list_neurons(&self, arg0: ListNeurons) -> Result<(ListNeuronsResponse,)> {
        ic_cdk::call(self.0, "list_neurons", (arg0,)).await
    }
    pub async fn list_node_providers(&self) -> Result<(ListNodeProvidersResponse,)> {
        ic_cdk::call(self.0, "list_node_providers", ()).await
    }
    pub async fn list_proposals(
        &self,
        arg0: ListProposalInfo,
    ) -> Result<(ListProposalInfoResponse,)> {
        ic_cdk::call(self.0, "list_proposals", (arg0,)).await
    }
    pub async fn manage_neuron(&self, arg0: ManageNeuron) -> Result<(ManageNeuronResponse,)> {
        ic_cdk::call(self.0, "manage_neuron", (arg0,)).await
    }
    pub async fn settle_community_fund_participation(
        &self,
        arg0: SettleCommunityFundParticipation,
    ) -> Result<(Result_,)> {
        ic_cdk::call(self.0, "settle_community_fund_participation", (arg0,)).await
    }
    pub async fn settle_neurons_fund_participation(
        &self,
        arg0: SettleNeuronsFundParticipationRequest,
    ) -> Result<(SettleNeuronsFundParticipationResponse,)> {
        ic_cdk::call(self.0, "settle_neurons_fund_participation", (arg0,)).await
    }
    pub async fn simulate_manage_neuron(
        &self,
        arg0: ManageNeuron,
    ) -> Result<(ManageNeuronResponse,)> {
        ic_cdk::call(self.0, "simulate_manage_neuron", (arg0,)).await
    }
    pub async fn transfer_gtc_neuron(&self, arg0: NeuronId, arg1: NeuronId) -> Result<(Result_,)> {
        ic_cdk::call(self.0, "transfer_gtc_neuron", (arg0, arg1)).await
    }
    pub async fn update_node_provider(&self, arg0: UpdateNodeProvider) -> Result<(Result_,)> {
        ic_cdk::call(self.0, "update_node_provider", (arg0,)).await
    }
}
