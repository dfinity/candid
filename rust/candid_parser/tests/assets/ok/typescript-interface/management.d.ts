import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type bitcoin_address = string;
export type bitcoin_network = {
    mainnet: null;
} | {
    testnet: null;
};
export type block_hash = Uint8Array | number[];
export type canister_id = Principal;
export interface canister_settings {
    freezing_threshold?: bigint;
    controllers?: Array<Principal>;
    memory_allocation?: bigint;
    compute_allocation?: bigint;
}
export interface definite_canister_settings {
    freezing_threshold: bigint;
    controllers: Array<Principal>;
    memory_allocation: bigint;
    compute_allocation: bigint;
}
export type ecdsa_curve = {
    secp256k1: null;
};
export interface get_balance_request {
    network: bitcoin_network;
    address: bitcoin_address;
    min_confirmations?: number;
}
export interface get_current_fee_percentiles_request {
    network: bitcoin_network;
}
export interface get_utxos_request {
    network: bitcoin_network;
    filter?: {
        page: Uint8Array | number[];
    } | {
        min_confirmations: number;
    };
    address: bitcoin_address;
}
export interface get_utxos_response {
    next_page?: Uint8Array | number[];
    tip_height: number;
    tip_block_hash: block_hash;
    utxos: Array<utxo>;
}
export interface http_header {
    value: string;
    name: string;
}
export interface http_response {
    status: bigint;
    body: Uint8Array | number[];
    headers: Array<http_header>;
}
export type millisatoshi_per_byte = bigint;
export interface outpoint {
    txid: Uint8Array | number[];
    vout: number;
}
export type satoshi = bigint;
export interface send_transaction_request {
    transaction: Uint8Array | number[];
    network: bitcoin_network;
}
export type user_id = Principal;
export interface utxo {
    height: number;
    value: satoshi;
    outpoint: outpoint;
}
export type wasm_module = Uint8Array | number[];
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => management;
export declare const canisterId: string;
export interface management {
    bitcoin_get_balance(arg0: get_balance_request): Promise<satoshi>;
    bitcoin_get_current_fee_percentiles(arg0: get_current_fee_percentiles_request): Promise<BigUint64Array | bigint[]>;
    bitcoin_get_utxos(arg0: get_utxos_request): Promise<get_utxos_response>;
    bitcoin_send_transaction(arg0: send_transaction_request): Promise<void>;
    canister_status(arg0: {
        canister_id: canister_id;
    }): Promise<{
        status: {
            stopped: null;
        } | {
            stopping: null;
        } | {
            running: null;
        };
        memory_size: bigint;
        cycles: bigint;
        settings: definite_canister_settings;
        idle_cycles_burned_per_day: bigint;
        module_hash?: Uint8Array | number[];
    }>;
    create_canister(arg0: {
        settings?: canister_settings;
    }): Promise<{
        canister_id: canister_id;
    }>;
    delete_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void>;
    deposit_cycles(arg0: {
        canister_id: canister_id;
    }): Promise<void>;
    ecdsa_public_key(arg0: {
        key_id: {
            name: string;
            curve: ecdsa_curve;
        };
        canister_id?: canister_id;
        derivation_path: Array<Uint8Array | number[]>;
    }): Promise<{
        public_key: Uint8Array | number[];
        chain_code: Uint8Array | number[];
    }>;
    http_request(arg0: {
        url: string;
        method: {
            get: null;
        } | {
            head: null;
        } | {
            post: null;
        };
        max_response_bytes?: bigint;
        body?: Uint8Array | number[];
        transform?: {
            function: [Principal, string];
            context: Uint8Array | number[];
        };
        headers: Array<http_header>;
    }): Promise<http_response>;
    install_code(arg0: {
        arg: Uint8Array | number[];
        wasm_module: wasm_module;
        mode: {
            reinstall: null;
        } | {
            upgrade: null;
        } | {
            install: null;
        };
        canister_id: canister_id;
    }): Promise<void>;
    provisional_create_canister_with_cycles(arg0: {
        settings?: canister_settings;
        specified_id?: canister_id;
        amount?: bigint;
    }): Promise<{
        canister_id: canister_id;
    }>;
    provisional_top_up_canister(arg0: {
        canister_id: canister_id;
        amount: bigint;
    }): Promise<void>;
    raw_rand(): Promise<Uint8Array | number[]>;
    sign_with_ecdsa(arg0: {
        key_id: {
            name: string;
            curve: ecdsa_curve;
        };
        derivation_path: Array<Uint8Array | number[]>;
        message_hash: Uint8Array | number[];
    }): Promise<{
        signature: Uint8Array | number[];
    }>;
    start_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void>;
    stop_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void>;
    uninstall_code(arg0: {
        canister_id: canister_id;
    }): Promise<void>;
    update_settings(arg0: {
        canister_id: Principal;
        settings: canister_settings;
    }): Promise<void>;
}

