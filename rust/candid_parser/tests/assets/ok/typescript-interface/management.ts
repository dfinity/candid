import { management as _management, createActor as _createActor, canisterId as _canisterId } from "declarations/management";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/management/management.did.d.js";
import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
function some<T>(value: T): Some<T> {
    return {
        _tag: "Some",
        value: value
    };
}
function none(): None {
    return {
        _tag: "None"
    };
}
function isNone<T>(option: Option<T>): option is None {
    return option._tag === "None";
}
function isSome<T>(option: Option<T>): option is Some<T> {
    return option._tag === "Some";
}
function unwrap<T>(option: Option<T>): T {
    if (isNone(option)) {
        throw new Error("unwrap: none");
    }
    return option.value;
}
function candid_some<T>(value: T): [T] {
    return [
        value
    ];
}
function candid_none<T>(): [] {
    return [];
}
function record_opt_to_undefined<T>(arg: T | null): T | undefined {
    return arg == null ? undefined : arg;
}
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
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): management {
    const actor = _createActor(canisterId, options);
    return new Management(actor);
}
export const canisterId = _canisterId;
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
import type { utxo as _utxo, canister_settings as _canister_settings, bitcoin_address as _bitcoin_address, get_utxos_response as _get_utxos_response, http_header as _http_header, bitcoin_network as _bitcoin_network, get_utxos_request as _get_utxos_request, get_balance_request as _get_balance_request, definite_canister_settings as _definite_canister_settings, block_hash as _block_hash, ecdsa_curve as _ecdsa_curve, canister_id as _canister_id } from "declarations/management/management.did.d.ts";
class Management implements management {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _management;
    }
    async bitcoin_get_balance(arg0: get_balance_request): Promise<satoshi> {
        const result = await this.#actor.bitcoin_get_balance(to_candid_get_balance_request_n1(arg0));
        return result;
    }
    async bitcoin_get_current_fee_percentiles(arg0: get_current_fee_percentiles_request): Promise<BigUint64Array | bigint[]> {
        const result = await this.#actor.bitcoin_get_current_fee_percentiles(arg0);
        return result;
    }
    async bitcoin_get_utxos(arg0: get_utxos_request): Promise<get_utxos_response> {
        const result = await this.#actor.bitcoin_get_utxos(to_candid_get_utxos_request_n3(arg0));
        return from_candid_get_utxos_response_n5(result);
    }
    async bitcoin_send_transaction(arg0: send_transaction_request): Promise<void> {
        const result = await this.#actor.bitcoin_send_transaction(arg0);
        return result;
    }
    async canister_status(arg0: {
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
    }> {
        const result = await this.#actor.canister_status(arg0);
        return from_candid_record_n8(result);
    }
    async create_canister(arg0: {
        settings?: canister_settings;
    }): Promise<{
        canister_id: canister_id;
    }> {
        const result = await this.#actor.create_canister(to_candid_record_n9(arg0));
        return result;
    }
    async delete_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        const result = await this.#actor.delete_canister(arg0);
        return result;
    }
    async deposit_cycles(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        const result = await this.#actor.deposit_cycles(arg0);
        return result;
    }
    async ecdsa_public_key(arg0: {
        key_id: {
            name: string;
            curve: ecdsa_curve;
        };
        canister_id?: canister_id;
        derivation_path: Array<Uint8Array | number[]>;
    }): Promise<{
        public_key: Uint8Array | number[];
        chain_code: Uint8Array | number[];
    }> {
        const result = await this.#actor.ecdsa_public_key(to_candid_record_n12(arg0));
        return result;
    }
    async http_request(arg0: {
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
    }): Promise<http_response> {
        const result = await this.#actor.http_request(to_candid_record_n13(arg0));
        return result;
    }
    async install_code(arg0: {
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
    }): Promise<void> {
        const result = await this.#actor.install_code(arg0);
        return result;
    }
    async provisional_create_canister_with_cycles(arg0: {
        settings?: canister_settings;
        specified_id?: canister_id;
        amount?: bigint;
    }): Promise<{
        canister_id: canister_id;
    }> {
        const result = await this.#actor.provisional_create_canister_with_cycles(to_candid_record_n14(arg0));
        return result;
    }
    async provisional_top_up_canister(arg0: {
        canister_id: canister_id;
        amount: bigint;
    }): Promise<void> {
        const result = await this.#actor.provisional_top_up_canister(arg0);
        return result;
    }
    async raw_rand(): Promise<Uint8Array | number[]> {
        const result = await this.#actor.raw_rand();
        return result;
    }
    async sign_with_ecdsa(arg0: {
        key_id: {
            name: string;
            curve: ecdsa_curve;
        };
        derivation_path: Array<Uint8Array | number[]>;
        message_hash: Uint8Array | number[];
    }): Promise<{
        signature: Uint8Array | number[];
    }> {
        const result = await this.#actor.sign_with_ecdsa(arg0);
        return result;
    }
    async start_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        const result = await this.#actor.start_canister(arg0);
        return result;
    }
    async stop_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        const result = await this.#actor.stop_canister(arg0);
        return result;
    }
    async uninstall_code(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        const result = await this.#actor.uninstall_code(arg0);
        return result;
    }
    async update_settings(arg0: {
        canister_id: Principal;
        settings: canister_settings;
    }): Promise<void> {
        const result = await this.#actor.update_settings(to_candid_record_n15(arg0));
        return result;
    }
}
export const management: management = new Management();
function to_candid_record_n2(value: {
    network: bitcoin_network;
    address: bitcoin_address;
    min_confirmations?: number;
}): {
    network: _bitcoin_network;
    address: _bitcoin_address;
    min_confirmations: [] | [number];
} {
    return {
        network: value.network,
        address: value.address,
        min_confirmations: value.min_confirmations ? candid_some(value.min_confirmations) : candid_none()
    };
}
function to_candid_canister_settings_n10(value: canister_settings): _canister_settings {
    return to_candid_record_n11(value);
}
function to_candid_record_n13(value: {
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
}): {
    url: string;
    method: {
        get: null;
    } | {
        head: null;
    } | {
        post: null;
    };
    max_response_bytes: [] | [bigint];
    body: [] | [Uint8Array | number[]];
    transform: [] | [{
            function: [Principal, string];
            context: Uint8Array | number[];
        }];
    headers: Array<_http_header>;
} {
    return {
        url: value.url,
        method: value.method,
        max_response_bytes: value.max_response_bytes ? candid_some(value.max_response_bytes) : candid_none(),
        body: value.body ? candid_some(value.body) : candid_none(),
        transform: value.transform ? candid_some(value.transform) : candid_none(),
        headers: value.headers
    };
}
function from_candid_opt_n7(value: [] | [Uint8Array | number[]]): Uint8Array | number[] | null {
    return value.length === 0 ? null : value[0];
}
function to_candid_record_n9(value: {
    settings?: canister_settings;
}): {
    settings: [] | [_canister_settings];
} {
    return {
        settings: value.settings ? candid_some(to_candid_canister_settings_n10(value.settings)) : candid_none()
    };
}
function from_candid_get_utxos_response_n5(value: _get_utxos_response): get_utxos_response {
    return from_candid_record_n6(value);
}
function to_candid_record_n4(value: {
    network: bitcoin_network;
    filter?: {
        page: Uint8Array | number[];
    } | {
        min_confirmations: number;
    };
    address: bitcoin_address;
}): {
    network: _bitcoin_network;
    filter: [] | [{
            page: Uint8Array | number[];
        } | {
            min_confirmations: number;
        }];
    address: _bitcoin_address;
} {
    return {
        network: value.network,
        filter: value.filter ? candid_some(value.filter) : candid_none(),
        address: value.address
    };
}
function to_candid_get_utxos_request_n3(value: get_utxos_request): _get_utxos_request {
    return to_candid_record_n4(value);
}
function to_candid_get_balance_request_n1(value: get_balance_request): _get_balance_request {
    return to_candid_record_n2(value);
}
function from_candid_record_n8(value: {
    status: {
        stopped: null;
    } | {
        stopping: null;
    } | {
        running: null;
    };
    memory_size: bigint;
    cycles: bigint;
    settings: _definite_canister_settings;
    idle_cycles_burned_per_day: bigint;
    module_hash: [] | [Uint8Array | number[]];
}): {
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
} {
    return {
        status: value.status,
        memory_size: value.memory_size,
        cycles: value.cycles,
        settings: value.settings,
        idle_cycles_burned_per_day: value.idle_cycles_burned_per_day,
        module_hash: record_opt_to_undefined(from_candid_opt_n7(value.module_hash))
    };
}
function to_candid_record_n11(value: {
    freezing_threshold?: bigint;
    controllers?: Array<Principal>;
    memory_allocation?: bigint;
    compute_allocation?: bigint;
}): {
    freezing_threshold: [] | [bigint];
    controllers: [] | [Array<Principal>];
    memory_allocation: [] | [bigint];
    compute_allocation: [] | [bigint];
} {
    return {
        freezing_threshold: value.freezing_threshold ? candid_some(value.freezing_threshold) : candid_none(),
        controllers: value.controllers ? candid_some(value.controllers) : candid_none(),
        memory_allocation: value.memory_allocation ? candid_some(value.memory_allocation) : candid_none(),
        compute_allocation: value.compute_allocation ? candid_some(value.compute_allocation) : candid_none()
    };
}
function to_candid_record_n12(value: {
    key_id: {
        name: string;
        curve: ecdsa_curve;
    };
    canister_id?: canister_id;
    derivation_path: Array<Uint8Array | number[]>;
}): {
    key_id: {
        name: string;
        curve: _ecdsa_curve;
    };
    canister_id: [] | [_canister_id];
    derivation_path: Array<Uint8Array | number[]>;
} {
    return {
        key_id: value.key_id,
        canister_id: value.canister_id ? candid_some(value.canister_id) : candid_none(),
        derivation_path: value.derivation_path
    };
}
function to_candid_record_n14(value: {
    settings?: canister_settings;
    specified_id?: canister_id;
    amount?: bigint;
}): {
    settings: [] | [_canister_settings];
    specified_id: [] | [_canister_id];
    amount: [] | [bigint];
} {
    return {
        settings: value.settings ? candid_some(to_candid_canister_settings_n10(value.settings)) : candid_none(),
        specified_id: value.specified_id ? candid_some(value.specified_id) : candid_none(),
        amount: value.amount ? candid_some(value.amount) : candid_none()
    };
}
function to_candid_record_n15(value: {
    canister_id: Principal;
    settings: canister_settings;
}): {
    canister_id: Principal;
    settings: _canister_settings;
} {
    return {
        canister_id: value.canister_id,
        settings: to_candid_canister_settings_n10(value.settings)
    };
}
function from_candid_record_n6(value: {
    next_page: [] | [Uint8Array | number[]];
    tip_height: number;
    tip_block_hash: _block_hash;
    utxos: Array<_utxo>;
}): {
    next_page?: Uint8Array | number[];
    tip_height: number;
    tip_block_hash: block_hash;
    utxos: Array<utxo>;
} {
    return {
        next_page: record_opt_to_undefined(from_candid_opt_n7(value.next_page)),
        tip_height: value.tip_height,
        tip_block_hash: value.tip_block_hash,
        utxos: value.utxos
    };
}

