import { management as _management, createActor as _createActor, canisterId as _canisterId } from "declarations/management";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/management/management.did.d.js";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
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
function extractAgentErrorMessage(error: string): string {
    const errorString = String(error);
    const match = errorString.match(/with message:\s*'([^']+)'/s);
    return match ? match[1] : errorString;
}
export type bitcoin_address = string;
export type bitcoin_network = "mainnet" | "testnet";
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
export type ecdsa_curve = "secp256k1";
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
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): managementInterface {
    if (!options) {
        options = {};
    }
    if (process.env.BACKEND_HOST) {
        options = {
            ...options,
            agentOptions: {
                ...options.agentOptions,
                host: process.env.BACKEND_HOST
            }
        };
    }
    const actor = _createActor(canisterId, options);
    return new Management(actor);
}
export const canisterId = _canisterId;
export interface managementInterface {
    bitcoin_get_balance(arg0: get_balance_request): Promise<satoshi>;
    bitcoin_get_current_fee_percentiles(arg0: get_current_fee_percentiles_request): Promise<BigUint64Array | bigint[]>;
    bitcoin_get_utxos(arg0: get_utxos_request): Promise<get_utxos_response>;
    bitcoin_send_transaction(arg0: send_transaction_request): Promise<void>;
    canister_status(arg0: {
        canister_id: canister_id;
    }): Promise<{
        status: "stopped" | "stopping" | "running";
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
        method: "get" | "head" | "post";
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
        mode: "reinstall" | "upgrade" | "install";
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
import type { bitcoin_address as _bitcoin_address, bitcoin_network as _bitcoin_network, block_hash as _block_hash, canister_id as _canister_id, canister_settings as _canister_settings, definite_canister_settings as _definite_canister_settings, ecdsa_curve as _ecdsa_curve, get_balance_request as _get_balance_request, get_current_fee_percentiles_request as _get_current_fee_percentiles_request, get_utxos_request as _get_utxos_request, get_utxos_response as _get_utxos_response, http_header as _http_header, send_transaction_request as _send_transaction_request, utxo as _utxo, wasm_module as _wasm_module } from "declarations/management/management.did.d.ts";
class Management implements managementInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        if (actor) {
            this.#actor = actor;
        } else {
            if (process.env.BACKEND_HOST) {
                this.#actor = _createActor(canisterId, {
                    agentOptions: {
                        host: process.env.BACKEND_HOST
                    }
                });
            } else {
                this.#actor = _createActor(canisterId);
            }
        }
    }
    async bitcoin_get_balance(arg0: get_balance_request): Promise<satoshi> {
        try {
            const result = await this.#actor.bitcoin_get_balance(to_candid_get_balance_request_n1(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async bitcoin_get_current_fee_percentiles(arg0: get_current_fee_percentiles_request): Promise<BigUint64Array | bigint[]> {
        try {
            const result = await this.#actor.bitcoin_get_current_fee_percentiles(to_candid_get_current_fee_percentiles_request_n5(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async bitcoin_get_utxos(arg0: get_utxos_request): Promise<get_utxos_response> {
        try {
            const result = await this.#actor.bitcoin_get_utxos(to_candid_get_utxos_request_n7(arg0));
            return from_candid_get_utxos_response_n10(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async bitcoin_send_transaction(arg0: send_transaction_request): Promise<void> {
        try {
            const result = await this.#actor.bitcoin_send_transaction(to_candid_send_transaction_request_n13(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async canister_status(arg0: {
        canister_id: canister_id;
    }): Promise<{
        status: "stopped" | "stopping" | "running";
        memory_size: bigint;
        cycles: bigint;
        settings: definite_canister_settings;
        idle_cycles_burned_per_day: bigint;
        module_hash?: Uint8Array | number[];
    }> {
        try {
            const result = await this.#actor.canister_status(arg0);
            return from_candid_record_n15(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async create_canister(arg0: {
        settings?: canister_settings;
    }): Promise<{
        canister_id: canister_id;
    }> {
        try {
            const result = await this.#actor.create_canister(to_candid_record_n17(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async delete_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        try {
            const result = await this.#actor.delete_canister(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async deposit_cycles(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        try {
            const result = await this.#actor.deposit_cycles(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
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
        try {
            const result = await this.#actor.ecdsa_public_key(to_candid_record_n20(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async http_request(arg0: {
        url: string;
        method: "get" | "head" | "post";
        max_response_bytes?: bigint;
        body?: Uint8Array | number[];
        transform?: {
            function: [Principal, string];
            context: Uint8Array | number[];
        };
        headers: Array<http_header>;
    }): Promise<http_response> {
        try {
            const result = await this.#actor.http_request(to_candid_record_n24(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async install_code(arg0: {
        arg: Uint8Array | number[];
        wasm_module: wasm_module;
        mode: "reinstall" | "upgrade" | "install";
        canister_id: canister_id;
    }): Promise<void> {
        try {
            const result = await this.#actor.install_code(to_candid_record_n26(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async provisional_create_canister_with_cycles(arg0: {
        settings?: canister_settings;
        specified_id?: canister_id;
        amount?: bigint;
    }): Promise<{
        canister_id: canister_id;
    }> {
        try {
            const result = await this.#actor.provisional_create_canister_with_cycles(to_candid_record_n28(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async provisional_top_up_canister(arg0: {
        canister_id: canister_id;
        amount: bigint;
    }): Promise<void> {
        try {
            const result = await this.#actor.provisional_top_up_canister(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async raw_rand(): Promise<Uint8Array | number[]> {
        try {
            const result = await this.#actor.raw_rand();
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
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
        try {
            const result = await this.#actor.sign_with_ecdsa(to_candid_record_n29(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async start_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        try {
            const result = await this.#actor.start_canister(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async stop_canister(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        try {
            const result = await this.#actor.stop_canister(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async uninstall_code(arg0: {
        canister_id: canister_id;
    }): Promise<void> {
        try {
            const result = await this.#actor.uninstall_code(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async update_settings(arg0: {
        canister_id: Principal;
        settings: canister_settings;
    }): Promise<void> {
        try {
            const result = await this.#actor.update_settings(to_candid_record_n30(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
}
export const management: managementInterface = new Management();
function from_candid_get_utxos_response_n10(value: _get_utxos_response): get_utxos_response {
    return from_candid_record_n11(value);
}
function from_candid_opt_n12(value: [] | [Uint8Array | number[]]): Uint8Array | number[] | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_record_n11(value: {
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
        next_page: record_opt_to_undefined(from_candid_opt_n12(value.next_page)),
        tip_height: value.tip_height,
        tip_block_hash: value.tip_block_hash,
        utxos: value.utxos
    };
}
function from_candid_record_n15(value: {
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
    status: "stopped" | "stopping" | "running";
    memory_size: bigint;
    cycles: bigint;
    settings: definite_canister_settings;
    idle_cycles_burned_per_day: bigint;
    module_hash?: Uint8Array | number[];
} {
    return {
        status: from_candid_variant_n16(value.status),
        memory_size: value.memory_size,
        cycles: value.cycles,
        settings: value.settings,
        idle_cycles_burned_per_day: value.idle_cycles_burned_per_day,
        module_hash: record_opt_to_undefined(from_candid_opt_n12(value.module_hash))
    };
}
function from_candid_variant_n16(value: {
    stopped: null;
} | {
    stopping: null;
} | {
    running: null;
}): "stopped" | "stopping" | "running" {
    return "stopped" in value ? "stopped" : "stopping" in value ? "stopping" : "running" in value ? "running" : value;
}
function to_candid_bitcoin_network_n3(value: bitcoin_network): _bitcoin_network {
    return to_candid_variant_n4(value);
}
function to_candid_canister_settings_n18(value: canister_settings): _canister_settings {
    return to_candid_record_n19(value);
}
function to_candid_ecdsa_curve_n22(value: ecdsa_curve): _ecdsa_curve {
    return to_candid_variant_n23(value);
}
function to_candid_get_balance_request_n1(value: get_balance_request): _get_balance_request {
    return to_candid_record_n2(value);
}
function to_candid_get_current_fee_percentiles_request_n5(value: get_current_fee_percentiles_request): _get_current_fee_percentiles_request {
    return to_candid_record_n6(value);
}
function to_candid_get_utxos_request_n7(value: get_utxos_request): _get_utxos_request {
    return to_candid_record_n8(value);
}
function to_candid_record_n14(value: {
    transaction: Uint8Array | number[];
    network: bitcoin_network;
}): {
    transaction: Uint8Array | number[];
    network: _bitcoin_network;
} {
    return {
        transaction: value.transaction,
        network: to_candid_bitcoin_network_n3(value.network)
    };
}
function to_candid_record_n17(value: {
    settings?: canister_settings;
}): {
    settings: [] | [_canister_settings];
} {
    return {
        settings: value.settings ? candid_some(to_candid_canister_settings_n18(value.settings)) : candid_none()
    };
}
function to_candid_record_n19(value: {
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
        network: to_candid_bitcoin_network_n3(value.network),
        address: value.address,
        min_confirmations: value.min_confirmations ? candid_some(value.min_confirmations) : candid_none()
    };
}
function to_candid_record_n20(value: {
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
        key_id: to_candid_record_n21(value.key_id),
        canister_id: value.canister_id ? candid_some(value.canister_id) : candid_none(),
        derivation_path: value.derivation_path
    };
}
function to_candid_record_n21(value: {
    name: string;
    curve: ecdsa_curve;
}): {
    name: string;
    curve: _ecdsa_curve;
} {
    return {
        name: value.name,
        curve: to_candid_ecdsa_curve_n22(value.curve)
    };
}
function to_candid_record_n24(value: {
    url: string;
    method: "get" | "head" | "post";
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
        method: to_candid_variant_n25(value.method),
        max_response_bytes: value.max_response_bytes ? candid_some(value.max_response_bytes) : candid_none(),
        body: value.body ? candid_some(value.body) : candid_none(),
        transform: value.transform ? candid_some(value.transform) : candid_none(),
        headers: value.headers
    };
}
function to_candid_record_n26(value: {
    arg: Uint8Array | number[];
    wasm_module: wasm_module;
    mode: "reinstall" | "upgrade" | "install";
    canister_id: canister_id;
}): {
    arg: Uint8Array | number[];
    wasm_module: _wasm_module;
    mode: {
        reinstall: null;
    } | {
        upgrade: null;
    } | {
        install: null;
    };
    canister_id: _canister_id;
} {
    return {
        arg: value.arg,
        wasm_module: value.wasm_module,
        mode: to_candid_variant_n27(value.mode),
        canister_id: value.canister_id
    };
}
function to_candid_record_n28(value: {
    settings?: canister_settings;
    specified_id?: canister_id;
    amount?: bigint;
}): {
    settings: [] | [_canister_settings];
    specified_id: [] | [_canister_id];
    amount: [] | [bigint];
} {
    return {
        settings: value.settings ? candid_some(to_candid_canister_settings_n18(value.settings)) : candid_none(),
        specified_id: value.specified_id ? candid_some(value.specified_id) : candid_none(),
        amount: value.amount ? candid_some(value.amount) : candid_none()
    };
}
function to_candid_record_n29(value: {
    key_id: {
        name: string;
        curve: ecdsa_curve;
    };
    derivation_path: Array<Uint8Array | number[]>;
    message_hash: Uint8Array | number[];
}): {
    key_id: {
        name: string;
        curve: _ecdsa_curve;
    };
    derivation_path: Array<Uint8Array | number[]>;
    message_hash: Uint8Array | number[];
} {
    return {
        key_id: to_candid_record_n21(value.key_id),
        derivation_path: value.derivation_path,
        message_hash: value.message_hash
    };
}
function to_candid_record_n30(value: {
    canister_id: Principal;
    settings: canister_settings;
}): {
    canister_id: Principal;
    settings: _canister_settings;
} {
    return {
        canister_id: value.canister_id,
        settings: to_candid_canister_settings_n18(value.settings)
    };
}
function to_candid_record_n6(value: {
    network: bitcoin_network;
}): {
    network: _bitcoin_network;
} {
    return {
        network: to_candid_bitcoin_network_n3(value.network)
    };
}
function to_candid_record_n8(value: {
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
        network: to_candid_bitcoin_network_n3(value.network),
        filter: value.filter ? candid_some(to_candid_variant_n9(value.filter)) : candid_none(),
        address: value.address
    };
}
function to_candid_send_transaction_request_n13(value: send_transaction_request): _send_transaction_request {
    return to_candid_record_n14(value);
}
function to_candid_variant_n23(value: "secp256k1"): {
    secp256k1: null;
} {
    return value == "secp256k1" ? {
        secp256k1: null
    } : value;
}
function to_candid_variant_n25(value: "get" | "head" | "post"): {
    get: null;
} | {
    head: null;
} | {
    post: null;
} {
    return value == "get" ? {
        get: null
    } : value == "head" ? {
        head: null
    } : value == "post" ? {
        post: null
    } : value;
}
function to_candid_variant_n27(value: "reinstall" | "upgrade" | "install"): {
    reinstall: null;
} | {
    upgrade: null;
} | {
    install: null;
} {
    return value == "reinstall" ? {
        reinstall: null
    } : value == "upgrade" ? {
        upgrade: null
    } : value == "install" ? {
        install: null
    } : value;
}
function to_candid_variant_n4(value: "mainnet" | "testnet"): {
    mainnet: null;
} | {
    testnet: null;
} {
    return value == "mainnet" ? {
        mainnet: null
    } : value == "testnet" ? {
        testnet: null
    } : value;
}
function to_candid_variant_n9(value: {
    page: Uint8Array | number[];
} | {
    min_confirmations: number;
}): {
    page: Uint8Array | number[];
} | {
    min_confirmations: number;
} {
    return "page" in value ? {
        page: value.page
    } : "min_confirmations" in value ? {
        min_confirmations: value.min_confirmations
    } : value;
}

