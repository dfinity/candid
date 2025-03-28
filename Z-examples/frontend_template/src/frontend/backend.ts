import { backend as _backend, createActor as _createActor, canisterId as _canisterId } from "../../declarations/backend";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "../../declarations/backend/backend.did.d.js";
import type { Principal } from "@dfinity/principal";
type Some<T> = {
    _tag: "Some";
    value: T;
};
type None = {
    _tag: "None";
};
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
export type Result = {
    ok: bigint;
} | {
    err: string;
};
export interface Tokens {
    e8s: bigint;
}
export interface TransferArgs {
    toPrincipal: Principal;
    amount: Tokens;
    toSubaccount?: Uint8Array | number[];
}
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): backend {
    const actor = _createActor(canisterId, options);
    return new Backend(actor);
}
export const canisterId = _canisterId;
interface backend {
    transfer(arg0: TransferArgs): Promise<Result>;
}
import type { Tokens as _Tokens, TransferArgs as _TransferArgs } from "../../declarations/backend/backend.did.d.ts";
class Backend implements backend {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _backend;
    }
    async transfer(arg0: TransferArgs): Promise<Result> {
        const result = await this.#actor.transfer(to_candid_TransferArgs_n1(arg0));
        return result;
    }
}
export const backend = new Backend();
function to_candid_TransferArgs_n1(value: TransferArgs): _TransferArgs {
    return to_candid_record_n2(value);
}
function to_candid_record_n2(value: {
    toPrincipal: Principal;
    amount: Tokens;
    toSubaccount?: Uint8Array | number[];
}): {
    toPrincipal: Principal;
    amount: _Tokens;
    toSubaccount: [] | [Uint8Array | number[]];
} {
    return {
        toPrincipal: value.toPrincipal,
        amount: value.amount,
        toSubaccount: value.toSubaccount ? candid_some(value.toSubaccount) : candid_none()
    };
}

