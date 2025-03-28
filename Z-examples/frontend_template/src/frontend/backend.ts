import { backend as _backend } from "declarations/backend";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/backend/backend.did.d.js";
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
type Result = {
    ok: bigint;
} | {
    err: string;
};
interface Tokens {
    e8s: bigint;
}
interface TransferArgs {
    toPrincipal: Principal;
    amount: Tokens;
    toSubaccount?: Uint8Array | number[];
}
interface backend {
    transfer(arg0: TransferArgs): Promise<Result>;
}
import type { Tokens as _Tokens, TransferArgs as _TransferArgs } from "declarations/backend/backend.did.d.ts";
class Backend implements backend {
    #actor: ActorSubclass<_SERVICE>;
    constructor(){
        this.#actor = _backend;
    }
    async transfer(arg0: TransferArgs): Promise<Result> {
        const result = await this.#actor.transfer(to_candid_TransferArgs_n1(arg0));
        return result;
    }
}
export const backend = new Backend();
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
function to_candid_TransferArgs_n1(value: TransferArgs): _TransferArgs {
    return to_candid_record_n2(value);
}

