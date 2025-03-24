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
function record_opt_to_undefined<T>(arg: T): T | undefined {
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
class Backend implements backend {
    #actor: ActorSubclass<_SERVICE>;
    constructor(){
        this.#actor = _backend;
    }
    async transfer(arg0: TransferArgs): Promise<Result> {
        const result = await this.#actor.transfer({
            toPrincipal: arg0.toPrincipal,
            amount: {
                e8s: arg0.amount.e8s
            },
            toSubaccount: arg0.toSubaccount ? candid_some(arg0.toSubaccount) : candid_none()
        });
        return result;
    }
}
export const backend = new Backend();

