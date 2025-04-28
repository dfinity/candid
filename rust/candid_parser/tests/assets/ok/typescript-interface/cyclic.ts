import { cyclic as _cyclic, createActor as _createActor, canisterId as _canisterId } from "declarations/cyclic";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/cyclic/cyclic.did.d.js";
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
export type A = Some<B> | None;
export type B = Some<C> | None;
export type C = A;
export type X = Y;
export type Y = Z;
export type Z = A;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): cyclicInterface {
    const actor = _createActor(canisterId, options);
    return new Cyclic(actor);
}
export const canisterId = _canisterId;
export interface cyclicInterface {
    f(arg0: A, arg1: B, arg2: C, arg3: X, arg4: Y, arg5: Z): Promise<void>;
}
import type { A as _A, B as _B, C as _C, X as _X, Y as _Y, Z as _Z } from "declarations/cyclic/cyclic.did.d.ts";
class Cyclic implements cyclicInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _cyclic;
    }
    async f(arg0: A, arg1: B, arg2: C, arg3: X, arg4: Y, arg5: Z): Promise<void> {
        const result = await this.#actor.f(to_candid_A_n1(arg0), to_candid_B_n3(arg1), to_candid_C_n5(arg2), to_candid_X_n6(arg3), to_candid_Y_n7(arg4), to_candid_Z_n8(arg5));
        return result;
    }
}
export const cyclic: cyclicInterface = new Cyclic();
function to_candid_A_n1(value: A): _A {
    return to_candid_opt_n2(value);
}
function to_candid_B_n3(value: B): _B {
    return to_candid_opt_n4(value);
}
function to_candid_C_n5(value: C): _C {
    return to_candid_opt_n2(value);
}
function to_candid_X_n6(value: X): _X {
    return to_candid_opt_n2(value);
}
function to_candid_Y_n7(value: Y): _Y {
    return to_candid_opt_n2(value);
}
function to_candid_Z_n8(value: Z): _Z {
    return to_candid_opt_n2(value);
}
function to_candid_opt_n2(value: Some<B> | None): [] | [_B] {
    return value._tag === "None" ? candid_none() : candid_some(value.value);
}
function to_candid_opt_n4(value: Some<C> | None): [] | [_C] {
    return value._tag === "None" ? candid_none() : candid_some(value.value);
}

