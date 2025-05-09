import { class as _class, createActor as _createActor, canisterId as _canisterId } from "declarations/class";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/class/class.did.d.js";
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
function extractAgentErrorMessage(error: string): string {
    const errorString = String(error);
    const match = errorString.match(/with message: '([^']+)'/);
    return match ? match[1] : errorString;
}
export type List = [bigint, List] | null;
export interface Profile {
    age: number;
    name: string;
}
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): classInterface {
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
    return new Class(actor);
}
export const canisterId = _canisterId;
export interface classInterface {
    get(): Promise<List>;
    set(arg0: List): Promise<List>;
}
import type { List as _List } from "declarations/class/class.did.d.ts";
class Class implements classInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        if (!actor) {
            this.#actor = _createActor(canisterId, {
                agentOptions: {
                    host: process.env.BACKEND_HOST
                }
            });
        } else {
            this.#actor = actor;
        }
    }
    async get(): Promise<List> {
        try {
            const result = await this.#actor.get();
            return from_candid_List_n1(result);
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async set(arg0: List): Promise<List> {
        try {
            const result = await this.#actor.set(to_candid_List_n4(arg0));
            return from_candid_List_n1(result);
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
}
export const class_: classInterface = new Class();
function from_candid_List_n1(value: _List): List {
    return from_candid_opt_n2(value);
}
function from_candid_opt_n2(value: [] | [[bigint, _List]]): [bigint, List] | null {
    return value.length === 0 ? null : from_candid_tuple_n3(value[0]);
}
function from_candid_tuple_n3(value: [bigint, _List]): [bigint, List] {
    return [
        value[0],
        from_candid_List_n1(value[1])
    ];
}
function to_candid_List_n4(value: List): _List {
    return to_candid_opt_n5(value);
}
function to_candid_opt_n5(value: [bigint, List] | null): [] | [[bigint, _List]] {
    return value === null ? candid_none() : candid_some(to_candid_tuple_n6(value));
}
function to_candid_tuple_n6(value: [bigint, List]): [bigint, _List] {
    return [
        value[0],
        to_candid_List_n4(value[1])
    ];
}

