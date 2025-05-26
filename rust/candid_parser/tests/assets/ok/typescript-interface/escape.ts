import { escape as _escape, createActor as _createActor, canisterId as _canisterId } from "declarations/escape";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/escape/escape.did.d.js";
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
export interface t {
    '\"': bigint;
    '\'': bigint;
    '\"\'': bigint;
    '\\\n\'\"': bigint;
}
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): escapeInterface {
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
    return new Escape(actor);
}
export const canisterId = _canisterId;
export interface escapeInterface {
    '\n\'\"\'\'\"\"\r\t'(arg0: t): Promise<void>;
}
class Escape implements escapeInterface {
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
    async '\n\'\"\'\'\"\"\r\t'(arg0: t): Promise<void> {
        try {
            const result = await this.#actor["\n'\"''\"\"\r	"](arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
}
export const escape: escapeInterface = new Escape();

