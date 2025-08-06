import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
export type Fn = (arg0: bigint) => Promise<bigint>;
export interface R {
    x: bigint;
    fn: [Principal, string];
    gn: [Principal, string];
    nested: {
        fn: [Principal, string];
    };
}
export interface RInline {
    x: bigint;
    fn: [Principal, string];
}
export type Gn = Fn;
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => inline_methodsInterface;
export declare const canisterId: string;
export interface inline_methodsInterface {
    add_two(arg0: bigint): Promise<bigint>;
    fn: Fn;
    high_order_fn(arg0: bigint, arg1: [Principal, string]): Promise<bigint>;
    high_order_fn_inline(arg0: bigint, arg1: [Principal, string]): Promise<bigint>;
    high_order_fn_via_id(arg0: bigint, arg1: [Principal, string]): Promise<[Principal, string]>;
    high_order_fn_via_record(arg0: R): Promise<bigint>;
    high_order_fn_via_record_inline(arg0: RInline): Promise<bigint>;
}

