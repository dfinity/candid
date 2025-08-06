import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export type A = B;
export type B = Some<A> | None;
export type List = {
    head: bigint;
    tail: List;
} | null;
export type a = {
    __kind__: "a";
    a: null;
} | {
    __kind__: "b";
    b: b;
};
export type b = [bigint, bigint];
export interface brokerInterface {
    find(name: string): Promise<Principal>;
}
export type f = (arg0: List, arg1: [Principal, string]) => Promise<[List | null, res]>;
export type list = node | null;
export type my_type = Principal;
export interface nested {
    _0_: bigint;
    _1_: bigint;
    _2_: [bigint, bigint];
    _3_: {
        _0_: bigint;
        _42_: bigint;
        _43_: number;
    };
    _40_: bigint;
    _41_: Variant__42__A_B_C;
    _42_: bigint;
}
export type nested_res = {
    __kind__: "Ok";
    Ok: Variant_Ok_Err;
} | {
    __kind__: "Err";
    Err: {
        __kind__: "Ok";
        Ok: {
            content: string;
        };
    } | {
        __kind__: "Err";
        Err: [bigint];
    };
};
export interface node {
    head: bigint;
    tail: list;
}
export type res = {
    __kind__: "Ok";
    Ok: [bigint, bigint];
} | {
    __kind__: "Err";
    Err: {
        error: string;
    };
};
export interface sInterface {
    f: t;
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (server: Principal) => Promise<void>;
export type tree = {
    __kind__: "branch";
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    __kind__: "leaf";
    leaf: bigint;
};
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => exampleInterface;
export declare const canisterId: string;
export enum Variant_Ok_Err {
    Ok = "Ok",
    Err = "Err"
}
export enum Variant__42__A_B_C {
    _42_ = "_42_",
    A = "A",
    B = "B",
    C = "C"
}
export enum Variant_a_b {
    a = "a",
    b = "b"
}
export interface exampleInterface {
    bbbbb(arg0: b): Promise<void>;
    f: t;
    f1(arg0: list, test: Uint8Array | number[], arg2: boolean | null): Promise<void>;
    g(arg0: list): Promise<[B, tree, stream]>;
    g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]>;
    h(arg0: Array<string | null>, arg1: {
        __kind__: "A";
        A: bigint;
    } | {
        __kind__: "B";
        B: string | null;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }>;
    i: f;
    x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            __kind__: "Ok";
            Ok: {
                result: string;
            };
        } | {
            __kind__: "Err";
            Err: Variant_a_b;
        }]>;
}

