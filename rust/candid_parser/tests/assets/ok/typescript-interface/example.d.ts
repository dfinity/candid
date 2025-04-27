import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type A = B;
export type B = Some<A> | None;
export type List = {
    head: bigint;
    tail: List;
} | null;
export type a = {
    a: null;
} | {
    b: b;
};
export type b = [bigint, bigint];
export interface brokerInterface {
    find(arg0: string): Promise<Principal>;
}
export type f = (arg0: List, arg1: [Principal, string]) => [List | null, res];
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
    _41_: {
        _42_: null;
    } | {
        A: null;
    } | {
        B: null;
    } | {
        C: null;
    };
    _42_: bigint;
}
export type nested_res = {
    Ok: {
        Ok: null;
    } | {
        Err: null;
    };
} | {
    Err: {
        Ok: {
            content: string;
        };
    } | {
        Err: [bigint];
    };
};
export interface node {
    head: bigint;
    tail: list;
}
export type res = {
    Ok: [bigint, bigint];
} | {
    Err: {
        error: string;
    };
};
export interface sInterface {
    f: [Principal, string];
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (arg0: Principal) => void;
export type tree = {
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    leaf: bigint;
};
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => example;
export declare const canisterId: string;
export interface exampleInterface {
    bbbbb(arg0: b): Promise<void>;
    f: [Principal, string];
    f1(arg0: list, arg1: Uint8Array | number[], arg2: boolean | null): Promise<void>;
    g(arg0: list): Promise<[B, tree, stream]>;
    g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]>;
    h(arg0: Array<string | null>, arg1: {
        A: bigint;
    } | {
        B?: string;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }>;
    i: [Principal, string];
    x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            Ok: {
                result: string;
            };
        } | {
            Err: {
                a: null;
            } | {
                b: null;
            };
        }]>;
}

