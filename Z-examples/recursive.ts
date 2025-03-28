import { recursive as _recursive } from "declarations/recursive";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "./recursive.did.d.js";
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
type Error_ = {
    InvalidAmount: null;
} | {
    TokenNotFound: null;
} | {
    PortfolioNotFound: null;
};
type List = [[string, number], List] | null;
type List_1 = [Token, List_1] | null;
interface Portfolio {
    id: bigint;
    name: string;
    tokens: List_1;
}
type Result = {
    ok: null;
} | {
    err: Error_;
};
type Result_1 = {
    ok: List;
} | {
    err: Error_;
};
type Result_2 = {
    ok: number;
} | {
    err: Error_;
};
type Time = bigint;
interface Token {
    id: bigint;
    purchasePrice: number;
    purchaseDate: Time;
    name: string;
    category: string;
    amount: number;
    symbol: string;
}
interface recursive {
    addToken(arg0: string, arg1: string, arg2: string, arg3: number, arg4: number): Promise<bigint>;
    addTokenToPortfolio(arg0: bigint, arg1: bigint): Promise<Result>;
    createPortfolio(arg0: string): Promise<bigint>;
    getAllPortfolios(): Promise<Array<Portfolio>>;
    getAllTokens(): Promise<Array<Token>>;
    getPortfolio(arg0: bigint): Promise<Portfolio | null>;
    getPortfolioValue(arg0: bigint): Promise<Result_2>;
    getPortfolioWeightings(arg0: bigint): Promise<Result_1>;
    getToken(arg0: bigint): Promise<Token | null>;
    setPortfolioWeightings(arg0: Result_1): Promise<bigint>;
    updateTokenAmount(arg0: bigint, arg1: number): Promise<Result>;
}
import type { Token as _Token, List as _List, Portfolio as _Portfolio, Result_1 as _Result_1, List_1 as _List_1, Error as _Error } from "./recursive.did.d.ts";
class Recursive implements recursive {
    #actor: ActorSubclass<_SERVICE>;
    constructor(){
        this.#actor = _recursive;
    }
    async addToken(arg0: string, arg1: string, arg2: string, arg3: number, arg4: number): Promise<bigint> {
        const result = await this.#actor.addToken(arg0, arg1, arg2, arg3, arg4);
        return result;
    }
    async addTokenToPortfolio(arg0: bigint, arg1: bigint): Promise<Result> {
        const result = await this.#actor.addTokenToPortfolio(arg0, arg1);
        return result;
    }
    async createPortfolio(arg0: string): Promise<bigint> {
        const result = await this.#actor.createPortfolio(arg0);
        return result;
    }
    async getAllPortfolios(): Promise<Array<Portfolio>> {
        const result = await this.#actor.getAllPortfolios();
        return from_candid_vec_n1(result);
    }
    async getAllTokens(): Promise<Array<Token>> {
        const result = await this.#actor.getAllTokens();
        return result;
    }
    async getPortfolio(arg0: bigint): Promise<Portfolio | null> {
        const result = await this.#actor.getPortfolio(arg0);
        return from_candid_opt_n7(result);
    }
    async getPortfolioValue(arg0: bigint): Promise<Result_2> {
        const result = await this.#actor.getPortfolioValue(arg0);
        return result;
    }
    async getPortfolioWeightings(arg0: bigint): Promise<Result_1> {
        const result = await this.#actor.getPortfolioWeightings(arg0);
        return from_candid_Result_1_n8(result);
    }
    async getToken(arg0: bigint): Promise<Token | null> {
        const result = await this.#actor.getToken(arg0);
        return from_candid_opt_n13(result);
    }
    async setPortfolioWeightings(arg0: Result_1): Promise<bigint> {
        const result = await this.#actor.setPortfolioWeightings(to_candid_Result_1_n14(arg0));
        return result;
    }
    async updateTokenAmount(arg0: bigint, arg1: number): Promise<Result> {
        const result = await this.#actor.updateTokenAmount(arg0, arg1);
        return result;
    }
}
export const recursive = new Recursive();
function from_candid_vec_n1(value: Array<_Portfolio>): Array<Portfolio> {
    return value.map((x)=>from_candid_Portfolio_n2(x));
}
function from_candid_tuple_n12(value: [[string, number], _List]): [[string, number], List] {
    return [
        value[0],
        from_candid_List_n10(value[1])
    ];
}
function from_candid_Portfolio_n2(value: _Portfolio): Portfolio {
    return from_candid_record_n3(value);
}
function from_candid_opt_n13(value: [] | [_Token]): Token | null {
    return value.length === 0 ? null : value[0];
}
function to_candid_List_n16(value: List): _List {
    return to_candid_opt_n17(value);
}
function to_candid_variant_n15(value: {
    ok: List;
} | {
    err: Error_;
}): {
    ok: _List;
} | {
    err: _Error;
} {
    return "ok" in value ? {
        ok: to_candid_List_n16(value.ok)
    } : "err" in value ? {
        err: value.err
    } : value;
}
function from_candid_List_n10(value: _List): List {
    return from_candid_opt_n11(value);
}
function from_candid_tuple_n6(value: [_Token, _List_1]): [Token, List_1] {
    return [
        value[0],
        from_candid_List_1_n4(value[1])
    ];
}
function to_candid_Result_1_n14(value: Result_1): _Result_1 {
    return to_candid_variant_n15(value);
}
function from_candid_opt_n7(value: [] | [_Portfolio]): Portfolio | null {
    return value.length === 0 ? null : from_candid_Portfolio_n2(value[0]);
}
function from_candid_Result_1_n8(value: _Result_1): Result_1 {
    return from_candid_variant_n9(value);
}
function from_candid_record_n3(value: {
    id: bigint;
    name: string;
    tokens: _List_1;
}): {
    id: bigint;
    name: string;
    tokens: List_1;
} {
    return {
        id: value.id,
        name: value.name,
        tokens: from_candid_List_1_n4(value.tokens)
    };
}
function from_candid_opt_n11(value: [] | [[[string, number], _List]]): [[string, number], List] | null {
    return value.length === 0 ? null : from_candid_tuple_n12(value[0]);
}
function from_candid_variant_n9(value: {
    ok: _List;
} | {
    err: _Error;
}): {
    ok: List;
} | {
    err: Error_;
} {
    return "ok" in value ? {
        ok: from_candid_List_n10(value.ok)
    } : "err" in value ? {
        err: value.err
    } : value;
}
function to_candid_opt_n17(value: [[string, number], List] | null): [] | [[[string, number], _List]] {
    return value === null ? candid_none() : candid_some(to_candid_tuple_n18(value));
}
function from_candid_List_1_n4(value: _List_1): List_1 {
    return from_candid_opt_n5(value);
}
function from_candid_opt_n5(value: [] | [[_Token, _List_1]]): [Token, List_1] | null {
    return value.length === 0 ? null : from_candid_tuple_n6(value[0]);
}
function to_candid_tuple_n18(value: [[string, number], List]): [[string, number], _List] {
    return [
        value[0],
        to_candid_List_n16(value[1])
    ];
}

