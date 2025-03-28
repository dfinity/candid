import type { Principal } from "@dfinity/principal";
type Some<T> = {
    _tag: "Some";
    value: T;
};
type None = {
    _tag: "None";
};
type Option<T> = Some<T> | None;
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

