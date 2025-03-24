import type { Principal } from "@dfinity/principal";
type Some<T> = {
    _tag: "Some";
    value: T;
};
type None = {
    _tag: "None";
};
type Option<T> = Some<T> | None;
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

