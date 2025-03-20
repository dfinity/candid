import type { Principal } from "@dfinity/principal";
type Some<T> = {
    _tag: "Some";
    value: T;
};
type None = {
    _tag: "None";
};
type Option<T> = Some<T> | None;
type Ciphertext = string;
type ComplexVariant = {
    a: bigint;
} | {
    b: boolean;
};
type DeviceAlias = string;
interface EncryptedNote {
    id: bigint;
    encrypted_text: EncryptedText;
}
interface EncryptedText {
    sender?: string;
    message: string;
}
type GetCiphertextError = {
    notSynced: null;
} | {
    notFound: null;
};
type PublicKey = string;
type Result = {
    ok: Ciphertext;
} | {
    err: GetCiphertextError;
};
interface _anon_class_23_1 {
    anon_record_in(arg0: DeviceAlias, arg1: PublicKey | null): Promise<boolean>;
    anon_record_out(): Promise<Array<[DeviceAlias, PublicKey]>>;
    anon_vec_in(arg0: Array<PublicKey>): Promise<void>;
    anon_vec_out(): Promise<Array<PublicKey>>;
    anon_vec_record_in(arg0: Array<EncryptedNote>): Promise<void>;
    anon_vec_record_out(): Promise<Array<EncryptedNote>>;
    nat_in(arg0: bigint): Promise<void>;
    nested_struct_in(arg0: EncryptedNote): Promise<void>;
    nested_struct_out(): Promise<EncryptedNote>;
    nested_three_in(arg0: Option<Option<bigint | null>>): Promise<void>;
    nested_three_out(): Promise<Option<Option<bigint | null>>>;
    nested_twice_in(arg0: Option<bigint | null>): Promise<void>;
    nested_twice_out(): Promise<Option<bigint | null>>;
    oneway_fn(arg0: DeviceAlias): Promise<void>;
    opt_nested_struct_in(arg0: EncryptedNote | null): Promise<void>;
    opt_nested_struct_out(): Promise<EncryptedNote | null>;
    opt_single_in(arg0: bigint | null): Promise<void>;
    opt_single_out(): Promise<bigint | null>;
    opt_struct_in(arg0: GetCiphertextError | null): Promise<void>;
    opt_struct_out(): Promise<GetCiphertextError | null>;
    struct_in(arg0: GetCiphertextError): Promise<void>;
    struct_out(): Promise<GetCiphertextError>;
    text_in(arg0: string): Promise<void>;
    variant_in(arg0: Result): Promise<void>;
    variant_out(): Promise<Result>;
}
declare interface encrypted_notes_motoko extends _anon_class_23_1 {
}

