import { encrypted_notes_motoko as _encrypted_notes_motoko } from "./encrypted_notes_motoko";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "./encrypted_notes_motoko/encrypted_notes_motoko.did.d.js";
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
interface encrypted_notes_motoko extends _anon_class_23_1 {
}
import type { GetCiphertextError as _GetCiphertextError, EncryptedNote as _EncryptedNote, EncryptedText as _EncryptedText, PublicKey as _PublicKey } from "./encrypted_notes_motoko/encrypted_notes_motoko.did.d.ts";
class Encrypted_notes_motoko implements encrypted_notes_motoko {
    #actor: ActorSubclass<_SERVICE>;
    constructor(){
        this.#actor = _encrypted_notes_motoko;
    }
    async anon_record_in(arg0: DeviceAlias, arg1: PublicKey | null): Promise<boolean> {
        const result = await this.#actor.anon_record_in(arg0, to_candid_opt_n1(arg1));
        return result;
    }
    async anon_record_out(): Promise<Array<[DeviceAlias, PublicKey]>> {
        const result = await this.#actor.anon_record_out();
        return result;
    }
    async anon_vec_in(arg0: Array<PublicKey>): Promise<void> {
        const result = await this.#actor.anon_vec_in(arg0);
        return result;
    }
    async anon_vec_out(): Promise<Array<PublicKey>> {
        const result = await this.#actor.anon_vec_out();
        return result;
    }
    async anon_vec_record_in(arg0: Array<EncryptedNote>): Promise<void> {
        const result = await this.#actor.anon_vec_record_in(to_candid_vec_n2(arg0));
        return result;
    }
    async anon_vec_record_out(): Promise<Array<EncryptedNote>> {
        const result = await this.#actor.anon_vec_record_out();
        return from_candid_vec_n7(result);
    }
    async nat_in(arg0: bigint): Promise<void> {
        const result = await this.#actor.nat_in(arg0);
        return result;
    }
    async nested_struct_in(arg0: EncryptedNote): Promise<void> {
        const result = await this.#actor.nested_struct_in(to_candid_EncryptedNote_n3(arg0));
        return result;
    }
    async nested_struct_out(): Promise<EncryptedNote> {
        const result = await this.#actor.nested_struct_out();
        return from_candid_EncryptedNote_n8(result);
    }
    async nested_three_in(arg0: Option<Option<bigint | null>>): Promise<void> {
        const result = await this.#actor.nested_three_in(to_candid_opt_n13(arg0));
        return result;
    }
    async nested_three_out(): Promise<Option<Option<bigint | null>>> {
        const result = await this.#actor.nested_three_out();
        return from_candid_opt_n16(result);
    }
    async nested_twice_in(arg0: Option<bigint | null>): Promise<void> {
        const result = await this.#actor.nested_twice_in(to_candid_opt_n14(arg0));
        return result;
    }
    async nested_twice_out(): Promise<Option<bigint | null>> {
        const result = await this.#actor.nested_twice_out();
        return from_candid_opt_n17(result);
    }
    async oneway_fn(arg0: DeviceAlias): Promise<void> {
        const result = await this.#actor.oneway_fn(arg0);
        return result;
    }
    async opt_nested_struct_in(arg0: EncryptedNote | null): Promise<void> {
        const result = await this.#actor.opt_nested_struct_in(to_candid_opt_n19(arg0));
        return result;
    }
    async opt_nested_struct_out(): Promise<EncryptedNote | null> {
        const result = await this.#actor.opt_nested_struct_out();
        return from_candid_opt_n20(result);
    }
    async opt_single_in(arg0: bigint | null): Promise<void> {
        const result = await this.#actor.opt_single_in(to_candid_opt_n15(arg0));
        return result;
    }
    async opt_single_out(): Promise<bigint | null> {
        const result = await this.#actor.opt_single_out();
        return from_candid_opt_n18(result);
    }
    async opt_struct_in(arg0: GetCiphertextError | null): Promise<void> {
        const result = await this.#actor.opt_struct_in(to_candid_opt_n21(arg0));
        return result;
    }
    async opt_struct_out(): Promise<GetCiphertextError | null> {
        const result = await this.#actor.opt_struct_out();
        return from_candid_opt_n22(result);
    }
    async struct_in(arg0: GetCiphertextError): Promise<void> {
        const result = await this.#actor.struct_in(arg0);
        return result;
    }
    async struct_out(): Promise<GetCiphertextError> {
        const result = await this.#actor.struct_out();
        return result;
    }
    async text_in(arg0: string): Promise<void> {
        const result = await this.#actor.text_in(arg0);
        return result;
    }
    async variant_in(arg0: Result): Promise<void> {
        const result = await this.#actor.variant_in(arg0);
        return result;
    }
    async variant_out(): Promise<Result> {
        const result = await this.#actor.variant_out();
        return result;
    }
}
export const encrypted_notes_motoko = new Encrypted_notes_motoko();
function to_candid_vec_n2(value: Array<EncryptedNote>): Array<_EncryptedNote> {
    return value.map((x)=>to_candid_EncryptedNote_n3(x));
}
function from_candid_EncryptedNote_n8(value: _EncryptedNote): EncryptedNote {
    return from_candid_record_n9(value);
}
function to_candid_record_n6(value: {
    sender?: string;
    message: string;
}): {
    sender: [] | [string];
    message: string;
} {
    return {
        sender: value.sender ? candid_some(value.sender) : candid_none(),
        message: value.message
    };
}
function from_candid_opt_n17(value: [] | [[] | [bigint]]): Option<bigint | null> {
    return value.length === 0 ? none() : some(from_candid_opt_n18(value[0]));
}
function to_candid_opt_n14(value: Option<bigint | null>): [] | [[] | [bigint]] {
    return isNone(value) ? candid_none() : candid_some(to_candid_opt_n15(unwrap(value)));
}
function to_candid_opt_n13(value: Option<Option<bigint | null>>): [] | [[] | [[] | [bigint]]] {
    return isNone(value) ? candid_none() : candid_some(to_candid_opt_n14(unwrap(value)));
}
function from_candid_EncryptedText_n10(value: _EncryptedText): EncryptedText {
    return from_candid_record_n11(value);
}
function to_candid_record_n4(value: {
    id: bigint;
    encrypted_text: EncryptedText;
}): {
    id: bigint;
    encrypted_text: _EncryptedText;
} {
    return {
        id: value.id,
        encrypted_text: to_candid_EncryptedText_n5(value.encrypted_text)
    };
}
function from_candid_record_n9(value: {
    id: bigint;
    encrypted_text: _EncryptedText;
}): {
    id: bigint;
    encrypted_text: EncryptedText;
} {
    return {
        id: value.id,
        encrypted_text: from_candid_EncryptedText_n10(value.encrypted_text)
    };
}
function from_candid_opt_n16(value: [] | [[] | [[] | [bigint]]]): Option<Option<bigint | null>> {
    return value.length === 0 ? none() : some(from_candid_opt_n17(value[0]));
}
function from_candid_opt_n18(value: [] | [bigint]): bigint | null {
    return value.length === 0 ? null : value[0];
}
function to_candid_opt_n19(value: EncryptedNote | null): [] | [_EncryptedNote] {
    return value === null ? candid_none() : candid_some(to_candid_EncryptedNote_n3(value));
}
function to_candid_opt_n21(value: GetCiphertextError | null): [] | [_GetCiphertextError] {
    return value === null ? candid_none() : candid_some(value);
}
function to_candid_opt_n1(value: PublicKey | null): [] | [_PublicKey] {
    return value === null ? candid_none() : candid_some(value);
}
function from_candid_record_n11(value: {
    sender: [] | [string];
    message: string;
}): {
    sender?: string;
    message: string;
} {
    return {
        sender: record_opt_to_undefined(from_candid_opt_n12(value.sender)),
        message: value.message
    };
}
function to_candid_opt_n15(value: bigint | null): [] | [bigint] {
    return value === null ? candid_none() : candid_some(value);
}
function from_candid_opt_n22(value: [] | [_GetCiphertextError]): GetCiphertextError | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n20(value: [] | [_EncryptedNote]): EncryptedNote | null {
    return value.length === 0 ? null : from_candid_EncryptedNote_n8(value[0]);
}
function from_candid_vec_n7(value: Array<_EncryptedNote>): Array<EncryptedNote> {
    return value.map((x)=>from_candid_EncryptedNote_n8(x));
}
function to_candid_EncryptedText_n5(value: EncryptedText): _EncryptedText {
    return to_candid_record_n6(value);
}
function from_candid_opt_n12(value: [] | [string]): string | null {
    return value.length === 0 ? null : value[0];
}
function to_candid_EncryptedNote_n3(value: EncryptedNote): _EncryptedNote {
    return to_candid_record_n4(value);
}

