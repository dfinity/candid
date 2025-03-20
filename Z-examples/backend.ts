import { encrypted_notes_motoko as _encrypted_notes_motoko } from "./encrypted_notes_motoko";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "./encrypted_notes_motoko/encrypted_notes_motoko.did";
import type { Principal } from "@dfinity/principal";
type Some<T> = {
    _tag: "Some";
    value: T;
};
type None = {
    _tag: "None";
};
type Option<T> = Some<T> | None;
function some<T>(value): Some<T> {
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
function unwrap<T>(option): T {
    if (isNone(option)) {
        throw new Error("unwrap: none");
    }
    return option.value;
}
function candid_some<T>(value): [T] {
    return [
        value
    ];
}
function candid_none<T>(): [] {
    return [];
}
function record_opt_to_undefined<T>(arg): T | undefined {
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
class encrypted_notes_motoko implements encrypted_notes_motoko {
    #actor: ActorSubclass<_SERVICE>;
    constructor(){
        this.#actor = _encrypted_notes_motoko;
    }
    async anon_record_in(arg0: DeviceAlias, arg1: PublicKey | null): Promise<boolean> {
        const result = await this.#actor.anon_record_in(arg0, arg1 === null ? candid_none() : candid_some(arg1));
        return result;
    }
    async anon_record_out(): Promise<Array<[DeviceAlias, PublicKey]>> {
        const result = await this.#actor.anon_record_out();
        return result.map((x)=>{
            return [
                x[0],
                x[1]
            ];
        });
    }
    async anon_vec_in(arg0: Array<PublicKey>): Promise<void> {
        const result = await this.#actor.anon_vec_in(arg0.map((x)=>{
            return x;
        }));
        return result;
    }
    async anon_vec_out(): Promise<Array<PublicKey>> {
        const result = await this.#actor.anon_vec_out();
        return result.map((x)=>{
            return x;
        });
    }
    async anon_vec_record_in(arg0: Array<EncryptedNote>): Promise<void> {
        const result = await this.#actor.anon_vec_record_in(arg0.map((x)=>{
            return {
                id: x.id,
                encrypted_text: {
                    sender: x.encrypted_text.sender === null ? candid_none() : candid_some(x.encrypted_text.sender),
                    message: x.encrypted_text.message
                }
            };
        }));
        return result;
    }
    async anon_vec_record_out(): Promise<Array<EncryptedNote>> {
        const result = await this.#actor.anon_vec_record_out();
        return result.map((x)=>{
            return {
                id: x.id,
                encrypted_text: {
                    sender: record_opt_to_undefined(x.encrypted_text.sender.length === 0 ? null : x.encrypted_text.sender[0]),
                    message: x.encrypted_text.message
                }
            };
        });
    }
    async nat_in(arg0: bigint): Promise<void> {
        const result = await this.#actor.nat_in(arg0);
        return result;
    }
    async nested_struct_in(arg0: EncryptedNote): Promise<void> {
        const result = await this.#actor.nested_struct_in({
            id: arg0.id,
            encrypted_text: {
                sender: arg0.encrypted_text.sender === null ? candid_none() : candid_some(arg0.encrypted_text.sender),
                message: arg0.encrypted_text.message
            }
        });
        return result;
    }
    async nested_struct_out(): Promise<EncryptedNote> {
        const result = await this.#actor.nested_struct_out();
        return {
            id: result.id,
            encrypted_text: {
                sender: record_opt_to_undefined(result.encrypted_text.sender.length === 0 ? null : result.encrypted_text.sender[0]),
                message: result.encrypted_text.message
            }
        };
    }
    async nested_three_in(arg0: Option<Option<bigint | null>>): Promise<void> {
        const result = await this.#actor.nested_three_in(isNone(arg0) ? candid_none() : candid_some(unwrap(arg0) === null ? candid_none() : candid_some(unwrap(arg0))));
        return result;
    }
    async nested_three_out(): Promise<Option<Option<bigint | null>>> {
        const result = await this.#actor.nested_three_out();
        return result.length === 0 ? none() : some(result[0].length === 0 ? none() : some(result[0][0].length === 0 ? null : result[0][0][0]));
    }
    async nested_twice_in(arg0: Option<bigint | null>): Promise<void> {
        const result = await this.#actor.nested_twice_in(isNone(arg0) ? candid_none() : candid_some(unwrap(arg0) === null ? candid_none() : candid_some(unwrap(arg0))));
        return result;
    }
    async nested_twice_out(): Promise<Option<bigint | null>> {
        const result = await this.#actor.nested_twice_out();
        return result.length === 0 ? none() : some(result[0].length === 0 ? null : result[0][0]);
    }
    async oneway_fn(arg0: DeviceAlias): Promise<void> {
        const result = await this.#actor.oneway_fn(arg0);
        return result;
    }
    async opt_nested_struct_in(arg0: EncryptedNote | null): Promise<void> {
        const result = await this.#actor.opt_nested_struct_in(arg0 === null ? candid_none() : candid_some(arg0));
        return result;
    }
    async opt_nested_struct_out(): Promise<EncryptedNote | null> {
        const result = await this.#actor.opt_nested_struct_out();
        return result.length === 0 ? null : {
            id: result[0].id,
            encrypted_text: {
                sender: record_opt_to_undefined(result[0].encrypted_text.sender.length === 0 ? null : result[0].encrypted_text.sender[0]),
                message: result[0].encrypted_text.message
            }
        };
    }
    async opt_single_in(arg0: bigint | null): Promise<void> {
        const result = await this.#actor.opt_single_in(arg0 === null ? candid_none() : candid_some(arg0));
        return result;
    }
    async opt_single_out(): Promise<bigint | null> {
        const result = await this.#actor.opt_single_out();
        return result.length === 0 ? null : result[0];
    }
    async opt_struct_in(arg0: GetCiphertextError | null): Promise<void> {
        const result = await this.#actor.opt_struct_in(arg0 === null ? candid_none() : candid_some(arg0));
        return result;
    }
    async opt_struct_out(): Promise<GetCiphertextError | null> {
        const result = await this.#actor.opt_struct_out();
        return result.length === 0 ? null : result[0];
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

