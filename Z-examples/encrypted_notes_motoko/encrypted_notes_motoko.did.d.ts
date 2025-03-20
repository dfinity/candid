import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type Ciphertext = string;
export type ComplexVariant = { 'a' : bigint } |
  { 'b' : boolean };
export type DeviceAlias = string;
export interface EncryptedNote {
  'id' : bigint,
  'encrypted_text' : EncryptedText,
}
export interface EncryptedText { 'sender' : [] | [string], 'message' : string }
export type GetCiphertextError = { 'notSynced' : null } |
  { 'notFound' : null };
export type PublicKey = string;
export type Result = { 'ok' : Ciphertext } |
  { 'err' : GetCiphertextError };
export interface _anon_class_23_1 {
  'anon_record_in' : ActorMethod<[DeviceAlias, [] | [PublicKey]], boolean>,
  'anon_record_out' : ActorMethod<[], Array<[DeviceAlias, PublicKey]>>,
  'anon_vec_in' : ActorMethod<[Array<PublicKey>], undefined>,
  'anon_vec_out' : ActorMethod<[], Array<PublicKey>>,
  'anon_vec_record_in' : ActorMethod<[Array<EncryptedNote>], undefined>,
  'anon_vec_record_out' : ActorMethod<[], Array<EncryptedNote>>,
  'nat_in' : ActorMethod<[bigint], undefined>,
  'nested_struct_in' : ActorMethod<[EncryptedNote], undefined>,
  'nested_struct_out' : ActorMethod<[], EncryptedNote>,
  'nested_three_in' : ActorMethod<[[] | [[] | [[] | [bigint]]]], undefined>,
  'nested_three_out' : ActorMethod<[], [] | [[] | [[] | [bigint]]]>,
  'nested_twice_in' : ActorMethod<[[] | [[] | [bigint]]], undefined>,
  'nested_twice_out' : ActorMethod<[], [] | [[] | [bigint]]>,
  'oneway_fn' : ActorMethod<[DeviceAlias], undefined>,
  'opt_nested_struct_in' : ActorMethod<[[] | [EncryptedNote]], undefined>,
  'opt_nested_struct_out' : ActorMethod<[], [] | [EncryptedNote]>,
  'opt_single_in' : ActorMethod<[[] | [bigint]], undefined>,
  'opt_single_out' : ActorMethod<[], [] | [bigint]>,
  'opt_struct_in' : ActorMethod<[[] | [GetCiphertextError]], undefined>,
  'opt_struct_out' : ActorMethod<[], [] | [GetCiphertextError]>,
  'struct_in' : ActorMethod<[GetCiphertextError], undefined>,
  'struct_out' : ActorMethod<[], GetCiphertextError>,
  'text_in' : ActorMethod<[string], undefined>,
  'variant_in' : ActorMethod<[Result], undefined>,
  'variant_out' : ActorMethod<[], Result>,
}
export interface _SERVICE extends _anon_class_23_1 {}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
