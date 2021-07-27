import type { Principal } from '@dfinity/principal';
export type Func = () => Promise<Principal>;
export interface Service { 'f' : Func }
export type Service2 = Service;
export interface _SERVICE {
  'asArray' : () => Promise<[Array<Principal>, Array<[Principal, string]>]>,
  'asPrincipal' : () => Promise<[Principal, [Principal, string]]>,
  'asRecord' : () => Promise<
      [Principal, [] | [Principal], [Principal, string]]
    >,
  'asVariant' : () => Promise<
      { 'a' : Principal } |
        { 'b' : { 'f' : [] | [[Principal, string]] } }
    >,
}
