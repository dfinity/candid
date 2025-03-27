import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type Error = { 'InvalidAmount' : null } |
  { 'TokenNotFound' : null } |
  { 'PortfolioNotFound' : null };
export type List = [] | [[[string, number], List]];
export type List_1 = [] | [[Token, List_1]];
export interface Portfolio { 'id' : bigint, 'name' : string, 'tokens' : List_1 }
export type Result = { 'ok' : null } |
  { 'err' : Error };
export type Result_1 = { 'ok' : List } |
  { 'err' : Error };
export type Result_2 = { 'ok' : number } |
  { 'err' : Error };
export type Time = bigint;
export interface Token {
  'id' : bigint,
  'purchasePrice' : number,
  'purchaseDate' : Time,
  'name' : string,
  'category' : string,
  'amount' : number,
  'symbol' : string,
}
export interface _SERVICE {
  'addToken' : ActorMethod<[string, string, string, number, number], bigint>,
  'addTokenToPortfolio' : ActorMethod<[bigint, bigint], Result>,
  'createPortfolio' : ActorMethod<[string], bigint>,
  'getAllPortfolios' : ActorMethod<[], Array<Portfolio>>,
  'getAllTokens' : ActorMethod<[], Array<Token>>,
  'getPortfolio' : ActorMethod<[bigint], [] | [Portfolio]>,
  'getPortfolioValue' : ActorMethod<[bigint], Result_2>,
  'getPortfolioWeightings' : ActorMethod<[bigint], Result_1>,
  'getToken' : ActorMethod<[bigint], [] | [Token]>,
  'setPortfolioWeightings' : ActorMethod<[Result_1], bigint>,
  'updateTokenAmount' : ActorMethod<[bigint, number], Result>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
