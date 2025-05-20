import { IDL } from '@dfinity/candid';

export const A = IDL.Record({
  '\u{e000}': IDL.Nat,
  '📦🍦': IDL.Nat,
  '字段名': IDL.Nat,
  '字 段 名2': IDL.Nat,
});
export const B = IDL.Variant({
  '': IDL.Null,
  '空的': IDL.Null,
  '  空的  ': IDL.Null,
  '1⃣️2⃣️3⃣️': IDL.Null,
});

export const _ServiceTypes = {
  '': IDL.Func([IDL.Nat], [IDL.Nat], []),
  '✈️  🚗 ⛱️ ': IDL.Func([], [], ['oneway']),
  '函数名': IDL.Func([A], [B], []),
  '👀': IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    '': _ServiceTypes[''],
    '✈️  🚗 ⛱️ ': _ServiceTypes['✈️  🚗 ⛱️ '],
    '函数名': _ServiceTypes['函数名'],
    '👀': _ServiceTypes['👀'],
  });
};

export const init = ({ IDL }) => { return []; };
