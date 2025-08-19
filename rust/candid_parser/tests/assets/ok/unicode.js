import { IDL } from '@dfinity/candid';

export const B = IDL.Variant({
  '' : IDL.Null,
  '空的' : IDL.Null,
  '  空的  ' : IDL.Null,
  '1⃣️2⃣️3⃣️' : IDL.Null,
});
export const A = IDL.Record({
  '\u{e000}' : IDL.Nat,
  '📦🍦' : IDL.Nat,
  '字段名' : IDL.Nat,
  '字 段 名2' : IDL.Nat,
});

export const idlService = IDL.Service({
  '' : IDL.Func([IDL.Nat], [IDL.Nat], []),
  '✈️  🚗 ⛱️ ' : IDL.Func([], [], ['oneway']),
  '函' : IDL.Func([B], [A], []),
  '函数名' : IDL.Func([A], [B], []),
  '👀' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
});

export const idlInitArgs = [];

export const idlFactory = ({ IDL }) => {
  const B = IDL.Variant({
    '' : IDL.Null,
    '空的' : IDL.Null,
    '  空的  ' : IDL.Null,
    '1⃣️2⃣️3⃣️' : IDL.Null,
  });
  const A = IDL.Record({
    '\u{e000}' : IDL.Nat,
    '📦🍦' : IDL.Nat,
    '字段名' : IDL.Nat,
    '字 段 名2' : IDL.Nat,
  });
  
  return IDL.Service({
    '' : IDL.Func([IDL.Nat], [IDL.Nat], []),
    '✈️  🚗 ⛱️ ' : IDL.Func([], [], ['oneway']),
    '函' : IDL.Func([B], [A], []),
    '函数名' : IDL.Func([A], [B], []),
    '👀' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
  });
};

export const init = ({ IDL }) => { return []; };
