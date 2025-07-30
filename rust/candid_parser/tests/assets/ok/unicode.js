import { IDL } from '@dfinity/candid';

export const A = IDL.Record({
  '\u{e000}' : IDL.Nat,
  '📦🍦' : IDL.Nat,
  '字段名' : IDL.Nat,
  '字 段 名2' : IDL.Nat,
});
export const B = IDL.Variant({
  '' : IDL.Null,
  '空的' : IDL.Null,
  '  空的  ' : IDL.Null,
  '1⃣️2⃣️3⃣️' : IDL.Null,
});

export const idlService = IDL.Service({
  '' : IDL.Func([IDL.Nat], [IDL.Nat], []),
  '✈️  🚗 ⛱️ ' : IDL.Func([], [], ['oneway']),
  '函数名' : IDL.Func([A], [B], []),
  '👀' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
});

export const idlInitArgs = [];

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const A = IDL.Record({
    '\u{e000}' : IDL.Nat,
    '📦🍦' : IDL.Nat,
    '字段名' : IDL.Nat,
    '字 段 名2' : IDL.Nat,
  });
  const B = IDL.Variant({
    '' : IDL.Null,
    '空的' : IDL.Null,
    '  空的  ' : IDL.Null,
    '1⃣️2⃣️3⃣️' : IDL.Null,
  });
  return IDL.Service({
    '' : IDL.Func([IDL.Nat], [IDL.Nat], []),
    '✈️  🚗 ⛱️ ' : IDL.Func([], [], ['oneway']),
    '函数名' : IDL.Func([A], [B], []),
    '👀' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
  });
};

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
