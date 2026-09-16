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
    '1⃣\u{fe0f}2⃣\u{fe0f}3⃣\u{fe0f}' : IDL.Null,
  });
  return IDL.Service({
    '' : IDL.Func([IDL.Nat], [IDL.Nat], []),
    '✈\u{fe0f}  🚗 ⛱\u{fe0f} ' : IDL.Func([], [], ['oneway']),
    '函数名' : IDL.Func([A], [B], []),
    '👀' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
  });
};
export const init = ({ IDL }) => { return []; };
