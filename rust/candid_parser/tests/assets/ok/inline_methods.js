export const idlFactory = ({ IDL }) => {
  const Fn = IDL.Func([IDL.Nat], [IDL.Nat], ['query']);
  const Gn = Fn;
  const R = IDL.Record({
    'x' : IDL.Nat,
    'fn' : Fn,
    'gn' : Gn,
    'nested' : IDL.Record({ 'fn' : Gn }),
  });
  const RInline = IDL.Record({
    'x' : IDL.Nat,
    'fn' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
  });
  return IDL.Service({
    'add_two' : IDL.Func([IDL.Nat], [IDL.Nat], []),
    'fn' : Fn,
    'high_order_fn' : IDL.Func([IDL.Nat, Fn], [IDL.Nat], []),
    'high_order_fn_inline' : IDL.Func(
        [IDL.Nat, IDL.Func([IDL.Nat], [IDL.Nat], ['query'])],
        [IDL.Nat],
        [],
      ),
    'high_order_fn_via_id' : IDL.Func([IDL.Nat, Gn], [Fn], []),
    'high_order_fn_via_record' : IDL.Func([R], [IDL.Nat], []),
    'high_order_fn_via_record_inline' : IDL.Func([RInline], [IDL.Nat], []),
  });
};
export const init = ({ IDL }) => { return []; };
