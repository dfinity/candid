export const idlFactory = ({ IDL }) => {
  const Fn = IDL.Func([IDL.Nat], [IDL.Nat], ['query']);
  const R = IDL.Record({ 'x' : IDL.Nat, 'fn' : Fn });
  const RInline = IDL.Record({
    'x' : IDL.Nat,
    'fn' : IDL.Func([IDL.Nat], [IDL.Nat], ['query']),
  });
  return IDL.Service({
    'add_two' : IDL.Func([IDL.Nat], [IDL.Nat], []),
    'fn' : Fn,
    'high_order_fn_inline' : IDL.Func(
        [IDL.Nat, IDL.Func([IDL.Nat], [IDL.Nat], ['query'])],
        [IDL.Nat],
        [],
      ),
    'high_order_fn_via_record' : IDL.Func([R], [IDL.Nat], []),
    'high_order_fn_via_record_inline' : IDL.Func([RInline], [IDL.Nat], []),
    'inline_fn' : IDL.Func([IDL.Nat], [IDL.Nat], []),
  });
};
export const init = ({ IDL }) => { return []; };
