export default function({ IDL }) {

  return IDL.Service({
    'fn1': IDL.Func([IDL.Nat32], [], []),
    'fn2': IDL.Func([], [IDL.Nat8], ['query']),
    'fn3': IDL.Func([IDL.Nat], [IDL.Int], ['query']),
    'fn4': IDL.Func([IDL.Bool], [IDL.Empty], ['query']),
  });
}
