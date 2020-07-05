({ IDL }) => {
  return IDL.Service({
    'foo' : IDL.Func([IDL.Record({ _2_ : IDL.Int })], [], []),
    'bar' : IDL.Func([IDL.Record({ '2' : IDL.Int })], [], []),
    'baz' : IDL.Func(
      [IDL.Record({ _2_ : IDL.Int, '2' : IDL.Nat })],
      [IDL.Record({})],
      []
    ),
    'bab' : IDL.Func([IDL.Int, IDL.Nat], [], []),
    'bas' : IDL.Func(
      [IDL.Tuple(IDL.Int, IDL.Int)],
      [IDL.Tuple(IDL.Text, IDL.Nat)],
      []
    ),
    'bib' : IDL.Func([IDL.Tuple(IDL.Int)], [IDL.Variant({ _0_ : IDL.Int })], [])
  });
}
