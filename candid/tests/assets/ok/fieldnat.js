export default ({ IDL }) => {
  return IDL.Service({
    'bab' : IDL.Func([IDL.Int, IDL.Nat], [], []),
    'bar' : IDL.Func([IDL.Record({ '2' : IDL.Int })], [], []),
    'bas' : IDL.Func(
      [IDL.Tuple(IDL.Int, IDL.Int)],
      [IDL.Tuple(IDL.Text, IDL.Nat)],
      []
    ),
    'baz' : IDL.Func(
      [IDL.Record({ _2_ : IDL.Int, '2' : IDL.Nat })],
      [IDL.Record({})],
      []
    ),
    'bib' : IDL.Func(
      [IDL.Tuple(IDL.Int)],
      [IDL.Variant({ _0_ : IDL.Int })],
      []
    ),
    'foo' : IDL.Func([IDL.Record({ _2_ : IDL.Int })], [], [])
  });
}
