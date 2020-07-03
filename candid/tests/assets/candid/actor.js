({ IDL }) => {
  const f = IDL.Func([IDL.Int8], [IDL.Int8], []);
  const g = f;
  const h = IDL.Func([f], [f], []);
  const o = IDL.Opt(o);
  return IDL.Service({
    'f' : IDL.Func([IDL.Nat], [h], []),
    'g' : f,
    'h' : g,
    'o' : IDL.Func([o], [o], [])
  });
}