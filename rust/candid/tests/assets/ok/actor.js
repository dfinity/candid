export const idlFactory = ({ IDL }) => {
  const o = IDL.Rec();
  const f = IDL.Func([IDL.Int8], [IDL.Int8], []);
  const h = IDL.Func([f], [f], []);
  const g = f;
  o.fill(IDL.Opt(o));
  return IDL.Service({
    'f' : IDL.Func([IDL.Nat], [h], []),
    'g' : f,
    'h' : g,
    'o' : IDL.Func([o], [o], []),
  });
};
export const init = ({ IDL }) => { return []; };
