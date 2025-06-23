export const idlFactory = ({ IDL }) => {
  const f = IDL.Func([IDL.Int8], [IDL.Int8], []);
  const h = IDL.Func([f], [f], []);
  const g = f;
  return IDL.Service({ 'f' : IDL.Func([IDL.Nat], [h], []), 'g' : f, 'h' : g });
};
export const init = ({ IDL }) => { return []; };
