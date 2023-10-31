export const idlFactory = ({ IDL }) => {
  const T = IDL.Rec();
  T.fill(IDL.Tuple(T));
  return IDL.Service({
    'f' : IDL.Func([IDL.Record({})], [IDL.Variant({})], []),
    'g' : IDL.Func([T], [IDL.Variant({ 'a' : T })], []),
    'h' : IDL.Func(
        [IDL.Tuple(T, IDL.Empty)],
        [IDL.Variant({ 'a' : T, 'b' : IDL.Record({}) })],
        [],
      ),
  });
};
export const init = ({ IDL }) => { return []; };
