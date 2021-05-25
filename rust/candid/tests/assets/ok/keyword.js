export default ({ IDL }) => {
  const list = IDL.Rec();
  const o = IDL.Rec();
  const stream = IDL.Rec();
  const t = IDL.Rec();
  const tree = IDL.Rec();
  o.fill(IDL.Opt(o));
  const node = IDL.Record({ 'head' : IDL.Nat, 'tail' : list });
  list.fill(IDL.Opt(node));
  tree.fill(
    IDL.Variant({
      'branch' : IDL.Record({ 'val' : IDL.Int, 'left' : tree, 'right' : tree }),
      'leaf' : IDL.Int,
    })
  );
  stream.fill(
    IDL.Opt(
      IDL.Record({
        'head' : IDL.Nat,
        'next' : IDL.Func([], [stream], ['query']),
      })
    )
  );
  const s = IDL.Service({
    'f' : t,
    'g' : IDL.Func([list], [tree, stream], []),
  });
  t.fill(IDL.Func([s], [], []));
  return IDL.Service({
    'f_' : IDL.Func([o], [o], []),
    'field' : IDL.Func(
        [IDL.Record({ 'test' : IDL.Nat16, _1291438163_ : IDL.Nat8 })],
        [IDL.Record({})],
        [],
      ),
    'fieldnat' : IDL.Func(
        [IDL.Record({ _2_ : IDL.Int, '2' : IDL.Nat })],
        [IDL.Tuple(IDL.Int)],
        [],
      ),
    'oneway' : IDL.Func([IDL.Nat8], [], ['oneway']),
    'oneway_' : IDL.Func([IDL.Nat8], [], ['oneway']),
    'query' : IDL.Func([IDL.Vec(IDL.Nat8)], [IDL.Vec(IDL.Nat8)], ['query']),
    'return' : IDL.Func([o], [o], []),
    'service' : t,
    'tuple' : IDL.Func(
        [IDL.Tuple(IDL.Int, IDL.Vec(IDL.Nat8), IDL.Text)],
        [IDL.Tuple(IDL.Int, IDL.Nat8)],
        [],
      ),
    'variant' : IDL.Func(
        [
          IDL.Variant({
            'A' : IDL.Null,
            'B' : IDL.Null,
            'C' : IDL.Null,
            'D' : IDL.Float64,
          }),
        ],
        [],
        [],
      ),
  });
};
export const init = ({ IDL }) => { return []; };
