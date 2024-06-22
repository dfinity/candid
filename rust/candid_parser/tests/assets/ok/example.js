export const idlFactory = ({ IDL }) => {
  const B = IDL.Rec();
  const List = IDL.Rec();
  const list = IDL.Rec();
  const stream = IDL.Rec();
  const t = IDL.Rec();
  const tree = IDL.Rec();
  const b = IDL.Tuple(IDL.Int, IDL.Nat);
  const node = IDL.Record({ 'head' : IDL.Nat, 'tail' : list });
  list.fill(IDL.Opt(node));
  const A = B;
  B.fill(IDL.Opt(A));
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
    'g' : IDL.Func([list], [B, tree, stream], []),
  });
  t.fill(IDL.Func([s], [], []));
  const my_type = IDL.Principal;
  List.fill(IDL.Opt(IDL.Record({ 'head' : IDL.Int, 'tail' : List })));
  const nested = IDL.Record({
    _0_ : IDL.Nat,
    _1_ : IDL.Nat,
    _2_ : IDL.Tuple(IDL.Nat, IDL.Int),
    _3_ : IDL.Record({ _0_ : IDL.Nat, _42_ : IDL.Nat, _43_ : IDL.Nat8 }),
    _40_ : IDL.Nat,
    _41_ : IDL.Variant({
      _42_ : IDL.Null,
      'A' : IDL.Null,
      'B' : IDL.Null,
      'C' : IDL.Null,
    }),
    _42_ : IDL.Nat,
  });
  const broker = IDL.Service({
    'find' : IDL.Func(
        [IDL.Text],
        [
          IDL.Service({
            'current' : IDL.Func([], [IDL.Nat32], []),
            'up' : IDL.Func([], [], []),
          }),
        ],
        [],
      ),
  });
  const nested_res = IDL.Variant({
    'Ok' : IDL.Variant({ 'Ok' : IDL.Null, 'Err' : IDL.Null }),
    'Err' : IDL.Variant({
      'Ok' : IDL.Record({ 'content' : IDL.Text }),
      'Err' : IDL.Tuple(IDL.Int),
    }),
  });
  const res = IDL.Variant({
    'Ok' : IDL.Tuple(IDL.Int, IDL.Nat),
    'Err' : IDL.Record({ 'error' : IDL.Text }),
  });
  const f = IDL.Func(
      [List, IDL.Func([IDL.Int32], [IDL.Int64], [])],
      [IDL.Opt(List), res],
      [],
    );
  const a = IDL.Variant({ 'a' : IDL.Null, 'b' : b });
  return IDL.Service({
    'bbbbb' : IDL.Func([b], [], []),
    'f' : t,
    'f1' : IDL.Func(
        [list, IDL.Vec(IDL.Nat8), IDL.Opt(IDL.Bool)],
        [],
        ['oneway'],
      ),
    'g' : IDL.Func([list], [B, tree, stream], []),
    'g1' : IDL.Func(
        [my_type, List, IDL.Opt(List), nested],
        [IDL.Int, broker, nested_res],
        ['query'],
      ),
    'h' : IDL.Func(
        [
          IDL.Vec(IDL.Opt(IDL.Text)),
          IDL.Variant({ 'A' : IDL.Nat, 'B' : IDL.Opt(IDL.Text) }),
          IDL.Opt(List),
        ],
        [IDL.Record({ _42_ : IDL.Record({}), 'id' : IDL.Nat })],
        [],
      ),
    'i' : f,
    'x' : IDL.Func(
        [a, b],
        [
          IDL.Opt(a),
          IDL.Opt(b),
          IDL.Variant({
            'Ok' : IDL.Record({ 'result' : IDL.Text }),
            'Err' : IDL.Variant({ 'a' : IDL.Null, 'b' : IDL.Null }),
          }),
        ],
        ['composite_query'],
      ),
  });
};
export const init = ({ IDL }) => { return []; };
