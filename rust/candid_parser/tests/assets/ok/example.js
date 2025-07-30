import { IDL } from '@dfinity/candid';

export const B = IDL.Rec();
export const List = IDL.Rec();
export const list = IDL.Rec();
export const stream = IDL.Rec();
export const t = IDL.Rec();
export const tree = IDL.Rec();
export const node = IDL.Record({ 'head' : IDL.Nat, 'tail' : list });
list.fill(IDL.Opt(node));
export const my_type = IDL.Principal;
List.fill(IDL.Opt(IDL.Record({ 'head' : IDL.Int, 'tail' : List })));
export const nested = IDL.Record({
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
export const broker = IDL.Service({
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
export const nested_res = IDL.Variant({
  'Ok' : IDL.Variant({ 'Ok' : IDL.Null, 'Err' : IDL.Null }),
  'Err' : IDL.Variant({
    'Ok' : IDL.Record({ 'content' : IDL.Text }),
    'Err' : IDL.Tuple(IDL.Int),
  }),
});
export const res = IDL.Variant({
  'Ok' : IDL.Tuple(IDL.Int, IDL.Nat),
  'Err' : IDL.Record({ 'error' : IDL.Text }),
});
export const f = IDL.Func(
    [List, IDL.Func([IDL.Int32], [IDL.Int64], [])],
    [IDL.Opt(List), res],
    [],
  );
export const b = IDL.Tuple(IDL.Int, IDL.Nat);
export const a = IDL.Variant({ 'a' : IDL.Null, 'b' : b });
export const nested_records = IDL.Record({
  'nested' : IDL.Opt(IDL.Record({ 'nested_field' : IDL.Text })),
});
export const my_variant = IDL.Variant({
  'a' : IDL.Record({ 'b' : IDL.Text }),
  'c' : IDL.Opt(
    IDL.Record({ 'd' : IDL.Text, 'e' : IDL.Vec(IDL.Record({ 'f' : IDL.Nat })) })
  ),
});
export const A = B;
B.fill(IDL.Opt(A));
tree.fill(
  IDL.Variant({
    'branch' : IDL.Record({ 'val' : IDL.Int, 'left' : tree, 'right' : tree }),
    'leaf' : IDL.Int,
  })
);
stream.fill(
  IDL.Opt(
    IDL.Record({ 'head' : IDL.Nat, 'next' : IDL.Func([], [stream], ['query']) })
  )
);
export const s = IDL.Service({
  'f' : t,
  'g' : IDL.Func([list], [B, tree, stream], []),
});
t.fill(IDL.Func([s], [], []));

export const idlService = IDL.Service({
  'f1' : IDL.Func([list, IDL.Vec(IDL.Nat8), IDL.Opt(IDL.Bool)], [], ['oneway']),
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
  'y' : IDL.Func(
      [nested_records],
      [IDL.Tuple(nested_records, my_variant)],
      ['query'],
    ),
  'f' : t,
  'g' : IDL.Func([list], [B, tree, stream], []),
  'bbbbb' : IDL.Func([b], [], []),
});

export const idlInitArgs = [];

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const B = IDL.Rec();
  const List = IDL.Rec();
  const list = IDL.Rec();
  const stream = IDL.Rec();
  const t = IDL.Rec();
  const tree = IDL.Rec();
  const node = IDL.Record({ 'head' : IDL.Nat, 'tail' : list });
  list.fill(IDL.Opt(node));
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
  const b = IDL.Tuple(IDL.Int, IDL.Nat);
  const a = IDL.Variant({ 'a' : IDL.Null, 'b' : b });
  const nested_records = IDL.Record({
    'nested' : IDL.Opt(IDL.Record({ 'nested_field' : IDL.Text })),
  });
  const my_variant = IDL.Variant({
    'a' : IDL.Record({ 'b' : IDL.Text }),
    'c' : IDL.Opt(
      IDL.Record({
        'd' : IDL.Text,
        'e' : IDL.Vec(IDL.Record({ 'f' : IDL.Nat })),
      })
    ),
  });
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
  return IDL.Service({
    'f1' : IDL.Func(
        [list, IDL.Vec(IDL.Nat8), IDL.Opt(IDL.Bool)],
        [],
        ['oneway'],
      ),
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
    'y' : IDL.Func(
        [nested_records],
        [IDL.Tuple(nested_records, my_variant)],
        ['query'],
      ),
    'f' : t,
    'g' : IDL.Func([list], [B, tree, stream], []),
    'bbbbb' : IDL.Func([b], [], []),
  });
};

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
