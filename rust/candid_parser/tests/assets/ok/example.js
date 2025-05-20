import { IDL } from '@dfinity/candid';

export const B = IDL.Rec();
export const List = IDL.Rec();
export const list = IDL.Rec();
export const stream = IDL.Rec();
export const t = IDL.Rec();
export const tree = IDL.Rec();
export const b = IDL.Tuple(IDL.Int, IDL.Nat);
export const node = IDL.Record({ 'head': IDL.Nat, 'tail': list });
list.fill(IDL.Opt(node));
export const A = B;
B.fill(IDL.Opt(A));
tree.fill(
  IDL.Variant({
    'branch': IDL.Record({ 'val': IDL.Int, 'left': tree, 'right': tree }),
    'leaf': IDL.Int,
  })
);
stream.fill(
  IDL.Opt(
    IDL.Record({ 'head': IDL.Nat, 'next': IDL.Func([], [stream], ['query']) })
  )
);
export const s = IDL.Service({
  'f': _ServiceTypes['f'],
  'g': _ServiceTypes['g'],
});
t.fill(IDL.Func([s], [], []));
export const my_type = IDL.Principal;
List.fill(IDL.Opt(IDL.Record({ 'head': IDL.Int, 'tail': List })));
export const nested = IDL.Record({
  _0_ : IDL.Nat,
  _1_ : IDL.Nat,
  _2_ : IDL.Tuple(IDL.Nat, IDL.Int),
  _3_ : IDL.Record({ _0_ : IDL.Nat, _42_ : IDL.Nat, _43_ : IDL.Nat8 }),
  _40_ : IDL.Nat,
  _41_ : IDL.Variant({
    _42_ : IDL.Null,
    'A': IDL.Null,
    'B': IDL.Null,
    'C': IDL.Null,
  }),
  _42_ : IDL.Nat,
});
export const broker = IDL.Service({ 'find': _ServiceTypes['find'] });
export const nested_res = IDL.Variant({
  'Ok': IDL.Variant({ 'Ok': IDL.Null, 'Err': IDL.Null }),
  'Err': IDL.Variant({
    'Ok': IDL.Record({ 'content': IDL.Text }),
    'Err': IDL.Tuple(IDL.Int),
  }),
});
export const res = IDL.Variant({
  'Ok': IDL.Tuple(IDL.Int, IDL.Nat),
  'Err': IDL.Record({ 'error': IDL.Text }),
});
export const f = IDL.Func(
    [List, IDL.Func([IDL.Int32], [IDL.Int64], [])],
    [IDL.Opt(List), res],
    [],
  );
export const a = IDL.Variant({ 'a': IDL.Null, 'b': b });

export const _ServiceTypes = {
  'bbbbb': IDL.Func([b], [], []),
  'f': t,
  'f1': IDL.Func([list, IDL.Vec(IDL.Nat8), IDL.Opt(IDL.Bool)], [], ['oneway']),
  'g': IDL.Func([list], [B, tree, stream], []),
  'g1': IDL.Func(
      [my_type, List, IDL.Opt(List), nested],
      [IDL.Int, broker, nested_res],
      ['query'],
    ),
  'h': IDL.Func(
      [
        IDL.Vec(IDL.Opt(IDL.Text)),
        IDL.Variant({ 'A': IDL.Nat, 'B': IDL.Opt(IDL.Text) }),
        IDL.Opt(List),
      ],
      [IDL.Record({ _42_ : IDL.Record({}), 'id': IDL.Nat })],
      [],
    ),
  'i': f,
  'x': IDL.Func(
      [a, b],
      [
        IDL.Opt(a),
        IDL.Opt(b),
        IDL.Variant({
          'Ok': IDL.Record({ 'result': IDL.Text }),
          'Err': IDL.Variant({ 'a': IDL.Null, 'b': IDL.Null }),
        }),
      ],
      ['composite_query'],
    ),
}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    'bbbbb': _ServiceTypes['bbbbb'],
    'f': _ServiceTypes['f'],
    'f1': _ServiceTypes['f1'],
    'g': _ServiceTypes['g'],
    'g1': _ServiceTypes['g1'],
    'h': _ServiceTypes['h'],
    'i': _ServiceTypes['i'],
    'x': _ServiceTypes['x'],
  });
};

export const init = ({ IDL }) => { return []; };
