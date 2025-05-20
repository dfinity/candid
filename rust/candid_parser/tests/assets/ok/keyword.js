import { IDL } from '@dfinity/candid';

export const if_ = IDL.Rec();
export const list = IDL.Rec();
export const o = IDL.Rec();
export const stream = IDL.Rec();
export const t = IDL.Rec();
o.fill(IDL.Opt(o));
export const node = IDL.Record({ 'head': IDL.Nat, 'tail': list });
list.fill(IDL.Opt(node));
if_.fill(
  IDL.Variant({
    'branch': IDL.Record({ 'val': IDL.Int, 'left': if_, 'right': if_ }),
    'leaf': IDL.Int,
  })
);
stream.fill(
  IDL.Opt(
    IDL.Record({ 'head': IDL.Nat, 'next': IDL.Func([], [stream], ['query']) })
  )
);
export const return_ = IDL.Service({
  'f': _ServiceTypes['f'],
  'g': _ServiceTypes['g'],
});
t.fill(IDL.Func([return_], [], []));

export const _ServiceTypes = {
  'Oneway': IDL.Func([], [], ['oneway']),
  'f_': IDL.Func([o], [o], []),
  'field': IDL.Func(
      [IDL.Record({ 'test': IDL.Nat16, _1291438163_ : IDL.Nat8 })],
      [IDL.Record({})],
      [],
    ),
  'fieldnat': IDL.Func(
      [IDL.Record({ _2_ : IDL.Int, '2': IDL.Nat })],
      [IDL.Tuple(IDL.Int)],
      [],
    ),
  'oneway': IDL.Func([IDL.Nat8], [], ['oneway']),
  'oneway_': IDL.Func([IDL.Nat8], [], ['oneway']),
  'query': IDL.Func([IDL.Vec(IDL.Nat8)], [IDL.Vec(IDL.Nat8)], ['query']),
  'return': IDL.Func([o], [o], []),
  'service': t,
  'tuple': IDL.Func(
      [IDL.Tuple(IDL.Int, IDL.Vec(IDL.Nat8), IDL.Text)],
      [IDL.Tuple(IDL.Int, IDL.Nat8)],
      [],
    ),
  'variant': IDL.Func(
      [
        IDL.Variant({
          'A': IDL.Null,
          'B': IDL.Null,
          'C': IDL.Null,
          'D': IDL.Float64,
        }),
      ],
      [],
      [],
    ),
}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    'Oneway': _ServiceTypes['Oneway'],
    'f_': _ServiceTypes['f_'],
    'field': _ServiceTypes['field'],
    'fieldnat': _ServiceTypes['fieldnat'],
    'oneway': _ServiceTypes['oneway'],
    'oneway_': _ServiceTypes['oneway_'],
    'query': _ServiceTypes['query'],
    'return': _ServiceTypes['return'],
    'service': _ServiceTypes['service'],
    'tuple': _ServiceTypes['tuple'],
    'variant': _ServiceTypes['variant'],
  });
};

export const init = ({ IDL }) => { return []; };
