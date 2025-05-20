import { IDL } from '@dfinity/candid';

export const B = IDL.Rec();
export const list = IDL.Rec();
export const s = IDL.Rec();
export const stream = IDL.Rec();
export const tree = IDL.Rec();
export const t = IDL.Func([s], [], []);
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
s.fill(IDL.Service({ 'f': _ServiceTypes['f'], 'g': _ServiceTypes['g'] }));

export const idlFactory = ({ IDL }) => { return s.getType(); };

export const init = ({ IDL }) => { return []; };
