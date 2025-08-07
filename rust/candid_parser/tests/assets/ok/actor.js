import { IDL } from '@dfinity/candid';

export const o = IDL.Rec();
export const f = IDL.Func([IDL.Int8], [IDL.Int8], []);
export const h = IDL.Func([f], [f], []);
export const g = f;
o.fill(IDL.Opt(o));

export const idlService = IDL.Service({
  'f' : IDL.Func([IDL.Nat], [h], []),
  'g' : f,
  'h' : g,
  'h2' : h,
  'o' : IDL.Func([o], [o], []),
});

export const idlInitArgs = [];

/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
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
    'h2' : h,
    'o' : IDL.Func([o], [o], []),
  });
};

/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
