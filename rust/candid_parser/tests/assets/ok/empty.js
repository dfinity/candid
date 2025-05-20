import { IDL } from '@dfinity/candid';

export const T = IDL.Rec();
T.fill(IDL.Tuple(T));

export const _ServiceTypes = {
  'f': IDL.Func([IDL.Record({})], [IDL.Variant({})], []),
  'g': IDL.Func([T], [IDL.Variant({ 'a': T })], []),
  'h': IDL.Func(
      [IDL.Tuple(T, IDL.Empty)],
      [IDL.Variant({ 'a': T, 'b': IDL.Record({}) })],
      [],
    ),
}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    'f': _ServiceTypes['f'],
    'g': _ServiceTypes['g'],
    'h': _ServiceTypes['h'],
  });
};

export const init = ({ IDL }) => { return []; };
