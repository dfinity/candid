import { IDL } from '@dfinity/candid';

export const tuple = IDL.Tuple(IDL.Text, IDL.Text);
export const non_tuple = IDL.Record({ _1_ : IDL.Text, _2_ : IDL.Text });

export const idlService = IDL.Service({
  'bab' : IDL.Func([IDL.Int, IDL.Nat], [], []),
  'bar' : IDL.Func(
      [IDL.Record({ '2' : IDL.Int })],
      [IDL.Variant({ 'e20' : IDL.Null, 'e30' : IDL.Null })],
      [],
    ),
  'bas' : IDL.Func(
      [IDL.Tuple(IDL.Int, IDL.Int)],
      [IDL.Tuple(IDL.Text, IDL.Nat)],
      [],
    ),
  'baz' : IDL.Func(
      [IDL.Record({ _2_ : IDL.Int, '2' : IDL.Nat })],
      [IDL.Record({})],
      [],
    ),
  'bba' : IDL.Func([tuple], [non_tuple], []),
  'bib' : IDL.Func([IDL.Tuple(IDL.Int)], [IDL.Variant({ _0_ : IDL.Int })], []),
  'foo' : IDL.Func(
      [IDL.Record({ _2_ : IDL.Int })],
      [IDL.Record({ _2_ : IDL.Int, '_2' : IDL.Int })],
      [],
    ),
});

export const idlInitArgs = [];

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const tuple = IDL.Tuple(IDL.Text, IDL.Text);
  const non_tuple = IDL.Record({ _1_ : IDL.Text, _2_ : IDL.Text });
  return IDL.Service({
    'bab' : IDL.Func([IDL.Int, IDL.Nat], [], []),
    'bar' : IDL.Func(
        [IDL.Record({ '2' : IDL.Int })],
        [IDL.Variant({ 'e20' : IDL.Null, 'e30' : IDL.Null })],
        [],
      ),
    'bas' : IDL.Func(
        [IDL.Tuple(IDL.Int, IDL.Int)],
        [IDL.Tuple(IDL.Text, IDL.Nat)],
        [],
      ),
    'baz' : IDL.Func(
        [IDL.Record({ _2_ : IDL.Int, '2' : IDL.Nat })],
        [IDL.Record({})],
        [],
      ),
    'bba' : IDL.Func([tuple], [non_tuple], []),
    'bib' : IDL.Func(
        [IDL.Tuple(IDL.Int)],
        [IDL.Variant({ _0_ : IDL.Int })],
        [],
      ),
    'foo' : IDL.Func(
        [IDL.Record({ _2_ : IDL.Int })],
        [IDL.Record({ _2_ : IDL.Int, '_2' : IDL.Int })],
        [],
      ),
  });
};

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
