import { IDL } from '@dfinity/candid';

export const Service = IDL.Rec();
export const Func = IDL.Func([], [Service], []);
Service.fill(IDL.Service({ 'f' : Func }));
export const Service2 = Service;

export const idlService = IDL.Service({
  'asArray' : IDL.Func([], [IDL.Vec(Service2), IDL.Vec(Func)], ['query']),
  'asPrincipal' : IDL.Func([], [Service2, Func], []),
  'asRecord' : IDL.Func([], [IDL.Tuple(Service2, IDL.Opt(Service), Func)], []),
  'asVariant' : IDL.Func(
      [],
      [
        IDL.Variant({
          'a' : Service2,
          'b' : IDL.Record({ 'f' : IDL.Opt(Func) }),
        }),
      ],
      [],
    ),
});

export const idlInitArgs = [];

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const Service = IDL.Rec();
  const Func = IDL.Func([], [Service], []);
  Service.fill(IDL.Service({ 'f' : Func }));
  const Service2 = Service;
  return IDL.Service({
    'asArray' : IDL.Func([], [IDL.Vec(Service2), IDL.Vec(Func)], ['query']),
    'asPrincipal' : IDL.Func([], [Service2, Func], []),
    'asRecord' : IDL.Func(
        [],
        [IDL.Tuple(Service2, IDL.Opt(Service), Func)],
        [],
      ),
    'asVariant' : IDL.Func(
        [],
        [
          IDL.Variant({
            'a' : Service2,
            'b' : IDL.Record({ 'f' : IDL.Opt(Func) }),
          }),
        ],
        [],
      ),
  });
};

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
