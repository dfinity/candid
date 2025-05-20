import { IDL } from '@dfinity/candid';

export const Service = IDL.Rec();
export const Func = IDL.Func([], [Service], []);
Service.fill(IDL.Service({ 'f': _ServiceTypes['f'] }));
export const Service2 = Service;

export const _ServiceTypes = {
  'asArray': IDL.Func([], [IDL.Vec(Service2), IDL.Vec(Func)], ['query']),
  'asPrincipal': IDL.Func([], [Service2, Func], []),
  'asRecord': IDL.Func([], [IDL.Tuple(Service2, IDL.Opt(Service), Func)], []),
  'asVariant': IDL.Func(
      [],
      [IDL.Variant({ 'a': Service2, 'b': IDL.Record({ 'f': IDL.Opt(Func) }) })],
      [],
    ),
}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    'asArray': _ServiceTypes['asArray'],
    'asPrincipal': _ServiceTypes['asPrincipal'],
    'asRecord': _ServiceTypes['asRecord'],
    'asVariant': _ServiceTypes['asVariant'],
  });
};

export const init = ({ IDL }) => { return []; };
