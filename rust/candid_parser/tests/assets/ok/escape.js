import { IDL } from '@dfinity/candid';

export const t = IDL.Record({
  '\"': IDL.Nat,
  '\'': IDL.Nat,
  '\"\'': IDL.Nat,
  '\\\n\'\"': IDL.Nat,
});

export const _ServiceTypes = {'\n\'\"\'\'\"\"\r\t': IDL.Func([t], [], [])}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    '\n\'\"\'\'\"\"\r\t': _ServiceTypes['\n\'\"\'\'\"\"\r\t'],
  });
};

export const init = ({ IDL }) => { return []; };
