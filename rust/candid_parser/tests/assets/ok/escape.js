import { IDL } from '@dfinity/candid';

export const t = IDL.Record({
  '\"' : IDL.Nat,
  '\'' : IDL.Nat,
  '\"\'' : IDL.Nat,
  '\\\n\'\"' : IDL.Nat,
});

export const idlService = IDL.Service({
  '\n\'\"\'\'\"\"\r\t' : IDL.Func([t], [], []),
});

export const idlInitArgs = [];

export const idlFactory = ({ IDL }) => {
  const t = IDL.Record({
    '\"' : IDL.Nat,
    '\'' : IDL.Nat,
    '\"\'' : IDL.Nat,
    '\\\n\'\"' : IDL.Nat,
  });
  return IDL.Service({ '\n\'\"\'\'\"\"\r\t' : IDL.Func([t], [], []) });
};

export const init = ({ IDL }) => { return []; };
