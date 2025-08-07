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

/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const t = IDL.Record({
    '\"' : IDL.Nat,
    '\'' : IDL.Nat,
    '\"\'' : IDL.Nat,
    '\\\n\'\"' : IDL.Nat,
  });
  return IDL.Service({ '\n\'\"\'\'\"\"\r\t' : IDL.Func([t], [], []) });
};

/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
