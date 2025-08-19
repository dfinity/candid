import { IDL } from '@dfinity/candid';

export const option1 = IDL.Opt(IDL.Nat);
export const option2 = IDL.Opt(option1);

export const idlService = IDL.Service({
  'f' : IDL.Func([], [option1, option2], []),
});

export const idlInitArgs = [];

export const idlFactory = ({ IDL }) => {
  const option1 = IDL.Opt(IDL.Nat);
  const option2 = IDL.Opt(option1);
  
  return IDL.Service({ 'f' : IDL.Func([], [option1, option2], []) });
};

export const init = ({ IDL }) => { return []; };
