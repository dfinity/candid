import { IDL } from '@dfinity/candid';

export const s = IDL.Rec();
s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));

export const idlService = s.getType();

export const idlInitArgs = [s];

export const idlFactory = ({ IDL }) => {
  const s = IDL.Rec();
  s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));
  
  return s.getType();
};

export const init = ({ IDL }) => {
  const s = IDL.Rec();
  s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));
  
  return [s];
};
