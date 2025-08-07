import { IDL } from '@dfinity/candid';

export const s = IDL.Rec();
s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));

export const idlService = s.getType();

export const idlInitArgs = [s];

/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const s = IDL.Rec();
  s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));
  return s.getType();
};

/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => {
  const s = IDL.Rec();
  s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));
  return [s];
};
