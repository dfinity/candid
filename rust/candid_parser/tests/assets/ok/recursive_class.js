import { IDL } from '@dfinity/candid';

export const s = IDL.Rec();
s.fill(IDL.Service({ 'next': _ServiceTypes['next'] }));

export const idlFactory = ({ IDL }) => { return s.getType(); };

export const init = ({ IDL }) => {
  const s = IDL.Rec();
  s.fill(IDL.Service({ 'next': _ServiceTypes['next'] }));
  return [s];
};
