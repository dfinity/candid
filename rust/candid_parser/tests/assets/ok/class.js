import { IDL } from '@dfinity/candid';

export const List = IDL.Rec();
List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
export const Profile = IDL.Record({ 'age': IDL.Nat8, 'name': IDL.Text });

export const _ServiceTypes = {
  'get': IDL.Func([], [List], []),
  'set': IDL.Func([List], [List], []),
}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    'get': _ServiceTypes['get'],
    'set': _ServiceTypes['set'],
  });
};

export const init = ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  const Profile = IDL.Record({ 'age': IDL.Nat8, 'name': IDL.Text });
  return [IDL.Int, List, Profile];
};
