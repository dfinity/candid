import { IDL } from '@dfinity/candid';

export const List = IDL.Rec();
List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
export const Profile = IDL.Record({ 'age' : IDL.Nat8, 'name' : IDL.Text });

export const idlService = IDL.Service({
  'get' : IDL.Func([], [List], []),
  'set' : IDL.Func([List], [List], []),
});

export const idlInitArgs = [IDL.Int, List, Profile];

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  const Profile = IDL.Record({ 'age' : IDL.Nat8, 'name' : IDL.Text });
  return IDL.Service({
    'get' : IDL.Func([], [List], []),
    'set' : IDL.Func([List], [List], []),
  });
};

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  const Profile = IDL.Record({ 'age' : IDL.Nat8, 'name' : IDL.Text });
  return [IDL.Int, List, Profile];
};
