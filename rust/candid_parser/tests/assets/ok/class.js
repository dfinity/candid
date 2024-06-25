export const idlFactory = ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  const Profile = IDL.Record({ 'age' : IDL.Nat8, 'name' : IDL.Text });
  return IDL.Service({
    'get' : IDL.Func([], [List], []),
    'set' : IDL.Func([List], [List], []),
  });
};
export const init = ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  const Profile = IDL.Record({ 'age' : IDL.Nat8, 'name' : IDL.Text });
  return [IDL.Int, List, Profile];
};
