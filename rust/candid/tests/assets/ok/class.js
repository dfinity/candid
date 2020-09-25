export default ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  return IDL.Service({
    'get' : IDL.Func([], [List], []),
    'set' : IDL.Func([List], [List], []),
  });
};
export const init = ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  return [IDL.Int, List];
};
