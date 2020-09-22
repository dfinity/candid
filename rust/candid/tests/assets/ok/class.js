export default ({ IDL }) => {
  const List = IDL.Rec();
  List.fill(IDL.Opt(IDL.Tuple(IDL.Int, List)));
  const __init = [IDL.Int, List];
  return IDL.Service({
    'get' : IDL.Func([], [List], []),
    'set' : IDL.Func([List], [List], []),
  });
};
