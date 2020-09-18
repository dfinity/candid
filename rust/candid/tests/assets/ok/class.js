export default ({ IDL }) => {
  return IDL.Service({
    'get' : IDL.Func([], [List], []),
    'set' : IDL.Func([List], [List], []),
  });
};
