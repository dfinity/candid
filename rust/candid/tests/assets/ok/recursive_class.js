export default ({ IDL }) => {
  const s = IDL.Rec();
  s.fill(IDL.Service({ 'next' : IDL.Func([], [s], []) }));
  return s.getType();
};
