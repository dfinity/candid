export const idlFactory = ({ IDL }) => {
  const MaliciousType = IDL.Record({ 'field' : IDL.Text });
  return IDL.Service({ 'get' : IDL.Func([], [MaliciousType], ['query']) });
};
export const init = ({ IDL }) => { return []; };
