export default ({ IDL }) => {
  const t = IDL.Record({
    '\"' : IDL.Nat,
    '\'' : IDL.Nat,
    '\"\'' : IDL.Nat,
    '\\\n\'\"' : IDL.Nat,
  });
  return IDL.Service({ '\n\'\"\'\'\"\"\r\t' : IDL.Func([t], [], []) });
};
export init ({ IDL }) => { return []; };
