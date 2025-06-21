export const idlFactory = ({ IDL }) => {
  const recursiveOpt = IDL.Rec();
  const doubleNestedOpt = IDL.Opt(IDL.Opt(IDL.Opt(IDL.Text)));
  const f = IDL.Func([IDL.Int8], [IDL.Int8], []);
  const h = IDL.Func([f], [f], []);
  const g = f;
  const nestedOpt = IDL.Opt(IDL.Opt(IDL.Text));
  const normalOpt = IDL.Opt(IDL.Text);
  recursiveOpt.fill(IDL.Opt(recursiveOpt));
  return IDL.Service({
    'doubleNestedOpt' : IDL.Func([doubleNestedOpt], [doubleNestedOpt], []),
    'f' : IDL.Func([IDL.Nat], [h], []),
    'g' : f,
    'h' : g,
    'nestedOpt' : IDL.Func([nestedOpt], [nestedOpt], []),
    'normalOpt' : IDL.Func([normalOpt], [normalOpt], []),
    'recursiveOpt' : IDL.Func([recursiveOpt], [recursiveOpt], []),
  });
};
export const init = ({ IDL }) => { return []; };
