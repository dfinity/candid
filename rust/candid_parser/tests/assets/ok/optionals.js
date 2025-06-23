export const idlFactory = ({ IDL }) => {
  const recursive_opt = IDL.Rec();
  const doubleNested_opt = IDL.Opt(IDL.Opt(IDL.Opt(IDL.Text)));
  const nested_opt = IDL.Opt(IDL.Opt(IDL.Text));
  const normal_opt = IDL.Opt(IDL.Text);
  recursive_opt.fill(IDL.Opt(recursive_opt));
  return IDL.Service({
    'doubleNested_opt' : IDL.Func([doubleNested_opt], [doubleNested_opt], []),
    'nested_opt' : IDL.Func([nested_opt], [nested_opt], []),
    'normal_opt' : IDL.Func([normal_opt], [normal_opt], []),
    'recursive_opt' : IDL.Func([recursive_opt], [recursive_opt], []),
  });
};
export const init = ({ IDL }) => { return []; };
