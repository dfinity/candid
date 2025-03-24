export const idlFactory = ({ IDL }) => {
  const Tokens = IDL.Record({ 'e8s' : IDL.Nat64 });
  const TransferArgs = IDL.Record({
    'toPrincipal' : IDL.Principal,
    'amount' : Tokens,
    'toSubaccount' : IDL.Opt(IDL.Vec(IDL.Nat8)),
  });
  const Result = IDL.Variant({ 'ok' : IDL.Nat64, 'err' : IDL.Text });
  return IDL.Service({ 'transfer' : IDL.Func([TransferArgs], [Result], []) });
};
export const init = ({ IDL }) => { return []; };
