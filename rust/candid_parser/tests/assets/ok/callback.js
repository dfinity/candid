const Fn = IDL.Rec();
const CallbacksAreFun = IDL.Record({
  'inline_callback' : IDL.Func([IDL.Nat], [IDL.Nat], []),
  'callback' : Fn,
});
Fn.fill(IDL.Func([IDL.Nat], [IDL.Nat], ['query']));

