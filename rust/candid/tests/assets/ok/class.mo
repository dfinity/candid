// This is a static generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type List = ?(Int, List);
type _SERVICE = (Int, List) -> async actor {
  get : shared () -> async List;
  set : shared List -> async List;
}
