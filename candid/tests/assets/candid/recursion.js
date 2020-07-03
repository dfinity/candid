({ IDL }) => {
  const A = B;
  const B = IDL.Opt(A);
  const list = IDL.Opt(node);
  const node = IDL.Record({'head' : IDL.Nat, 'tail' : list});
  const s = IDL.Service({
    'f' : t,
    'g' : IDL.Func([list], [B, tree, stream], [])
  });
  const stream = IDL.Opt(
    IDL.Record({'head' : IDL.Nat, 'next' : IDL.Func([], [stream], ['query'])})
  );
  const t = IDL.Func([s], [], []);
  const tree = IDL.Variant({
    'branch' : IDL.Record({'val' : IDL.Int, 'left' : tree, 'right' : tree}),
    'leaf' : IDL.Int
  });
  return s;
}