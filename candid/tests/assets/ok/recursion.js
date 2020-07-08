export default ({ IDL }) => {
  const B = IDL.Rec();
  const list = IDL.Rec();
  const s = IDL.Rec();
  const stream = IDL.Rec();
  const tree = IDL.Rec();
  const t = IDL.Func([s], [], []);
  const node = IDL.Record({ 'head' : IDL.Nat, 'tail' : list });
  list.fill(IDL.Opt(node));
  const A = B;
  B.fill(IDL.Opt(A));
  tree.fill(
    IDL.Variant({
      'branch' : IDL.Record({ 'val' : IDL.Int, 'left' : tree, 'right' : tree }),
      'leaf' : IDL.Int
    })
  );
  stream.fill(
    IDL.Opt(
      IDL.Record({
        'head' : IDL.Nat,
        'next' : IDL.Func([], [stream], ['query'])
      })
    )
  );
  s.fill(
    IDL.Service({ 'f' : t, 'g' : IDL.Func([list], [B, tree, stream], []) })
  );
  return s.getType();
}
