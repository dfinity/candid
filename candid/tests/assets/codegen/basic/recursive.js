export default function({ IDL }) {
  const List = IDL.Record({
    'head': IDL.Nat32,
    'tail': List,
  });

  const DoubleRecursion = IDL.Record({
    'a': DoubleRecursionA,
  });

  const DoubleRecursionA = IDL.Opt(DoubleRecursion);

}
