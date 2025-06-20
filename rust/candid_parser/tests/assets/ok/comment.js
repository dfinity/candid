const b = IDL.Rec();
const a = IDL.Variant({ 'a' : IDL.Null, 'b' : b });
b.fill(IDL.Tuple(IDL.Int, IDL.Nat));
const id = IDL.Nat8;

