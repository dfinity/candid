export const getServiceTypes = ({ IDL }) => {
  const o = IDL.Rec();
  const f = IDL.Func([IDL.Int8], [IDL.Int8], []);
  const h = IDL.Func([f], [f], []);
  const g = f;
  o.fill(IDL.Opt(o));

  
  return {
    'f': IDL.Func([IDL.Nat], [h], []),
    'g': f,
    'h': g,
    'o': IDL.Func([o], [o], []),
  };
};


export const idlFactory = ({ IDL }) => {
  const _ServiceTypes = getServiceTypes({ IDL });

  return IDL.Service({
    'f': _ServiceTypes['f'],
    'g': _ServiceTypes['g'],
    'h': _ServiceTypes['h'],
    'o': _ServiceTypes['o'],
  });
};

export const init = ({ IDL }) => { return []; };
