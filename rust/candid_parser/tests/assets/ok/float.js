export const idlFactory = ({ IDL }) => {
  return IDL.Service({
    'identity32' : IDL.Func([IDL.Float32], [IDL.Float32], []),
    'to_f32' : IDL.Func([IDL.Float64], [IDL.Float32], []),
    'to_f64' : IDL.Func([IDL.Float32], [IDL.Float64], []),
  });
};
export const init = ({ IDL }) => { return []; };
