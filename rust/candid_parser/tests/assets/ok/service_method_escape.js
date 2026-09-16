export const idlFactory = ({ IDL }) => {
  const f = IDL.Func([], [], []);
  const inner = IDL.Service({
    'backslash\\' : f,
    'braces { } and parens ( )' : f,
    'comment markers // and /* */' : f,
    'newline\nand carriage return\r' : f,
    'quote\"' : f,
    'tab\tand semicolon;' : f,
  });
  return IDL.Service({
    'ping' : IDL.Func([], [IDL.Text], []),
    'use_inner' : IDL.Func([inner], [], []),
  });
};
export const init = ({ IDL }) => { return []; };
