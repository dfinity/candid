import type { Principal } from '@dfinity/principal';
export interface t {
  '\"' : bigint,
  '\'' : bigint,
  '\"\'' : bigint,
  '\\\n\'\"' : bigint,
}
export interface _SERVICE {
  '\n\'\"\'\'\"\"\r\t' : (arg_0: t) => Promise<undefined>,
}
