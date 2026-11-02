/-
An assertion from `test/*.test.did`, as `conformance/tools/test-did` translates it.

The `.test.did` files are the suite this one replaces (`conformance/README.md`,
"Migration"). Each assertion names a message, the types to read it at, and a claim
about the outcome. The translation keeps all three and adds nothing: the types become a
`TypeSeq`, and a message in the textual syntax keeps its source, with the values
`candid_parser` reads it as, since this model has no textual syntax yet. What the model
makes of each assertion is `Oracle/TestDid.lean`'s business.
-/

import Oracle.Vector

namespace Oracle.TestDid

open Candid

/-- One side of an assertion: bytes, or text in the textual syntax. Text keeps the
values `candid_parser` reads it as at the assertion's types, or `none` if it cannot. -/
inductive Input where
  | blob (hex : String)
  | text (source : String) (values : Option (List Value))

/-- `assert <input> : <tuptype>`, `!:`, `== <input>` and `!= <input>`. -/
inductive Claim where
  /-- The input is accepted at the types. -/
  | decodes
  /-- The input is rejected at the types. -/
  | rejects
  /-- Both inputs are accepted, as equal values. -/
  | equals (other : Input)
  /-- Both inputs are accepted, as different values. -/
  | differs (other : Input)

structure Assert where
  /-- The file, without `.test.did`. -/
  file : String
  /-- The assertion's description, made unique within its file. -/
  name : String
  input : Input
  types : TypeSeq
  claim : Claim

end Oracle.TestDid
