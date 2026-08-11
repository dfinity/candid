/-
Field identifiers and the Candid field-id hash.
-/

namespace Candid

/-- A record or variant field identifier.

Fields are identified by a 32-bit number. In the textual syntax that number may be
written literally or as a name that hashes to it, and the two forms are
*indistinguishable at the type level* -- `record { 24860 : nat }` and
`record { ok : nat }` are the same type. So the model keys fields on `FieldId` and
leaves names to the syntax layer, which is also what keeps field equality honest:
two fields are equal exactly when their ids are.
-/
abbrev FieldId := UInt32

/-- The normative field-id hash, from `spec/Candid.md`:

```
hash(id) = ( Sum_(i=0..k) utf8(id)[i] * 223^(k-i) ) mod 2^32   where k = |utf8(id)|-1
```

Evaluated in Horner form over the UTF-8 *bytes* of the name -- not its characters,
which differ for any name outside ASCII. `UInt32` arithmetic in Lean is modular, so
the `mod 2^32` is the type, not an operation. -/
def hashFieldName (name : String) : FieldId :=
  name.toUTF8.foldl (fun acc byte => acc * 223 + byte.toUInt32) 0

/- The spec notes that this hash makes collisions within one record disallowed
rather than resolved, so a record type carrying two fields with equal ids is
malformed. Checking that is `TypeExpr.wellFormed`'s job, not the hash's. -/

end Candid
