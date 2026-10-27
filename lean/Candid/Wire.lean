/-
The binary format: a message as bytes, in both directions.

Rules are from `spec/Candid.md`, "Binary Format". A message is

```
B(kv* : <datatype>*) =
  i8('D') i8('I') i8('D') i8('L')      magic number
  T*(<comptype>*)                      type definition table
  I*(<datatype>*)                      types of the argument list
  M(kv* : <datatype>*)                 values of argument list
```

and deserialising it at an expected type sequence is "the inverse of the `T` function",
then "the inverse of the `M` function", then coercion. `decode` is the two inverses and
`deserialize` adds the coercion, so a decoded value has its *wire* type and only
`deserialize` knows what the receiver expected.

**The encoder is a choice, the decoder is not.** The spec says type serialisation "is not
technically a function but a relation": an encoder picks its type table. `encode` writes
the table it is given, in its order, with each entry's members sorted as the spec
assumes; another encoder may share, split or reorder entries and be just as right. So
encoding conformance is a property of bytes -- they decode to an equivalent type and the
same value -- and never a comparison with these bytes. The decoder has no such freedom:
every byte string is accepted or rejected, with one answer.

**What the decoder rejects**, beyond bytes that run out:

- A wrong magic number, and bytes left over after the last value.
- In the type table: a primitive opcode in an entry position (`spec/Candid.md`: "The type
  table may only contain composite types"); a composite opcode in a slot position, since
  `I` is a primitive or an index; record and variant fields not in strictly ascending id
  order, and methods not in strictly ascending name order -- the spec "assume[s]" both
  orders and `candid` 0.10 enforces them, so a repeated label is rejected here rather
  than by well-formedness; a field id that does not fit in 32 bits; an unknown function
  annotation; a method name that is not UTF-8; and then everything
  `RawTypeTable.check` rejects.
- In the values: a `bool` that is not `0` or `1`; text that is not UTF-8; an `opt` tag
  that is not `0` or `1`; a variant index past the variant's last alternative; a value
  of type `empty`, which has none; and an opaque reference -- see below.
- A value of a type that has none, because its every value would be infinitely long:
  `type R = record { R }`. See "Termination".

Every value is decoded, including one the receiver will drop: an argument past the
expected ones, and a record field the expected type does not declare. The spec decodes
the whole message and then coerces, so a malformed value is a malformed message wherever
it sits.

**Choices the spec leaves open**, made here and recorded so they can be revisited:

- **Non-shortest LEB128 is accepted.** The spec says "LEB128" and nothing about
  redundant continuation bytes; `candid` 0.10 accepts them. Encoding writes the shortest
  form.
- **Opaque references are rejected.** `M(ref(r) : principal) = i8(0)` stands for a
  reference carried outside the byte stream, in `R`, and the spec leaves unspecified how
  the two are bundled. A `Value` has no reference table to point into, and `candid` 0.10
  rejects them too ("Opaque reference not supported").
- **Future types are not modelled.** The spec reserves opcodes below `-24` for types an
  older decoder can skip. This model has no such types, so it rejects them, where the
  spec says to skip; `candid` 0.10 implements the skipping. That is a gap in the model,
  and no vector exercises it until it is closed.

**Termination.** Decoding a value consumes bytes, except at a record, whose encoding is
only its fields'. So a record type can recurse into itself without consuming anything --
`type R = record { R }`, or `record { null; R }` -- and its decoder would never return.
The spec does not say so, but `M` is defined by recursion on the value, so such a type
has no finite value and nothing decodes at it. The decoder detects it exactly: a record
entered at the position where an enclosing record started, and with the same entry, is
the same question asked again, and it cannot be answered. Counting is enough to detect
that, since a chain of records at one position longer than the table has a repeat; so
the decoder carries `stall`, the number of records on its path that started at the
current position, and gives up when it would pass the table's size. The measure is then
(bytes remaining, `size - stall`, the step's place in its list), and every step lowers
it.

**What is not bounded.** A vector of a type with zero-length values -- `vec null`,
`vec record {}` -- can claim any length in a few bytes, and decoding it builds a value
that long. That is the cost model's problem (`spec/Candid.md`, "Deserialisation":
"deserialising data of exponential size"), and the model does not have one yet.
-/

import Candid.Coerce

namespace Candid

/-! ## LEB128 -/

/-- Unsigned LEB128, shortest form. -/
def leb128 (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else (n % 128 + 128).toUInt8 :: leb128 (n / 128)
termination_by n
decreasing_by omega

/-- Signed LEB128, shortest form: stop once the rest is all sign, and the last byte's
bit 6 says which sign. -/
def sleb128 (i : Int) : List UInt8 :=
  let low := (i % 128).toNat
  let rest := i / 128
  if (rest == 0 && low < 64) || (rest == -1 && 64 ≤ low) then [low.toUInt8]
  else (low + 128).toUInt8 :: sleb128 rest
termination_by i.toNat + (-i).toNat
decreasing_by
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    not_and] at *
  omega

/-! ## Opcodes -/

def Prim.opcode : Prim → Int
  | .null => -1 | .bool => -2 | .nat => -3 | .int => -4
  | .nat8 => -5 | .nat16 => -6 | .nat32 => -7 | .nat64 => -8
  | .int8 => -9 | .int16 => -10 | .int32 => -11 | .int64 => -12
  | .float32 => -13 | .float64 => -14
  | .text => -15 | .reserved => -16 | .empty => -17
  | .principal => -24

def Prim.ofOpcode? (op : Int) : Option Prim :=
  match (-op).toNat with
  | 1 => some .null | 2 => some .bool | 3 => some .nat | 4 => some .int
  | 5 => some .nat8 | 6 => some .nat16 | 7 => some .nat32 | 8 => some .nat64
  | 9 => some .int8 | 10 => some .int16 | 11 => some .int32 | 12 => some .int64
  | 13 => some .float32 | 14 => some .float64
  | 15 => some .text | 16 => some .reserved | 17 => some .empty
  | 24 => some .principal
  | _ => none

def FuncAnnot.code : FuncAnnot → UInt8
  | .query => 1 | .oneway => 2 | .compositeQuery => 3

def FuncAnnot.ofCode? : UInt8 → Option FuncAnnot
  | 1 => some .query | 2 => some .oneway | 3 => some .compositeQuery
  | _ => none

/-! ## Encoding -/

/-- `T*`: a length, then each item. -/
def lebList (xs : List α) (f : α → List UInt8) : List UInt8 :=
  leb128 xs.length ++ xs.flatMap f

/-- `n` as `k` bytes, least significant first. -/
def leBytes (k n : Nat) : List UInt8 :=
  (List.range k).map fun i => (n / 256 ^ i % 256).toUInt8

/-- `I`: a primitive's opcode, or a table index -- signed, like the opcodes. -/
def Slot.encode : Slot → List UInt8
  | .prim p => sleb128 p.opcode
  | .ref r => sleb128 r

def sortById (fs : List (FieldId × α)) : List (FieldId × α) :=
  fs.mergeSort fun a b => a.1 ≤ b.1

def sortByName (ms : List (String × α)) : List (String × α) :=
  ms.mergeSort fun a b => decide (a.1 ≤ b.1)

def utf8Bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- `T` on a table entry. Members are written in the order the spec assumes: fields by
id, methods by name. -/
def Composite.encode : Composite → List UInt8
  | .opt t => sleb128 (-18) ++ t.encode
  | .vec t => sleb128 (-19) ++ t.encode
  | .record fs => sleb128 (-20) ++ lebList (sortById fs) fun (id, t) => leb128 id.toNat ++ t.encode
  | .variant fs => sleb128 (-21) ++ lebList (sortById fs) fun (id, t) => leb128 id.toNat ++ t.encode
  | .func args rets ann =>
    sleb128 (-22) ++ lebList args Slot.encode ++ lebList rets Slot.encode ++
      lebList ann fun a => [a.code]
  | .service ms =>
    sleb128 (-23) ++ lebList (sortByName ms) fun (n, t) =>
      leb128 (utf8Bytes n).length ++ utf8Bytes n ++ t.encode

/-- `M(id(v*) : principal)`, and the same for a service reference. -/
def encodeId (id : PrincipalBytes) : List UInt8 := 1 :: leb128 id.length ++ id

def encodeText (s : String) : List UInt8 := leb128 (utf8Bytes s).length ++ utf8Bytes s

def encodePrim : Value → Option (List UInt8)
  | .null => some []
  | .bool b => some [if b then 1 else 0]
  | .nat n => some (leb128 n)
  | .int i => some (sleb128 i)
  | .nat8 n => some (leBytes 1 n.toNat) | .nat16 n => some (leBytes 2 n.toNat)
  | .nat32 n => some (leBytes 4 n.toNat) | .nat64 n => some (leBytes 8 n.toNat)
  | .int8 i => some (leBytes 1 i.toUInt8.toNat) | .int16 i => some (leBytes 2 i.toUInt16.toNat)
  | .int32 i => some (leBytes 4 i.toUInt32.toNat) | .int64 i => some (leBytes 8 i.toUInt64.toNat)
  | .float32 b => some (leBytes 4 b.toNat) | .float64 b => some (leBytes 8 b.toNat)
  | .text s => some (encodeText s)
  | .principal id => some (encodeId id)
  | _ => none

mutual

/-- `M(v : t)`, for a `v` of type `t` in `T`; `none` if it is not. Recurses on the value,
as `TypeTable.hasType` does. -/
def TypeTable.encodeValue (T : TypeTable) : Value → Slot → Option (List UInt8)
  | v, .prim p => if v.hasPrim p then encodePrim v else none
  | v, .ref r => match v, T.lookup? r with
    | .null, some (.opt _) => some [0]
    | .opt w, some (.opt t) => ([1] ++ ·) <$> T.encodeValue w t
    | .vec ws, some (.vec t) => (leb128 ws.length ++ ·) <$> T.encodeAll ws t
    | .record vs, some (.record fs) => T.encodeFields vs fs
    | .variant id w, some (.variant fs) =>
      -- The index is the tag's place among the alternatives in id order: the order
      -- the type table was written in.
      match (sortById fs).findIdx? (·.1 == id), fieldAt fs id with
      | some i, some t => (leb128 i ++ ·) <$> T.encodeValue w t
      | _, _ => none
    | .service id, some (.service _) => some (encodeId id)
    | .func id m, some (.func _ _ _) => some (1 :: encodeId id ++ encodeText m)
    | _, _ => none

def TypeTable.encodeAll (T : TypeTable) : List Value → Slot → Option (List UInt8)
  | [], _ => some []
  | w :: ws, t => do return (← T.encodeValue w t) ++ (← T.encodeAll ws t)

/-- A record's fields, in the value's order -- ascending id, which is the wire's. -/
def TypeTable.encodeFields (T : TypeTable) :
    List (FieldId × Value) → List (FieldId × Slot) → Option (List UInt8)
  | [], _ => some []
  | (id, w) :: vs, fs => do
    let t ← fieldAt fs id
    return (← T.encodeValue w t) ++ (← T.encodeFields vs fs)

end

def magic : List UInt8 := [0x44, 0x49, 0x44, 0x4c]

/-- `B(kv* : <datatype>*)`, writing `T`'s whole table. `none` if the lengths differ or a
value does not have its type. -/
def encode (T : TypeTable) (types : List Slot) (values : List Value) : Option ByteArray := do
  unless types.length == values.length do none
  let ms ← (values.zip types).mapM fun (v, t) => T.encodeValue v t
  return ⟨(magic ++ lebList T.raw.entries.toList Composite.encode ++
    lebList types Slot.encode ++ ms.flatten).toArray⟩

/-! ## Reading bytes

A reader is given the input and a position, and returns what it read and where it
stopped -- with that position's relation to the start, which is what the termination
argument for values needs. -/

/-- Why a message was rejected, and where. Vectors say only *that* a message is
rejected; the reason is for people. -/
structure DecodeError where
  pos : Nat
  msg : String
  deriving Repr

/-- Read from `pos`, consuming at least one byte. -/
abbrev Read1 (bs : ByteArray) (pos : Nat) (α : Type) :=
  Except DecodeError (α × {p : Nat // pos < p ∧ p ≤ bs.size})

/-- Read from `pos`, consuming any number of bytes, possibly none. -/
abbrev Read (bs : ByteArray) (pos : Nat) (α : Type) :=
  Except DecodeError (α × {p : Nat // pos ≤ p ∧ p ≤ bs.size})

def Read1.weaken {bs : ByteArray} {pos : Nat} : Read1 bs pos α → Read bs pos α
  | .ok (a, ⟨p, h⟩) => .ok (a, ⟨p, Nat.le_of_lt h.1, h.2⟩)
  | .error e => .error e

def readByte (bs : ByteArray) (pos : Nat) : Read1 bs pos UInt8 :=
  if h : pos < bs.size then .ok (bs[pos], ⟨pos + 1, by omega, by omega⟩)
  else .error ⟨pos, "unexpected end of input"⟩

/-- LEB128 from `pos`, which started at `start`. Redundant continuation bytes are
accepted; see the header. -/
def readLebFrom (bs : ByteArray) (start pos shift acc : Nat) (hs : start ≤ pos) :
    Read1 bs start Nat :=
  if h : pos < bs.size then
    let b := bs[pos].toNat
    let acc := if b % 128 == 0 then acc else acc + b % 128 * 2 ^ shift
    if b < 128 then .ok (acc, ⟨pos + 1, by omega, by omega⟩)
    else readLebFrom bs start (pos + 1) (shift + 7) acc (by omega)
  else .error ⟨start, "LEB128 runs past the end of the input"⟩
termination_by bs.size - pos

def readLeb (bs : ByteArray) (pos : Nat) : Read1 bs pos Nat :=
  readLebFrom bs pos pos 0 0 (Nat.le_refl _)

/-- Signed LEB128 from `pos`: the unsigned reading, sign-extended from the last byte's
bit 6. -/
def readSlebFrom (bs : ByteArray) (start pos shift acc : Nat) (hs : start ≤ pos) :
    Read1 bs start Int :=
  if h : pos < bs.size then
    let b := bs[pos].toNat
    let acc := if b % 128 == 0 then acc else acc + b % 128 * 2 ^ shift
    if b < 128 then
      let v : Int := if b < 64 then acc else (acc : Int) - 2 ^ (shift + 7)
      .ok (v, ⟨pos + 1, by omega, by omega⟩)
    else readSlebFrom bs start (pos + 1) (shift + 7) acc (by omega)
  else .error ⟨start, "SLEB128 runs past the end of the input"⟩
termination_by bs.size - pos

def readSleb (bs : ByteArray) (pos : Nat) : Read1 bs pos Int :=
  readSlebFrom bs pos pos 0 0 (Nat.le_refl _)

/-- `k` bytes, least significant first. -/
def readFixed (bs : ByteArray) (pos k : Nat) (hk : 0 < k) : Read1 bs pos Nat :=
  if h : pos + k ≤ bs.size then
    .ok ((List.range k).foldr (fun i acc => bs[pos + i]!.toNat + 256 * acc) 0,
      ⟨pos + k, by omega, h⟩)
  else .error ⟨pos, s!"{k} bytes run past the end of the input"⟩

/-- `len` bytes. -/
def readBytes (bs : ByteArray) (pos len : Nat) : Read bs pos ByteArray :=
  if h : pos + len ≤ bs.size then .ok (bs.extract pos (pos + len), ⟨pos + len, by omega, h⟩)
  else .error ⟨pos, s!"{len} bytes run past the end of the input"⟩

/-- A length, then that many bytes. -/
def readBlob (bs : ByteArray) (pos : Nat) : Read1 bs pos ByteArray :=
  match readLeb bs pos with
  | .error e => .error e
  | .ok (len, ⟨p, hp⟩) => match readBytes bs p len with
    | .error e => .error e
    | .ok (b, ⟨q, hq⟩) => .ok (b, ⟨q, by omega, hq.2⟩)

def readText (bs : ByteArray) (pos : Nat) : Read1 bs pos String :=
  match readBlob bs pos with
  | .error e => .error e
  | .ok (b, p) => match String.fromUTF8? b with
    | some s => .ok (s, p)
    | none => .error ⟨pos, "text is not UTF-8"⟩

/-- `M(id(v*))`: flag `1`, then the bytes. Flag `0` is an opaque reference, which this
model does not have; see the header. -/
def readId (bs : ByteArray) (pos : Nat) : Read1 bs pos PrincipalBytes :=
  match readByte bs pos with
  | .error e => .error e
  | .ok (1, ⟨p, hp⟩) => match readBlob bs p with
    | .error e => .error e
    | .ok (b, ⟨q, hq⟩) => .ok (b.toList, ⟨q, by omega, hq.2⟩)
  | .ok (0, _) => .error ⟨pos, "opaque reference"⟩
  | .ok (f, _) => .error ⟨pos, s!"reference flag {f}, neither 0 nor 1"⟩

/-! ## Decoding the header

The type table and the argument types. Every loop here is over a count read from the
input, and every item consumes at least one byte, so a count larger than the input
fails when the bytes run out rather than running long. -/

/-- A reader over the input, with the position as state. -/
abbrev Parse := ReaderT ByteArray (StateT Nat (Except DecodeError))

def Parse.fail (msg : String) : Parse α := do throw ⟨← get, msg⟩

def Parse.lift (r : (bs : ByteArray) → (pos : Nat) → Read1 bs pos α) : Parse α :=
  fun bs pos => match r bs pos with
    | .ok (a, p) => .ok (a, p.1)
    | .error e => .error e

def Parse.byte : Parse UInt8 := .lift readByte
def Parse.leb : Parse Nat := .lift readLeb
def Parse.sleb : Parse Int := .lift readSleb

/-- `n` items, in order. -/
def Parse.times (n : Nat) (p : Parse α) : Parse (List α) :=
  go n []
where
  go : Nat → List α → Parse (List α)
    | 0, acc => pure acc.reverse
    | n + 1, acc => do go n ((← p) :: acc)

/-- `T*`: a count, then that many items. -/
def Parse.list (p : Parse α) : Parse (List α) := do Parse.times (← Parse.leb) p

open Parse in
/-- `I`: a primitive's opcode, or an index into the table. Whether the index resolves
is `RawTypeTable.check`'s to say. -/
def Parse.slot : Parse Slot := do
  let op ← sleb
  if 0 ≤ op then return .ref op.toNat
  match Prim.ofOpcode? op with
  | some p => return .prim p
  | none => fail s!"opcode {op} where a primitive type or a table index belongs"

open Parse in
/-- Fields in strictly ascending id order, which also rules out a repeated one. -/
def Parse.fields : Parse (List (FieldId × Slot)) := do
  let fs ← list do
    let id ← leb
    unless id < UInt32.size do fail s!"field id {id} does not fit in 32 bits"
    return (id.toUInt32, ← slot)
  unless ascending (fs.map (·.1)) do fail "fields not in strictly ascending id order"
  return fs

/-- Strictly ascending names. -/
def namesAscending : List String → Bool
  | a :: b :: rest => decide (a < b) && namesAscending (b :: rest)
  | _ => true

open Parse in
def Parse.entry : Parse Composite := do
  let op ← sleb
  match (-op).toNat with
  | 18 => return .opt (← slot)
  | 19 => return .vec (← slot)
  | 20 => return .record (← fields)
  | 21 => return .variant (← fields)
  | 22 =>
    let args ← list slot
    let rets ← list slot
    let ann ← list do
      let b ← byte
      match FuncAnnot.ofCode? b with
      | some a => return a
      | none => fail s!"unknown function annotation {b}"
    return .func args rets ann
  | 23 =>
    let ms ← list do
      let name ← Parse.lift readText
      return (name, ← slot)
    unless namesAscending (ms.map (·.1)) do
      fail "methods not in strictly ascending name order"
    return .service ms
  | _ =>
    if (Prim.ofOpcode? op).isSome then fail s!"primitive type {op} in the type table"
    else if op < -24 then fail s!"future type {op}, which this model does not have"
    else fail s!"opcode {op} is not a type"

open Parse in
/-- The magic number, the type table, and the argument types. -/
def Parse.header : Parse (RawTypeTable × List Slot) := do
  for b in magic do
    unless (← byte) == b do fail "not a Candid message: the magic number is not DIDL"
  let entries ← list entry
  let types ← list slot
  return ({ entries := entries.toArray }, types)

/-! ## Decoding values -/

/-- A primitive value. `null` and `reserved` consume nothing; `empty` has no value. -/
def decodePrim (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size) : Prim → Read bs pos Value
  | .null | .reserved => .ok (.null, ⟨pos, Nat.le_refl _, hpos⟩)
  | .empty => .error ⟨pos, "a value of type empty"⟩
  | .bool => match readByte bs pos with
    | .ok (0, p) => .ok (.bool false, ⟨p.1, Nat.le_of_lt p.2.1, p.2.2⟩)
    | .ok (1, p) => .ok (.bool true, ⟨p.1, Nat.le_of_lt p.2.1, p.2.2⟩)
    | .ok (b, _) => .error ⟨pos, s!"bool {b}, neither 0 nor 1"⟩
    | .error e => .error e
  | .nat => Read1.weaken ((readLeb bs pos).map fun (n, p) => (.nat n, p))
  | .int => Read1.weaken ((readSleb bs pos).map fun (i, p) => (.int i, p))
  | .nat8 => fixed 1 fun n => .nat8 n.toUInt8
  | .nat16 => fixed 2 fun n => .nat16 n.toUInt16
  | .nat32 => fixed 4 fun n => .nat32 n.toUInt32
  | .nat64 => fixed 8 fun n => .nat64 n.toUInt64
  | .int8 => fixed 1 fun n => .int8 n.toUInt8.toInt8
  | .int16 => fixed 2 fun n => .int16 n.toUInt16.toInt16
  | .int32 => fixed 4 fun n => .int32 n.toUInt32.toInt32
  | .int64 => fixed 8 fun n => .int64 n.toUInt64.toInt64
  | .float32 => fixed 4 fun n => .float32 n.toUInt32
  | .float64 => fixed 8 fun n => .float64 n.toUInt64
  | .text => Read1.weaken ((readText bs pos).map fun (s, p) => (.text s, p))
  | .principal => Read1.weaken ((readId bs pos).map fun (id, p) => (.principal id, p))
where
  fixed (k : Nat) (f : Nat → Value) : Read bs pos Value :=
    if hk : 0 < k then Read1.weaken ((readFixed bs pos k hk).map fun (n, p) => (f n, p))
    else .error ⟨pos, "unreachable: a fixed width of zero"⟩

/-- A function reference: `M(pub(s,n) : func) = i8(1) M(s : service {}) M(n : text)`. -/
def readFuncRef (bs : ByteArray) (pos : Nat) : Read1 bs pos Value :=
  match readByte bs pos with
  | .error e => .error e
  | .ok (1, ⟨p, hp⟩) => match readId bs p with
    | .error e => .error e
    | .ok (id, ⟨q, hq⟩) => match readText bs q with
      | .error e => .error e
      | .ok (m, ⟨r, hr⟩) => .ok (.func id m, ⟨r, by omega, hr.2⟩)
  | .ok (0, _) => .error ⟨pos, "opaque reference"⟩
  | .ok (f, _) => .error ⟨pos, s!"reference flag {f}, neither 0 nor 1"⟩

/-- The lexicographic order the value decoder descends in, unfolded. -/
theorem lex3 {a b c a' b' c' : Nat}
    (h : a' < a ∨ (a' = a ∧ (b' < b ∨ (b' = b ∧ c' < c)))) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a', b', c') (a, b, c) := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · exact Prod.Lex.right _ (Prod.Lex.right _ h)

mutual

/-- The inverse of `M`: a value of type `t` in `A`, read from `pos`. `stall` is the
number of records on the path here that started at `pos`; see the header. -/
def decodeValue (A : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (stall : Nat) (t : Slot) : Read bs pos Value :=
  match t with
  | .prim p => decodePrim bs pos hpos p
  | .ref r => match A.lookup? r with
    | none => .error ⟨pos, s!"type index {r} does not resolve"⟩
    | some (.opt inner) => match readByte bs pos with
      | .error e => .error e
      | .ok (0, ⟨p, hp⟩) => .ok (.null, ⟨p, Nat.le_of_lt hp.1, hp.2⟩)
      | .ok (1, ⟨p, hp⟩) => match decodeValue A bs p hp.2 0 inner with
        | .error e => .error e
        | .ok (v, ⟨q, hq⟩) => .ok (.opt v, ⟨q, by omega, hq.2⟩)
      | .ok (b, _) => .error ⟨pos, s!"option tag {b}, neither 0 nor 1"⟩
    | some (.vec inner) => match readLeb bs pos with
      | .error e => .error e
      | .ok (n, ⟨p, hp⟩) => match decodeElems A bs p hp.2 n inner with
        | .error e => .error e
        | .ok (vs, ⟨q, hq⟩) => .ok (.vec vs, ⟨q, by omega, hq.2⟩)
    | some (.record fs) =>
      if h : stall < A.size then
        match decodeFields A bs pos hpos (stall + 1) fs with
        | .error e => .error e
        | .ok (vs, q) => .ok (.record vs, q)
      else .error ⟨pos, "a record type that contains itself at no cost has no value"⟩
    | some (.variant fs) => match readLeb bs pos with
      | .error e => .error e
      | .ok (i, ⟨p, hp⟩) => match fs[i]? with
        | none => .error ⟨pos, s!"variant index {i} past the last of {fs.length} alternatives"⟩
        | some (id, inner) => match decodeValue A bs p hp.2 0 inner with
          | .error e => .error e
          | .ok (v, ⟨q, hq⟩) => .ok (.variant id v, ⟨q, by omega, hq.2⟩)
    | some (.service _) => Read1.weaken ((readId bs pos).map fun (id, p) => (.service id, p))
    | some (.func _ _ _) => Read1.weaken (readFuncRef bs pos)
termination_by (bs.size - pos, A.size - stall, 0)
decreasing_by all_goals (apply lex3; omega)

/-- A record's fields, in order. The first starts where the record does, so it shares
the record's `stall`; a later one does too unless bytes were consumed in between. -/
def decodeFields (A : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (stall : Nat) (fs : List (FieldId × Slot)) : Read bs pos (List (FieldId × Value)) :=
  match fs with
  | [] => .ok ([], ⟨pos, Nat.le_refl _, hpos⟩)
  | (id, t) :: rest => match decodeValue A bs pos hpos stall t with
    | .error e => .error e
    | .ok (v, ⟨p, hp⟩) =>
      let next := if p = pos then stall else 0
      match decodeFields A bs p hp.2 next rest with
      | .error e => .error e
      | .ok (vs, ⟨q, hq⟩) => .ok ((id, v) :: vs, ⟨q, by omega, hq.2⟩)
termination_by (bs.size - pos, A.size - stall, fs.length + 1)
decreasing_by
  all_goals apply lex3
  · omega
  · simp only [List.length_cons]; split <;> omega

/-- `n` elements of type `t`. None starts where the vector did, since the length came
first, so each starts with no stall. -/
def decodeElems (A : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (n : Nat) (t : Slot) : Read bs pos (List Value) :=
  match n with
  | 0 => .ok ([], ⟨pos, Nat.le_refl _, hpos⟩)
  | n + 1 => match decodeValue A bs pos hpos 0 t with
    | .error e => .error e
    | .ok (v, ⟨p, hp⟩) => match decodeElems A bs p hp.2 n t with
      | .error e => .error e
      | .ok (vs, ⟨q, hq⟩) => .ok (v :: vs, ⟨q, by omega, hq.2⟩)
termination_by (bs.size - pos, A.size, n + 1)
decreasing_by all_goals (apply lex3; omega)

end

/-- The values of a message, one per argument type. -/
def decodeArgs (A : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size) :
    List Slot → Read bs pos (List Value)
  | [] => .ok ([], ⟨pos, Nat.le_refl _, hpos⟩)
  | t :: ts => match decodeValue A bs pos hpos 0 t with
    | .error e => .error e
    | .ok (v, ⟨p, hp⟩) => match decodeArgs A bs p hp.2 ts with
      | .error e => .error e
      | .ok (vs, ⟨q, hq⟩) => .ok (v :: vs, ⟨q, by omega, hq.2⟩)

/-! ## Messages -/

/-- A decoded message: its type table, its argument types, and its values, each of its
type. Nothing has been coerced. -/
structure Message where
  table : TypeTable
  types : List Slot
  values : List Value

/-- The inverse of `B`: the header, then the values at the header's types, then nothing. -/
def decode (bs : ByteArray) : Except DecodeError Message := do
  let ((raw, types), pos) ← (Parse.header.run bs).run 0
  let some table := raw.check
    | throw ⟨pos, "the type table is not well formed"⟩
  unless types.all table.resolves do
    throw ⟨pos, "an argument type does not resolve"⟩
  if hpos : pos ≤ bs.size then
    match decodeArgs table bs pos hpos types with
    | .error e => throw e
    | .ok (values, ⟨q, _⟩) =>
      unless q == bs.size do throw ⟨q, s!"{bs.size - q} bytes after the last value"⟩
      return { table, types, values }
  else throw ⟨pos, "unreachable: the header ends past the input"⟩

/-- Deserialisation at the expected types `expected` in `B`: decode, then coerce the
whole argument sequence. `none` is a rejected message, for whatever reason. -/
def deserialize (bs : ByteArray) (B : TypeTable) (expected : List Slot) :
    Option (List Value) :=
  match decode bs with
  | .error _ => none
  | .ok m => match (coerceArgs m.table B m.values m.types expected).run with
    | .ok r => r
    | .error _ => none

end Candid
