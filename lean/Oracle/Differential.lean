/-
Differential cases: random messages, each with the model's exact answer
(`conformance/README.md`, "Exact answers").

A conformance vector says only *that* a message is rejected, which is all conformance
asks. An implementation that reports why and where, as `decodeAt`
(`Candid/DecodeAt.lean`) does, can be held to more: the same values, the same failure or
undefined coercion, and for a message it rejects, the same `Rejection` at the same byte.
These cases are where that is asked.

**A case** is a message, the receiver's types, a limit on the values decoded, and the
answer `decodeAt` gives. The messages are built to reach what hand-written vectors miss,
which is combinations:

- a random type table and argument types, and random values of those types, encoded;
- then, often, damaged: cut short, a byte changed, a byte inserted, bytes appended --
  so that an error can come in the header, in a value, after a value that failed to
  coerce, or after an undefined one;
- read at the sender's own types, at a variation of them -- a primitive changed, a field
  added or dropped, an `opt` put around a type, an argument added or dropped, an infinite
  option put in -- or at unrelated types;
- within a limit: the oracle's, or exactly the values the message has, or one fewer, so
  that the count is checked to the value.

**Deterministic.** The cases come from a seed. `lake exe oracle differential <file>`
writes the committed cases, `conformance/differential/cases.json`, from a fixed seed,
and CI writes them again and fails on a difference, as it does for the vectors. Another
seed and count give more cases, for a longer run.

The self-test also checks `decodeAt_eq` on every case: these are the messages that
reach the most combinations, so they are where the one pass is most likely to differ
from decoding then coercing.
-/

import Oracle.Vector

namespace Oracle.Differential

open Candid Lean

/-! ## Randomness -/

/-- A computation that draws on a seeded generator. -/
abbrev Generation := StateM StdGen

/-- Uniform in `[0, n)`; `0` if `n` is `0`. -/
def below (n : Nat) : Generation Nat := do
  if n == 0 then return 0
  let (k, g) := randNat (← get) 0 (n - 1)
  set g
  return k

/-- `true` `k` times in `n`. -/
def chance (k n : Nat) : Generation Bool := return (← below n) < k

def pick [Inhabited α] (xs : List α) : Generation α := return xs[← below xs.length]!

/-! ## Types -/

/-- A slot in a table of `n` entries. -/
def slot (n : Nat) : Generation Slot := do
  if n > 0 && (← chance 1 2) then return .ref (← below n)
  return .primitive (← pick Primitive.all)

/-- Fields or alternatives: distinct ids, ascending, a few of them, each with a slot. -/
def labelled (n : Nat) : Generation (List (FieldId × Slot)) := do
  let ids ← (List.range 6).filterM fun _ => chance 1 3
  ids.mapM fun id => return (id.toUInt32, ← slot n)

def composite (n : Nat) : Generation Composite := do
  match ← below 12 with
  | 0 | 1 | 2 => return .opt (← slot n)
  | 3 => return .vec (← slot n)
  | 4 => return .vec (.primitive .nat8)
  | 5 | 6 | 7 => return .record (← labelled n)
  | 8 | 9 => return .variant (← labelled n)
  | 10 => return .func [← slot n] [] []
  | _ => if ← chance 1 2 then return .service [] else return .future (-25 - (← below 3)) []

/-- A service's methods, each a function entry of the table: a method's type must
denote a function. -/
def methods (entries : List Composite) : Generation Composite := do
  let funcs := (List.range entries.length).filter fun i =>
    match entries[i]? with | some (.func _ _ _) => true | _ => false
  if funcs.isEmpty then return .service []
  let names ← ["a", "b", "go"].filterM fun _ => chance 1 2
  return .service (← names.mapM fun m => return (m, .ref (← pick funcs)))

/-- A table of up to four entries, and up to three argument types in it. -/
def types : Generation (RawTypeTable × List Slot) := do
  let n ← below 5
  let entries ← (List.range n).mapM fun _ => composite n
  let entries ← entries.mapM fun
    | .service _ => methods entries
    | c => pure c
  let roots ← (List.range (← below 4)).mapM fun _ => slot n
  return ({ entries := entries.toArray }, roots)

/-! ## Values -/

def someBytes (most : Nat) : Generation (List UInt8) := do
  (List.range (← below (most + 1))).mapM fun _ => return (← below 256).toUInt8

def primitiveValue : Primitive → Generation (Option Value)
  | .null | .reserved => return some .null
  | .empty => return none
  | .bool => return some (.bool (← chance 1 2))
  | .nat => return some (.nat (← pick [0, 1, 127, 128, 300, 2 ^ 64, ← below 100000]))
  | .int => return some (.int (← pick [0, -1, 63, -64, 64, -(2 ^ 70), ((← below 1000) : Int) - 500]))
  | .nat8 => return some (.nat8 (← below 256).toUInt8)
  | .nat16 => return some (.nat16 (← below 65536).toUInt16)
  | .nat32 => return some (.nat32 (← below (2 ^ 32)).toUInt32)
  | .nat64 => return some (.nat64 (← below (2 ^ 64)).toUInt64)
  | .int8 => return some (.int8 (← below 256).toUInt8.toInt8)
  | .int16 => return some (.int16 (← below 65536).toUInt16.toInt16)
  | .int32 => return some (.int32 (← below (2 ^ 32)).toUInt32.toInt32)
  | .int64 => return some (.int64 (← below (2 ^ 64)).toUInt64.toInt64)
  | .float32 => return some (.float32 (← below (2 ^ 32)).toUInt32)
  | .float64 => return some (.float64 (← below (2 ^ 64)).toUInt64)
  | .text => return some (.text (← pick ["", "a", "héllo", "☃", "line\nbreak"]))
  | .principal => return some (.principal (← someBytes 29))

/-- A value of type `t`, if one is found within `fuel` levels of nesting. -/
partial def value (T : TypeTable) (fuel : Nat) (t : Slot) : Generation (Option Value) := do
  match t with
  | .primitive p => primitiveValue p
  | .ref r => match T.lookup? r with
    | none => return none
    | some (.opt inner) =>
      if fuel == 0 || (← chance 1 3) then return some .null
      return (← value T (fuel - 1) inner).map .opt <|> some .null
    | some (.vec inner) =>
      let n ← if fuel == 0 then pure 0 else below 4
      let vs ← (List.range n).mapM fun _ => value T (fuel - 1) inner
      return some (.vec (vs.filterMap id))
    | some (.record fs) =>
      if fuel == 0 && !fs.isEmpty then return none
      let vs ← fs.mapM fun (id, s) => return (← value T (fuel - 1) s).map (id, ·)
      return (vs.mapM id).map .record
    | some (.variant fs) =>
      if fuel == 0 || fs.isEmpty then return none
      let start ← below fs.length
      let order := fs.drop start ++ fs.take start
      for (id, s) in order do
        if let some v ← value T (fuel - 1) s then return some (.variant id v)
      return none
    | some (.func _ _ _) => return some (.func (← someBytes 29) (← pick ["", "m", "go"]))
    | some (.service _) => return some (.service (← someBytes 29))
    | some (.future _ _) => return some .null

/-! ## Receivers -/

def mapSlotsM (f : Slot → Generation Slot) : Composite → Generation Composite
  | .opt t => return .opt (← f t)
  | .vec t => return .vec (← f t)
  | .record fs => return .record (← fs.mapM fun (id, t) => return (id, ← f t))
  | .variant fs => return .variant (← fs.mapM fun (id, t) => return (id, ← f t))
  | .func a r ann => return .func (← a.mapM f) (← r.mapM f) ann
  | .service ms => return .service (← ms.mapM fun (m, t) => return (m, ← f t))
  | c@(.future _ _) => return c

/-- Add a field at an id not taken, or drop one. -/
def reshape (fs : List (FieldId × Slot)) (n : Nat) : Generation (List (FieldId × Slot)) := do
  if !fs.isEmpty && (← chance 1 2) then
    let k ← below fs.length
    return fs.eraseIdx k
  let id := (← below 8).toUInt32
  if fs.any (·.1 == id) then return fs
  return sortById ((id, ← slot n) :: fs)

/-- One change to a receiver's types, which may append entries to the table. -/
def change (entries : Array Composite) (roots : List Slot) :
    Generation (Array Composite × List Slot) := do
  let n := entries.size
  let some_slot (s : Slot) : Generation Slot := do
    if ← chance 1 3 then slot n else return s
  match ← below 7 with
  | 0 =>
    -- A slot changed, in one entry.
    if n == 0 then return (entries, roots)
    let i ← below n
    return (entries.set! i (← mapSlotsM some_slot entries[i]!), roots)
  | 1 =>
    -- A field added or dropped.
    if n == 0 then return (entries, roots)
    let i ← below n
    match entries[i]! with
    | .record fs => return (entries.set! i (.record (← reshape fs n)), roots)
    | .variant fs => return (entries.set! i (.variant (← reshape fs n)), roots)
    | _ => return (entries, roots)
  | 2 => return (entries, ← roots.mapM some_slot)
  | 3 =>
    -- An argument added or dropped.
    if !roots.isEmpty && (← chance 1 2) then return (entries, roots.dropLast)
    return (entries, roots ++ [← slot n])
  | 4 =>
    -- An `opt` put around a root.
    if roots.isEmpty then return (entries, roots)
    let k ← below roots.length
    return (entries.push (.opt roots[k]!), roots.set k (.ref n))
  | 5 =>
    -- An `opt` put around a type in an entry: a field's, an element's, an alternative's.
    if n == 0 then return (entries, roots)
    let i ← below n
    let slots := entries[i]!.slots
    if slots.isEmpty then return (entries, roots)
    let t ← pick slots
    let c ← mapSlotsM (fun s => pure (if s == t then .ref n else s)) entries[i]!
    return ((entries.set! i c).push (.opt t), roots)
  | _ =>
    -- An infinite option, `R = opt R`, in place of a root.
    if roots.isEmpty then return (entries, roots)
    let k ← below roots.length
    return (entries.push (.opt (.ref n)), roots.set k (.ref n))

/-- The receiver's types: the sender's, a variation of them, or unrelated ones. Always
well formed: a change that would leave them malformed is not made, and the others are. -/
def receiver (sender : RawTypeTable) (roots : List Slot) : Generation TypeSequence := do
  let same : TypeSequence := ⟨sender, roots⟩
  match ← below 8 with
  | 0 => return same
  | 1 =>
    let (t, rs) ← types
    let s : TypeSequence := ⟨t, rs⟩
    return if s.check?.isSome then s else same
  | _ =>
    let mut s := same
    for _ in List.range (1 + (← below 3)) do
      let (entries, rs) ← change s.table.entries s.roots
      let changed : TypeSequence := ⟨{ entries }, rs⟩
      if changed.check?.isSome then s := changed
    return s

/-! ## Messages -/

/-- The message as sent, or damaged: more often in its values, which come after a
header of `header` bytes, than in the header. -/
def damage (header : Nat) (bs : List UInt8) : Generation (List UInt8) := do
  let inValues ← chance 3 4
  let cut ← if inValues then (header + ·) <$> below (bs.length - header + 1)
    else below (bs.length + 1)
  match ← below 9 with
  | 0 => return bs.take cut
  | 1 =>
    if cut == bs.length then return bs
    return bs.set cut (← below 256).toUInt8
  | 2 => return bs.take cut ++ [(← below 256).toUInt8] ++ bs.drop cut
  | 3 => return bs ++ (← someBytes 2)
  | _ => return bs

/-- An entry as `Composite.encode` writes it, but with its members in the order given,
which may not be the one the format requires. -/
def encodeAsGiven : Composite → List UInt8
  | .record fs => sleb128 (-20) ++ lebList fs fun (id, t) => leb128 id.toNat ++ t.encode
  | .variant fs => sleb128 (-21) ++ lebList fs fun (id, t) => leb128 id.toNat ++ t.encode
  | .service ms => sleb128 (-23) ++ lebList ms fun (n, t) =>
      leb128 (utf8Bytes n).length ++ utf8Bytes n ++ t.encode
  | c => c.encode

/-- The members of a record, a variant or a service, if it has two or more, reversed. -/
def reversed? : Composite → Option Composite
  | .record fs@(_ :: _ :: _) => some (.record fs.reverse)
  | .variant fs@(_ :: _ :: _) => some (.variant fs.reverse)
  | .service ms@(_ :: _ :: _) => some (.service ms.reverse)
  | _ => none

/-- The message with its header written again, one entry's members out of order: what
damage to single bytes almost never does. -/
def disorder (A : TypeTable) (roots : List Slot) (header : Nat) (bs : List UInt8) :
    Generation (List UInt8) := do
  let entries := A.raw.entries.toList
  let candidates := (List.range entries.length).filter fun i =>
    (entries[i]?.bind reversed?).isSome
  if candidates.isEmpty then return bs
  let k ← pick candidates
  let entries := entries.mapIdx fun i c => if i == k then (reversed? c).getD c else c
  return magic ++ lebList entries encodeAsGiven ++ lebList roots Slot.encode ++ bs.drop header

/-! ## Answers -/

/-- `decodeAt`'s answer within `limit`, with how many values it counted if it read the
whole message. -/
def answerAt (bs : ByteArray) (B : TypeTable) (us : List Slot) (limit : Nat) :
    Except DecodeError (Outcome (List Value)) × Option Nat :=
  match decodeAtCounting bs B us (some limit) with
  | .error e => (.error e, none)
  | .ok (o, used) => (.ok o, some used)

def _root_.Candid.Rejection.name : Rejection → String
  | .endOfInput => "endOfInput"
  | .missingMagicNumber => "missingMagicNumber"
  | .notATypeReference => "notATypeReference"
  | .notAType => "notAType"
  | .primitiveInTable => "primitiveInTable"
  | .fieldIdTooLarge => "fieldIdTooLarge"
  | .fieldsOutOfOrder => "fieldsOutOfOrder"
  | .methodsOutOfOrder => "methodsOutOfOrder"
  | .unknownAnnotation => "unknownAnnotation"
  | .textNotUtf8 => "textNotUtf8"
  | .malformedTable => "malformedTable"
  | .unresolvedArgument => "unresolvedArgument"
  | .notABool => "notABool"
  | .notAnOptTag => "notAnOptTag"
  | .notAReferenceFlag => "notAReferenceFlag"
  | .opaqueReference => "opaqueReference"
  | .principalTooLong => "principalTooLong"
  | .variantIndexOutOfRange => "variantIndexOutOfRange"
  | .valueOfEmpty => "valueOfEmpty"
  | .recordWithoutValue => "recordWithoutValue"
  | .bytesAfterValues => "bytesAfterValues"
  | .tooManyValues => "tooManyValues"
  | .unreachable => "unreachable"

/-- An answer: `{"values": [...]}`, `"failure"`, `"undefined"`, or
`{"rejection": <kind>, "position": <byte>}`. -/
def answerToJson : Except DecodeError (Outcome (List Value)) → Json
  | .ok (.ok (some vs)) => .mkObj [("values", .arr (vs.map valueToJson).toArray)]
  | .ok (.ok none) => .str "failure"
  | .ok (.error _) => .str "undefined"
  | .error e => .mkObj [("rejection", .str e.rejection.name), ("position", .num e.position)]

structure Case where
  message : ByteArray
  receiver : TypeSequence
  limit : Nat
  answer : Except DecodeError (Outcome (List Value))

def Case.toJson (c : Case) : Json :=
  .mkObj [("message", .str (bytesToHex c.message.toList)), ("receiver", c.receiver.toJson),
    ("limit", .num c.limit), ("answer", answerToJson c.answer)]

/-- A sender's types and values, if the types have values to find. -/
def sent : Generation (Option (TypeTable × List Slot × ByteArray)) := do
  for _ in List.range 20 do
    let (raw, roots) ← types
    let some A := raw.check | continue
    let some vs := (← roots.mapM (value A 4)).mapM id | continue
    let some bs := encode A roots vs | continue
    return some (A, roots, bs)
  return none

/-- A byte that is more often one with a meaning -- a tag, a flag, a small length, the
edge of LEB128 -- than not. -/
def someByte : Generation UInt8 := do
  if ← chance 1 2 then return (← pick [0, 0, 1, 1, 2, 0x1e, 0x7f, 0x80, 0xff] : Nat).toUInt8
  return (← below 256).toUInt8

/-- A header, then bytes that are not values of its types, chosen at random: so that a
message reaches the rejections no value of the types does -- an opaque reference, a
value of `empty`, a record with no value. -/
def unsent : Generation (Option (TypeTable × List Slot × ByteArray)) := do
  let (raw, roots) ← types
  let some A := raw.check | return none
  let header := magic ++ lebList raw.entries.toList Composite.encode ++ lebList roots Slot.encode
  let rest ← (List.range (← below 7)).mapM fun _ => someByte
  return some (A, roots, ⟨(header ++ rest).toArray⟩)

/-- The cases from one message: at the oracle's limit, and if the message is read to its
end, at exactly the values it has and, sometimes, one fewer. -/
def casesFrom : Generation (List Case) := do
  let message ← if ← chance 1 6 then unsent else sent
  let some (A, roots, bs) := message | return []
  let header := match decodeHeader bs with
    | .ok h => h.pos
    | .error _ => 0
  let damaged ← if ← chance 1 10 then disorder A roots header bs.toList
    else damage header bs.toList
  let bs : ByteArray := ⟨damaged.toArray⟩
  let r ← receiver A.raw roots
  let some ⟨B, us⟩ := r.check? | return []
  let us := us.map (·.1)
  let (answer, used) := answerAt bs B us costlyLimit
  match used with
  | none => return [⟨bs, r, costlyLimit, answer⟩]
  | some used =>
    -- Within `used`, the answer is the one within the oracle's limit.
    let exact : Case := ⟨bs, r, used, answer⟩
    if used > 0 && (← chance 1 2) then
      return [exact, ⟨bs, r, used - 1, (answerAt bs B us (used - 1)).1⟩]
    return [exact]

def cases (seed count : Nat) : List Case :=
  let go : Generation (List Case) := do
    let mut all := #[]
    for _ in List.range count do
      all := all ++ (← casesFrom).toArray
    return all.toList
  (go.run (mkStdGen seed)).1

/-- The committed cases: `conformance/differential/cases.json`. -/
def corpusSeed : Nat := 803
def corpusCount : Nat := 2000

def render (cs : List Case) : String :=
  "[\n" ++ ",\n".intercalate (cs.map (·.toJson.compress)) ++ "\n]\n"

/-- `decodeAt_eq` on every case, at its limit: the one pass gives what decoding then
coercing gives. -/
def violations (cs : List Case) : List String :=
  cs.filterMap fun c => c.receiver.check?.bind fun ⟨B, us⟩ =>
    (onePassDisagreement c.message B (us.map (·.1)) [some c.limit]).map fun why =>
      s!"differential {bytesToHex c.message.toList}: {why}"

end Oracle.Differential
