/-
Decoding at the receiver's types, in one pass: what `candid_binary` will do.

`deserialize` (`Wire.lean`) is the spec's order: decode the whole message at the
sender's types, then coerce the values to the receiver's. A decoder that works that way
builds every value twice, and a typed one would need a coercion of its own beside the
decoder -- a second implementation of one behaviour. So the Rust decoder does both at
once: it reads each value at a pair of types, the sender's and the receiver's, and
builds only the receiver's value. `decodeAt` is that pass, written the way the Rust is,
so that the Rust can be a transcription of it; and `decodeAt_eq` says it is the spec.

**Reading at a pair of types.** `decodeValueAt` follows `coerce`, case for case, but where
`coerce` is handed a value it reads one. A scalar is read at the sender's type and
then coerced, as `coerceAt` does. An `opt`, a `vec`, a `record` and a `variant` are read
part by part, each part at its own pair of types.

**Skipping, not rewinding.** When a value fails to coerce -- the spec's *failure*, which
an enclosing `opt` turns into `null` -- or is undefined, its bytes still have to be read:
a malformed byte after it still rejects the message, and every value counts against the
limit, wherever it is (`Wire.lean`, "Costly messages"). So `decodeValueAt` never goes back.
It reads on from where it is with `decodeValue`, at the sender's types alone, to the end
of the value -- and of every value around it whose outcome is now decided. Every byte is
read once, every value counted once, in the order `decode` reads them, and every error
is the one `decode` gives. What a value coerces to, the receiver's type decides; whether
the message is well formed and how much it costs, the sender's.

**Outcomes.** A value read at a pair of types has `coerce`'s three outcomes, as data
rather than as effects -- `Except Undefined (Option α)`, which is what `Coercion α` runs to
-- since reading goes on after any of them. A `DecodeError` is the message's: malformed,
or past the limit. So a message's answer is an error, or else an outcome for the whole
argument sequence.

**Termination.** By `decodeValue`'s measure, with one more step: `decodeValueAt` hands the same
value, at the same position, to `decodeCoreAt` once it has peeled the receiver's
options. `decodeValueAt` is one notch above `decodeCoreAt`, and the lists of fields and
elements above both.

**The theorem.** `decodeAt_eq` is the claim, stated here and checked by `lake exe oracle`
over every `decode` vector, and every `coerce` vector as encode-then-decode
(`Oracle/Generate.lean`, `decodeAtViolations`), not yet proved:

    theorem decodeAt_eq (bs : ByteArray) (B : TypeTable) (us : List Slot)
        (limit : Option Nat) :
        decodeAt bs B us limit =
          (do let m ← decode bs limit; pure (coerceArguments m.table B m.values m.types us).run)

Equality, not agreement on whether a message is accepted: the same error, at the same
byte, for a message either rejects for its bytes.
-/

import Candid.Wire

namespace Candid

/-- What a value read at a pair of types comes to: `coerce`'s three outcomes. -/
abbrev Outcome (α : Type) := Except Undefined (Option α)

/-- A value that coerced, changed by `f`; a failure or an undefined one as it was. -/
def Outcome.map (f : α → β) : Outcome α → Outcome β
  | .ok (some a) => .ok (some (f a))
  | .ok none => .ok none
  | .error e => .error e

/-- `coerce`'s `<|>`: a value changed by `f`, a failure recovered as `d`, and an
undefined one passed on. -/
def Outcome.recover (f : α → β) (d : β) : Outcome α → Outcome β
  | .ok (some a) => .ok (some (f a))
  | .ok none => .ok (some d)
  | .error e => .error e

/-- A value read at the sender's type `t` alone, and what `f` makes of it. -/
def decodeThen (A : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (stall : Nat) (limit : Option Nat) (used : Nat) (t : Slot) (f : Value → β) :
    Read bs pos (β × Nat) :=
  match decodeValue A bs pos hpos stall limit used t with
  | .error e => .error e
  | .ok ((v, used), q) => .ok ((f v, used), q)

/-- The expected fields a value does not have: each is `null`, if its type accepts it. -/
def missingFields (B : TypeTable) (gs : List (FieldId × Slot)) :
    Option (List (FieldId × Value)) :=
  gs.mapM fun (id, u) => if B.acceptsNull u then some (id, .null) else none

/-- A scalar `v`, read at `t` in `A`, coerced to `u` in `B`: `coerceAt` where nothing is
left to read. -/
def coerceScalar (A B : TypeTable) (v : Value) (t u : Slot) : Outcome Value :=
  match t, u with
  | _, .primitive .reserved => .ok (some .null)
  | .primitive p, .primitive q =>
    if p == q then .ok (some v)
    else match v, p, q with
      | .nat n, .nat, .int => .ok (some (.int n))
      | _, _, _ => .ok none
  | .ref i, .primitive .principal =>
    match v, A.lookup? i with
    | .service id, some (.service _) => .ok (some (.principal id))
    | _, _ => .ok none
  | .ref i, .ref j =>
    match v, A.lookup? i, B.lookup? j with
    | .func _ _, some (.func _ _ _), some (.func _ _ _)
    | .service _, some (.service _), some (.service _) =>
      match A.root? t, B.root? u with
      | some a, some b => .ok (if decSubtype A B a b then some v else none)
      | _, _ => .ok none
    | .null, some (.future op d), some (.future op' d') =>
      .ok (if op == op' && d == d' then some .null else none)
    | _, _, _ => .ok none
  | _, _ => .ok none

mutual

/-- The value at `pos`, of type `t` in the sender's table `A`, read at `u` in the
receiver's `B`. `coerce`, reading as it goes. -/
def decodeValueAt (A B : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (stall : Nat) (limit : Option Nat) (used : Nat) (t u : Slot) :
    Read bs pos (Outcome Value × Nat) :=
  match B.optOf? u with
  | none => decodeCoreAt A B bs pos hpos stall limit used t u
  | some inner =>
    if A.acceptsNull t then
      match A.optOf? t with
      | some t' =>
        -- An option at an option: `null` stays `null`, and a value that fails under
        -- it becomes `null`.
        match charge pos limit used with
        | .error e => .error e
        | .ok used => match readByte bs pos with
          | .error e => .error e
          | .ok (0, ⟨p, hp⟩) => .ok ((.ok (some .null), used), ⟨p, Nat.le_of_lt hp.1, hp.2⟩)
          | .ok (1, ⟨p, hp⟩) => match decodeValueAt A B bs p hp.2 0 limit used t' inner with
            | .error e => .error e
            | .ok ((o, used), ⟨q, hq⟩) =>
              .ok ((o.recover .opt .null, used), ⟨q, by omega, hq.2⟩)
          | .ok (b, _) => .error ⟨pos, s!"option tag {b}, neither 0 nor 1"⟩
      -- `null` or `reserved`: `null` at any option.
      | none => decodeThen A bs pos hpos stall limit used t fun _ => .ok (some .null)
    else
      match optLayers B inner (B.size + 1) with
      | none => decodeThen A bs pos hpos stall limit used t fun _ => .error .infiniteOption
      | some (n, core) => match decodeCoreAt A B bs pos hpos stall limit used t core with
        | .error e => .error e
        | .ok ((o, used), q) => .ok ((o.recover (wrapOpt (n + 1)) (wrapOpt n .null), used), q)
termination_by (bs.size - pos, A.size - stall, 1)
decreasing_by all_goals (apply lex3; omega)

/-- `decodeValueAt` at a receiver's type that is not an option: `coerceAt`, reading as it goes. -/
def decodeCoreAt (A B : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (stall : Nat) (limit : Option Nat) (used : Nat) (t u : Slot) :
    Read bs pos (Outcome Value × Nat) :=
  let scalar (_ : Unit) := decodeThen A bs pos hpos stall limit used t
    fun v => coerceScalar A B v t u
  match t, u with
  | .ref i, .ref j =>
    match A.lookup? i, B.lookup? j with
    | some (.vec t'), some (.vec u') => match charge pos limit used with
      | .error e => .error e
      | .ok used => match readLeb bs pos with
        | .error e => .error e
        | .ok (n, ⟨p, hp⟩) => match decodeElementsAt A B bs p hp.2 limit used n t' u' with
          | .error e => .error e
          | .ok ((o, used), ⟨q, hq⟩) => .ok ((o.map .vec, used), ⟨q, by omega, hq.2⟩)
    | some (.record fs), some (.record gs) => match charge pos limit used with
      | .error e => .error e
      | .ok used =>
        if h : stall < A.size then
          match decodeFieldsAt A B bs pos hpos (stall + 1) limit used fs (sortFields gs) with
          | .error e => .error e
          | .ok ((o, used), q) => .ok ((o.map .record, used), q)
        else .error ⟨pos, "a record type that contains itself at no cost has no value"⟩
    | some (.variant fs), some (.variant gs) => match charge pos limit used with
      | .error e => .error e
      | .ok used => match readLeb bs pos with
        | .error e => .error e
        | .ok (i, ⟨p, hp⟩) => match fs[i]? with
          | none => .error ⟨pos, s!"variant index {i} past the last of {fs.length} alternatives"⟩
          | some (id, t') => match fieldAt gs id with
            | some u' => match decodeValueAt A B bs p hp.2 0 limit used t' u' with
              | .error e => .error e
              | .ok ((o, used), ⟨q, hq⟩) => .ok ((o.map (.variant id), used), ⟨q, by omega, hq.2⟩)
            -- An alternative the receiver does not have.
            | none => match decodeValue A bs p hp.2 0 limit used t' with
              | .error e => .error e
              | .ok ((_, used), ⟨q, hq⟩) => .ok ((.ok none, used), ⟨q, by omega, hq.2⟩)
    | _, _ => scalar ()
  | _, _ => scalar ()
termination_by (bs.size - pos, A.size - stall, 0)
decreasing_by all_goals (apply lex3; omega)

/-- A record's fields `fs`, read in order, against the expected fields `gs` in ascending
id: `coerceFields`, reading as it goes. A field the receiver does not expect is skipped;
an expected one the record lacks is `null`, if its type accepts it. Once a field fails
or is undefined, the rest are skipped and that is the record's outcome. -/
def decodeFieldsAt (A B : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (stall : Nat) (limit : Option Nat) (used : Nat) (fs gs : List (FieldId × Slot)) :
    Read bs pos (Outcome (List (FieldId × Value)) × Nat) :=
  match fs with
  | [] => .ok ((.ok (missingFields B gs), used), ⟨pos, Nat.le_refl _, hpos⟩)
  | (id, t) :: rest =>
    -- The expected fields before this one are missing from the record.
    match missingFields B (gs.takeWhile (·.1 < id)) with
    | none => match decodeFields A bs pos hpos stall limit used fs with
      | .error e => .error e
      | .ok ((_, used), q) => .ok ((.ok none, used), q)
    | some nulls =>
      let gs := gs.dropWhile (·.1 < id)
      match gs.head?.filter (·.1 == id) with
      | some (_, u) =>
        match decodeValueAt A B bs pos hpos stall limit used t u with
        | .error e => .error e
        | .ok ((.ok (some w), used), ⟨p, hp⟩) =>
          let next := if p = pos then stall else 0
          match decodeFieldsAt A B bs p hp.2 next limit used rest gs.tail with
          | .error e => .error e
          | .ok ((o, used), ⟨q, hq⟩) =>
            .ok ((o.map (nulls ++ (id, w) :: ·), used), ⟨q, by omega, hq.2⟩)
        | .ok ((o, used), ⟨p, hp⟩) =>
          let next := if p = pos then stall else 0
          match decodeFields A bs p hp.2 next limit used rest with
          | .error e => .error e
          | .ok ((_, used), ⟨q, hq⟩) => .ok ((o.map fun _ => [], used), ⟨q, by omega, hq.2⟩)
      -- A field the receiver does not expect: read it, and go on.
      | none => match decodeValue A bs pos hpos stall limit used t with
        | .error e => .error e
        | .ok ((_, used), ⟨p, hp⟩) =>
          let next := if p = pos then stall else 0
          match decodeFieldsAt A B bs p hp.2 next limit used rest gs with
          | .error e => .error e
          | .ok ((o, used), ⟨q, hq⟩) => .ok ((o.map (nulls ++ ·), used), ⟨q, by omega, hq.2⟩)
termination_by (bs.size - pos, A.size - stall, fs.length + 2)
decreasing_by
  all_goals apply lex3
  all_goals (simp only [List.length_cons, true_and]; first | omega | (split <;> omega))

/-- `n` elements, of type `t` read at `u`: `coerceAll`, reading as it goes. Once one fails
or is undefined, the rest are skipped and that is the vector's outcome. -/
def decodeElementsAt (A B : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (limit : Option Nat) (used : Nat) (n : Nat) (t u : Slot) :
    Read bs pos (Outcome (List Value) × Nat) :=
  match n with
  | 0 => .ok ((.ok (some []), used), ⟨pos, Nat.le_refl _, hpos⟩)
  | n + 1 => match decodeValueAt A B bs pos hpos 0 limit used t u with
    | .error e => .error e
    | .ok ((.ok (some w), used), ⟨p, hp⟩) =>
      match decodeElementsAt A B bs p hp.2 limit used n t u with
      | .error e => .error e
      | .ok ((o, used), ⟨q, hq⟩) => .ok ((o.map (w :: ·), used), ⟨q, by omega, hq.2⟩)
    | .ok ((o, used), ⟨p, hp⟩) => match decodeElements A bs p hp.2 limit used n t with
      | .error e => .error e
      | .ok ((_, used), ⟨q, hq⟩) => .ok ((o.map fun _ => [], used), ⟨q, by omega, hq.2⟩)
termination_by (bs.size - pos, A.size, n + 2)
decreasing_by all_goals (apply lex3; omega)

end

/-- The expected arguments a message does not have: each is `null`, if its type accepts
it. -/
def missingArguments (B : TypeTable) (us : List Slot) : Option (List Value) :=
  us.mapM fun u => if B.acceptsNull u then some .null else none

/-- The values of a message, of types `ts`, read at the expected types `us`:
`coerceArguments`, reading as it goes. An argument past the expected ones is skipped, and
an expected one past the message's is `null`, if its type accepts it. Once one fails or
is undefined, the rest are skipped and that is the message's outcome. -/
def decodeArgumentsAt (A B : TypeTable) (bs : ByteArray) (pos : Nat) (hpos : pos ≤ bs.size)
    (limit : Option Nat) (used : Nat) :
    List Slot → List Slot → Read bs pos (Outcome (List Value) × Nat)
  | ts, [] => match decodeArguments A bs pos hpos limit used ts with
    | .error e => .error e
    | .ok ((_, used), q) => .ok ((.ok (some []), used), q)
  | [], us => .ok ((.ok (missingArguments B us), used), ⟨pos, Nat.le_refl _, hpos⟩)
  | t :: ts, u :: us => match decodeValueAt A B bs pos hpos 0 limit used t u with
    | .error e => .error e
    | .ok ((.ok (some w), used), ⟨p, hp⟩) => match decodeArgumentsAt A B bs p hp.2 limit used ts us with
      | .error e => .error e
      | .ok ((o, used), ⟨q, hq⟩) => .ok ((o.map (w :: ·), used), ⟨q, by omega, hq.2⟩)
    | .ok ((o, used), ⟨p, hp⟩) => match decodeArguments A bs p hp.2 limit used ts with
      | .error e => .error e
      | .ok ((_, used), ⟨q, hq⟩) => .ok ((o.map fun _ => [], used), ⟨q, by omega, hq.2⟩)

/-- A message, read at the expected types `us` in `B`, decoding at most `limit` values:
its header, then its values in one pass, then nothing. An error is the message's --
malformed, or past the limit; otherwise the outcome of coercing its arguments. The same
answer as `decode` then `coerceArguments` (`decodeAt_eq`, in the header). -/
def decodeAt (bs : ByteArray) (B : TypeTable) (us : List Slot) (limit : Option Nat := none) :
    Except DecodeError (Outcome (List Value)) := do
  let ⟨table, types, pos, hpos⟩ ← decodeHeader bs
  match decodeArgumentsAt table B bs pos hpos limit 0 types us with
  | .error e => throw e
  | .ok ((o, _), ⟨q, _⟩) =>
    finish bs q
    return o

/-- `deserializeWithin`, in one pass: decode at most `limit` values. `some` is the
answer, `none` in it a rejected message; `none` alone is the decoder reaching its limit
first. -/
def deserializeAtWithin (limit : Nat) (bs : ByteArray) (B : TypeTable) (us : List Slot) :
    Option (Option (List Value)) :=
  match decodeAt bs B us (some limit) with
  | .error e => if e.isExhaustion then none else some none
  | .ok (.ok r) => some r
  | .ok (.error _) => some none

end Candid
