/-
The assertions of `test/*.test.did`, held to the model and turned into vectors.

Each assertion is a claim written by people, independently of this model, and the
model has to agree with it: `violations` is every assertion it disagrees with, and the
oracle fails on any. The vectors carry the model's answers rather than the claims, so
that they say more than an assertion did -- `assert blob "..." : (nat)` says only that
a message is accepted, and its vector says as what. A message on the right of `==` is a
vector of its own.

**Text** is read by the model (`Candid/Text`, after `lean/Spec/TextValues.md`), on
either side. The translation also carries the values `candid_parser` reads it as, and
the model is held to those too (`parserViolations`): text in `test/` is written for
`candid_parser`, so where the two differ, the assertion is not testing what it says.

**`spacebomb.test.did` is about resources.** Its messages are valid, and take a lot of
time or memory to decode; the file asserts that they are rejected, by a decoder with
self-metering. The spec lets an implementation reject a message for lack of resources,
and leaves to it which ones (`spec/Candid.md`, "Resource limits"), so the claim is read
as that: these messages are costly. The model holds to it by running out too -- it
decodes none of them within `costlyLimit` (`Candid/Wire.lean`) -- and they become
`costly` vectors, which ask an implementation not to crash on them.

**Equality.** `==` and `!=` are "the host language's equality" (`test/README.md`), and
here that is `Value`'s: floats are equal when their bits are. Rust's runner compares
them numerically, so the two differ on `-0` against `0`, and on a NaN against itself. No
assertion depends on either; one that did would hold in one host and not another, and
would show up here as a violation to settle.

**Disagreements.** `disputed` lists the assertions the model disagrees with on purpose,
each with the reason. Each is a question about the spec, so the list is empty unless one
is open.
-/

import Oracle.TestDid.Data

namespace Oracle.TestDid

open Candid

def Assert.id (a : Assert) : String := s!"{a.file}.test.did: {a.name}"

/-- Does the assertion claim its message is costly, rather than rejected? See the
header. -/
def Assert.isCostly (a : Assert) : Bool := a.file == "spacebomb"

/-- The assertions the model disagrees with on purpose, by id, and why. -/
def disputed : List (String × String) := []

def showValues (vs : List Value) : String := (expectValuesToJson (some vs)).compress

/-- The model's reading of one side at `roots` in `B`: bytes deserialised, text read.
`none` is a rejection. -/
def Input.answer (B : TypeTable) (roots : List Slot) : Input → Except String (Option (List Value))
  | .blob hex => do
    let bs ← bytesFromHex? (.str hex)
    return deserialize ⟨bs.toArray⟩ B roots
  | .text src _ => return Text.readArgs src B roots

/-- Does the model agree with the claim? -/
def Assert.check (a : Assert) : Except String Unit := do
  let some ⟨B, us⟩ := a.types.check? | throw "a type is malformed"
  let roots := us.map (·.1)
  if a.isCostly then
    match a.claim, a.input with
    | .rejects, .blob hex =>
      let bs ← bytesFromHex? (.str hex)
      if let some got := deserializeWithin costlyLimit ⟨bs.toArray⟩ B roots then
        throw s!"not costly: the model answers {(expectValuesToJson got).compress}"
      return
    | _, _ => throw "a spacebomb assertion is a blob claimed to be rejected"
  let left ← a.input.answer B roots
  let both (o : Input) : Except String (List Value × List Value) := do
    match left, ← o.answer B roots with
    | some l, some r => return (l, r)
    | none, _ => throw "the model rejects the left-hand side"
    | _, none => throw "the model rejects the right-hand side"
  match a.claim with
  | .decodes => unless left.isSome do throw "the model rejects it"
  | .rejects => if let some vs := left then throw s!"the model accepts it, as {showValues vs}"
  | .equals o =>
    let (l, r) ← both o
    unless l == r do throw s!"the model reads {showValues l} and {showValues r}"
  | .differs o =>
    let (l, r) ← both o
    if l == r then throw s!"the model reads both as {showValues l}"

/-- The vectors an assertion becomes: one per message, with the model's answer. -/
def Assert.vectors (a : Assert) : List Vector :=
  match a.types.check? with
  | none => []
  | some ⟨B, us⟩ =>
    let one (suffix hex : String) : List Vector :=
      match bytesFromHex? (.str hex) with
      | .ok bs =>
        let bs : ByteArray := ⟨bs.toArray⟩
        [⟨a.id ++ suffix, if a.isCostly then .decodeCostly bs a.types
          else .decode bs a.types (deserialize bs B (us.map (·.1)))⟩]
      | .error _ => []
    let text (suffix src : String) : List Vector :=
      [⟨a.id ++ suffix, .parse src a.types (Text.readArgs src B (us.map (·.1)))⟩]
    let side (suffix : String) : Input → List Vector
      | .blob hex => one suffix hex
      | .text src _ => text suffix src
    let right := match a.claim with
      | .equals o | .differs o => side " (right)" o
      | _ => []
    side "" a.input ++ right

def vectors : List Vector := asserts.flatMap Assert.vectors

/-- Assertions the model disagrees with that are not `disputed`, disputed ones it now
agrees with, and disputes that name no assertion. -/
def violations : List String :=
  let checked := asserts
  let disagreements := checked.filterMap fun a =>
    match a.check, disputed.lookup a.id with
    | .ok (), none => none
    | .ok (), some _ => some s!"{a.id}: disputed, but the model now agrees"
    | .error _, some _ => none
    | .error e, none => some s!"{a.id}: {e}"
  let stale := disputed.filterMap fun (id, _) =>
    if checked.any (·.id == id) then none else some s!"{id}: disputed, but no such assertion"
  disagreements ++ stale

/-- Text that the model reads differently from `candid_parser`. See the header. -/
def parserViolations : List String :=
  asserts.flatMap fun a =>
    match a.types.check? with
    | none => []
    | some ⟨B, us⟩ =>
      let sides := a.input :: match a.claim with
        | .equals o | .differs o => [o]
        | _ => []
      sides.filterMap fun
        | .text src parsed =>
          let got := Text.readArgs src B (us.map (·.1))
          if got == parsed then none
          else some s!"{a.id}: the model reads {repr src} as {(expectValuesToJson got).compress}, candid_parser as {(expectValuesToJson parsed).compress}"
        | .blob _ => none

end Oracle.TestDid
