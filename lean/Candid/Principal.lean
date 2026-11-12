/-
The textual form of a principal (`lean/Spec/TextValues.md`, Appendix A).

A principal is its bytes `p`. Its text is the base32 encoding (RFC 4648, lowercase, no
padding) of the CRC-32 of `p`, most significant byte first, followed by `p`, in groups of
five characters joined by `-`. Text is read by computing that form for the bytes it
encodes and comparing, ignoring ASCII case: any other spelling is rejected, so the
checksum, the base32 and the dashes are all checked by one comparison.

The length of `p` is not bounded here. The Internet Computer bounds it at 29 bytes, and
so does `candid` 0.10; see `conformance/README.md`, "Findings".
-/

import Candid.Value

namespace Candid

/-- CRC-32 as ISO 3309 and zlib compute it: reflected, polynomial `0xEDB88320`, initial
value and final XOR all ones. Bitwise, eight steps per byte. -/
def crc32 (bs : List UInt8) : UInt32 :=
  let step (c : UInt32) (_ : Nat) : UInt32 :=
    if c &&& 1 == 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1
  let byte (c : UInt32) (b : UInt8) : UInt32 :=
    (List.range 8).foldl step (c ^^^ b.toUInt32)
  (bs.foldl byte 0xFFFFFFFF) ^^^ 0xFFFFFFFF

def base32Alphabet : List Char := "abcdefghijklmnopqrstuvwxyz234567".toList

/-- RFC 4648 base32, lowercase, without padding: five bits per character, the last
character padded with zero bits. -/
def base32 (bs : List UInt8) : String :=
  let bits := bs.flatMap fun b => (List.range 8).reverse.map fun i => (b.toNat >>> i) % 2
  let groups := (List.range ((bits.length + 4) / 5)).map fun g =>
    ((bits.drop (5 * g)).take 5 ++ List.replicate 5 0).take 5
  String.ofList (groups.map fun g => base32Alphabet.getD (g.foldl (2 * · + ·) 0) 'a')

/-- `s` in groups of five characters, joined by `-`. -/
def dashed (s : String) : String :=
  let cs := s.toList
  "-".intercalate ((List.range ((cs.length + 4) / 5)).map fun g =>
    String.ofList ((cs.drop (5 * g)).take 5))

def crcBytes (p : List UInt8) : List UInt8 :=
  let c := (crc32 p).toNat
  [c >>> 24, c >>> 16, c >>> 8, c].map (·.toUInt8)

/-- The canonical text of a principal. -/
def principalText (p : PrincipalBytes) : String := dashed (base32 (crcBytes p ++ p))

/-- The value of a base32 character, either case. -/
def base32Value? (c : Char) : Option Nat :=
  base32Alphabet.idxOf? c.toLower

/-- The bytes that base32 text encodes, dropping the bits of a partial last byte.
Whether those bits were zero, and whether the length was one an encoder produces, is
left to the comparison with the canonical text. -/
def unbase32? (s : String) : Option (List UInt8) := do
  let vs ← s.toList.mapM base32Value?
  let bits := vs.flatMap fun v => (List.range 5).reverse.map fun i => (v >>> i) % 2
  return (List.range (bits.length / 8)).map fun i =>
    ((bits.drop (8 * i)).take 8).foldl (2 * · + ·) 0 |>.toUInt8

/-- The principal that `s` is the text of, if any. -/
def principalOfText? (s : String) : Option PrincipalBytes := do
  let all ← unbase32? (String.ofList (s.toList.filter (· != '-')))
  guard (all.length ≥ 4)
  let p := all.drop 4
  guard (principalText p == String.ofList (s.toList.map Char.toLower))
  return p

end Candid
