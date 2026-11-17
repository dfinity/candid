/-
Rounding a float literal to `float32` or `float64` (`lean/Spec/TextValues.md`,
Section 5.3).

A literal's value is exact: a sign, and a magnitude `m * 10^e` or `m * 2^e`. It is
rounded once, directly to the target format, with IEEE 754's roundTiesToEven, which
overflows to infinity and keeps the literal's sign on a zero. All arithmetic is on
naturals, so nothing here is itself rounded.

Exponents are unbounded in the syntax, so a magnitude far outside the format is decided
before anything is multiplied out: `1e999999999` must not compute `10^999999999`. The
bounds below are loose enough for `float64`, and so for `float32` too. Inside them the
numbers stay below about 2^2600 times the literal's digits.
-/

namespace Candid

/-- An IEEE 754 binary interchange format. `p` counts the significand's bits including
the implicit one, and the bias is `emax`. -/
structure FloatFormat where
  width : Nat
  p : Nat
  emin : Int
  emax : Int

def binary32 : FloatFormat := { width := 32, p := 24, emin := -126, emax := 127 }
def binary64 : FloatFormat := { width := 64, p := 53, emin := -1022, emax := 1023 }

/-- `n / d ≥ 2^k`, exactly. -/
def atLeastPow2 (n d : Nat) (k : Int) : Bool :=
  if k ≥ 0 then n ≥ d * 2 ^ k.toNat else n * 2 ^ (-k).toNat ≥ d

/-- The bits of the format's number nearest to `n / d`, ties to even, with sign bit
`sign`. `n` and `d` are positive. -/
def roundRatio (f : FloatFormat) (sign n d : Nat) : Nat :=
  let inf := sign + (2 ^ (f.width - f.p) - 1) * 2 ^ (f.p - 1)
  -- The binade: 2^e ≤ n/d < 2^(e+1). The difference of the bit lengths is within one.
  let e0 : Int := (Nat.log2 n : Int) - Nat.log2 d
  let e := if atLeastPow2 n d e0 then e0 else e0 - 1
  -- Below the normal range the step stays that of the smallest binade: subnormals.
  let e := max e f.emin
  -- The significand, `n/d` in units of the last place, rounded.
  let k := e - (f.p - 1 : Nat)
  let (num, den) := if k ≥ 0 then (n, d * 2 ^ k.toNat) else (n * 2 ^ (-k).toNat, d)
  let q := num / den
  let r := num % den
  let q := if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q
  -- Rounding up can carry into the next binade.
  let (q, e) := if q == 2 ^ f.p then (2 ^ (f.p - 1), e + 1) else (q, e)
  if e > f.emax then inf
  else if q < 2 ^ (f.p - 1) then sign + q  -- subnormal, or zero
  else sign + (e + f.emax).toNat * 2 ^ (f.p - 1) + (q - 2 ^ (f.p - 1))

/-- The bits of `(-1)^neg * m * base^exp` rounded to `f`, where `base` is 2 if `binary`
and 10 otherwise. -/
def roundLiteral (f : FloatFormat) (neg : Bool) (m : Nat) (binary : Bool) (exp : Int) : Nat :=
  let sign := if neg then 2 ^ (f.width - 1) else 0
  let inf := sign + (2 ^ (f.width - f.p) - 1) * 2 ^ (f.p - 1)
  if m == 0 then sign else
  -- `m * base^exp` lies in [base^lo, base^(lo+1)).
  let lo : Int := exp + (if binary then Nat.log2 m else (toString m).length - 1 : Nat)
  let (tooBig, tooSmall) : Int × Int := if binary then (1100, -1200) else (400, -400)
  if lo > tooBig then inf
  else if lo < tooSmall then sign
  else
    let base := if binary then 2 else 10
    if exp ≥ 0 then roundRatio f sign (m * base ^ exp.toNat) 1
    else roundRatio f sign m (base ^ (-exp).toNat)

end Candid
