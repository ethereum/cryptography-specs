import EthCryptographySpecs.Bls.Errors

/-!
# `Fp`

The BLS12-381 base field. `Fp` elements live in `[0, p)` where

  p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624
      1eabfffeb153ffffb9feffffffffaaab

`Fp` is `Fin Fp.modulus`, so canonicity (`val < modulus`) holds by
construction. Same modulus story as `Fr`, just a different prime.

Lean core already equips `Fin n` with the modular arithmetic this spec
needs: `+`, `*`, and `-` reduce modulo `n` (core's subtraction
`((n - b) + a) % n` computes the same value as the previous spec's
`(a + n - b) % n`), and negation is `(n - a) % n`. `OfNat`, `Inhabited`,
`BEq` (via `DecidableEq`), and `Repr` instances come from core as well,
given `NeZero Fp.modulus`. The definitions below are thin wrappers kept
so the rest of the spec is unaffected by the representation change.

Inversion uses Fermat's little theorem (`x^(p-2)`); square root uses
the fact that `p ≡ 3 (mod 4)` so `sqrt(x) = x^((p+1)/4)`.

There's no Montgomery form, Barrett reduction, or other optimization
here: the goal is clarity, not speed.
-/

namespace EthCryptographySpecs.Bls

/-- BLS12-381 base field modulus. -/
def Fp.modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

protected theorem Fp.modulus_pos : 0 < Fp.modulus := by decide

-- Named explicitly: the anonymous-instance name would collide with
-- `Fr`'s `NeZero` instance (both auto-generate `instNeZeroNatModulus`).
instance Fp.instNeZeroModulus : NeZero Fp.modulus := ⟨by decide⟩

/-- An element of the BLS12-381 base field. -/
abbrev Fp := Fin Fp.modulus

namespace Fp

@[inline] def ofNat (n : Nat) : Fp := Fin.ofNat modulus n

@[inline] def zero : Fp := ⟨0, Fp.modulus_pos⟩
@[inline] def one  : Fp := ⟨1, by decide⟩

@[inline] def add (a b : Fp) : Fp := a + b
@[inline] def sub (a b : Fp) : Fp := a - b
@[inline] def neg (a : Fp)   : Fp := -a
@[inline] def mul (a b : Fp) : Fp := a * b

@[inline] def beq (a b : Fp) : Bool := a.val == b.val
@[inline] def isZero (a : Fp) : Bool := a.val == 0

/-- Square-and-multiply modular exponentiation. -/
def powNat (base : Fp) (e : Nat) : Fp :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-- Multiplicative inverse via Fermat's little theorem. -/
@[inline] def inverse (a : Fp) : Fp := powNat a (modulus - 2)

/-- Field division `a * b⁻¹`. Registered with high priority because core
already has a `Div (Fin n)` instance that performs *`Nat` division* of
the underlying values — silently picking that one up would be wrong for
a field element, so this instance must shadow it. -/
instance (priority := high) : Div Fp := ⟨fun a b => a * b.inverse⟩

/-- Square root, valid for `p ≡ 3 (mod 4)`. Throws `notASquare` if `a`
is not a square. -/
def sqrt (a : Fp) : Except BlsError Fp :=
  let cand := powNat a ((modulus + 1) / 4)
  if (cand * cand).beq a then .ok cand else .error .notASquare

/-- Decode big-endian bytes as a `Nat`. -/
def bytesBEToNat (b : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:b.size] do
    acc := (acc <<< 8) ||| b[i]!.toNat
  return acc

/-- Decode a 48-byte big-endian integer as an `Fp`. Throws if the input
has the wrong size or the integer is `≥ p`. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fp :=
  if b.size ≠ 48 then .error .nonCanonicalFieldElement
  else
    let n := bytesBEToNat b
    if h : n < modulus then .ok ⟨n, h⟩ else .error .nonCanonicalFieldElement

/-- Encode as 48 big-endian bytes. -/
def toBytesBE (a : Fp) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 48) fun i =>
    UInt8.ofNat ((a.val >>> ((47 - i.val) * 8)) &&& 0xff)

end Fp

end EthCryptographySpecs.Bls
