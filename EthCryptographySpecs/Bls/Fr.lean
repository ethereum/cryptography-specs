import EthCryptographySpecs.Bls.Errors

/-!
# `Fr`

The BLS12-381 *scalar* field. `Fr` elements live in `[0, r)` where

  r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

`Fr` is `Fin Fr.modulus`, so canonicity (`val < modulus`) holds by
construction. Same modulus story as `Fp`, just a different prime.
Keeping scalars and base-field elements as distinct types prevents
accidental mixing between them.

Lean core already equips `Fin n` with the modular arithmetic this spec
needs: `+`, `*`, and `-` reduce modulo `n` (core's subtraction
`((n - b) + a) % n` computes the same value as the previous spec's
`(a + n - b) % n`), and negation is `(n - a) % n`. `OfNat`, `Inhabited`,
`BEq` (via `DecidableEq`), and `Repr` instances come from core as well,
given `NeZero Fr.modulus`. The definitions below are thin wrappers kept
so the rest of the spec is unaffected by the representation change.
-/

namespace EthCryptographySpecs.Bls

/-- BLS12-381 scalar field modulus (= group order). -/
def Fr.modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

protected theorem Fr.modulus_pos : 0 < Fr.modulus := by decide

instance : NeZero Fr.modulus := ⟨by decide⟩

/-- An element of the BLS12-381 scalar field. -/
abbrev Fr := Fin Fr.modulus

namespace Fr

@[inline] def ofNat (n : Nat) : Fr := Fin.ofNat modulus n

@[inline] def zero : Fr := ⟨0, Fr.modulus_pos⟩
@[inline] def one  : Fr := ⟨1, by decide⟩

@[inline] def add (a b : Fr) : Fr := a + b
@[inline] def sub (a b : Fr) : Fr := a - b
@[inline] def neg (a : Fr)   : Fr := -a
@[inline] def mul (a b : Fr) : Fr := a * b

@[inline] def beq (a b : Fr) : Bool := a.val == b.val
@[inline] def isZero (a : Fr) : Bool := a.val == 0

/-- Square-and-multiply modular exponentiation. -/
def powNat (base : Fr) (e : Nat) : Fr :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-- Multiplicative inverse via Fermat's little theorem. -/
@[inline] def inverse (a : Fr) : Fr := powNat a (modulus - 2)

/-- Field division `a * b⁻¹`. Registered with high priority because core
already has a `Div (Fin n)` instance that performs *`Nat` division* of
the underlying values — silently picking that one up would be wrong for
a field element, so this instance must shadow it. -/
instance (priority := high) : Div Fr := ⟨fun a b => a * b.inverse⟩

/-- `a ^ b` raises `a` to `b.val`, treating the exponent as an integer. -/
instance : HPow Fr Fr Fr := ⟨fun a b => powNat a b.val⟩

/-- Big-endian accumulation of `bytes` onto `acc`. -/
def fromBytesBEAux (acc : Nat) : List UInt8 → Nat
  | [] => acc
  | b :: rest => fromBytesBEAux ((acc <<< 8) ||| b.toNat) rest

/-- Decode a 32-byte big-endian integer as an `Fr`. Throws if the input
has the wrong size or the integer is `≥ r`. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fr :=
  if b.size ≠ 32 then .error .nonCanonicalFieldElement
  else
    let acc := fromBytesBEAux 0 b.data.toList
    if h : acc < modulus then .ok ⟨acc, h⟩ else .error .nonCanonicalFieldElement

/-- Encode as 32 big-endian bytes. -/
def toBytesBE (a : Fr) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 32) fun i =>
    UInt8.ofNat ((a.val >>> ((31 - i.val) * 8)) &&& 0xff)

end Fr

end EthCryptographySpecs.Bls
