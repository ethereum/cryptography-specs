import EthCryptographySpecs.Bls.Errors

/-!
# `Fr`

The BLS12-381 *scalar* field. `Fr` elements live in `[0, r)` where

  r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

Same shape as `Fp`, just a different modulus. Splitting them into
separate types prevents accidental mixing between scalars and base-field
elements.
-/

namespace EthCryptographySpecs.Bls

/-- BLS12-381 scalar field modulus (= group order). -/
def Fr.modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- An element of the BLS12-381 scalar field. -/
structure Fr where
  val : Nat
deriving Inhabited, BEq, Repr

namespace Fr

@[inline] def ofNat (n : Nat) : Fr := ⟨n % modulus⟩
instance : OfNat Fr n := ⟨ofNat n⟩

@[inline] def zero : Fr := ⟨0⟩
@[inline] def one  : Fr := ⟨1⟩

@[inline] def add (a b : Fr) : Fr := ⟨(a.val + b.val) % modulus⟩
@[inline] def sub (a b : Fr) : Fr := ⟨(a.val + modulus - b.val) % modulus⟩
@[inline] def neg (a : Fr)   : Fr := ⟨(modulus - a.val) % modulus⟩
@[inline] def mul (a b : Fr) : Fr := ⟨(a.val * b.val) % modulus⟩

instance : Add Fr := ⟨add⟩
instance : Sub Fr := ⟨sub⟩
instance : Mul Fr := ⟨mul⟩
instance : Neg Fr := ⟨neg⟩

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

instance : Div Fr := ⟨fun a b => a * b.inverse⟩

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
    if acc < modulus then .ok ⟨acc⟩ else .error .nonCanonicalFieldElement

/-- Encode as 32 big-endian bytes. -/
def toBytesBE (a : Fr) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 32) fun i =>
    UInt8.ofNat ((a.val >>> ((31 - i.val) * 8)) &&& 0xff)

end Fr

end EthCryptographySpecs.Bls
