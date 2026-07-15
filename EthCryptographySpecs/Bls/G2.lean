import EthCryptographySpecs.Bls.Fp2
import EthCryptographySpecs.Bls.Fr

/-!
# `G2`

The "twisted" curve `E' : y² = x³ + 4·(1 + i)` over `Fp2`. This is the
same shape as `G1` but with `Fp2` coordinates and the constant `b' =
4·(1 + i)` instead of `4`.

The arithmetic formulas are identical to G1's; we just substitute `Fp`
operations with `Fp2` ones.
-/

namespace EthCryptographySpecs.Bls

/-- A G2 point in Jacobian projective coordinates over `Fp2`. `z = 0`
is the point at infinity. -/
structure G2 where
  x : Fp2
  y : Fp2
  z : Fp2
deriving Inhabited, BEq, Repr

namespace G2

/-- Affine generator of G2, embedded with `z = 1`. -/
def generator : G2 :=
  let x : Fp2 :=
    ⟨ Fp.ofNat 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8
    , Fp.ofNat 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e ⟩
  let y : Fp2 :=
    ⟨ Fp.ofNat 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801
    , Fp.ofNat 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be ⟩
  ⟨x, y, Fp2.one⟩

/-- The point at infinity. -/
def zero : G2 := ⟨Fp2.one, Fp2.one, Fp2.zero⟩

@[inline] def isInfinity (p : G2) : Bool := p.z.isZero

/-- The constant `b' = 4·(1 + i)` defining the G2 curve. -/
def bTwist : Fp2 := ⟨Fp.ofNat 4, Fp.ofNat 4⟩

/-- Jacobian point doubling for `a = 0` curves. -/
def double (p : G2) : G2 :=
  if p.z.isZero then p else
    let two := Fp2.ofFp (Fp.ofNat 2)
    let three := Fp2.ofFp (Fp.ofNat 3)
    let eight := Fp2.ofFp (Fp.ofNat 8)
    let A := p.x * p.x
    let B := p.y * p.y
    let C := B * B
    let D := two * ((p.x + B) * (p.x + B) - A - C)
    let E := three * A
    let F := E * E
    let x' := F - two * D
    let y' := E * (D - x') - eight * C
    let z' := two * p.y * p.z
    ⟨x', y', z'⟩

@[inline] def neg (p : G2) : G2 := ⟨p.x, -p.y, p.z⟩

/-- Jacobian addition (Bernstein–Lange 2007). -/
def add (p q : G2) : G2 :=
  if p.z.isZero then q else
  if q.z.isZero then p else
    let two := Fp2.ofFp (Fp.ofNat 2)
    let z1z1 := p.z * p.z
    let z2z2 := q.z * q.z
    let u1   := p.x * z2z2
    let u2   := q.x * z1z1
    let s1   := p.y * q.z * z2z2
    let s2   := q.y * p.z * z1z1
    if u1.beq u2 then
      if s1.beq s2 then double p else zero
    else
      let h := u2 - u1
      let i := (two * h) * (two * h)
      let j := h * i
      let r := two * (s2 - s1)
      let v := u1 * i
      let x' := r * r - j - two * v
      let y' := r * (v - x') - two * s1 * j
      let z' := ((p.z + q.z) * (p.z + q.z) - z1z1 - z2z2) * h
      ⟨x', y', z'⟩

instance : Add G2 := ⟨add⟩
instance : Neg G2 := ⟨neg⟩

/-- Project a Jacobian point to affine `(x, y)`. Undefined at infinity. -/
def toAffine (p : G2) : Fp2 × Fp2 :=
  if p.z.isZero then (Fp2.zero, Fp2.zero)
  else
    let zinv  := p.z.inverse
    let zinv2 := zinv * zinv
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Scalar multiplication via double-and-add. -/
def mulNat (p : G2) (k : Nat) : G2 :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

@[inline] def mul (p : G2) (s : Fr) : G2 := mulNat p s.val

end G2

end EthCryptographySpecs.Bls
