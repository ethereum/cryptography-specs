import EthCryptographySpecs.Bls.Fp
import EthCryptographySpecs.Bls.Fr

/-!
# `G1`

The curve `E : y² = x³ + 4` over `Fp`. We represent points in **Jacobian
projective** coordinates `(X, Y, Z)` with the affine map `(x, y) =
(X/Z², Y/Z³)`. The point at infinity is encoded as any `(X, Y, 0)`.

Why projective? Affine arithmetic needs an inversion per addition,
which costs `O(log p)` muls. Jacobian doubling/adding is inversion-free,
just polynomial in the coordinates. We pay one inversion at the end
when we serialize.

Arithmetic formulas are the textbook ones from Bernstein–Lange's
[explicit-formulas database](https://hyperelliptic.org/EFD/) for short
Weierstrass curves with `a = 0`.
-/

namespace EthCryptographySpecs.Bls

/-- A G1 point in Jacobian projective coordinates. `z = 0` is the
point at infinity. -/
structure G1 where
  x : Fp
  y : Fp
  z : Fp
deriving Inhabited, BEq, Repr

namespace G1

/-- Affine generator of G1, embedded with `z = 1`. -/
def generator : G1 :=
  { x := Fp.ofNat 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
  , y := Fp.ofNat 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1
  , z := Fp.one }

/-- The point at infinity. -/
def zero : G1 := ⟨Fp.one, Fp.one, Fp.zero⟩

@[inline] def isInfinity (p : G1) : Bool := p.z.isZero

/-- Jacobian point doubling for `a = 0` curves. -/
def double (p : G1) : G1 :=
  if p.z.isZero then p else
    let A := p.x * p.x
    let B := p.y * p.y
    let C := B * B
    let D := Fp.ofNat 2 * ((p.x + B) * (p.x + B) - A - C)
    let E := Fp.ofNat 3 * A
    let F := E * E
    let x' := F - Fp.ofNat 2 * D
    let y' := E * (D - x') - Fp.ofNat 8 * C
    let z' := Fp.ofNat 2 * p.y * p.z
    ⟨x', y', z'⟩

/-- Negation: `(x, y, z) ↦ (x, −y, z)`. -/
@[inline] def neg (p : G1) : G1 := ⟨p.x, -p.y, p.z⟩

/-- Jacobian addition (Bernstein–Lange 2007). Handles all special
cases (infinity, doubling, opposite-sign points). -/
def add (p q : G1) : G1 :=
  if p.z.isZero then q else
  if q.z.isZero then p else
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
      let i := (Fp.ofNat 2 * h) * (Fp.ofNat 2 * h)
      let j := h * i
      let r := Fp.ofNat 2 * (s2 - s1)
      let v := u1 * i
      let x' := r * r - j - Fp.ofNat 2 * v
      let y' := r * (v - x') - Fp.ofNat 2 * s1 * j
      let z' := ((p.z + q.z) * (p.z + q.z) - z1z1 - z2z2) * h
      ⟨x', y', z'⟩

instance : Add G1 := ⟨add⟩
instance : Neg G1 := ⟨neg⟩

/-- Project a Jacobian point to affine `(x, y)`. Undefined at infinity. -/
def toAffine (p : G1) : Fp × Fp :=
  if p.z.isZero then (Fp.zero, Fp.zero)
  else
    let zinv  := p.z.inverse
    let zinv2 := zinv * zinv
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Scalar multiplication via double-and-add. -/
def mulNat (p : G1) (k : Nat) : G1 :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

/-- Unfolding equation for `mulNat`. Stated here because the
compiler-generated equations of a recursive definition are only
available in its defining module. -/
theorem mulNat_def (p : G1) (k : Nat) :
    mulNat p k = if k = 0 then zero
      else if k % 2 = 1 then add p (mulNat (double p) (k / 2))
      else mulNat (double p) (k / 2) := by
  rw [mulNat]

@[inline] def mul (p : G1) (s : Fr) : G1 := mulNat p s.val

/-- Multi-scalar multiplication via windowed Pippenger.

Scalars are split into `w`-bit windows; per window we bucket points by
their window value, sum each bucket once via a running-sum trick, then
combine. Roughly linear in the number of points instead of quadratic. -/
def msm (points : Array G1) (scalars : Array Fr) : G1 := Id.run do
  let n := if points.size ≤ scalars.size then points.size else scalars.size
  if n = 0 then return zero

  -- Window width: 8 bits is a reasonable default for n in the low thousands.
  -- For very small n a smaller window would be slightly faster, but the
  -- difference is small and we keep the algorithm un-tuned for clarity.
  let w := 8
  let bucketCount := 1 <<< w  -- 2^w
  let mask : Nat := bucketCount - 1

  -- Bit-length we have to process (the largest scalar's). BLS Fr is at
  -- most 255 bits but skipping leading zeros saves doublings on early
  -- windows.
  let mut maxBits : Nat := 0
  for j in [:n] do
    let v := scalars[j]!.val
    if v ≠ 0 then
      let bits := v.log2 + 1
      if bits > maxBits then maxBits := bits
  if maxBits = 0 then return zero

  let nWindows := (maxBits + w - 1) / w
  let mut acc : G1 := zero

  -- Walk windows from most-significant to least.
  let mut k : Nat := nWindows
  while k > 0 do
    k := k - 1
    -- Shift `acc` up by `w` bits (i.e. multiply by 2^w) — except on the
    -- very first iteration, where `acc = 0` and doubling is a no-op.
    if k + 1 < nWindows then
      for _ in [:w] do
        acc := double acc

    -- Bucket the points: `buckets[v]` accumulates points whose window
    -- value is `v`. Bucket 0 is unused (points with `v = 0` contribute
    -- nothing).
    let mut buckets : Array G1 := Array.replicate bucketCount zero
    for j in [:n] do
      let v := (scalars[j]!.val >>> (k * w)) &&& mask
      if v ≠ 0 then
        buckets := buckets.set! v (add buckets[v]! points[j]!)

    -- Compute Σ_{v=1}^{2^w − 1} v · buckets[v] via the running-sum trick.
    let mut running : G1 := zero
    let mut partialSum : G1 := zero
    let mut v : Nat := bucketCount - 1
    while v > 0 do
      running := add running buckets[v]!
      partialSum := add partialSum running
      v := v - 1
    acc := add acc partialSum

  return acc

end G1

end EthCryptographySpecs.Bls
