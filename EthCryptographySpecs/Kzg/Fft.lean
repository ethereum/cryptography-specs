import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Constants

/-!
# `Fft`

Number-theoretic transforms over `Fr`, including a coset variant.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

open EthCryptographySpecs.Kzg.Constants

/-- Every other element of `xs`, starting at index `start`. -/
def fftHalve (xs : Array Fr) (start : Nat) : Array Fr :=
  Array.ofFn (n := xs.size / 2) fun i => xs[start + 2 * i.val]!

/-- Cooley-Tukey radix-2 forward FFT. `rootsOfUnity` must have the same
length as `vals`. -/
def fftFieldAux
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    : Array Fr :=
  if vals.size ≤ 1 then
    vals
  else
    let halfRoots := fftHalve rootsOfUnity 0
    let l := fftFieldAux (fftHalve vals 0) halfRoots
    let r := fftFieldAux (fftHalve vals 1) halfRoots
    let n := vals.size
    let halfL := l.size  -- = n / 2
    -- Butterfly: for each `i ∈ [0, n/2)` let `t = r[i] * rootsOfUnity[i]`,
    -- then write `l[i] + t` to `o[i]` and `l[i] - t` to `o[i + n/2]`.
    -- The same root index `i` (not `i + n/2`) is used for both halves.
    Array.ofFn (n := n) fun i =>
      let baseIdx     := if i.val < halfL then i.val else i.val - halfL
      let lAt         := l[baseIdx]!
      let rAt         := r[baseIdx]!
      let yTimesRoot  := rAt * rootsOfUnity[baseIdx]!
      if i.val < halfL then lAt + yTimesRoot
      else                  lAt - yTimesRoot
termination_by vals.size
decreasing_by all_goals (simp [fftHalve]; omega)

/-- Forward (`inv = false`) or inverse FFT (`inv = true`) over `vals`.
The inverse reverses the roots of unity and divides each output by
`len(vals)`. -/
def fftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  if inv then
    let invlen := (Fr.ofNat vals.size).inverse
    -- Reverse: keep roots[0] then reverse roots[1..]
    let reversed := Array.ofFn (n := rootsOfUnity.size) fun i =>
      if i.val = 0 then rootsOfUnity[0]!
      else rootsOfUnity[rootsOfUnity.size - i.val]!
    (fftFieldAux vals reversed).map (· * invlen)
  else
    fftFieldAux vals rootsOfUnity

/-- Multiply successive elements of `vals` by successive powers of
`factor`, starting at `shift`. -/
def shiftValsAux (factor : Fr) : Fr → List Fr → List Fr
  | _, [] => []
  | shift, v :: rest => (v * shift) :: shiftValsAux factor (shift * factor) rest

/-- Multiply `vals[i]` by `factor ^ i`, shifting the values onto a coset. -/
def shiftVals
    (vals : Array Fr) (factor : Fr)
    : Array Fr :=
  (shiftValsAux factor Fr.one vals.toList).toArray

/-- FFT/IFFT over a coset of the roots of unity. Useful for dividing by
a polynomial that vanishes on the unshifted domain. -/
def cosetFftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  let shiftFactor : Fr := Fr.ofNat PRIMITIVE_ROOT_OF_UNITY
  if inv then
    let post := fftField vals rootsOfUnity inv
    shiftVals post shiftFactor.inverse
  else
    let pre := shiftVals vals shiftFactor
    fftField pre rootsOfUnity inv

end EthCryptographySpecs.Kzg
