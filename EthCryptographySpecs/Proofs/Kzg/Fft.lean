import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Proofs.Bls.Fr

/-!
# Proofs: `Fft`

Shape and element-wise properties of the FFT helpers: every transform in
this file preserves the size of its input, `fftHalve` picks out every
other element, and `shiftVals` multiplies element `i` by `factor ^ i`.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

@[simp] theorem size_fftHalve (xs : Array Fr) (start : Nat) :
    (fftHalve xs start).size = xs.size / 2 := by
  simp [fftHalve]

/-- `fftHalve` picks out every other element, starting at `start`. -/
theorem getElem_fftHalve (xs : Array Fr) (start i : Nat)
    (h : i < (fftHalve xs start).size) :
    (fftHalve xs start)[i] = xs[start + 2 * i]! := by
  simp [fftHalve]

@[simp] theorem size_fftFieldAux (vals rootsOfUnity : Array Fr) :
    (fftFieldAux vals rootsOfUnity).size = vals.size := by
  rw [fftFieldAux]
  split
  · rfl
  · simp

@[simp] theorem size_fftField (vals rootsOfUnity : Array Fr) (inv : Bool) :
    (fftField vals rootsOfUnity inv).size = vals.size := by
  cases inv <;> simp [fftField]

@[simp] theorem length_shiftValsAux (factor shift : Fr) (l : List Fr) :
    (shiftValsAux factor shift l).length = l.length := by
  induction l generalizing shift with
  | nil => rfl
  | cons v rest ih => simp [shiftValsAux, ih]

@[simp] theorem size_shiftVals (vals : Array Fr) (factor : Fr) :
    (shiftVals vals factor).size = vals.size := by
  simp [shiftVals]

/-- Element `i` of `shiftValsAux factor shift l` is
`l[i] * (shift * factor ^ i)`. -/
theorem getElem_shiftValsAux (factor shift : Fr) (l : List Fr) (i : Nat)
    (h : i < (shiftValsAux factor shift l).length) :
    (shiftValsAux factor shift l)[i] =
      l[i]'(by rwa [length_shiftValsAux] at h) *
        (shift * Fr.powNat factor i) := by
  induction l generalizing shift i with
  | nil => exact absurd h (by simp)
  | cons v rest ih =>
    cases i with
    | zero =>
      simp only [shiftValsAux, List.getElem_cons_zero, Fr.powNat_zero,
        Fr.mul_mul_one]
    | succ i =>
      simp only [shiftValsAux, List.getElem_cons_succ]
      rw [ih, Fr.powNat_succ, ← Fr.mul_assoc shift factor]

/-- Element `i` of `shiftVals vals factor` is `vals[i] * factor ^ i`. -/
theorem getElem_shiftVals (vals : Array Fr) (factor : Fr) (i : Nat)
    (h : i < (shiftVals vals factor).size) :
    (shiftVals vals factor)[i] =
      vals[i]'(by rwa [size_shiftVals] at h) * Fr.powNat factor i := by
  have hl : i < (shiftValsAux factor Fr.one vals.toList).length := by
    simpa [shiftVals] using h
  show (shiftValsAux factor Fr.one vals.toList).toArray[i] = _
  rw [List.getElem_toArray, getElem_shiftValsAux factor Fr.one vals.toList i hl,
    Fr.mul_one_mul, Array.getElem_toList]

@[simp] theorem size_cosetFftField (vals rootsOfUnity : Array Fr)
    (inv : Bool) :
    (cosetFftField vals rootsOfUnity inv).size = vals.size := by
  cases inv <;> simp [cosetFftField]

end EthCryptographySpecs.Kzg
