import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Proofs.Bls.FrZMod
import EthCryptographySpecs.Proofs.Kzg.BitReversal
import EthCryptographySpecs.Proofs.Kzg.Polynomials
import Batteries.Data.Array.Lemmas

/-!
# Proofs: the roots-of-unity evaluation domain

Characterizes `rootsOfUnityBrp n` for power-of-two `n` dividing
`r - 1`: element `i` is `ω ^ reverseBits i n` for `ω` a primitive
`n`-th root of unity (`domainRoot`), the elements are pairwise
distinct, and membership is exactly "is an `n`-th root of unity"
(`mem_rootsOfUnityBrp`). The `idxOf?` bridges translate the two
branches of `evaluatePolynomialInEvaluationFormAux` into algebra:
a hit pins down `z` as a domain element, and a miss means
`z ^ n ≠ 1` — in particular no barycentric denominator `z - D[i]`
vanishes (`sub_getElem_ne_zero_of_idxOf?_eq_none`).

Uses the scoped `Field Fr` instance from `Proofs.Bls.FrZMod`.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)
open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal
open scoped EthCryptographySpecs.Bls.Fr

-- See the note in `Proofs.Bls.FrZMod`: core's grind-tactic `HPow`
-- instance on `Fin` shadows Mathlib's monoid power on `Fr` and breaks
-- `rw` with Mathlib `pow` lemmas. File-local, so repeated here.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- The blob width is the power of two the bit-reversal lemmas expect. -/
theorem field_elements_per_blob_eq_two_pow :
    FIELD_ELEMENTS_PER_BLOB = 2 ^ 12 := rfl

/-- The blob width divides `r - 1`, so a primitive
`FIELD_ELEMENTS_PER_BLOB`-th root of unity exists. -/
theorem field_elements_per_blob_dvd_modulus_sub_one :
    FIELD_ELEMENTS_PER_BLOB ∣ BLS_MODULUS - 1 :=
  Nat.dvd_of_mod_eq_zero (by decide)

/-- The root of unity `computeRootsOfUnity order` builds its powers
from: `7 ^ ((r - 1) / order)`. -/
def domainRoot (order : Nat) : Fr :=
  Fr.ofNat PRIMITIVE_ROOT_OF_UNITY ^ Fr.ofNat ((BLS_MODULUS - 1) / order)

/-- `domainRoot order` is a primitive `order`-th root of unity whenever
`order ∣ r - 1`. -/
theorem isPrimitiveRoot_domainRoot {order : Nat}
    (h : order ∣ BLS_MODULUS - 1) :
    IsPrimitiveRoot (domainRoot order) order :=
  Bls.Fr.isPrimitiveRoot_ofNat_seven_pow h

/-- `computeRootsOfUnity order` lists the powers of `domainRoot order`
in order: element `i` is `ω ^ i`. -/
theorem getElem_computeRootsOfUnity (order i : Nat)
    (h : i < (computeRootsOfUnity order).size) :
    (computeRootsOfUnity order)[i] = domainRoot order ^ i := by
  show (computePowers (domainRoot order) order)[i] = _
  rw [getElem_computePowers]
  exact Bls.Fr.powNat_eq_pow _ _

/-- Element `i` of the bit-reversed domain is `ω ^ reverseBits i n`.
The power-of-two hypothesis is phrased as an equation so the lemma
applies directly to width constants like `FIELD_ELEMENTS_PER_BLOB`
(with `hnk := field_elements_per_blob_eq_two_pow`). -/
theorem getElem_rootsOfUnityBrp {n k : Nat} (hnk : n = 2 ^ k) (i : Nat)
    (h : i < (rootsOfUnityBrp n).size) :
    (rootsOfUnityBrp n)[i] = domainRoot n ^ reverseBits i n := by
  subst hnk
  have hrev : reverseBits i (2 ^ k) < (computeRootsOfUnity (2 ^ k)).size := by
    rw [size_computeRootsOfUnity]
    exact reverseBits_lt_two_pow i k
  have hsize : i < (bitReversalPermutation (computeRootsOfUnity (2 ^ k))).size := h
  show (bitReversalPermutation (computeRootsOfUnity (2 ^ k)))[i] = _
  rw [getElem_bitReversalPermutation, size_computeRootsOfUnity,
      getElem!_pos (computeRootsOfUnity (2 ^ k)) (reverseBits i (2 ^ k)) hrev,
      getElem_computeRootsOfUnity]

/-- The bit-reversed domain has no repeated elements. -/
theorem getElem_rootsOfUnityBrp_inj {n k : Nat} (hnk : n = 2 ^ k)
    (hdvd : n ∣ BLS_MODULUS - 1) {i j : Nat}
    (hi : i < n) (hj : j < n)
    (h : (rootsOfUnityBrp n)[i]! = (rootsOfUnityBrp n)[j]!) :
    i = j := by
  subst hnk
  have hsi : i < (rootsOfUnityBrp (2 ^ k)).size := by
    rwa [size_rootsOfUnityBrp]
  have hsj : j < (rootsOfUnityBrp (2 ^ k)).size := by
    rwa [size_rootsOfUnityBrp]
  rw [getElem!_pos (rootsOfUnityBrp (2 ^ k)) i hsi,
      getElem!_pos (rootsOfUnityBrp (2 ^ k)) j hsj,
      getElem_rootsOfUnityBrp rfl, getElem_rootsOfUnityBrp rfl] at h
  have hrev := (isPrimitiveRoot_domainRoot hdvd).pow_inj
    (reverseBits_lt_two_pow i k) (reverseBits_lt_two_pow j k) h
  have := congrArg (reverseBits · (2 ^ k)) hrev
  simpa [reverseBits_reverseBits hi, reverseBits_reverseBits hj] using this

/-- The bit-reversed domain enumerates exactly the `2 ^ k`-th roots of
unity: `z` occurs in it iff `z ^ (2 ^ k) = 1`. -/
theorem mem_rootsOfUnityBrp {n k : Nat} (hnk : n = 2 ^ k)
    (hdvd : n ∣ BLS_MODULUS - 1) (z : Fr) :
    z ∈ rootsOfUnityBrp n ↔ z ^ n = 1 := by
  subst hnk
  have hprim := isPrimitiveRoot_domainRoot hdvd
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hz
    -- Restated `have`s pin Mathlib facts to this goal's instance path
    -- so the `rw`s below match (see the elaboration notes in the plan).
    have hone : domainRoot (2 ^ k) ^ 2 ^ k = 1 := hprim.pow_eq_one
    rw [getElem_rootsOfUnityBrp rfl i hi, ← pow_mul, Nat.mul_comm, pow_mul,
        hone]
    exact one_pow _
  · intro hz
    have : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
    obtain ⟨i, hik, hi⟩ := hprim.eq_pow_of_pow_eq_one hz
    refine Array.mem_iff_getElem.mpr ⟨reverseBits i (2 ^ k), ?_, ?_⟩
    · rw [size_rootsOfUnityBrp]
      exact reverseBits_lt_two_pow i k
    · rw [getElem_rootsOfUnityBrp rfl, reverseBits_reverseBits hik]
      exact hi

/-- A domain hit locates `z`: if `idxOf?` answers `some i`, then `i` is
in range and `z` is element `i` of the domain. Generic in the domain
size (no power-of-two hypothesis needed). -/
theorem idxOf?_rootsOfUnityBrp_eq_some {n : Nat} {z : Fr} {i : Nat}
    (h : (rootsOfUnityBrp n).idxOf? z = some i) :
    i < n ∧ (rootsOfUnityBrp n)[i]! = z := by
  rw [← Array.idxOf?_toList] at h
  obtain ⟨hlen, heq, -⟩ := List.idxOf?_eq_some_iff.mp h
  have hsize : i < (rootsOfUnityBrp n).size := by simpa using hlen
  refine ⟨by simpa using hsize, ?_⟩
  rw [getElem!_pos (rootsOfUnityBrp n) i hsize]
  simpa using heq

/-- A domain miss means `z` is not an `n`-th root of unity. -/
theorem pow_ne_one_of_idxOf?_eq_none {n k : Nat} (hnk : n = 2 ^ k)
    (hdvd : n ∣ BLS_MODULUS - 1) {z : Fr}
    (h : (rootsOfUnityBrp n).idxOf? z = none) :
    z ^ n ≠ 1 := fun hpow =>
  Array.idxOf?_eq_none_iff.mp h ((mem_rootsOfUnityBrp hnk hdvd z).mpr hpow)

/-- On a domain miss, no barycentric denominator vanishes:
`z - D[i] ≠ 0` for every in-range `i`. Generic in the domain size. -/
theorem sub_getElem_ne_zero_of_idxOf?_eq_none {n : Nat} {z : Fr}
    (h : (rootsOfUnityBrp n).idxOf? z = none) {i : Nat} (hi : i < n) :
    z - (rootsOfUnityBrp n)[i]! ≠ 0 := by
  have hsi : i < (rootsOfUnityBrp n).size := by rwa [size_rootsOfUnityBrp]
  have hz : z ∉ rootsOfUnityBrp n := Array.idxOf?_eq_none_iff.mp h
  rw [getElem!_pos (rootsOfUnityBrp n) i hsi]
  exact sub_ne_zero_of_ne fun hzeq =>
    hz (hzeq ▸ Array.mem_iff_getElem.mpr ⟨i, hsi, rfl⟩)

end EthCryptographySpecs.Kzg
