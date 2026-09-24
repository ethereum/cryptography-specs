import EthCryptographySpecs.Xmss.Encoding
import Mathlib.Tactic

/-!
# Proofs: `Xmss.Encoding`

What an accepted encoding is, and what it guarantees.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

variable {pp : PublicParam} {msg : Message} {rnd : Randomness} {epoch : Epoch}
  {x : Vector (Fin CHAIN_LENGTH) V}

/-- Acceptance returns the digest's own digits. -/
theorem wotsEncode_eq_digits (h : wotsEncode pp msg rnd epoch = some x) :
    x = Internal.digits
      (tweakHash pp .encoding 0 epoch (encodingPayload msg rnd)) := by
  -- Only the accepting branch produces a result, and it returns the digits.
  simp only [wotsEncode] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h (by simp)

/-- An accepted encoding has both spare bits zero. -/
theorem padded_of_wotsEncode (h : wotsEncode pp msg rnd epoch = some x) :
    Internal.padded
      (tweakHash pp .encoding 0 epoch (encodingPayload msg rnd)) = true := by
  simp only [wotsEncode] at h
  split at h
  · simp_all
  · exact absurd h (by simp)

/-- An accepted encoding's digits sum to the target.

A fixed sum is what fixes the verifier's step count. -/
theorem sum_of_wotsEncode (h : wotsEncode pp msg rnd epoch = some x) :
    x.foldl (fun sum d => sum + d.val) 0 = TARGET_SUM := by
  simp only [wotsEncode] at h
  split at h
  · rename_i hcond
    obtain ⟨_, htarget⟩ := (Bool.and_eq_true _ _).mp hcond
    rw [← Option.some_inj.mp h]
    -- The narrow rewrite keeps the digest from being evaluated.
    simp only [Internal.onTarget, beq_iff_eq] at htarget
    exact htarget
  · exact absurd h (by simp)

/-! ## Incomparability

Distinct codewords must each exceed the other somewhere.

Chains only ever walk forward.

So a signature for one codeword reaches another only if that one dominates it.

A constant digit sum rules that out. -/

/-- The digit sum the specification folds is the sum over indices.

Stated so the codeword sum can be handled with ordinary sum lemmas. -/
theorem digitSum_eq_sum (x : Vector (Fin CHAIN_LENGTH) V) :
    x.foldl (fun sum d => sum + d.val) 0 = ∑ i : Fin V, (x[i] : Nat) := by
  -- A vector fold is a fold over its list.
  have h1 : x.foldl (fun sum d => sum + d.val) 0
      = x.toList.foldl (fun sum d => sum + d.val) 0 := by
    obtain ⟨arr, harr⟩ := x
    simp [Array.foldl_toList]
  -- Adding the digit values is summing the mapped list.
  have h2 : x.toList.foldl (fun sum d => sum + d.val) 0
      = (x.toList.map Fin.val).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
  -- A vector is the tabulation of its entries, so that list sum is indexed.
  have h3 : (x.toList.map Fin.val).sum = ∑ i : Fin V, (x[i] : Nat) := by
    conv_lhs => rw [← Vector.ofFn_getElem (xs := x)]
    rw [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [h1, h2, h3]

/-- Pointwise domination with equal sums forces equality. -/
theorem eq_of_le_of_sum_eq {x y : Vector (Fin CHAIN_LENGTH) V}
    (hle : ∀ i : Fin V, (x[i] : Nat) ≤ (y[i] : Nat))
    (hsum : ∑ i : Fin V, (x[i] : Nat) = ∑ i : Fin V, (y[i] : Nat)) : x = y := by
  by_contra hne
  -- Unequal vectors differ at some index.
  obtain ⟨j, hj⟩ : ∃ j : Fin V, (x[j] : Nat) ≠ (y[j] : Nat) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (Vector.ext fun i hi => Fin.val_inj.mp (hall ⟨i, hi⟩))
  -- One strict index among weak ones makes the whole sum strict.
  have hlt : ∑ i : Fin V, (x[i] : Nat) < ∑ i : Fin V, (y[i] : Nat) :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hle j) hj⟩
  omega

/-- Two accepted encodings are equal, or each exceeds the other somewhere.

Neither can be reached from the other by walking chains forward. -/
theorem wotsEncode_incomparable
    {pp₁ pp₂ : PublicParam} {m₁ m₂ : Message} {r₁ r₂ : Randomness}
    {e₁ e₂ : Epoch} {x y : Vector (Fin CHAIN_LENGTH) V}
    (h₁ : wotsEncode pp₁ m₁ r₁ e₁ = some x)
    (h₂ : wotsEncode pp₂ m₂ r₂ e₂ = some y) (hne : x ≠ y) :
    (∃ i : Fin V, (x[i] : Nat) < (y[i] : Nat)) ∧
      (∃ i : Fin V, (y[i] : Nat) < (x[i] : Nat)) := by
  -- Acceptance pins both sums to the target, so the two sums agree.
  have hx : ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
    rw [← digitSum_eq_sum]; exact sum_of_wotsEncode h₁
  have hy : ∑ i : Fin V, (y[i] : Nat) = TARGET_SUM := by
    rw [← digitSum_eq_sum]; exact sum_of_wotsEncode h₂
  constructor
  -- Were one never to exceed the other, equal sums would make them equal.
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno (hy.trans hx.symm)).symm
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno (hx.trans hy.symm))

/-! ## Known answer

Pins the bit layout: which half a digit comes from, and where in that half. -/

/-- A digest whose 42 digits are spread across both halves and all widths. -/
theorem digits_known_answer :
    (Internal.digits
      ⟨#[0xfc, 0x04, 0x19, 0xbf, 0xf7, 0xd7, 0x8b, 0x7f,
         0xae, 0x81, 0x32, 0xe6, 0xed, 0xf6, 0x2b, 0x7f], rfl⟩).toList.map
        Fin.val =
      [4, 7, 3, 2, 0, 2, 6, 0, 7, 7, 6, 3, 7, 7, 5, 6, 3, 1, 6, 7, 7,
       6, 5, 6, 0, 0, 5, 4, 1, 6, 4, 7, 6, 6, 5, 5, 7, 3, 5, 4, 7, 7] := by
  decide +kernel

end EthCryptographySpecs.Xmss
