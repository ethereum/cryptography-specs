import EthCryptographySpecs.Proofs.Xmss.Encoding

/-!
# Proofs: the size of the target-sum code

The code is every string of 42 digits, each from 0 to 7, summing to 195.

Its size fixes how often one grinding attempt lands in the code.

```text
|C| = sum over b of (-1)^b * C(42, b) * C(195 - 8b + 41, 41)
|C| / 2^128 >= 2^-15
```
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-- The number of codewords. -/
def CODE_SIZE : ℕ := 11539185377238682781344003244544752

/-! ## Counting digit strings -/

/-- Strings of `n` digits below `k` that sum to `s`. -/
abbrev DigitStrings (n k s : ℕ) := {x : Fin n → Fin k // ∑ i, (x i : ℕ) = s}

/-- Only the empty string has no digits, and it sums to 0. -/
theorem card_digitStrings_zero (k s : ℕ) :
    Fintype.card (DigitStrings 0 k s) = if s = 0 then 1 else 0 := by
  split <;> rename_i h <;> simp [DigitStrings, Fintype.card_subtype, h, eq_comm]

/-- Fixing the first digit `d` leaves the rest to sum to `s - d`. -/
theorem card_digitStrings_succ (n k s : ℕ) :
    Fintype.card (DigitStrings (n + 1) k s)
      = ∑ d ∈ Finset.range k,
          if d ≤ s then Fintype.card (DigitStrings n k (s - d)) else 0 := by
  -- Split a string into its first digit and the rest.
  let e : DigitStrings (n + 1) k s
      ≃ Σ d : Fin k, {y : Fin n → Fin k // (d : ℕ) + ∑ i, (y i : ℕ) = s} :=
    { toFun := fun x => ⟨x.1 0, Fin.tail x.1, by
        have h := x.2
        rw [Fin.sum_univ_succ] at h
        exact h⟩
      invFun := fun p => ⟨Fin.cons p.1 p.2.1, by
        rw [Fin.sum_univ_succ]; simpa using p.2.2⟩
      left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma,
    ← Fin.sum_univ_eq_sum_range (fun d =>
      if d ≤ s then Fintype.card (DigitStrings n k (s - d)) else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  split
  -- A first digit up to `s` leaves exactly `s - d` for the rest.
  · rename_i hd
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun y => by omega)
  -- A first digit above `s` overshoots on its own.
  · rename_i hd
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun y => by have := y.2; omega⟩

/-! ## The same count by dynamic programming

Row `n` lists the counts for length `n`, one entry per sum up to a bound.

Each row is the previous one, added to itself shifted by every digit. -/

/-- A row, added to itself shifted by each of the first `d` digits. -/
def shiftAdd (r : List ℕ) : ℕ → List ℕ
  | 0 => List.replicate r.length 0
  | d + 1 => List.zipWith (· + ·) (shiftAdd r d) (List.replicate d 0 ++ r)

/-- Counts of `n`-digit strings with digits below `k`, for each sum. -/
def countRow (k bound : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate bound 0
  | n + 1 => shiftAdd (countRow k bound n) k

/-- Adding two rows adds their entries, wherever both have one. -/
theorem getD_zipWith_add {a b : List ℕ} {s : ℕ} (ha : s < a.length)
    (hb : s < b.length) :
    (List.zipWith (· + ·) a b).getD s 0 = a.getD s 0 + b.getD s 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

/-- Shifting a row by `d` puts `d` zeros in front of it. -/
theorem getD_shift (r : List ℕ) (d s : ℕ) :
    (List.replicate d 0 ++ r).getD s 0
      = if d ≤ s then r.getD (s - d) 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_replicate, List.getElem?_replicate]
  -- Below the shift the entry is a padding zero, above it a row entry.
  split <;> split <;> first | omega | simp_all

/-- Shifting keeps the length, and entry `s` gathers one term per digit. -/
theorem shiftAdd_spec (r : List ℕ) :
    ∀ d, (shiftAdd r d).length = r.length ∧
      ∀ s < r.length, (shiftAdd r d).getD s 0
        = ∑ j ∈ Finset.range d, if j ≤ s then r.getD (s - j) 0 else 0 := by
  intro d
  induction d with
  | zero =>
    refine ⟨by simp [shiftAdd], fun s hs => ?_⟩
    simp [shiftAdd, List.getD_eq_getElem?_getD, hs]
  | succ d ih =>
    obtain ⟨hlen, hget⟩ := ih
    refine ⟨by simp [shiftAdd, hlen], fun s hs => ?_⟩
    -- Both rows have entry `s`, so the sum has it too.
    rw [shiftAdd, getD_zipWith_add (by omega) (by simp; omega), hget s hs,
      getD_shift, Finset.sum_range_succ]

/-- Every row has one entry per sum, from 0 to the bound. -/
theorem countRow_length (k bound n : ℕ) :
    (countRow k bound n).length = bound + 1 := by
  induction n with
  | zero => simp [countRow]
  | succ n ih => rw [countRow, (shiftAdd_spec _ k).1, ih]

/-- The dynamic program counts the digit strings. -/
theorem countRow_eq_card (k bound : ℕ) :
    ∀ n, ∀ s ≤ bound,
      (countRow k bound n).getD s 0 = Fintype.card (DigitStrings n k s) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rw [card_digitStrings_zero]
    rcases s with _ | s <;> simp [countRow, List.getD_eq_getElem?_getD]
    -- Entries past the first are the zeros the row starts with.
    rw [List.getElem?_replicate]
    split <;> simp
  | succ n ih =>
    intro s hs
    rw [countRow, (shiftAdd_spec _ k).2 s (by rw [countRow_length]; omega),
      card_digitStrings_succ]
    -- Each term reads an earlier entry of the previous row.
    refine Finset.sum_congr rfl fun d _ => ?_
    split
    · exact ih (s - d) (by omega)
    · rfl

/-! ## The size of the code -/

/-- The number of codewords. -/
theorem card_digitStrings_code :
    Fintype.card (DigitStrings V CHAIN_LENGTH TARGET_SUM)
      = CODE_SIZE := by
  rw [← countRow_eq_card CHAIN_LENGTH TARGET_SUM V TARGET_SUM (le_refl _)]
  -- About 66,000 additions of large numbers, which the kernel evaluates.
  decide +kernel

/-- The inclusion-exclusion count gives the same number.

Term `b` corrects for `b` digits forced above 7. -/
theorem inclusion_exclusion_code :
    (∑ b ∈ Finset.range (TARGET_SUM / CHAIN_LENGTH + 1),
      (-1 : ℤ) ^ b * (Nat.choose V b : ℤ)
        * (Nat.choose (TARGET_SUM - CHAIN_LENGTH * b + V - 1) (V - 1) : ℤ))
      = CODE_SIZE := by
  -- Pascal's recursion is exponential, falling factorials are linear.
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- Codewords as the specification stores them: vectors on target. -/
theorem card_onTarget :
    Nat.card {x : Vector (Fin CHAIN_LENGTH) V // Internal.onTarget x = true}
      = CODE_SIZE := by
  -- A vector is a function from positions to digits.
  let e : {x : Vector (Fin CHAIN_LENGTH) V // Internal.onTarget x = true}
      ≃ DigitStrings V CHAIN_LENGTH TARGET_SUM :=
    { toFun := fun x => ⟨fun i => x.1[i], by
        have := x.2
        simp only [Internal.onTarget, beq_iff_eq, digitSum_eq_sum] at this
        simpa using this⟩
      invFun := fun y => ⟨Vector.ofFn y.1, by
        simp only [Internal.onTarget, beq_iff_eq, digitSum_eq_sum]
        simpa using y.2⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_digitStrings_code]

/-- The code is at least a `2^-15` share of all `2^128` digests.

The completeness bound reads that share as one attempt's chance of success. -/
theorem code_probability :
    (1 : ℚ) / 2 ^ 15
      ≤ (Fintype.card (DigitStrings V CHAIN_LENGTH TARGET_SUM) : ℚ)
        / 2 ^ 128 := by
  rw [card_digitStrings_code, CODE_SIZE]
  norm_num

end EthCryptographySpecs.Xmss
