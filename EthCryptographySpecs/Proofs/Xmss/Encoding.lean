import EthCryptographySpecs.Xmss.Encoding

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
