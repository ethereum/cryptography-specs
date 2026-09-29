import EthCryptographySpecs.Xmss.Ots

/-!
# Proofs: `Xmss.Ots`

Correctness of the one-time signature.
-/

set_option maxRecDepth 100000

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

variable {pp : PublicParam} {epoch : Epoch} {index : Fin V}
  {start s₁ s₂ : Nat} {value : Digest}

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    chain pp epoch index start 0 h value = value := rfl

/-- Walking `s₁` steps then `s₂` more is walking `s₁ + s₂` steps. -/
theorem chain_add (h₁ : start + s₁ < CHAIN_LENGTH)
    (h : start + s₁ + s₂ < CHAIN_LENGTH) :
    chain pp epoch index (start + s₁) s₂ h (chain pp epoch index start s₁ h₁ value)
      = chain pp epoch index start (s₁ + s₂) (by omega) value := by
  induction s₂ with
  | zero => rfl
  | succ s ih =>
    -- The last step leaves `start + s₁ + s`, the same as `start + (s₁ + s)`.
    show chainStep pp epoch index ⟨start + s₁ + s, _⟩ _ = _
    rw [ih (by omega)]
    show _ = chainStep pp epoch index ⟨start + (s₁ + s), _⟩ _
    -- The position carries its bound, so the rewrite goes through a congruence.
    congr 1
    exact Fin.ext (Nat.add_assoc _ _ _)

/-- Recovery from an honest signature returns the honest public values. -/
theorem otsRecover_otsReveal (pp : PublicParam) (epoch : Epoch)
    (sk : Vector Digest V) (x : Vector (Fin CHAIN_LENGTH) V) :
    otsRecover pp epoch (otsReveal pp epoch sk x) x
      = otsPublicKey pp epoch sk := by
  apply Vector.ext
  intro i hi
  have hb := (x[i]'hi).isLt
  simp only [otsRecover, otsReveal, otsPublicKey, Vector.getElem_ofFn,
    Fin.getElem_fin]
  -- The signer walks to the digit, the verifier walks the rest of the way.
  have hsplit := chain_add (pp := pp) (epoch := epoch) (index := ⟨i, hi⟩)
    (start := 0) (s₁ := (x[i]'hi : Nat))
    (s₂ := CHAIN_LENGTH - 1 - (x[i]'hi : Nat)) (value := sk[i]'hi)
    (by simp) (by omega)
  simp only [Nat.zero_add] at hsplit
  rw [hsplit]
  -- Steps revealed plus steps walked is the whole chain.
  congr 1
  omega

/-! ## Known answer -/

/-- Pins the chain step's call site and its position `8 * index + step`. -/
theorem chainStep_known_answer :
    (chainStep (Vector.ofFn fun i => UInt8.ofNat i.val) 7 ⟨3, by decide⟩
      ⟨5, by decide⟩ (Vector.replicate 16 0xaa)).toArray =
        #[0x5a, 0x8e, 0x56, 0x75, 0x52, 0x2c, 0x4c, 0xfb,
          0xf8, 0x28, 0x55, 0x6b, 0xa4, 0xd5, 0x7b, 0x0d] := by
  decide +kernel

end EthCryptographySpecs.Xmss
