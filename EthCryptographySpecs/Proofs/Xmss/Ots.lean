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
@[simp] theorem chain_zero : chain pp epoch index start 0 value = value := rfl

/-- Walking `s₁` steps then `s₂` more is walking `s₁ + s₂` steps. -/
theorem chain_add :
    chain pp epoch index (start + s₁) s₂ (chain pp epoch index start s₁ value)
      = chain pp epoch index start (s₁ + s₂) value := by
  induction s₂ with
  | zero => rfl
  | succ s ih =>
    -- The last step leaves `start + s₁ + s`, the same as `start + (s₁ + s)`.
    show chainStep pp epoch index (start + s₁ + s) _ = _
    rw [ih, Nat.add_assoc]
    rfl

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
  rw [Nat.zero_add] at hsplit
  -- Steps revealed plus steps walked is the whole chain.
  have hsteps : (x[i]'hi : Nat) + (CHAIN_LENGTH - 1 - (x[i]'hi : Nat))
      = CHAIN_LENGTH - 1 := by
    simp only [CHAIN_LENGTH, W] at hb ⊢
    omega
  rw [hsplit, hsteps]

/-! ## Known answer -/

/-- Pins the chain step's call site and its position `8 * index + step`. -/
theorem chainStep_known_answer :
    (chainStep (Vector.ofFn fun i => UInt8.ofNat i.val) 7 ⟨3, by decide⟩ 5
      (Vector.replicate 16 0xaa)).toArray =
        #[0x5a, 0x8e, 0x56, 0x75, 0x52, 0x2c, 0x4c, 0xfb,
          0xf8, 0x28, 0x55, 0x6b, 0xa4, 0xd5, 0x7b, 0x0d] := by
  decide +kernel

end EthCryptographySpecs.Xmss
