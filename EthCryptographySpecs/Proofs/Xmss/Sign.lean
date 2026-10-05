import EthCryptographySpecs.Xmss.Sign
import EthCryptographySpecs.Proofs.Xmss.KeyGen

/-!
# Proofs: `Xmss.Sign`
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

variable {pp : PublicParam} {seed : Seed} {msg : Message} {epoch : Epoch}
  {rnd : Randomness} {x : Vector (Fin CHAIN_LENGTH) V}

/-! ## Grinding -/

/-- Grinding only ever returns an admissible randomizer, with its digits. -/
theorem findRandomness_wotsEncode :
    ∀ {trial fuel : Nat},
      Internal.findRandomness pp seed msg epoch trial fuel = some (rnd, x) →
        wotsEncode pp msg rnd epoch = some x := by
  intro trial fuel
  induction fuel generalizing trial with
  | zero => simp [Internal.findRandomness]
  | succ fuel ih =>
    intro hs
    simp only [Internal.findRandomness] at hs
    split at hs
    -- The attempt that stopped the search is the one returned.
    · rename_i h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      exact h
    -- A rejected attempt hands the search to the next one.
    · exact ih hs

/-- Grinding returns the first admissible attempt within its budget.

So the randomizer is a function of the key, message and epoch alone. -/
theorem findRandomness_first :
    ∀ {trial fuel : Nat},
      Internal.findRandomness pp seed msg epoch trial fuel = some (rnd, x) →
        ∃ t, trial ≤ t ∧ t < trial + fuel ∧
          rnd = randomizer pp seed msg epoch t ∧
          ∀ t', trial ≤ t' → t' < t →
            wotsEncode pp msg (randomizer pp seed msg epoch t') epoch
              = none := by
  intro trial fuel
  induction fuel generalizing trial with
  | zero => simp [Internal.findRandomness]
  | succ fuel ih =>
    intro hs
    simp only [Internal.findRandomness] at hs
    split at hs
    -- The current attempt is admissible: nothing before it was tried.
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
      exact ⟨trial, Nat.le_refl _, by omega, rfl, fun _ _ _ => by omega⟩
    -- The current attempt failed: the search resumes one attempt later.
    · rename_i hnone
      obtain ⟨t, h₁, h₂, hr, hfirst⟩ := ih hs
      refine ⟨t, by omega, by omega, hr, fun t' h₁' h₂' => ?_⟩
      rcases Nat.eq_or_lt_of_le h₁' with rfl | hlt
      · exact hnone
      · exact hfirst t' (by omega) h₂'

/-! ## Signing -/

variable {sk : SecretKey} {σ : Signature}

/-- Signing rejects the epoch exactly when it is outside the key's range. -/
theorem sign_eq_error_epochOutOfRange :
    sign sk msg epoch
        = .error (.epochOutOfRange epoch sk.epochStart sk.epochEnd)
      ↔ epoch < sk.epochStart ∨ sk.epochEnd < epoch := by
  unfold sign
  split
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    simp [h]
  · rename_i h
    constructor
    -- In range, the only failure left is grinding, a different error.
    · intro he
      dsimp only at he
      split at he <;> simp at he
    · intro h'
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      exact absurd h' h

/-- What an accepted signature is made of.

- The epoch is in the key's range.
- The randomizer is admissible.
- The chain elements and the co-path are the honest ones. -/
theorem sign_eq_ok (h : sign sk msg epoch = .ok σ) :
    sk.epochStart ≤ epoch ∧ epoch ≤ sk.epochEnd ∧
      ∃ x, wotsEncode sk.publicParam msg σ.randomness epoch = some x ∧
        σ.chainElements =
          otsReveal sk.publicParam epoch
            (otsSecretKey sk.publicParam sk.seed epoch) x ∧
        σ.merklePath = sk.tree.authPath sk.leaves epoch := by
  unfold sign at h
  split at h
  · exact absurd h (by simp)
  · rename_i hr
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, UInt32.not_lt] at hr
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i rnd' x' hf
      cases Except.ok.inj h
      exact ⟨hr.1, hr.2, x', findRandomness_wotsEncode hf, rfl, rfl⟩

/-! ## Known answer -/

/-- Signing at epoch 7 gives the reference signature. -/
theorem sign_known_answer :
    (keyGen exampleSeed 6 8 >>= fun (sk, _) =>
      sign sk exampleMessage 7).toOption = some exampleSignature := by
  -- Grinding takes thousands of attempts, so native evaluation again.
  native_decide

/-- An epoch outside the range rejects, before any hashing. -/
theorem sign_out_of_range :
    (keyGen exampleSeed 6 8 >>= fun (sk, _) =>
      sign sk exampleMessage 9).toOption.isNone := by
  decide +kernel

end EthCryptographySpecs.Xmss
