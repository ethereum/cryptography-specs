import EthCryptographySpecs.Xmss.KeyGen
import EthCryptographySpecs.Proofs.Xmss.Verify

/-!
# Proofs: `Xmss.KeyGen`
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

variable {seed : Seed} {epochStart epochEnd : Epoch} {sk : SecretKey}
  {pk : PublicKey}

/-- Key generation fails exactly on an empty range. -/
theorem keyGen_eq_error_iff :
    (∃ err, keyGen seed epochStart epochEnd = .error err)
      ↔ epochEnd < epochStart := by
  unfold keyGen
  split
  · rename_i h
    simp only [reduceCtorEq, exists_false, false_iff, UInt32.not_lt]
    exact h
  · rename_i h
    simp only [Except.error.injEq, exists_eq', true_iff]
    exact UInt32.not_le.mp h

/-- An accepted key pair is the seed's key over the requested range. -/
theorem keyGen_eq_ok (h : keyGen seed epochStart epochEnd = .ok (sk, pk)) :
    pk = sk.publicKey ∧ sk.seed = seed ∧
      sk.epochStart = epochStart ∧ sk.epochEnd = epochEnd := by
  unfold keyGen at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exact absurd h (by simp)

/-- The leaf at an epoch hashes that epoch's one-time public key. -/
theorem leaves_toNat (sk : SecretKey) (epoch : Epoch) :
    sk.leaves epoch.toNat = otsLeaf sk.publicParam epoch
      (otsPublicKey sk.publicParam epoch
        (otsSecretKey sk.publicParam sk.seed epoch)) := by
  -- A 32-bit epoch survives the round trip through the natural numbers.
  simp only [SecretKey.leaves, UInt32.ofNat_toNat]

/-! ## Known answer -/

/-- The seed `0, 1, ..., 31` the reference key is grown from. -/
def exampleSeed : Seed := Vector.ofFn fun i => UInt8.ofNat i.val

/-- Key generation over epochs 6 to 8 gives the reference public key. -/
theorem keyGen_known_answer :
    (keyGen exampleSeed 6 8).toOption.map Prod.snd = some examplePublicKey := by
  -- A root over three leaves is too deep for the kernel's evaluator.
  -- The native evaluator checks the closed computation.
  native_decide

/-- An empty epoch range rejects. -/
theorem keyGen_empty_range : (keyGen exampleSeed 8 6).toOption.isNone := by
  decide +kernel

end EthCryptographySpecs.Xmss
