import EthCryptographySpecs.Proofs.Xmss.Ots
import EthCryptographySpecs.Proofs.Xmss.Merkle
import EthCryptographySpecs.Proofs.Xmss.Sign

/-!
# Proofs: XMSS correctness

A signature this specification produces is one it accepts.

This is Lemma 3 of the construction paper (https://eprint.iacr.org/2025/055).

The paper also bounds how often signing fails.

That bound is probabilistic, so here signing is assumed to succeed.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-- Verification accepts every signature the secret key produces. -/
theorem verify_sign {sk : SecretKey} {msg : Message} {epoch : Epoch}
    {σ : Signature} (h : sign sk msg epoch = .ok σ) :
    verify sk.publicKey msg σ epoch = true := by
  obtain ⟨h₁, h₂, x, hx, hc, hp⟩ := sign_eq_ok h
  rw [verify_iff]
  -- The public key carries the secret key's parameter and root.
  simp only [SecretKey.publicKey]
  -- Step 1: the verifier recomputes the signer's digits.
  refine ⟨x, hx, ?_⟩
  -- Step 2: walking the revealed chains on gives the honest public values.
  rw [hc, otsRecover_otsReveal, hp, ← leaves_toNat]
  -- Step 3: the honest leaf and its co-path lead to the honest root.
  exact computeRoot_authPath sk sk.leaves epoch
    (UInt32.le_iff_toNat_le.mp h₁) (UInt32.le_iff_toNat_le.mp h₂)

/-- Correctness: a generated key pair verifies every signature it makes. -/
theorem verify_keyGen_sign {seed : Seed} {epochStart epochEnd : Epoch}
    {sk : SecretKey} {pk : PublicKey} {msg : Message} {epoch : Epoch}
    {σ : Signature}
    (hk : keyGen seed epochStart epochEnd = .ok (sk, pk))
    (hs : sign sk msg epoch = .ok σ) :
    verify pk msg σ epoch = true := by
  -- The public key is the one the secret key derives.
  rw [(keyGen_eq_ok hk).1]
  exact verify_sign hs

end EthCryptographySpecs.Xmss
