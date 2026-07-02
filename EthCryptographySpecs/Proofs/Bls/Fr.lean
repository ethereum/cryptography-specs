import EthCryptographySpecs.Bls.Fr

/-!
# Proofs: `Fr`

Algebraic facts about `Fr` multiplication and `powNat`.

`Fr` does not enforce `val < modulus` by construction, so lemmas like
`a * one = a` do not hold for non-canonical values; the lemmas below are
stated in forms that re-reduce modulo `modulus` and therefore hold
unconditionally.
-/

namespace EthCryptographySpecs.Bls.Fr

protected theorem mul_comm (a b : Fr) : a * b = b * a := by
  show Fr.mk _ = Fr.mk _
  rw [Nat.mul_comm]

protected theorem mul_assoc (a b c : Fr) : a * b * c = a * (b * c) := by
  show Fr.mk (a.val * b.val % modulus * c.val % modulus)
      = Fr.mk (a.val * (b.val * c.val % modulus) % modulus)
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-- Multiplication only depends on the right operand's value modulo
`modulus`. -/
theorem mul_mk_mod (a : Fr) (n : Nat) : a * ⟨n % modulus⟩ = a * ⟨n⟩ := by
  show Fr.mk _ = Fr.mk _
  rw [Nat.mul_mod_mod]

/-- A trailing `* one` cancels under an outer multiplication. -/
theorem mul_mul_one (a b : Fr) : a * (b * one) = a * b := by
  show a * ⟨b.val * 1 % modulus⟩ = a * b
  rw [Nat.mul_one]
  exact mul_mk_mod a b.val

/-- A leading `one *` cancels under an outer multiplication. -/
theorem mul_one_mul (a b : Fr) : a * (one * b) = a * b := by
  show a * ⟨1 * b.val % modulus⟩ = a * b
  rw [Nat.one_mul]
  exact mul_mk_mod a b.val

theorem powNat_zero (a : Fr) : powNat a 0 = one := by
  simp [powNat]

/-- Simple-recursion model of `powNat` (repeated multiplication). -/
def powNatModel (a : Fr) : Nat → Fr
  | 0 => one
  | e + 1 => a * powNatModel a e

private theorem powNatModel_sq (a : Fr) (k : Nat) :
    powNatModel (a * a) k = powNatModel a (2 * k) := by
  induction k with
  | zero => simp [powNatModel]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    simp only [powNatModel]
    rw [ih, Fr.mul_assoc]

/-- Square-and-multiply computes repeated multiplication. -/
theorem powNat_eq_powNatModel (a : Fr) (e : Nat) :
    powNat a e = powNatModel a e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [powNat]
    split
    · rename_i h; subst h; rfl
    · rename_i h
      simp only [ih (e / 2) (by omega), powNatModel_sq]
      by_cases h2 : e % 2 = 1
      · rw [if_pos h2]
        generalize hk : e / 2 = k
        rw [show e = 2 * k + 1 by omega, powNatModel]
      · rw [if_neg h2]
        generalize hk : e / 2 = k
        rw [show e = 2 * k by omega]

theorem powNat_succ (a : Fr) (e : Nat) : powNat a (e + 1) = a * powNat a e := by
  rw [powNat_eq_powNatModel, powNat_eq_powNatModel, powNatModel]

end EthCryptographySpecs.Bls.Fr
