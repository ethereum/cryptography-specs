import EthCryptographySpecs.Bls.Fr

/-!
# Proofs: `Fr`

Algebraic facts about `Fr` multiplication and addition and `powNat`.

`Fr` is `Fin Fr.modulus`, so every value is canonical (`val < modulus`)
by construction and the lemmas below hold unconditionally. Several are
thin restatements of core `Fin` lemmas, kept under the `Fr` namespace so
downstream proofs are unaffected by the representation change.
-/

namespace EthCryptographySpecs.Bls.Fr

/-- `Fr.one` agrees with the `OfNat` numeral `1`. -/
theorem one_eq_one : one = (1 : Fr) := rfl

/-- `ofNat` always produces a canonical value. -/
theorem val_ofNat_lt (n : Nat) : (ofNat n).val < modulus :=
  (ofNat n).isLt

protected theorem mul_comm (a b : Fr) : a * b = b * a :=
  Fin.mul_comm a b

protected theorem mul_assoc (a b c : Fr) : a * b * c = a * (b * c) :=
  Fin.mul_assoc a b c

/-- A trailing `* one` cancels under an outer multiplication. -/
theorem mul_mul_one (a b : Fr) : a * (b * one) = a * b := by
  rw [one_eq_one, Fin.mul_one]

/-- A leading `one *` cancels under an outer multiplication. -/
theorem mul_one_mul (a b : Fr) : a * (one * b) = a * b := by
  rw [one_eq_one, Fin.one_mul]

/-- `one *` is the identity on any product. -/
theorem one_mul_mul (a b : Fr) : one * (a * b) = a * b := by
  rw [one_eq_one, Fin.one_mul]


/-- Addition is commutative -/
protected theorem add_comm (a b : Fr) : a + b = b + a := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_add, Nat.add_comm]

/-- Addition is associative -/
protected theorem add_assoc (a b c : Fr) : a + b + c = a + (b + c) := by
  apply Fin.ext
  simp only [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- Addition is commutative, even with an addition before -/
protected theorem add_right_comm (a b c : Fr) : a + b + c = a + c + b := by
  rw [Fr.add_assoc, Fr.add_comm b, ← Fr.add_assoc]

/-- 0th power is always one -/
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

/-- A successful `fromBytesBE` implies: the input was 32 bytes, the value
is the big-endian decoding, and the value is canonical. -/
theorem fromBytesBE_ok {b : ByteArray} {f : Fr}
    (h : fromBytesBE b = .ok f) :
    b.size = 32 ∧ f.val = fromBytesBEAux 0 b.data.toList ∧
      f.val < modulus := by
  rw [fromBytesBE] at h
  split at h
  · cases h
  · rename_i hsz
    dsimp only [] at h
    split at h
    · rename_i hlt
      cases h
      exact ⟨by omega, rfl, hlt⟩
    · cases h

/-- `powNat` always produces a canonical value. -/
protected theorem powNat_val_lt (a : Fr) (e : Nat) :
    (powNat a e).val < modulus :=
  (powNat a e).isLt

/-- Absorbing a trailing `* one` into a `powNat`. -/
private theorem powNat_mul_one (a : Fr) (e : Nat) :
    powNat a e * Fr.one = powNat a e := by
  rw [one_eq_one, Fin.mul_one]

/-- `a^(m + n) = a^m * a^n`. -/
theorem powNat_add (a : Fr) (m n : Nat) :
    powNat a (m + n) = powNat a m * powNat a n := by
  induction n with
  | zero => rw [Nat.add_zero, powNat_zero, powNat_mul_one]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega,
        powNat_succ, powNat_succ, ih,
        ← Fr.mul_assoc, Fr.mul_comm a (powNat a m), Fr.mul_assoc]

/-- `a^(m * n) = (a^m)^n`. -/
theorem powNat_mul (a : Fr) (m n : Nat) :
    powNat a (m * n) = powNat (powNat a m) n := by
  induction n with
  | zero => rw [Nat.mul_zero, powNat_zero, powNat_zero]
  | succ n ih =>
    rw [Nat.mul_succ, powNat_add, ih, powNat_succ, Fr.mul_comm]

end EthCryptographySpecs.Bls.Fr
