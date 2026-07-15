import Mathlib.Data.ZMod.Basic

/-!
# Proofs: kernel-friendly modular exponentiation

`powModAux fuel m b e` is `b ^ e % m` (for `e < 2 ^ fuel`), computed by
a fuel-based square-and-multiply whose every step is a GMP-accelerated
`Nat` operation, so the kernel can evaluate it via `decide` even for
exponents hundreds of bits wide. `natCast_pow_eq_one_iff` and
`natCast_pow_div_ne_one` convert such computations into the
`(b : ZMod m) ^ e = 1` / `≠ 1` facts that Lucas primality certificates
(`lucas_primality`) consume.

This generalizes (over the modulus) the private infrastructure that
`Proofs.Bls.FrZMod` introduced for the scalar-field modulus; the
base-field certificate chain in `Proofs.Bls.FpZMod` needs it for a
dozen different moduli, one per node of its Pratt tree.
-/

namespace EthCryptographySpecs.PowMod

/-- Fuel-based modular square-and-multiply: `powModAux fuel m b e` is
`b ^ e % m` provided `e < 2 ^ fuel`. Structural recursion on `fuel`
keeps kernel reduction shallow. -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, m, _, _ => 1 % m
  | fuel+1, m, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then powModAux fuel m (b * b % m) (e / 2) * b % m
    else powModAux fuel m (b * b % m) (e / 2)

theorem powModAux_eq (fuel m b e : Nat) (he : e < 2 ^ fuel) :
    powModAux fuel m b e = b ^ e % m := by
  induction fuel generalizing b e with
  | zero =>
    have h1 : e < 1 := by simpa using he
    have h0 : e = 0 := by omega
    subst h0
    simp [powModAux]
  | succ fuel ih =>
    by_cases h0 : e = 0
    · subst h0; simp [powModAux]
    · have h2 : e / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at he; omega
      have hrec := ih (b * b % m) (e / 2) h2
      by_cases h1 : e % 2 = 1
      · rw [powModAux, if_neg h0, if_pos h1, hrec, ← Nat.pow_mod, ← Nat.pow_two,
            ← Nat.pow_mul, Nat.mod_mul_mod, ← Nat.pow_succ,
            show (2 * (e / 2)).succ = e by omega]
      · rw [powModAux, if_neg h0, if_neg h1, hrec, ← Nat.pow_mod, ← Nat.pow_two,
            ← Nat.pow_mul, show 2 * (e / 2) = e by omega]

/-- `(b : ZMod m) ^ e = 1` is decided by one `powModAux` computation. -/
theorem natCast_pow_eq_one_iff (m fuel b e : Nat) (he : e < 2 ^ fuel) :
    ((b : ZMod m) ^ e = 1) ↔ powModAux fuel m b e = 1 % m := by
  rw [powModAux_eq fuel m b e he, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod m),
      ZMod.natCast_eq_natCast_iff]
  exact Iff.rfl

/-- The `≠ 1` half of a Lucas certificate: refute
`(b : ZMod m) ^ ((m - 1) / q) = 1` by one `powModAux` computation. -/
theorem natCast_pow_div_ne_one (m fuel b q : Nat) (hm : m - 1 < 2 ^ fuel)
    (hne : powModAux fuel m b ((m - 1) / q) ≠ 1 % m) :
    ((b : ZMod m) ^ ((m - 1) / q)) ≠ 1 := fun h =>
  hne ((natCast_pow_eq_one_iff m fuel b _
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm)).mp h)

end EthCryptographySpecs.PowMod
