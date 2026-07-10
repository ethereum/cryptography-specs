import EthCryptographySpecs.Bls.Fr
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: `Fr` as a Mathlib finite field

Connects `Fr` (= `Fin Fr.modulus`) to Mathlib's `ZMod Fr.modulus`.
Because `Fr.modulus` is a positive numeral, `ZMod Fr.modulus` reduces
definitionally to `Fin Fr.modulus`, and Mathlib deliberately builds
`ZMod`'s ring structure to be definitionally equal to the one on `Fin`,
so the ring isomorphism below is the identity.

## Primality of the modulus

`modulus_prime` proves that the BLS12-381 scalar field order `r` is
prime via a Lucas certificate (`lucas_primality`): `7` has order
`r - 1` in `(ZMod r)ˣ`, which is checked from the full factorization

  r - 1 = 2³² · 3 · 11 · 19 · 10177 · 125527 · 859267 · 906349² ·
          2508409 · 2529403 · 52437899 · 254760293²

by verifying `7 ^ (r-1) = 1` and `7 ^ ((r-1)/q) ≠ 1` for each prime
factor `q`. The modular exponentiations are carried out by the kernel
through `powModAux`, a fuel-based square-and-multiply whose steps are
GMP-accelerated `Nat` operations, so the whole certificate checks in
seconds without `native_decide`.
-/

namespace EthCryptographySpecs.Bls.Fr

-- Kernel evaluation of `powModAux` (256 recursion steps) exceeds the
-- default `maxRecDepth` of the `decide` calls below.
set_option maxRecDepth 4000

/-- Fuel-based modular square-and-multiply: `powModAux fuel m b e` is
`b ^ e % m` provided `e < 2 ^ fuel`. Structural recursion on `fuel`
keeps kernel reduction shallow, and every arithmetic step is a
GMP-accelerated `Nat` operation, so `decide` can evaluate it even for
255-bit exponents. -/
private def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, m, _, _ => 1 % m
  | fuel+1, m, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then powModAux fuel m (b * b % m) (e / 2) * b % m
    else powModAux fuel m (b * b % m) (e / 2)

private theorem powModAux_eq (fuel m b e : Nat) (he : e < 2 ^ fuel) :
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

private theorem natCast_pow_eq_one_iff (b e : Nat) (he : e < 2 ^ 256) :
    ((b : ZMod modulus) ^ e = 1) ↔ powModAux 256 modulus b e = 1 % modulus := by
  rw [powModAux_eq 256 modulus b e he, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod modulus),
      ZMod.natCast_eq_natCast_iff]
  exact Iff.rfl

private theorem seven_pow_div_ne_one (q : Nat)
    (hne : powModAux 256 modulus 7 ((modulus - 1) / q) ≠ 1 % modulus) :
    ((7 : ℕ) : ZMod modulus) ^ ((modulus - 1) / q) ≠ 1 :=
  fun h => hne ((natCast_pow_eq_one_iff 7 _
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide))).mp h)

/-- The BLS12-381 scalar field modulus is prime, by a Lucas primality
certificate with witness `7` (a primitive root mod `r`, the same
generator the consensus specs use for roots of unity). -/
theorem modulus_prime : Nat.Prime modulus := by
  refine lucas_primality modulus ((7 : ℕ) : ZMod modulus) ?_ ?_
  · rw [natCast_pow_eq_one_iff 7 (modulus - 1) (by decide)]
    decide
  · intro q hq hdvd
    have heq : ∀ p : Nat, p.Prime → q ∣ p → q = p := fun p hp h =>
      (Nat.prime_dvd_prime_iff_eq hq hp).mp h
    have hfact : modulus - 1 =
        2 ^ 32 * (3 * (11 * (19 * (10177 * (125527 * (859267 * (906349 ^ 2 *
          (2508409 * (2529403 * (52437899 * 254760293 ^ 2)))))))))) := by decide
    rw [hfact] at hdvd
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
      exact seven_pow_div_ne_one 2 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 3 (by norm_num) h
      exact seven_pow_div_ne_one 3 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 11 (by norm_num) h
      exact seven_pow_div_ne_one 11 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 19 (by norm_num) h
      exact seven_pow_div_ne_one 19 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 10177 (by norm_num) h
      exact seven_pow_div_ne_one 10177 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 125527 (by norm_num) h
      exact seven_pow_div_ne_one 125527 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 859267 (by norm_num) h
      exact seven_pow_div_ne_one 859267 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 906349 (by norm_num) (hq.dvd_of_dvd_pow h)
      exact seven_pow_div_ne_one 906349 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 2508409 (by norm_num) h
      exact seven_pow_div_ne_one 2508409 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 2529403 (by norm_num) h
      exact seven_pow_div_ne_one 2529403 (by decide)
    rcases (hq.dvd_mul).mp hdvd with h | hdvd
    · obtain rfl := heq 52437899 (by norm_num) h
      exact seven_pow_div_ne_one 52437899 (by decide)
    · obtain rfl := heq 254760293 (by norm_num) (hq.dvd_of_dvd_pow hdvd)
      exact seven_pow_div_ne_one 254760293 (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fr` is (definitionally) Mathlib's `ZMod Fr.modulus`, as rings. -/
def toZMod : Fr ≃+* ZMod modulus := RingEquiv.refl _

/-- With primality, `ZMod Fr.modulus` — and hence `Fr`, via `toZMod` —
is a finite field. (Not registered as a global `Field Fr` instance:
Mathlib's field division would clash with the spec's `Div Fr`
instance.) -/
example : Field (ZMod modulus) := inferInstance

end EthCryptographySpecs.Bls.Fr
