import EthCryptographySpecs.Bls.Fp
import EthCryptographySpecs.Proofs.PowMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic

/-!
# Proofs: `Fp` as a Mathlib finite field

Connects `Fp` (= `Fin Fp.modulus`) to Mathlib's `ZMod Fp.modulus`,
mirroring `Proofs.Bls.FrZMod` for the scalar field. See that file for
the design notes on the scoped `Field` instance (its `Div` data must be
the spec's own high-priority Fermat-inverse division) and the
elaboration pitfalls of `Fin`-abbrev field types.

## Primality of the modulus

Unlike `r - 1`, the factorization of `p - 1` contains primes far beyond
`norm_num` range (up to 234 bits), so `modulus_prime` is proved by a
*chain* of Lucas certificates (`lucas_primality`) — a Pratt tree:

  p - 1 = 2 · 3² · 11 · 23 · 47 · 10177 · 859267 · 52437899
            · 2584487767265781317813
            · 15778400344354997994418419698270088123916926905054652752758194827714659

and each of the two large factors recursively carries its own
certificate, ten auxiliary primes in total. All modular exponentiations
go through `EthCryptographySpecs.PowMod.powModAux`, so the entire tree
is kernel-checked without `native_decide`.

The square-root helper (`Fp.sqrt`) is *not* treated here; its
correctness proof belongs with the decompression proofs that need it.
-/

namespace EthCryptographySpecs.Bls.Fp

-- Kernel evaluation of `powModAux` (384 recursion steps) and the
-- `decide`-checked factorization identities exceed the default depth.
set_option maxRecDepth 8000
-- The `2 ^ 384` fuel bounds below are only ever evaluated by the
-- kernel inside `decide`; keep the elaborator from warning about them.
set_option exponentiation.threshold 512

/-! ## The Lucas certificate chain (Pratt tree) for `p` -/

private theorem pow_card_sub_one_9272813673901 :
    ((2 : Nat) : ZMod 9272813673901) ^ (9272813673901 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 9272813673901 384 2 (9272813673901 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_9272813673901 :
    ∀ q : Nat, q.Prime → q ∣ 9272813673901 - 1 →
      ((2 : Nat) : ZMod 9272813673901) ^ ((9272813673901 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 9272813673901 - 1 = 2 ^ 2 * (3 * (5 ^ 2 * (7 * (7577 * (582767))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 7 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7577 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 7577 (by decide) (by decide)
  · obtain rfl := heq 582767 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 582767 (by decide) (by decide)

/-- Pratt-tree node: `9272813673901` is prime (Lucas certificate, witness `2`). -/
private theorem prime_9272813673901 : Nat.Prime 9272813673901 :=
  lucas_primality 9272813673901 ((2 : Nat) : ZMod 9272813673901)
    pow_card_sub_one_9272813673901 pow_div_prime_ne_one_9272813673901

private theorem pow_card_sub_one_1928745244171409 :
    ((3 : Nat) : ZMod 1928745244171409) ^ (1928745244171409 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1928745244171409 384 3 (1928745244171409 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1928745244171409 :
    ∀ q : Nat, q.Prime → q ∣ 1928745244171409 - 1 →
      ((3 : Nat) : ZMod 1928745244171409) ^ ((1928745244171409 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1928745244171409 - 1 = 2 ^ 4 * (13 * (9272813673901)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1928745244171409 384 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 13 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1928745244171409 384 3 13 (by decide) (by decide)
  · obtain rfl := heq 9272813673901 prime_9272813673901 hdvd
    exact PowMod.natCast_pow_div_ne_one 1928745244171409 384 3 9272813673901 (by decide) (by decide)

/-- Pratt-tree node: `1928745244171409` is prime (Lucas certificate, witness `3`). -/
private theorem prime_1928745244171409 : Nat.Prime 1928745244171409 :=
  lucas_primality 1928745244171409 ((3 : Nat) : ZMod 1928745244171409)
    pow_card_sub_one_1928745244171409 pow_div_prime_ne_one_1928745244171409

private theorem pow_card_sub_one_7259797099061183477 :
    ((2 : Nat) : ZMod 7259797099061183477) ^ (7259797099061183477 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 7259797099061183477 384 2 (7259797099061183477 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_7259797099061183477 :
    ∀ q : Nat, q.Prime → q ∣ 7259797099061183477 - 1 →
      ((2 : Nat) : ZMod 7259797099061183477) ^ ((7259797099061183477 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 7259797099061183477 - 1 = 2 ^ 2 * (941 * (1928745244171409)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 7259797099061183477 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 941 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 7259797099061183477 384 2 941 (by decide) (by decide)
  · obtain rfl := heq 1928745244171409 prime_1928745244171409 hdvd
    exact PowMod.natCast_pow_div_ne_one 7259797099061183477 384 2 1928745244171409 (by decide) (by decide)

/-- Pratt-tree node: `7259797099061183477` is prime (Lucas certificate, witness `2`). -/
private theorem prime_7259797099061183477 : Nat.Prime 7259797099061183477 :=
  lucas_primality 7259797099061183477 ((2 : Nat) : ZMod 7259797099061183477)
    pow_card_sub_one_7259797099061183477 pow_div_prime_ne_one_7259797099061183477

private theorem pow_card_sub_one_2584487767265781317813 :
    ((2 : Nat) : ZMod 2584487767265781317813) ^ (2584487767265781317813 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 2584487767265781317813 384 2 (2584487767265781317813 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_2584487767265781317813 :
    ∀ q : Nat, q.Prime → q ∣ 2584487767265781317813 - 1 →
      ((2 : Nat) : ZMod 2584487767265781317813) ^ ((2584487767265781317813 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 2584487767265781317813 - 1 = 2 ^ 2 * (89 * (7259797099061183477)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 2584487767265781317813 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 89 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 2584487767265781317813 384 2 89 (by decide) (by decide)
  · obtain rfl := heq 7259797099061183477 prime_7259797099061183477 hdvd
    exact PowMod.natCast_pow_div_ne_one 2584487767265781317813 384 2 7259797099061183477 (by decide) (by decide)

/-- Pratt-tree node: `2584487767265781317813` is prime (Lucas certificate, witness `2`). -/
private theorem prime_2584487767265781317813 : Nat.Prime 2584487767265781317813 :=
  lucas_primality 2584487767265781317813 ((2 : Nat) : ZMod 2584487767265781317813)
    pow_card_sub_one_2584487767265781317813 pow_div_prime_ne_one_2584487767265781317813

private theorem pow_card_sub_one_64881703735777 :
    ((5 : Nat) : ZMod 64881703735777) ^ (64881703735777 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 64881703735777 384 5 (64881703735777 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_64881703735777 :
    ∀ q : Nat, q.Prime → q ∣ 64881703735777 - 1 →
      ((5 : Nat) : ZMod 64881703735777) ^ ((64881703735777 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 64881703735777 - 1 = 2 ^ 5 * (3 ^ 7 * (927093389)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 64881703735777 384 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 64881703735777 384 5 3 (by decide) (by decide)
  · obtain rfl := heq 927093389 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 64881703735777 384 5 927093389 (by decide) (by decide)

/-- Pratt-tree node: `64881703735777` is prime (Lucas certificate, witness `5`). -/
private theorem prime_64881703735777 : Nat.Prime 64881703735777 :=
  lucas_primality 64881703735777 ((5 : Nat) : ZMod 64881703735777)
    pow_card_sub_one_64881703735777 pow_div_prime_ne_one_64881703735777

private theorem pow_card_sub_one_92691255082156974996979 :
    ((3 : Nat) : ZMod 92691255082156974996979) ^ (92691255082156974996979 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 92691255082156974996979 384 3 (92691255082156974996979 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_92691255082156974996979 :
    ∀ q : Nat, q.Prime → q ∣ 92691255082156974996979 - 1 →
      ((3 : Nat) : ZMod 92691255082156974996979) ^ ((92691255082156974996979 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 92691255082156974996979 - 1 = 2 * (3 * (31 * (467 * (16447 * (64881703735777))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 31 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 31 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 467 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 467 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 16447 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 16447 (by decide) (by decide)
  · obtain rfl := heq 64881703735777 prime_64881703735777 hdvd
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 64881703735777 (by decide) (by decide)

/-- Pratt-tree node: `92691255082156974996979` is prime (Lucas certificate, witness `3`). -/
private theorem prime_92691255082156974996979 : Nat.Prime 92691255082156974996979 :=
  lucas_primality 92691255082156974996979 ((3 : Nat) : ZMod 92691255082156974996979)
    pow_card_sub_one_92691255082156974996979 pow_div_prime_ne_one_92691255082156974996979

private theorem pow_card_sub_one_43670061551 :
    ((7 : Nat) : ZMod 43670061551) ^ (43670061551 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 43670061551 384 7 (43670061551 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_43670061551 :
    ∀ q : Nat, q.Prime → q ∣ 43670061551 - 1 →
      ((7 : Nat) : ZMod 43670061551) ^ ((43670061551 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 43670061551 - 1 = 2 * (5 ^ 2 * (17 * (51376543))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 17 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 17 (by decide) (by decide)
  · obtain rfl := heq 51376543 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 51376543 (by decide) (by decide)

/-- Pratt-tree node: `43670061551` is prime (Lucas certificate, witness `7`). -/
private theorem prime_43670061551 : Nat.Prime 43670061551 :=
  lucas_primality 43670061551 ((7 : Nat) : ZMod 43670061551)
    pow_card_sub_one_43670061551 pow_div_prime_ne_one_43670061551

private theorem pow_card_sub_one_13090036741 :
    ((10 : Nat) : ZMod 13090036741) ^ (13090036741 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 13090036741 384 10 (13090036741 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_13090036741 :
    ∀ q : Nat, q.Prime → q ∣ 13090036741 - 1 →
      ((10 : Nat) : ZMod 13090036741) ^ ((13090036741 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 13090036741 - 1 = 2 ^ 2 * (3 * (5 * (11 * (47 * (421987))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 11 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 47 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 47 (by decide) (by decide)
  · obtain rfl := heq 421987 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 421987 (by decide) (by decide)

/-- Pratt-tree node: `13090036741` is prime (Lucas certificate, witness `10`). -/
private theorem prime_13090036741 : Nat.Prime 13090036741 :=
  lucas_primality 13090036741 ((10 : Nat) : ZMod 13090036741)
    pow_card_sub_one_13090036741 pow_div_prime_ne_one_13090036741

private theorem pow_card_sub_one_3819663927398918131021 :
    ((6 : Nat) : ZMod 3819663927398918131021) ^ (3819663927398918131021 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 3819663927398918131021 384 6 (3819663927398918131021 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_3819663927398918131021 :
    ∀ q : Nat, q.Prime → q ∣ 3819663927398918131021 - 1 →
      ((6 : Nat) : ZMod 3819663927398918131021) ^ ((3819663927398918131021 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 3819663927398918131021 - 1 = 2 ^ 2 * (3 ^ 2 * (5 * (19 * (113 * (755057 * (13090036741)))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 19 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 19 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 113 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 113 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 755057 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 755057 (by decide) (by decide)
  · obtain rfl := heq 13090036741 prime_13090036741 hdvd
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 13090036741 (by decide) (by decide)

/-- Pratt-tree node: `3819663927398918131021` is prime (Lucas certificate, witness `6`). -/
private theorem prime_3819663927398918131021 : Nat.Prime 3819663927398918131021 :=
  lucas_primality 3819663927398918131021 ((6 : Nat) : ZMod 3819663927398918131021)
    pow_card_sub_one_3819663927398918131021 pow_div_prime_ne_one_3819663927398918131021

private theorem pow_card_sub_one_1125266252156850182658904441386709967 :
    ((5 : Nat) : ZMod 1125266252156850182658904441386709967) ^ (1125266252156850182658904441386709967 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1125266252156850182658904441386709967 384 5 (1125266252156850182658904441386709967 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1125266252156850182658904441386709967 :
    ∀ q : Nat, q.Prime → q ∣ 1125266252156850182658904441386709967 - 1 →
      ((5 : Nat) : ZMod 1125266252156850182658904441386709967) ^ ((1125266252156850182658904441386709967 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1125266252156850182658904441386709967 - 1 = 2 * (3373 * (43670061551 * (3819663927398918131021))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3373 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 3373 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 43670061551 prime_43670061551 h
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 43670061551 (by decide) (by decide)
  · obtain rfl := heq 3819663927398918131021 prime_3819663927398918131021 hdvd
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 3819663927398918131021 (by decide) (by decide)

/-- Pratt-tree node: `1125266252156850182658904441386709967` is prime (Lucas certificate, witness `5`). -/
private theorem prime_1125266252156850182658904441386709967 : Nat.Prime 1125266252156850182658904441386709967 :=
  lucas_primality 1125266252156850182658904441386709967 ((5 : Nat) : ZMod 1125266252156850182658904441386709967)
    pow_card_sub_one_1125266252156850182658904441386709967 pow_div_prime_ne_one_1125266252156850182658904441386709967

private theorem pow_card_sub_one_15778400344354997994418419698270088123916926905054652752758194827714659 :
    ((2 : Nat) : ZMod 15778400344354997994418419698270088123916926905054652752758194827714659) ^ (15778400344354997994418419698270088123916926905054652752758194827714659 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 (15778400344354997994418419698270088123916926905054652752758194827714659 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_15778400344354997994418419698270088123916926905054652752758194827714659 :
    ∀ q : Nat, q.Prime → q ∣ 15778400344354997994418419698270088123916926905054652752758194827714659 - 1 →
      ((2 : Nat) : ZMod 15778400344354997994418419698270088123916926905054652752758194827714659) ^ ((15778400344354997994418419698270088123916926905054652752758194827714659 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 15778400344354997994418419698270088123916926905054652752758194827714659 - 1 = 2 * (3 * (53 * (475709467 * (92691255082156974996979 * (1125266252156850182658904441386709967))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 53 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 53 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 475709467 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 475709467 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 92691255082156974996979 prime_92691255082156974996979 h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 92691255082156974996979 (by decide) (by decide)
  · obtain rfl := heq 1125266252156850182658904441386709967 prime_1125266252156850182658904441386709967 hdvd
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 1125266252156850182658904441386709967 (by decide) (by decide)

/-- Pratt-tree node: `15778400344354997994418419698270088123916926905054652752758194827714659` is prime (Lucas certificate, witness `2`). -/
private theorem prime_15778400344354997994418419698270088123916926905054652752758194827714659 : Nat.Prime 15778400344354997994418419698270088123916926905054652752758194827714659 :=
  lucas_primality 15778400344354997994418419698270088123916926905054652752758194827714659 ((2 : Nat) : ZMod 15778400344354997994418419698270088123916926905054652752758194827714659)
    pow_card_sub_one_15778400344354997994418419698270088123916926905054652752758194827714659 pow_div_prime_ne_one_15778400344354997994418419698270088123916926905054652752758194827714659

private theorem pow_card_sub_one_modulus :
    ((2 : Nat) : ZMod modulus) ^ (modulus - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff modulus 384 2 (modulus - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_modulus :
    ∀ q : Nat, q.Prime → q ∣ modulus - 1 →
      ((2 : Nat) : ZMod modulus) ^ ((modulus - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : modulus - 1 = 2 * (3 ^ 2 * (11 * (23 * (47 * (10177 * (859267 * (52437899 * (2584487767265781317813 * (15778400344354997994418419698270088123916926905054652752758194827714659))))))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 11 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 23 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 23 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 47 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 47 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 10177 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 10177 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 859267 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 859267 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 52437899 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 52437899 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2584487767265781317813 prime_2584487767265781317813 h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 2584487767265781317813 (by decide) (by decide)
  · obtain rfl := heq 15778400344354997994418419698270088123916926905054652752758194827714659 prime_15778400344354997994418419698270088123916926905054652752758194827714659 hdvd
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 15778400344354997994418419698270088123916926905054652752758194827714659 (by decide) (by decide)

/-- The BLS12-381 base field modulus is prime, by a Lucas certificate
chain (Pratt tree): every prime factor of `p - 1` beyond `norm_num`
range carries its own certificate above. Witness: `2` is a
primitive root mod `p`. -/
theorem modulus_prime : Nat.Prime modulus :=
  lucas_primality modulus ((2 : Nat) : ZMod modulus)
    pow_card_sub_one_modulus pow_div_prime_ne_one_modulus

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fp` is (definitionally) Mathlib's `ZMod Fp.modulus`, as rings. -/
def toZMod : Fp ≃+* ZMod modulus := RingEquiv.refl _

/-! ## Bridge: spec operations = Mathlib operations -/

/-- `Fp.powNat` is monoid power, phrased over `ZMod Fp.modulus`
(definitionally `Fp`). Public (unlike `Fr`'s analogue): downstream
proofs at large exponents must stay inside the `ZMod` instance world —
a cross-instance defeq check on `x ^ ((p+1)/4)` would try to unfold
the power. `Fp`-facing version: `powNat_eq_pow`. -/
theorem powNat_eq_zmod_pow (a : ZMod modulus) (n : Nat) :
    Fp.powNat a n = a ^ n := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [Fp.powNat]
    split
    · rename_i h
      subst h
      rw [pow_zero]
      rfl
    · rename_i h
      rw [ih (n / 2) (by omega)]
      by_cases h2 : n % 2 = 1
      -- `show` re-elaborates the goal with uniform `ZMod` instance
      -- paths (the `*` inherited from `powNat`'s body is the spec's
      -- `Fin` one), so the `pow` rewrites below can match.
      · rw [if_pos h2]
        show a * (a * a) ^ (n / 2) = a ^ n
        rw [← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [if_neg h2]
        show (a * a) ^ (n / 2) = a ^ n
        rw [← pow_two, ← pow_mul]
        congr 1
        omega

/-- The spec's Fermat-little-theorem `Fp.inverse` is the field inverse
of `ZMod Fp.modulus` (both send `0` to `0`). Public `Fp`-facing
version: `inverse_eq_inv`. -/
private theorem inverse_eq_zmod_inv (a : ZMod modulus) :
    Fp.inverse a = a⁻¹ := by
  rw [inverse, powNat_eq_zmod_pow]
  by_cases h : a = 0
  · subst h
    rw [zero_pow (by decide : modulus - 2 ≠ 0), inv_zero]
  · have h2 : a ^ (modulus - 2) * a = 1 := by
      rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
      exact ZMod.pow_card_sub_one_eq_one h
    exact eq_inv_of_mul_eq_one_left h2

/-- The Mathlib field structure on `ZMod Fp.modulus`, named so it can be
used as the source of the structure update in `instField` below. -/
@[reducible] private def zmodField : Field (ZMod modulus) := inferInstance

/-- Field structure on `Fp`, transported from `Field (ZMod Fp.modulus)`
with one change: the `Div` data is the spec's own high-priority
Fermat-inverse division from `Bls/Fp.lean`. See `Fr.instField` in
`Proofs.Bls.FrZMod` for why this alignment is forced and why the
instance is scoped. Activate with
`open scoped EthCryptographySpecs.Bls.Fp`. -/
scoped instance instField : Field Fp :=
  { zmodField with
    div := (· / ·)
    div_eq_mul_inv := fun a b =>
      congrArg (fun x : ZMod modulus =>
          @HMul.hMul (ZMod modulus) (ZMod modulus) (ZMod modulus) _ a x)
        (inverse_eq_zmod_inv b)
    nnratCast_def := fun q => by
      have h : (q : ZMod modulus)
          = (q.num : ZMod modulus) / (q.den : ZMod modulus) := NNRat.cast_def q
      rw [div_eq_mul_inv, ← inverse_eq_zmod_inv] at h
      exact h
    ratCast_def := fun q => by
      have h : (q : ZMod modulus)
          = (q.num : ZMod modulus) / (q.den : ZMod modulus) := Rat.cast_def q
      rw [div_eq_mul_inv, ← inverse_eq_zmod_inv] at h
      exact h }

@[simp] theorem zero_def : Fp.zero = (0 : Fp) := rfl

@[simp] theorem one_def : Fp.one = (1 : Fp) := rfl

/-- The spec's `Fp.ofNat` is Mathlib's `Nat.cast`. -/
theorem ofNat_eq_natCast (n : Nat) : Fp.ofNat n = (n : Fp) := by
  apply Fin.ext
  rw [ofNat, Fin.val_ofNat]
  exact (ZMod.val_natCast modulus n).symm

/-- The spec's `Fp.powNat` is Mathlib's monoid power. -/
theorem powNat_eq_pow (a : Fp) (n : Nat) : a.powNat n = a ^ n :=
  powNat_eq_zmod_pow a n

/-- The spec's Fermat-little-theorem `Fp.inverse` is the field inverse.
Both send `0` to `0`. -/
theorem inverse_eq_inv (a : Fp) : a.inverse = a⁻¹ :=
  inverse_eq_zmod_inv a

/-- The spec's division (`a * b.inverse`, registered at high priority
over core's `Fin` Nat-division) is field division. -/
theorem div_eq_mul_inv' (a b : Fp) : a / b = a * b⁻¹ := by
  show a * b.inverse = a * b⁻¹
  rw [inverse_eq_inv]

-- Smoke tests: the scoped field structure interoperates with the
-- globally available `Fin` instances the executable spec uses.
example (a b : Fp) : a * b = b * a := mul_comm a b
example (a b : Fp) : a - b = a + -b := sub_eq_add_neg a b
example (a : Fp) (h : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ h

end EthCryptographySpecs.Bls.Fp
