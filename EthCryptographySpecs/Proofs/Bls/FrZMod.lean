import EthCryptographySpecs.Bls.Fr
import EthCryptographySpecs.Proofs.Bls.Fr
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

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
factor `q` (`seven_pow_card_sub_one`, `seven_pow_div_prime_ne_one`).
The modular exponentiations are carried out by the kernel through
`powModAux`, a fuel-based square-and-multiply whose steps are
GMP-accelerated `Nat` operations, so the whole certificate checks in
seconds without `native_decide`.

The same two facts pin down the multiplicative order of `7` exactly
(`orderOf_seven`), making `7` a primitive `(r-1)`-th root of unity and
`7 ^ ((r-1)/n)` a primitive `n`-th root of unity for every `n ∣ r - 1`
(`isPrimitiveRoot_seven_pow`) — the algebraic backbone of the FFT and
barycentric-evaluation domains.

## Bridge layer

The last section relates every arithmetic operation the executable spec
defines on `Fr` to its Mathlib counterpart: `Fr.ofNat` is `Nat.cast`,
`Fr.powNat` is monoid `^`, `Fr.inverse` is field `⁻¹` (by Fermat's
little theorem, using primality), and spec division is `a * b⁻¹`.
The `Field Fr` instance is `Field (ZMod Fr.modulus)` with one change:
its `Div` data is the spec's own division (`Bls/Fr.lean` registers a
high-priority Fermat-inverse `Div Fr`), so `a / b` written anywhere in
the spec *is* the field's division — copying ZMod's gcd-based division
data instead would leave two propositionally-but-not-definitionally
equal `Div Fr` instances in scope, and the kernel rejects the resulting
structure. Downstream proofs activate the field structure with
`open scoped EthCryptographySpecs.Bls.Fr` — it is scoped, not global,
for the same reason Mathlib keeps `Fin.instCommRing` scoped (see the
note in `Mathlib.Data.ZMod.Defs` about coercion loops).
-/

namespace EthCryptographySpecs.Bls.Fr

-- Kernel evaluation of `powModAux` (256 recursion steps) exceeds the
-- default `maxRecDepth` of the `decide` calls below.
set_option maxRecDepth 4000

-- Core registers a global `HPow (Fin n) Nat (Fin n)` (and its `Pow`)
-- for the `grind` tactic. Because `Fr` is an abbrev of `Fin modulus`,
-- `a ^ n` with a `Nat` exponent elaborates through that instance
-- instead of Mathlib's `Monoid.toPow` — the two are definitionally but
-- not syntactically equal, so `rw` with Mathlib's `pow` lemmas fails
-- against statements phrased with the grind instance. Remove them for
-- this file so every `Fr ^ Nat` below is Mathlib's monoid power.
-- NOTE: `attribute [-instance]` is file-local; proof files that state
-- `Fr ^ Nat` lemmas must repeat these two lines.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

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

/-- First half of the Lucas certificate: `7 ^ (r - 1) = 1` in `ZMod r`. -/
theorem seven_pow_card_sub_one : ((7 : ℕ) : ZMod modulus) ^ (modulus - 1) = 1 := by
  rw [natCast_pow_eq_one_iff 7 (modulus - 1) (by decide)]
  decide

/-- Second half of the Lucas certificate: `7 ^ ((r - 1) / q) ≠ 1` in
`ZMod r` for every prime factor `q` of `r - 1`. Together with
`seven_pow_card_sub_one` this pins the order of `7` to exactly `r - 1`. -/
theorem seven_pow_div_prime_ne_one : ∀ q : Nat, q.Prime → q ∣ modulus - 1 →
    ((7 : ℕ) : ZMod modulus) ^ ((modulus - 1) / q) ≠ 1 := by
  intro q hq hdvd
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

/-- The BLS12-381 scalar field modulus is prime, by a Lucas primality
certificate with witness `7` (a primitive root mod `r`, the same
generator the consensus specs use for roots of unity). -/
theorem modulus_prime : Nat.Prime modulus :=
  lucas_primality modulus ((7 : ℕ) : ZMod modulus)
    seven_pow_card_sub_one seven_pow_div_prime_ne_one

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fr` is (definitionally) Mathlib's `ZMod Fr.modulus`, as rings. -/
def toZMod : Fr ≃+* ZMod modulus := RingEquiv.refl _

/-- With primality, `ZMod Fr.modulus` — and hence `Fr`, via `toZMod` —
is a finite field. (See `Fr.instField` below for the scoped instance.) -/
example : Field (ZMod modulus) := inferInstance

/-! ## Roots of unity -/

/-- `7` has multiplicative order exactly `r - 1` in `ZMod r`: it is a
generator of the multiplicative group. Reuses the two halves of the
Lucas certificate. -/
theorem orderOf_seven : orderOf ((7 : ℕ) : ZMod modulus) = modulus - 1 :=
  orderOf_eq_of_pow_and_pow_div_prime (by decide)
    seven_pow_card_sub_one seven_pow_div_prime_ne_one

/-- `7` is a primitive `(r-1)`-th root of unity in `ZMod r`. -/
theorem isPrimitiveRoot_seven :
    IsPrimitiveRoot ((7 : ℕ) : ZMod modulus) (modulus - 1) :=
  orderOf_seven ▸ IsPrimitiveRoot.orderOf _

/-- `7 ^ ((r-1)/n)` is a primitive `n`-th root of unity for every
`n ∣ r - 1`. This is the root the KZG spec's `computeRootsOfUnity`
builds its evaluation domains from. -/
theorem isPrimitiveRoot_seven_pow {n : Nat} (hn : n ∣ modulus - 1) :
    IsPrimitiveRoot (((7 : ℕ) : ZMod modulus) ^ ((modulus - 1) / n)) n :=
  isPrimitiveRoot_seven.pow (by decide) (Nat.div_mul_cancel hn).symm

/-! ## Bridge: spec operations = Mathlib operations -/

/-- `Fr.powNat` is monoid power, phrased over `ZMod Fr.modulus`
(definitionally `Fr`) so it is usable while constructing `Fr`'s own
`Field` instance below. Public `Fr`-facing version: `powNat_eq_pow`. -/
private theorem powNat_eq_zmod_pow (a : ZMod modulus) (n : Nat) :
    Fr.powNat a n = a ^ n := by
  induction n with
  | zero => rw [powNat_zero, pow_zero]; rfl
  | succ n ih => rw [powNat_succ, ih, pow_succ']; rfl

/-- The spec's Fermat-little-theorem `Fr.inverse` is the field inverse
of `ZMod Fr.modulus` (both send `0` to `0`), phrased over
`ZMod Fr.modulus` for the same reason as `powNat_eq_zmod_pow`. Public
`Fr`-facing version: `inverse_eq_inv`. -/
private theorem inverse_eq_zmod_inv (a : ZMod modulus) :
    Fr.inverse a = a⁻¹ := by
  rw [inverse, powNat_eq_zmod_pow]
  by_cases h : a = 0
  · subst h
    rw [zero_pow (by decide : modulus - 2 ≠ 0), inv_zero]
  · have h2 : a ^ (modulus - 2) * a = 1 := by
      rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
      exact ZMod.pow_card_sub_one_eq_one h
    exact eq_inv_of_mul_eq_one_left h2

/-- The Mathlib field structure on `ZMod Fr.modulus`, named so it can be
used as the source of the structure update in `instField` below. -/
@[reducible] private def zmodField : Field (ZMod modulus) := inferInstance

/-- Field structure on `Fr`, transported from `Field (ZMod Fr.modulus)`
with one change: the `Div` data is the spec's own high-priority
Fermat-inverse division from `Bls/Fr.lean`, so that `a / b` written
anywhere in the spec is definitionally the field's division. (Copying
ZMod's gcd-based division data instead makes the kernel reject the
instance: the `div`-mentioning axioms would be stated with the spec's
`Div Fr` but proved for ZMod's.) The three axioms whose statements
mention `/` are re-proved via `inverse_eq_zmod_inv` — phrased over
`ZMod Fr.modulus`, where all instances exist, and handed over by
definitional equality; all other data and proofs are ZMod's.

Scoped rather than global for the same reason Mathlib keeps
`Fin.instCommRing` scoped (see `Mathlib.Data.ZMod.Defs`): the `NatCast`
coercion it introduces can change how mixed `Fin`/`Nat` expressions
elaborate. Activate with `open scoped EthCryptographySpecs.Bls.Fr`. -/
scoped instance instField : Field Fr :=
  { zmodField with
    div := (· / ·)
    div_eq_mul_inv := fun a b =>
      -- Explicit `@HMul.hMul` because `a * ·` would make the binop
      -- elaborator look for `HMul (ZMod modulus) Fr` on the mixed-type
      -- operands; the defeq handover to the goal is checked by `exact`.
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

@[simp] theorem zero_def : Fr.zero = (0 : Fr) := rfl

@[simp] theorem one_def : Fr.one = (1 : Fr) := rfl

/-- The spec's `Fr.ofNat` is Mathlib's `Nat.cast`. -/
theorem ofNat_eq_natCast (n : Nat) : Fr.ofNat n = (n : Fr) := by
  apply Fin.ext
  rw [ofNat, Fin.val_ofNat]
  exact (ZMod.val_natCast modulus n).symm

/-- The spec's `Fr.powNat` is Mathlib's monoid power. -/
theorem powNat_eq_pow (a : Fr) (n : Nat) : a.powNat n = a ^ n :=
  powNat_eq_zmod_pow a n

/-- The spec's `HPow Fr Fr Fr` (used as `a ^ b`) is Mathlib's monoid
power at the exponent's value. -/
theorem hpow_eq_pow (a b : Fr) : a ^ b = a ^ b.val :=
  powNat_eq_pow a b.val

/-- Specialization of `hpow_eq_pow` to an `ofNat`-embedded exponent:
when `w` is canonical the round-trip through `Fr` is invisible. -/
theorem hpow_ofNat_eq_pow (a : Fr) {w : Nat} (hw : w < modulus) :
    a ^ Fr.ofNat w = a ^ w := by
  rw [hpow_eq_pow]
  congr 1
  show w % modulus = w
  exact Nat.mod_eq_of_lt hw

/-- The spec's Fermat-little-theorem `Fr.inverse` is the field inverse.
Both send `0` to `0`. -/
theorem inverse_eq_inv (a : Fr) : a.inverse = a⁻¹ :=
  inverse_eq_zmod_inv a

/-- The spec's division (`a * b.inverse`, registered at high priority
over core's `Fin` Nat-division) is field division. -/
theorem div_eq_mul_inv' (a b : Fr) : a / b = a * b⁻¹ := by
  show a * b.inverse = a * b⁻¹
  rw [inverse_eq_inv]

/-- `Fr`-facing form of `isPrimitiveRoot_seven_pow`, phrased with the
spec's own operations (`Fr.ofNat` and the `Fr`-exponent power): the root
`computeRootsOfUnity n` starts from is a primitive `n`-th root of
unity. -/
theorem isPrimitiveRoot_ofNat_seven_pow {n : Nat} (hn : n ∣ modulus - 1) :
    IsPrimitiveRoot (Fr.ofNat 7 ^ Fr.ofNat ((modulus - 1) / n)) n := by
  have hlt : (modulus - 1) / n < modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt Fr.modulus_pos Nat.one_pos)
  have hval : (Fr.ofNat ((modulus - 1) / n)).val = (modulus - 1) / n := by
    rw [ofNat, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt hlt
  rw [hpow_eq_pow, hval, ofNat_eq_natCast]
  exact isPrimitiveRoot_seven_pow hn

-- Smoke tests: the scoped field structure interoperates with the
-- globally available `Fin` instances the executable spec uses.
example (a b : Fr) : a * b = b * a := mul_comm a b
example (a b : Fr) : a - b = a + -b := sub_eq_add_neg a b
example (a : Fr) (h : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ h

end EthCryptographySpecs.Bls.Fr
