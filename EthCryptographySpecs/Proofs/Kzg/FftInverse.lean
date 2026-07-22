import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Proofs.Kzg.Fft
import EthCryptographySpecs.Proofs.Bls.FrZMod
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Proofs: the FFT round-trip `IFFT (FFT x) = x`

This file works towards the correctness of the number-theoretic transform
in `Kzg/Fft.lean`: for a vector `x` of length `n = 2 ^ k` and a table of
roots of unity `roots[i] = ω ^ i` with `ω` a primitive `n`-th root, the
inverse transform recovers the input,

    fftField (fftField x roots false) roots true = x

    and

    fftField (fftField x roots true) roots false = x

The argument/file has three parts:

* **Orthogonality** (`geom_sum_root_ne_one`, `sum_pow_mul`): the geometric
  sum of the powers of an `n`-th root of unity is `n` when the root is `1`
  and `0` otherwise. This is the algebraic reason interpolation inverts
  evaluation.
* **DFT characterisation** (`getElem_fftFieldAux`): the Cooley–Tukey
  recursion computes the discrete Fourier transform
  `y[j] = ∑ i, x[i] * ω ^ (i * j)`. Proved by strong induction on `k`
  using the even/odd split `sum_range_split_even_odd`.
* **Round-trip** (`fftField_fftField_inv` and `fftField_inv_fftField`)

Uses the scoped `Field Fr` instance from `Proofs.Bls.FrZMod`.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)
open EthCryptographySpecs.Kzg.Constants
open scoped EthCryptographySpecs.Bls.Fr

-- See the note in `Proofs.Bls.FrZMod`: core's grind-tactic `HPow`
-- instance on `Fin` shadows Mathlib's monoid power on `Fr` and breaks
-- `rw` with Mathlib `pow` lemmas. File-local, so repeated here.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-! ## Even/odd splitting of a range sum -/

/-- A sum over `range (2 * m)` splits into its even- and odd-indexed
parts. The backbone of the Cooley–Tukey induction. -/
theorem sum_range_split_even_odd {M : Type*} [AddCommMonoid M]
    (m : Nat) (f : Nat → M) :
    ∑ i ∈ Finset.range (2 * m), f i
      = (∑ i ∈ Finset.range m, f (2 * i))
        + ∑ i ∈ Finset.range m, f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
    -- rearrange (E + O) + f(2m) + f(2m+1) = (E + f(2m)) + (O + f(2m+1))
    abel

/-! ## Orthogonality of roots of unity

These are stated generically over an arbitrary `Field F`. Proving them
abstractly (rather than directly on `Fr`) avoids the instance-diamond
friction that arises when Mathlib's group/field `rw` lemmas meet `Fr`'s
`Fin`-derived structure; we instantiate at `F := Fr` where the round-trip
needs them. -/

section Orthogonality

variable {F : Type*} [Field F]

/-- The geometric sum of the powers of a root of unity that is not `1`
vanishes: if `c ^ n = 1` and `c ≠ 1` then `∑_{j < n} c ^ j = 0`. -/
theorem geom_sum_root_ne_one {c : F} {n : Nat} (hcn : c ^ n = 1)
    (hc : c ≠ 1) : ∑ j ∈ Finset.range n, c ^ j = 0 := by
  rw [geom_sum_eq hc n, hcn, sub_self, zero_div]

/-- The geometric sum of the powers of `1`. -/
theorem geom_sum_one (n : Nat) :
    ∑ j ∈ Finset.range n, (1 : F) ^ j = (n : F) := by
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]

/-- Orthogonality relation. For `ω` a primitive `n`-th root of unity and
`a b < n`, the sum `∑_{j < n} (ω ^ a * (ω⁻¹) ^ b) ^ j` is `n` when
`a = b` and `0` otherwise. This is the exact shape produced by composing
the forward transform (root `ω`) with the inverse transform (root
`ω⁻¹`). -/
theorem sum_pow_orthogonal {ω : F} {n : Nat} (hω : IsPrimitiveRoot ω n)
    {a b : Nat} (ha : a < n) (hb : b < n) :
    ∑ j ∈ Finset.range n, (ω ^ a * (ω⁻¹) ^ b) ^ j
      = if a = b then (n : F) else 0 := by
  have hunit : ω ≠ 0 := hω.ne_zero (by omega)
  have hane : ω ^ a ≠ 0 := pow_ne_zero a hunit
  have hbne : ω ^ b ≠ 0 := pow_ne_zero b hunit
  have hinv : (ω⁻¹) ^ n = 1 := by rw [inv_pow, hω.pow_eq_one, inv_one]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hc1 : ω ^ a * (ω⁻¹) ^ a = 1 := by
      rw [inv_pow, mul_inv_cancel₀ hane]
    rw [hc1, geom_sum_one]
  · rw [if_neg hab]
    have hcn : (ω ^ a * (ω⁻¹) ^ b) ^ n = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a n,
          Nat.mul_comm b n, pow_mul, pow_mul, hω.pow_eq_one, hinv,
          one_pow, one_pow, mul_one]
    have hc1 : ω ^ a * (ω⁻¹) ^ b ≠ 1 := by
      rw [inv_pow]
      intro h
      exact hab (hω.pow_inj ha hb ((mul_inv_eq_one₀ hbne).mp h))
    exact geom_sum_root_ne_one hcn hc1

/-- A primitive `2 * m`-th root of unity, raised to the `m`, is `-1`:
its square is `1` but it is not `1`, and in a field the only other
square root of `1` is `-1`. Used for the odd-half sign flip in the
Cooley–Tukey butterfly. -/
theorem pow_half_eq_neg_one {ω : F} {m : Nat} (hm : 0 < m)
    (hω : IsPrimitiveRoot ω (2 * m)) : ω ^ m = -1 := by
  have hsq : ω ^ m * ω ^ m = 1 := by
    rw [← pow_add, ← two_mul, hω.pow_eq_one]
  have hne : ω ^ m ≠ 1 := hω.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hne
  · exact h

end Orthogonality

/-- `getElem!` form of `getElem_fftHalve`: for `i` in range, `fftHalve`
selects element `start + 2 * i`. -/
theorem getElem!_fftHalve (xs : Array Fr) (start i : Nat)
    (h : i < xs.size / 2) :
    (fftHalve xs start)[i]! = xs[start + 2 * i]! := by
  rw [getElem!_pos (fftHalve xs start) i (by rw [size_fftHalve]; exact h),
      getElem_fftHalve]

/-! ## One step of the Cooley–Tukey recursion

`getElem_fftFieldAux_step` reads off a single output element of
`fftFieldAux` in the recursive (`1 < size`) case as the butterfly
combination of the even/odd sub-transforms. Isolating the `Array.ofFn`
unfolding keeps the DFT induction below purely algebraic. -/

theorem getElem_fftFieldAux_step (vals roots : Array Fr)
    (hsz : 1 < vals.size) (p : Nat) (hp : p < vals.size) :
    (fftFieldAux vals roots)[p]! =
      (if p < vals.size / 2
        then (fftFieldAux (fftHalve vals 0) (fftHalve roots 0))[p]!
              + (fftFieldAux (fftHalve vals 1) (fftHalve roots 0))[p]!
                * roots[p]!
        else (fftFieldAux (fftHalve vals 0) (fftHalve roots 0))[p - vals.size / 2]!
              - (fftFieldAux (fftHalve vals 1) (fftHalve roots 0))[p - vals.size / 2]!
                * roots[p - vals.size / 2]!) := by
  -- Fold the two sub-transforms so the RHS holds no bare `fftFieldAux`
  -- application; `rw [fftFieldAux]` then unambiguously unfolds the LHS.
  set l := fftFieldAux (fftHalve vals 0) (fftHalve roots 0) with hl
  set r := fftFieldAux (fftHalve vals 1) (fftHalve roots 0) with hr
  rw [fftFieldAux, if_neg (by omega : ¬ vals.size ≤ 1)]
  rw [getElem!_pos _ p (by simpa using hp)]
  -- reduce the `let`s, apply `Array.getElem_ofFn`, and refold the
  -- sub-transforms
  simp only [Array.getElem_ofFn, ← hl, ← hr]
  -- `l.size = vals.size / 2`, so both `if` conditions and the base index
  -- agree; splitting on the condition collapses the inner `if`s.
  have hlsize : l.size = vals.size / 2 := by
    rw [hl, size_fftFieldAux, size_fftHalve]
  rw [hlsize]
  split <;> rfl

/-! ## `Fr` algebra bridges

`Fr` carries two definitionally-equal but syntactically-distinct sets of
algebraic operations: the executable spec's (inherited from `Fin`) and
Mathlib's scoped `Field` structure. `rw` needs syntactic agreement, and
the terms produced by `fftFieldAux`/`getElem_fftFieldAux_step` use the
spec's `*`, `1`, `-`. These bridges restate the Mathlib rewrite lemmas
with the spec's operations (the proof term supplies the Mathlib lemma,
type-checked across the definitional gap), so the DFT proof can rewrite
without ever mixing the two instance families. -/

private theorem fr_pow_zero (a : Fr) : a ^ 0 = 1 := pow_zero a
private theorem fr_pow_add (a : Fr) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := pow_add a m n
private theorem fr_one_pow (n : Nat) : (1 : Fr) ^ n = 1 := one_pow n
private theorem fr_mul_one (a : Fr) : a * 1 = a := mul_one a
private theorem fr_mul_neg (a b : Fr) : a * -b = -(a * b) := mul_neg a b
private theorem fr_mul_pow (a b : Fr) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n :=
  mul_pow a b n
private theorem fr_pow_mul (a : Fr) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n :=
  pow_mul a m n
private theorem fr_mul_right_comm (a b c : Fr) : a * b * c = a * c * b :=
  mul_right_comm a b c

/-! ## The forward transform computes the DFT

`fftFieldAux vals roots`, with `roots[i] = ω ^ i` for a primitive
`2 ^ k`-th root `ω`, evaluates the polynomial with coefficients `vals`
at the powers of `ω`: output `j` is `∑ i, vals[i] * ω ^ (i * j)`. Proved
by strong induction on `k` via the butterfly step lemma and the even/odd
split, using that `ω ^ 2` is a primitive `2 ^ (k-1)`-th root and
`ω ^ 2 ^ (k-1) = -1`. -/

theorem getElem!_fftFieldAux_dft {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i)
    (j : Nat) (hj : j < 2 ^ k) :
    (fftFieldAux vals roots)[j]!
      = ∑ i ∈ Finset.range (2 ^ k), vals[i]! * ω ^ (i * j) := by
  induction k generalizing ω vals roots j with
  | zero =>
    simp only [pow_zero] at hn hj hroots ⊢
    rw [fftFieldAux, if_pos (by omega : vals.size ≤ 1)]
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Finset.sum_range_one, Nat.zero_mul, fr_pow_zero, fr_mul_one]
  | succ k ih =>
    have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hhalf : vals.size / 2 = 2 ^ k := by rw [hn, h2]; omega
    have hsz : 1 < vals.size := by rw [hn, h2]; omega
    have hω2 : IsPrimitiveRoot (ω ^ 2) (2 ^ k) :=
      hω.pow (Nat.two_pow_pos (k + 1)) h2
    have hpow1 : ω ^ (2 ^ (k + 1)) = 1 := hω.pow_eq_one
    have hneg : ω ^ (2 ^ k) = -1 := pow_half_eq_neg_one hpk (h2 ▸ hω)
    -- sub-array shapes and the sub-transform's roots table
    have hsize0 : (fftHalve vals 0).size = 2 ^ k := by rw [size_fftHalve, hhalf]
    have hsize1 : (fftHalve vals 1).size = 2 ^ k := by rw [size_fftHalve, hhalf]
    have hsizeR : (fftHalve roots 0).size = 2 ^ k := by
      rw [size_fftHalve, hrs, h2]; omega
    have hroots2 : ∀ i, i < 2 ^ k → (fftHalve roots 0)[i]! = (ω ^ 2) ^ i := by
      intro i hi
      rw [getElem!_fftHalve roots 0 i (by rw [hrs, h2]; omega), Nat.zero_add,
          hroots (2 * i) (by rw [h2]; omega), ← pow_mul]
    -- even/odd sub-transforms, via the induction hypothesis
    have hl : ∀ q, q < 2 ^ k →
        (fftFieldAux (fftHalve vals 0) (fftHalve roots 0))[q]!
          = ∑ i ∈ Finset.range (2 ^ k), vals[2 * i]! * ω ^ (2 * i * q) := by
      intro q hq
      rw [ih hω2 (fftHalve vals 0) (fftHalve roots 0) hsize0 hsizeR hroots2 q hq]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [getElem!_fftHalve vals 0 i (by rw [hhalf]; exact hi), Nat.zero_add,
          ← pow_mul, Nat.mul_assoc]
    have hr : ∀ q, q < 2 ^ k →
        (fftFieldAux (fftHalve vals 1) (fftHalve roots 0))[q]!
          = ∑ i ∈ Finset.range (2 ^ k), vals[2 * i + 1]! * ω ^ (2 * i * q) := by
      intro q hq
      rw [ih hω2 (fftHalve vals 1) (fftHalve roots 0) hsize1 hsizeR hroots2 q hq]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [getElem!_fftHalve vals 1 i (by rw [hhalf]; exact hi),
          show (1 : Nat) + 2 * i = 2 * i + 1 by ring, ← pow_mul, Nat.mul_assoc]
    -- unfold one butterfly step, then split the target sum
    rw [getElem_fftFieldAux_step vals roots hsz j (by rw [hn]; exact hj), hhalf,
        show (2 : Nat) ^ (k + 1) = 2 * 2 ^ k from h2,
        sum_range_split_even_odd (2 ^ k) (fun i => vals[i]! * ω ^ (i * j))]
    by_cases hjk : j < 2 ^ k
    · -- top half: output = l[j] + r[j] * ω ^ j
      rw [if_pos hjk, hl j hjk, hr j hjk, hroots j (by rw [h2]; omega)]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Bls.Fr.mul_assoc, ← fr_pow_add,
          show (2 * i + 1) * j = 2 * i * j + j by ring]
    · -- bottom half: output = l[q] - r[q] * ω ^ q with q = j - 2 ^ k
      rw [if_neg hjk]
      set q := j - 2 ^ k with hqdef
      have hjq : j = q + 2 ^ k := by omega
      have hq2 : q < 2 ^ k := by omega
      have hEven :
          (∑ i ∈ Finset.range (2 ^ k), vals[2 * i]! * ω ^ (2 * i * j))
            = ∑ i ∈ Finset.range (2 ^ k), vals[2 * i]! * ω ^ (2 * i * q) :=
        Finset.sum_congr rfl (fun i hi => by
          rw [show 2 * i * j = 2 * i * q + 2 ^ (k + 1) * i by rw [hjq, h2]; ring,
              fr_pow_add, pow_mul ω (2 ^ (k + 1)) i, hpow1, fr_one_pow, fr_mul_one])
      have hOdd :
          (∑ i ∈ Finset.range (2 ^ k), vals[2 * i + 1]! * ω ^ ((2 * i + 1) * j))
            = (∑ i ∈ Finset.range (2 ^ k), vals[2 * i + 1]! * ω ^ (2 * i * q))
                * (-ω ^ q) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [show (2 * i + 1) * j = 2 * i * q + q + 2 ^ (k + 1) * i + 2 ^ k by
              rw [hjq, h2]; ring,
            fr_pow_add, hneg, fr_pow_add, pow_mul ω (2 ^ (k + 1)) i, hpow1,
            fr_one_pow, fr_mul_one, fr_pow_add, fr_mul_neg, fr_mul_one,
            ← fr_mul_neg, ← Bls.Fr.mul_assoc]
      rw [hl q hq2, hr q hq2, hroots q (by rw [h2]; omega), hEven, hOdd, fr_mul_neg]
      abel

/-! ## The inverse transform inverts the forward transform

`fftField _ _ true` reverses the root table (turning `ω` into `ω⁻¹`) and
divides by `n`; composing it after `fftField _ _ false` recovers the
input. The proof characterises both directions with the DFT lemma and
collapses the resulting double sum with `sum_pow_orthogonal`. -/

/-- Indexing into `Array.map (· * c)`. -/
private theorem getElem!_map_mul (arr : Array Fr) (c : Fr) (m : Nat)
    (h : m < arr.size) : (arr.map (· * c))[m]! = arr[m]! * c := by
  rw [getElem!_pos (arr.map (· * c)) m (by rw [Array.size_map]; exact h),
      Array.getElem_map, ← getElem!_pos arr m h]

/-- The reversed root table used by the inverse transform is the root
table for `ω⁻¹`: element `i` is `(ω⁻¹) ^ i`. -/
private theorem getElem!_reversedRoots {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k)) (roots : Array Fr) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i) (i : Nat) (hi : i < 2 ^ k) :
    (Array.ofFn (n := roots.size) fun j : Fin roots.size =>
        if j.val = 0 then roots[0]! else roots[roots.size - j.val]!)[i]!
      = (ω⁻¹) ^ i := by
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; rw [hrs]; exact hi),
      Array.getElem_ofFn]
  by_cases hi0 : i = 0
  · subst hi0
    simp [hroots 0 (Nat.two_pow_pos k)]
  · rw [if_neg (by simpa using hi0),
        hroots (roots.size - i) (by rw [hrs]; omega), inv_pow]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, Nat.sub_add_cancel (by rw [hrs]; omega : i ≤ roots.size), hrs]
    exact hω.pow_eq_one

/-- `Fr`-form of `sum_pow_orthogonal`: the DFT orthogonality relation with
the exponents split as `a * j` and `b * j`, matching the double sum that
arises when composing the two transforms. -/
private theorem sum_pow_orthogonal_fr {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k)) {a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    ∑ j ∈ Finset.range (2 ^ k), ω ^ (a * j) * (ω⁻¹) ^ (b * j)
      = if a = b then ((2 ^ k : Nat) : Fr) else 0 := by
  rw [show (∑ j ∈ Finset.range (2 ^ k), ω ^ (a * j) * (ω⁻¹) ^ (b * j))
        = ∑ j ∈ Finset.range (2 ^ k), (ω ^ a * (ω⁻¹) ^ b) ^ j from
      Finset.sum_congr rfl (fun j _ => by
        rw [fr_mul_pow, ← fr_pow_mul, ← fr_pow_mul])]
  exact sum_pow_orthogonal hω ha hb

/-- **FFT round-trip.** For a length-`2 ^ k` vector `vals` and a root
table `roots[i] = ω ^ i` with `ω` a primitive `2 ^ k`-th root of unity,
the inverse transform recovers the input. This is the correctness of
NTT-based interpolation: evaluating a polynomial on the roots of unity
and interpolating back is the identity. -/
theorem fftField_fftField_inv {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i) :
    fftField (fftField vals roots false) roots true = vals := by
  have hωinv : IsPrimitiveRoot ω⁻¹ (2 ^ k) := hω.inv
  -- `n = 2 ^ k` is invertible in `Fr`
  have hnz : Fr.ofNat (2 ^ k) ≠ 0 := by
    rw [Bls.Fr.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_two]
    exact pow_ne_zero k (by decide)
  set y := fftField vals roots false with hy
  have hysize : y.size = 2 ^ k := by rw [hy, size_fftField, hn]
  -- forward transform: y[j] = ∑ i, vals[i] * ω ^ (i * j)
  have hyval : ∀ j, j < 2 ^ k →
      y[j]! = ∑ i ∈ Finset.range (2 ^ k), vals[i]! * ω ^ (i * j) := by
    intro j hj
    rw [hy, fftField]
    exact getElem!_fftFieldAux_dft hω vals roots hn hrs hroots j hj
  -- element-wise: composing recovers `vals[m]`
  apply Array.ext
  · rw [size_fftField, size_fftField]
  · intro m h1 _
    have hm : m < 2 ^ k := by
      rw [size_fftField, size_fftField, hn] at h1; exact h1
    rw [← getElem!_pos _ m h1, ← getElem!_pos vals m (by rw [hn]; exact hm)]
    -- unfold the inverse transform
    rw [hy] at hysize ⊢
    conv_lhs => rw [fftField]
    simp only [if_pos]
    rw [getElem!_map_mul _ _ m (by rw [size_fftFieldAux, ← hy, hysize]; exact hm)]
    -- DFT of the inverse direction over the reversed (ω⁻¹) roots
    rw [getElem!_fftFieldAux_dft hωinv (fftField vals roots false) _ (by
          rw [size_fftField, hn]) (by rw [Array.size_ofFn, hrs])
        (getElem!_reversedRoots hω roots hrs hroots) m hm]
    -- substitute the forward transform for each y[j]
    rw [← hy]
    conv_lhs =>
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [hyval j (Finset.mem_range.mp hj)])]
    -- collapse the double sum with orthogonality
    have hinner : ∀ i, i < 2 ^ k →
        (∑ j ∈ Finset.range (2 ^ k), ω ^ (i * j) * (ω⁻¹) ^ (j * m))
          = if i = m then ((2 ^ k : Nat) : Fr) else 0 := by
      intro i hi
      rw [← sum_pow_orthogonal_fr hω hi hm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Nat.mul_comm m j])
    have hcollapse :
        (∑ j ∈ Finset.range (2 ^ k),
            (∑ i ∈ Finset.range (2 ^ k), vals[i]! * ω ^ (i * j)) * (ω⁻¹) ^ (j * m))
          = vals[m]! * ((2 ^ k : Nat) : Fr) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [Bls.Fr.mul_assoc, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [hinner i (Finset.mem_range.mp hi)])]
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' (Finset.range (2 ^ k)) m
            (fun i => vals[i]! * ((2 ^ k : Nat) : Fr)),
          if_pos (Finset.mem_range.mpr hm)]
    rw [hcollapse]
    -- cancel the `1 / n` normalisation: `n * n⁻¹ = 1`
    have hn0 : ((2 ^ k : Nat) : Fr) ≠ 0 := by
      rw [← Bls.Fr.ofNat_eq_natCast]; exact hnz
    rw [show (Fr.ofNat y.size).inverse = ((2 ^ k : Nat) : Fr)⁻¹ from by
          rw [hy, size_fftField, hn, Bls.Fr.inverse_eq_inv,
              Bls.Fr.ofNat_eq_natCast],
        Bls.Fr.mul_assoc,
        show ((2 ^ k : Nat) : Fr) * ((2 ^ k : Nat) : Fr)⁻¹ = 1 from
          mul_inv_cancel₀ hn0]
    exact fr_mul_one _

/-- **FFT round-trip, the other order.** Applying the forward transform
after the inverse transform is also the identity. Same ingredients as
`fftField_fftField_inv`, with the two directions swapped: the inverse
transform (root `ω⁻¹`, scaled by `1 / n`) runs first, the forward
transform (root `ω`) second. -/
theorem fftField_inv_fftField {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i) :
    fftField (fftField vals roots true) roots false = vals := by
  have hωinv : IsPrimitiveRoot ω⁻¹ (2 ^ k) := hω.inv
  have hnz : Fr.ofNat (2 ^ k) ≠ 0 := by
    rw [Bls.Fr.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_two]
    exact pow_ne_zero k (by decide)
  have hn0 : ((2 ^ k : Nat) : Fr) ≠ 0 := by
    rw [← Bls.Fr.ofNat_eq_natCast]; exact hnz
  -- inverse transform: y[j] = (∑ i, vals[i] * (ω⁻¹) ^ (i * j)) / n
  have hyval : ∀ j, j < 2 ^ k →
      (fftField vals roots true)[j]!
        = (∑ i ∈ Finset.range (2 ^ k), vals[i]! * (ω⁻¹) ^ (i * j))
            * (Fr.ofNat vals.size).inverse := by
    intro j hj
    conv_lhs => rw [fftField]
    simp only [if_pos]
    rw [getElem!_map_mul _ _ j (by rw [size_fftFieldAux, hn]; exact hj),
        getElem!_fftFieldAux_dft hωinv vals _ hn (by rw [Array.size_ofFn]; exact hrs)
          (getElem!_reversedRoots hω roots hrs hroots) j hj]
  -- element-wise
  apply Array.ext
  · rw [size_fftField, size_fftField]
  · intro m h1 _
    have hm : m < 2 ^ k := by
      rw [size_fftField, size_fftField, hn] at h1; exact h1
    rw [← getElem!_pos _ m h1, ← getElem!_pos vals m (by rw [hn]; exact hm)]
    -- forward transform (the `false` branch is definitionally `fftFieldAux`)
    show (fftFieldAux (fftField vals roots true) roots)[m]! = vals[m]!
    rw [getElem!_fftFieldAux_dft hω (fftField vals roots true) roots
          (by rw [size_fftField, hn]) hrs hroots m hm]
    -- substitute the inverse transform for each entry
    conv_lhs =>
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [hyval j (Finset.mem_range.mp hj)])]
    -- orthogonality (roles of the two indices swapped vs. the other order)
    have hinner : ∀ i, i < 2 ^ k →
        (∑ j ∈ Finset.range (2 ^ k), (ω⁻¹) ^ (i * j) * ω ^ (j * m))
          = if m = i then ((2 ^ k : Nat) : Fr) else 0 := by
      intro i hi
      rw [← sum_pow_orthogonal_fr hω hm hi]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [Bls.Fr.mul_comm ((ω⁻¹) ^ (i * j)) (ω ^ (j * m)), Nat.mul_comm j m])
    have hcollapse :
        (∑ j ∈ Finset.range (2 ^ k),
            (∑ i ∈ Finset.range (2 ^ k), vals[i]! * (ω⁻¹) ^ (i * j)) * ω ^ (j * m))
          = vals[m]! * ((2 ^ k : Nat) : Fr) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [Bls.Fr.mul_assoc, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [hinner i (Finset.mem_range.mp hi)])]
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq (Finset.range (2 ^ k)) m
            (fun i => vals[i]! * ((2 ^ k : Nat) : Fr)),
          if_pos (Finset.mem_range.mpr hm)]
    -- factor the `1 / n` out of the sum, collapse, then cancel
    have hrw :
        (∑ j ∈ Finset.range (2 ^ k),
            (∑ i ∈ Finset.range (2 ^ k), vals[i]! * (ω⁻¹) ^ (i * j))
              * (Fr.ofNat vals.size).inverse * ω ^ (j * m))
          = (∑ j ∈ Finset.range (2 ^ k),
              (∑ i ∈ Finset.range (2 ^ k), vals[i]! * (ω⁻¹) ^ (i * j)) * ω ^ (j * m))
              * (Fr.ofNat vals.size).inverse := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => fr_mul_right_comm _ _ _)
    rw [hrw, hcollapse]
    -- (vals[m]! * n) * n⁻¹ = vals[m]!
    rw [show (Fr.ofNat vals.size).inverse = ((2 ^ k : Nat) : Fr)⁻¹ from by
          rw [hn, Bls.Fr.inverse_eq_inv, Bls.Fr.ofNat_eq_natCast],
        Bls.Fr.mul_assoc,
        show ((2 ^ k : Nat) : Fr) * ((2 ^ k : Nat) : Fr)⁻¹ = 1 from
          mul_inv_cancel₀ hn0]
    exact fr_mul_one _

end EthCryptographySpecs.Kzg
