import EthCryptographySpecs.Bls.G1
import EthCryptographySpecs.Proofs.Bls.FpZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.Tactic.Module

/-!
# Proofs: the `G1` group structure

Bridges the spec's `G1` (Jacobian-coordinate points of `y² = x³ + 4`
over `Fp`, with Bernstein–Lange arithmetic) to Mathlib's
`WeierstrassCurve.Jacobian` machinery, which quotients nonsingular
Jacobian representatives by weighted scaling and carries a *proven*
`AddCommGroup` on the affine side.

* `curve` is `y² = x³ + 4` over `ZMod Fp.modulus` (all algebra here is
  phrased over `ZMod`, where `ring`/`linear_combination` work — see the
  instance notes in `Proofs.Bls.FrZMod`; `Fp` values cross over by
  definitional equality).
* `rep P = ![P.x, P.y, P.z]` is the Mathlib representative of a spec
  point; `Valid P` says it is nonsingular (in particular on the curve —
  for `P.z = 0` this pins the sentinel class `![1, 1, 0]`).
* `toPoint` maps a spec point to Mathlib's affine point group.
* `toPoint_zero`, `toPoint_neg`, `toPoint_double`, `toPoint_add` (and
  the `Valid` preservation lemmas) say the spec's arithmetic *is* the
  curve group law. The doubling formulas agree with Mathlib's
  `dblXYZ` on the nose; the addition formulas agree with `addXYZ` up to
  the weighted scaling `u = -(2·z₁·z₂)`, modulo the two curve
  equations.
-/

namespace EthCryptographySpecs.Bls.G1

open WeierstrassCurve (Jacobian)
open WeierstrassCurve.Jacobian

/-- The BLS12-381 curve `y² = x³ + 4`, as a Mathlib Weierstrass curve
in Jacobian coordinates over `ZMod Fp.modulus`. -/
def curve : Jacobian (ZMod Fp.modulus) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 4 }

/-- The Mathlib Jacobian representative of a spec point. -/
def rep (P : G1) : Fin 3 → ZMod Fp.modulus := ![P.x, P.y, P.z]

@[simp] theorem rep_x (P : G1) : rep P 0 = P.x := rfl
@[simp] theorem rep_y (P : G1) : rep P 1 = P.y := rfl
@[simp] theorem rep_z (P : G1) : rep P 2 = P.z := rfl

/-- Validity of a spec point: its representative is a nonsingular curve
point. Spec-produced points satisfy this (see the `valid_*` lemmas);
raw `G1.mk` triples need not. -/
def Valid (P : G1) : Prop := curve.Nonsingular (rep P)

/-- The group element a spec point denotes: the affine Mathlib point of
its representative. Total — singular representatives are sent to `0` —
but only meaningful on `Valid` points. -/
noncomputable def toPoint (P : G1) : curve.toAffine.Point :=
  WeierstrassCurve.Jacobian.Point.toAffine curve (rep P)

/-! ## Boolean-test bridges -/

theorem isZero_iff {a : Fp} : a.isZero = true ↔ (a : ZMod Fp.modulus) = 0 := by
  rw [Fp.isZero, beq_iff_eq]
  exact ZMod.val_eq_zero (n := Fp.modulus) a

theorem beq_iff {a b : Fp} : a.beq b = true ↔ (a : ZMod Fp.modulus) = b := by
  rw [Fp.beq, beq_iff_eq]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

/-! ## Zero and negation -/

theorem rep_zero : rep zero = ![1, 1, 0] := by
  funext i
  fin_cases i <;> rfl

theorem valid_zero : Valid zero := by
  rw [Valid, rep_zero]
  exact nonsingular_zero

theorem toPoint_zero : toPoint zero = 0 := by
  rw [toPoint, rep_zero]
  exact Point.toAffine_zero

/-- `negY` on our curve is plain negation (`a₁ = a₃ = 0`). Phrased over
honest `ZMod` binders so the algebra stays in `ring`-friendly land. -/
private theorem curve_negY (Q : Fin 3 → ZMod Fp.modulus) :
    curve.negY Q = -Q 1 := by
  rw [negY, show curve.a₁ = 0 from rfl, show curve.a₃ = 0 from rfl]
  ring

theorem rep_neg (P : G1) : rep (neg P) = curve.neg (rep P) := by
  funext i
  fin_cases i
  · rfl
  · show (-P.y : ZMod Fp.modulus) = curve.negY (rep P)
    rw [curve_negY]
    rfl
  · rfl

theorem valid_neg {P : G1} (h : Valid P) : Valid (neg P) := by
  rw [Valid, rep_neg]
  exact nonsingular_neg h

theorem toPoint_neg {P : G1} (h : Valid P) : toPoint (neg P) = -toPoint P := by
  rw [toPoint, rep_neg]
  exact Point.toAffine_neg h


/-! ## Doubling

The spec's Bernstein–Lange `dbl-2009-l` formulas coincide with
Mathlib's `dblXYZ` on our curve *on the nose* (scaling `u = 1`), as
pure polynomial identities — no curve equation needed. Each component
lemma is phrased over `ZMod` binders (so `ring` applies) with the
spec's exact let-expansion on the left; `rep_double` hands the spec
expressions over by definitional equality. -/

private theorem dblX_eq (x y z : ZMod Fp.modulus) :
    3 * (x * x) * (3 * (x * x))
        - 2 * (2 * ((x + y * y) * (x + y * y) - x * x - y * y * (y * y)))
      = curve.dblX ![x, y, z] := by
  rw [dblX, dblU_eq, curve_negY]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₄ = 0 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem dblY_eq (x y z : ZMod Fp.modulus) :
    3 * (x * x)
          * (2 * ((x + y * y) * (x + y * y) - x * x - y * y * (y * y))
            - (3 * (x * x) * (3 * (x * x))
              - 2 * (2 * ((x + y * y) * (x + y * y) - x * x
                - y * y * (y * y)))))
        - 8 * (y * y * (y * y))
      = curve.dblY ![x, y, z] := by
  rw [dblY, curve_negY]
  show _ = -curve.negDblY ![x, y, z]
  rw [negDblY, dblX, dblU_eq, curve_negY]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₄ = 0 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem dblZ_eq (x y z : ZMod Fp.modulus) :
    2 * y * z = curve.dblZ ![x, y, z] := by
  rw [dblZ, curve_negY]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem rep_double {P : G1} (hz : ¬P.z.isZero = true) :
    rep (double P) = curve.dblXYZ (rep P) := by
  funext i
  fin_cases i
  · show (double P).x = curve.dblX (rep P)
    rw [double, if_neg hz]
    exact dblX_eq P.x P.y P.z
  · show (double P).y = curve.dblY (rep P)
    rw [double, if_neg hz]
    exact dblY_eq P.x P.y P.z
  · show (double P).z = curve.dblZ (rep P)
    rw [double, if_neg hz]
    exact dblZ_eq P.x P.y P.z

theorem valid_double {P : G1} (h : Valid P) : Valid (double P) := by
  by_cases hz : P.z.isZero = true
  · rw [Valid, double, if_pos hz]
    exact h
  · rw [Valid, rep_double hz, ← add_of_equiv (Setoid.refl (rep P))]
    exact nonsingular_add h h

theorem toPoint_double {P : G1} (h : Valid P) :
    toPoint (double P) = toPoint P + toPoint P := by
  by_cases hz : P.z.isZero = true
  · have h0 : toPoint P = 0 :=
      Point.toAffine_of_Z_eq_zero (isZero_iff.mp hz)
    rw [double, show (if P.z.isZero = true then P else _) = P from if_pos hz]
    rw [h0, add_zero]
  · rw [toPoint, rep_double hz, ← add_of_equiv (Setoid.refl (rep P))]
    exact Point.toAffine_add h h

/-! ## Addition

The spec's Bernstein–Lange `add-2007-bl` formulas agree with Mathlib's
`addXYZ` up to the weighted Jacobian scaling `u = -(2·z₁·z₂)`, *modulo
the curve equations* of the two inputs (the `linear_combination`
coefficients below were computed symbolically). The special branches
(`z = 0`, doubling, opposite points) are handled through Mathlib's
equivalence lemmas at the affine level. -/

/-- The curve equation of a valid point, in `linear_combination`-ready
form (`y² = x³ + 4z⁶`), phrased over `rep` projections so every
operation is syntactically over `ZMod`. -/
private theorem valid_equation {P : G1} (h : Valid P) :
    rep P 1 ^ 2 = rep P 0 ^ 3 + 4 * rep P 2 ^ 6 := by
  have heq := ((nonsingular_iff (rep P)).mp h).1
  rw [equation_iff] at heq
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = (4 : ZMod Fp.modulus) from rfl] at heq
  linear_combination heq

/-- The three components of the spec's general-case addition, as
weighted scalings of Mathlib's `addXYZ`, modulo the two curve
equations. The intermediate values of the Bernstein–Lange formula are
*binders* pinned by defining equations: the caller instantiates them
with the spec's own subexpressions and discharges each equation by
(cheap, small) definitional equality, keeping the elaborator away from
one giant cross-instance comparison. The `linear_combination`
coefficients were computed symbolically and checked numerically. -/
private theorem spec_add_components
    (x1 y1 z1 x2 y2 z2 z11 z22 u1 u2 s1 s2 h i j r v xp : ZMod Fp.modulus)
    (hz11 : z11 = z1 * z1) (hz22 : z22 = z2 * z2)
    (hu1 : u1 = x1 * z22) (hu2 : u2 = x2 * z11)
    (hs1 : s1 = y1 * z2 * z22) (hs2 : s2 = y2 * z1 * z11)
    (hh : h = u2 - u1) (hi : i = 2 * h * (2 * h)) (hj : j = h * i)
    (hr : r = 2 * (s2 - s1)) (hv : v = u1 * i)
    (hxp : xp = r * r - j - 2 * v)
    (hP : y1 ^ 2 = x1 ^ 3 + 4 * z1 ^ 6) (hQ : y2 ^ 2 = x2 ^ 3 + 4 * z2 ^ 6) :
    xp = (-(2 * (z1 * z2))) ^ 2 * curve.addX ![x1, y1, z1] ![x2, y2, z2]
    ∧ r * (v - xp) - 2 * s1 * j
        = (-(2 * (z1 * z2))) ^ 3 * curve.addY ![x1, y1, z1] ![x2, y2, z2]
    ∧ ((z1 + z2) * (z1 + z2) - z11 - z22) * h
        = -(2 * (z1 * z2))
            * WeierstrassCurve.Jacobian.addZ ![x1, y1, z1] ![x2, y2, z2] := by
  subst hz11 hz22 hu1 hu2 hs1 hs2 hh hi hj hr hv hxp
  refine ⟨?_, ?_, ?_⟩
  · rw [addX]
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
      show curve.a₆ = (4 : ZMod Fp.modulus) from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination (4 * z2 ^ 6) * hP + (4 * z1 ^ 6) * hQ
  · rw [addY, curve_negY]
    show _ = (-(2 * (z1 * z2))) ^ 3
      * -curve.negAddY ![x1, y1, z1] ![x2, y2, z2]
    rw [negAddY]
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
      show curve.a₆ = (4 : ZMod Fp.modulus) from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination (8 * z2 ^ 6 * (y1 * z2 ^ 3 - y2 * z1 ^ 3)) * hP
      + (8 * z1 ^ 6 * (y1 * z2 ^ 3 - y2 * z1 ^ 3)) * hQ
  · rw [addZ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-! ### Branch extraction for `G1.add` -/

private theorem add_of_left_zero {P Q : G1} (hz1 : P.z.isZero = true) :
    add P Q = Q := by
  rw [add]
  exact if_pos hz1

private theorem add_of_right_zero {P Q : G1} (hz1 : ¬P.z.isZero = true)
    (hz2 : Q.z.isZero = true) : add P Q = P := by
  rw [add, if_neg hz1]
  exact if_pos hz2

private theorem add_of_dbl {P Q : G1} (hz1 : ¬P.z.isZero = true)
    (hz2 : ¬Q.z.isZero = true)
    (hu : (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true)
    (hs : (P.y * Q.z * (Q.z * Q.z)).beq (Q.y * P.z * (P.z * P.z)) = true) :
    add P Q = double P := by
  rw [add, if_neg hz1, if_neg hz2]
  exact (if_pos hu).trans (if_pos hs)

private theorem add_of_opp {P Q : G1} (hz1 : ¬P.z.isZero = true)
    (hz2 : ¬Q.z.isZero = true)
    (hu : (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true)
    (hs : ¬(P.y * Q.z * (Q.z * Q.z)).beq (Q.y * P.z * (P.z * P.z)) = true) :
    add P Q = zero := by
  rw [add, if_neg hz1, if_neg hz2]
  exact (if_pos hu).trans (if_neg hs)

private theorem rep_add_general {P Q : G1} (hP : Valid P) (hQ : Valid Q)
    (hz1 : ¬P.z.isZero = true) (hz2 : ¬Q.z.isZero = true)
    (hu : ¬(P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true) :
    rep (add P Q)
      = (-(2 * (rep P 2 * rep Q 2)))
          • curve.addXYZ (rep P) (rep Q) := by
  obtain ⟨hX, hY, hZ⟩ := spec_add_components P.x P.y P.z Q.x Q.y Q.z
    (P.z * P.z) (Q.z * Q.z) (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z))
    (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))
    (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))
    ((Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)))))
    (Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z))))
    ((P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)))))
    ((Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) * (Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) - ((Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))) - Fp.ofNat 2 * ((P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))))
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (valid_equation hP) (valid_equation hQ)
  have hbranch : add P Q = G1.mk
      ((Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) * (Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) - ((Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))) - Fp.ofNat 2 * ((P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))))
      ((Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) * (((P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))) - ((Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) * (Fp.ofNat 2 * ((Q.y * P.z * (P.z * P.z)) - (P.y * Q.z * (Q.z * Q.z)))) - ((Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))) - Fp.ofNat 2 * ((P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))))) - Fp.ofNat 2 * (P.y * Q.z * (Q.z * Q.z)) * ((Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z)) * (Fp.ofNat 2 * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))))))
      (((P.z + Q.z) * (P.z + Q.z) - (P.z * P.z) - (Q.z * Q.z)) * (Q.x * (P.z * P.z) - P.x * (Q.z * Q.z))) := by
    rw [add, if_neg hz1, if_neg hz2]
    exact if_neg hu
  rw [hbranch]
  funext k
  fin_cases k
  · exact hX.trans
      ((smul_fin3_ext (curve.addXYZ (rep P) (rep Q))
        (-(2 * (rep P 2 * rep Q 2)))).1).symm
  · exact hY.trans
      ((smul_fin3_ext (curve.addXYZ (rep P) (rep Q))
        (-(2 * (rep P 2 * rep Q 2)))).2.1).symm
  · exact hZ.trans
      ((smul_fin3_ext (curve.addXYZ (rep P) (rep Q))
        (-(2 * (rep P 2 * rep Q 2)))).2.2).symm

/-! ### The addition homomorphism -/

/-- The two `beq` branch conditions of `G1.add`, restated over `rep`
projections (definitionally equal, but with every operation
syntactically over `ZMod`, as `linear_combination` needs). -/
private theorem beq_x_iff {P Q : G1} :
    (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true
      ↔ rep P 0 * (rep Q 2 * rep Q 2) = rep Q 0 * (rep P 2 * rep P 2) :=
  beq_iff

private theorem beq_y_iff {P Q : G1} :
    (P.y * Q.z * (Q.z * Q.z)).beq (Q.y * P.z * (P.z * P.z)) = true
      ↔ rep P 1 * rep Q 2 * (rep Q 2 * rep Q 2)
          = rep Q 1 * rep P 2 * (rep P 2 * rep P 2) :=
  beq_iff

private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

/-- `P.z ≠ 0` in `ZMod` form. -/
private theorem z_ne_zero {P : G1} (hz : ¬P.z.isZero = true) :
    rep P 2 ≠ 0 := fun h => hz (isZero_iff.mpr h)

/-- The scaling unit of the general addition branch is a unit. -/
private theorem isUnit_scale {P Q : G1} (hz1 : ¬P.z.isZero = true)
    (hz2 : ¬Q.z.isZero = true) :
    IsUnit (-(2 * (rep P 2 * rep Q 2))) := by
  exact (neg_ne_zero.mpr (mul_ne_zero two_ne_zero'
    (mul_ne_zero (z_ne_zero hz1) (z_ne_zero hz2)))).isUnit

theorem valid_add {P Q : G1} (hP : Valid P) (hQ : Valid Q) :
    Valid (add P Q) := by
  by_cases hz1 : P.z.isZero = true
  · rwa [Valid, add_of_left_zero hz1]
  by_cases hz2 : Q.z.isZero = true
  · rwa [Valid, add_of_right_zero hz1 hz2]
  by_cases hu : (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true
  · by_cases hs : (P.y * Q.z * (Q.z * Q.z)).beq (Q.y * P.z * (P.z * P.z)) = true
    · rw [Valid, add_of_dbl hz1 hz2 hu hs]
      exact valid_double hP
    · rw [Valid, add_of_opp hz1 hz2 hu hs]
      exact valid_zero
  · rw [Valid, rep_add_general hP hQ hz1 hz2 hu]
    rw [nonsingular_smul _ (isUnit_scale hz1 hz2),
        ← add_of_not_equiv (fun heq => hu (beq_x_iff.mpr (by linear_combination X_eq_of_equiv heq)))]
    exact nonsingular_add hP hQ

theorem toPoint_add {P Q : G1} (hP : Valid P) (hQ : Valid Q) :
    toPoint (add P Q) = toPoint P + toPoint Q := by
  by_cases hz1 : P.z.isZero = true
  · rw [add_of_left_zero hz1,
      show toPoint P = 0 from Point.toAffine_of_Z_eq_zero (isZero_iff.mp hz1),
      zero_add]
  by_cases hz2 : Q.z.isZero = true
  · rw [add_of_right_zero hz1 hz2,
      show toPoint Q = 0 from Point.toAffine_of_Z_eq_zero (isZero_iff.mp hz2),
      add_zero]
  by_cases hu : (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true
  · -- Cross-multiplied X-coordinates agree.
    have hx : rep P 0 * rep Q 2 ^ 2 = rep Q 0 * rep P 2 ^ 2 := by
      linear_combination beq_x_iff.mp hu
    by_cases hs : (P.y * Q.z * (Q.z * Q.z)).beq (Q.y * P.z * (P.z * P.z)) = true
    · -- Same point: spec doubles, and `toPoint Q = toPoint P`.
      have hy : rep P 1 * rep Q 2 ^ 3 = rep Q 1 * rep P 2 ^ 3 := by
        linear_combination beq_y_iff.mp hs
      have hequiv : rep P ≈ rep Q :=
        equiv_of_X_eq_of_Y_eq (z_ne_zero hz1) (z_ne_zero hz2) hx hy
      rw [add_of_dbl hz1 hz2 hu hs, toPoint_double hP,
        show toPoint P = toPoint Q from Point.toAffine_of_equiv hequiv]
    · -- Opposite points: spec returns zero, and `toPoint Q = -toPoint P`.
      have hy : rep P 1 * rep Q 2 ^ 3 ≠ rep Q 1 * rep P 2 ^ 3 := fun heq =>
        hs (beq_y_iff.mpr (by linear_combination heq))
      have hyneg := Y_eq_of_Y_ne ((nonsingular_iff (rep P)).mp hP).1
        ((nonsingular_iff (rep Q)).mp hQ).1 hx hy
      have hequiv : rep P ≈ curve.neg (rep Q) := by
        refine equiv_of_X_eq_of_Y_eq (z_ne_zero hz1) ?_ ?_ ?_
        · show rep Q 2 ≠ 0
          exact z_ne_zero hz2
        · show rep P 0 * rep Q 2 ^ 2 = curve.neg (rep Q) 0 * rep P 2 ^ 2
          rw [neg_X]
          exact hx
        · show rep P 1 * rep Q 2 ^ 3 = curve.neg (rep Q) 1 * rep P 2 ^ 3
          rw [neg_Y]
          exact hyneg
      rw [add_of_opp hz1 hz2 hu hs, toPoint_zero,
        show toPoint P = -toPoint Q from (Point.toAffine_of_equiv hequiv).trans
          (Point.toAffine_neg hQ),
        neg_add_cancel]
  · -- General branch: the spec output is a unit scaling of `addXYZ`.
    have hne : ¬rep P ≈ rep Q := fun heq =>
      hu (beq_x_iff.mpr (by linear_combination X_eq_of_equiv heq))
    rw [toPoint, rep_add_general hP hQ hz1 hz2 hu]
    rw [Point.toAffine_of_equiv (smul_equiv _ (isUnit_scale hz1 hz2)),
        ← add_of_not_equiv hne]
    exact Point.toAffine_add hP hQ

/-! ### Scalar multiplication -/

theorem valid_mulNat {P : G1} (h : Valid P) (k : Nat) : Valid (mulNat P k) := by
  induction k using Nat.strongRecOn generalizing P with
  | _ k ih =>
    rw [mulNat_def]
    split
    · exact valid_zero
    · rename_i hk
      show Valid (if k % 2 = 1 then add P (mulNat (double P) (k / 2))
        else mulNat (double P) (k / 2))
      by_cases h2 : k % 2 = 1
      · rw [if_pos h2]
        exact valid_add h (ih (k / 2) (by omega) (valid_double h))
      · rw [if_neg h2]
        exact ih (k / 2) (by omega) (valid_double h)

/-- The spec's double-and-add scalar multiplication is Mathlib's `ℕ`
scalar action on the curve group. -/
theorem toPoint_mulNat {P : G1} (h : Valid P) (k : Nat) :
    toPoint (mulNat P k) = k • toPoint P := by
  induction k using Nat.strongRecOn generalizing P with
  | _ k ih =>
    rw [mulNat_def]
    split
    · rename_i hk
      subst hk
      rw [toPoint_zero]
      exact (zero_nsmul _).symm
    · rename_i hk
      show toPoint (if k % 2 = 1 then add P (mulNat (double P) (k / 2))
        else mulNat (double P) (k / 2)) = k • toPoint P
      by_cases h2 : k % 2 = 1
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
        have hm : (2 * m + 1) / 2 = m := by omega
        rw [if_pos h2, toPoint_add h (valid_mulNat (valid_double h) _), hm,
            ih m (by omega) (valid_double h), toPoint_double h]
        module
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
        have hm : 2 * m / 2 = m := by omega
        rw [if_neg h2, hm, ih m (by omega) (valid_double h), toPoint_double h]
        module

/-- The spec's `Fr`-scalar multiplication acts through the scalar's
value. -/
theorem toPoint_mul {P : G1} (h : Valid P) (s : Fr) :
    toPoint (mul P s) = s.val • toPoint P :=
  toPoint_mulNat h s.val

theorem valid_mul {P : G1} (h : Valid P) (s : Fr) : Valid (mul P s) :=
  valid_mulNat h s.val

end EthCryptographySpecs.Bls.G1
